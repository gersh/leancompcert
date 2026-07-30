/* Reference for the R2* residue: the fold [Ramare--Zuniga Alterman 2024,
 * Lemma 6.2] reduces to.
 *
 * The reduced family (claude_math, MathExtras/NumberTheory/Reductions/
 * FiniteCiteFloorReductions.lean, RamareZunigaLemma62NatFamily) is
 *
 *   forall 3 <= n <= 2.1e10,   |R2*(n)| <= 1.93 * sqrt(n) * log(n),
 *
 * with (MathExtras/NumberTheory/Mertens/RamareEq22.lean)
 *
 *   R2*(N) = sum_{k<=N} [ (Lambda*Lambda)(k) - Lambda(k) log k + 2 gamma ].
 *
 * The convolution collapses to a *classification*:
 *
 *   k = p^a          ->  -log^2 p
 *   k = p^a q^b      ->  +2 log p log q
 *   omega(k) >= 3    ->   nothing
 *
 * so R2*(N) = 2 gamma N - sum_{p^a<=N} log^2 p + 2 sum_{p^a q^b<=N} log p log q.
 * Evaluating it needs a FACTORISATION sieve, not a primality sieve: per cell
 * the number of distinct primes, both of their logarithms, and whether a
 * prime factor above sqrt(hi) is left over.
 *
 * This file is the oracle for LeanCompCert/Ports/R2SegSieve.lean: the same
 * three planes (prod, lsum, W), the same packing, the same four modes, the
 * same fixed point, so the two agree bit for bit on every slot.  It is an
 * independent implementation of the same algorithm, not a copy of the
 * artifact: the artifact is a straight-line branchless AProgram compiled
 * through the proved fragment, this is ordinary C with branches and loops.
 *
 * THE LOGARITHM.  logFix below is the algorithm proved in
 * LeanCompCert/Verified/LogFixed.lean: normalise n to a 62-bit mantissa
 * (exact), then square S times, emitting one bit of log2 per round.  The
 * proved bracket is
 *
 *     2^logFix(S,n) <= n^(2^S) < 2^(logFix(S,n) + 2),
 *
 * two units in the last place; two more come from the conversion to natural
 * logarithm, so lnFix undershoots 2^S*ln n by at most 4 ulps.  A jump is a
 * PRODUCT of two such values, so it is off by at most 2*4*(log p + log q) <=
 * 16*log n ulps; the running budget `err` is incremented by
 * 16*(floor(log2 n)+1)*ln2 + 2 per test point and is added to both clause
 * tests, so a clean run bounds the real R2* and not merely its image.
 *
 * ONE 64-BIT WORD IS ENOUGH, unlike psi.  |R2*| <= 6.7e6 over the whole
 * range, so 2^24 * |R2*| <= 1.1e14 and the biased accumulator 2^48 + 2^S R2*
 * never leaves [1.7e14, 3.9e14].  S is capped from above instead: a jump is a
 * 64x64 product of two lnFix values, so (2^S log hi)^2 < 2^64 forces S <= 27.
 *
 *   cc -O2 -o ref_r2 bench/ref_r2.c -lm
 *   ./ref_r2 LO HI SEGLEN
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#define S        24
#define B62      UINT64_C(4611686018427387904)
#define B63      UINT64_C(9223372036854775808)
/* floor(2^64 * ln 2) */
#define L2       UINT64_C(12786308645202655659)
/* 2^(S+24), the accumulator's bias */
#define BIAS     UINT64_C(281474976710656)
/* floor(2 gamma * 2^S), ceil(2^S ln 2), floor(1.93 * 2^16) */
#define GSTEP    UINT64_C(19368143)
#define LN2UP    UINT64_C(11629080)
#define A193     UINT64_C(126484)

#define VALBITS  35
#define WTBITS   28
#define MASKWT   ((UINT64_C(1) << WTBITS) - 1)

/* ---------------------------------------------------------------- logFix */

/* floor(x^2 / 2^62) for x < 2^63, by the half-limb split of Verified.LogFixed
 * (no 128-bit type is used, so the file is portable to compilers that lack
 * one -- ccomp has __int128 but the artifact never needs it). */
static uint64_t sq62(uint64_t x)
{
    uint64_t x1 = x >> 32, x0 = x & UINT64_C(0xffffffff);
    uint64_t hi = x1 * x1, mid = x1 * x0, lo = x0 * x0;
    uint64_t carry = ((mid & UINT64_C(0x1fffffff)) * UINT64_C(8589934592)
                      + (lo & (B62 - 1))) >= B62;
    return 4 * hi + (mid >> 29) + (lo >> 62) + carry;
}

/* floor(2^S * log2 n), n >= 1 */
static uint64_t logFix(uint64_t n)
{
    int e = 63;
    while (((n >> e) & 1) == 0) e--;             /* e = floor(log2 n) */
    uint64_t x = n << (62 - e), a = 0;
    for (int k = 0; k < S; k++) {
        uint64_t y = sq62(x);
        uint64_t b = (y >= B63);
        a = 2 * a + b;
        x = y >> b;
    }
    return ((uint64_t)e << S) + a;
}

/* floor(2^S * ln n) minus at most 4 ulps: the high word of logFix * L2 */
static uint64_t lnFix(uint64_t n)
{
    uint64_t f = logFix(n);
    uint64_t flo = f & UINT64_C(0xffffffff), fhi = f >> 32;
    uint64_t l2lo = L2 & UINT64_C(0xffffffff), l2hi = L2 >> 32;
    uint64_t mid = flo * l2hi + fhi * l2lo + ((flo * l2lo) >> 32);
    return fhi * l2hi + (mid >> 32);
}

/* ------------------------------------------------------------ mark table */

typedef struct { uint64_t q, w; int first; } Entry;

static Entry *table;
static long   tablen;

static void build_table(uint64_t hi)
{
    uint64_t root = (uint64_t)sqrtl((long double)hi);
    while ((root + 1) * (root + 1) <= hi) root++;
    while (root * root > hi) root--;
    char *sieve = calloc(root + 2, 1);
    long cap = 1024;
    table = malloc(cap * sizeof(Entry));
    tablen = 0;
    for (uint64_t p = 2; p <= root; p++) {
        if (sieve[p]) continue;
        for (uint64_t m = p * p; m <= root; m += p) sieve[m] = 1;
        uint64_t w = lnFix(p), q = p;
        int first = 1;
        while (q <= hi) {
            if (tablen == cap) { cap *= 2; table = realloc(table, cap * sizeof(Entry)); }
            table[tablen].q = q; table[tablen].w = w; table[tablen].first = first;
            tablen++;
            first = 0;
            if (q > hi / p) break;
            q *= p;
        }
    }
    free(sieve);
}

/* -------------------------------------------------------------- the fold */

static uint64_t D, err, terms, prev, sq, sq2, ex, th, lnlo, thr, viol;
static double   worst;
static uint64_t worst_n;

/* apply one test point: n, mode, and the two factors of the jump */
static void jump(uint64_t n, int mode, uint64_t u, uint64_t v, uint64_t lnn)
{
    while (n >= th) { ex++; th *= 2; }
    if (n - prev >= 65536) viol++;
    D += GSTEP * (n - prev - 1);
    if (D + err + n > BIAS + thr) {
        viol++;
        fprintf(stderr, "clause 1 fails at n=%llu\n", (unsigned long long)n);
    }
    D += GSTEP;
    while (n >= sq2) { sq++; sq2 = (sq + 1) * (sq + 1); }
    if (mode < 2) lnlo = lnn;
    thr = (A193 * sq * lnlo) >> 16;
    uint64_t t = (u * v) << (mode & 1) >> S;
    if (mode & 1) D += t; else D -= t;
    err += (((ex + 1) * LN2UP) >> (S - 4)) + 2;
    terms++;
    if (D + thr < BIAS + err) {
        viol++;
        fprintf(stderr, "clause 2 fails at n=%llu\n", (unsigned long long)n);
    }
    prev = n;
    double r = fabs((double)(int64_t)(D - BIAS)) / (double)(UINT64_C(1) << S)
             / (sqrt((double)n) * log((double)n));
    if (r > worst) { worst = r; worst_n = n; }
}

/* the head [1, lo-1], by trial division, with both clauses tested at *every*
 * integer -- the artifact's prev-based clause 1 is too coarse at the bottom
 * of the range, where floor(sqrt n) is */
static void head(uint64_t top, uint64_t root)
{
    D = BIAS; err = terms = prev = 0; sq = 0; sq2 = 1; ex = 0; th = 2;
    lnlo = thr = viol = 0; worst = 0; worst_n = 0;
    for (uint64_t n = 1; n <= top; n++) {
        D += GSTEP;
        while (n >= sq2) { sq++; sq2 = (sq + 1) * (sq + 1); }
        while (n >= th)  { ex++; th *= 2; }
        uint64_t m = n, ps[8]; int np = 0;
        for (uint64_t d = 2; d * d <= m && np < 8; d++)
            if (m % d == 0) { ps[np++] = d; while (m % d == 0) m /= d; }
        if (m > 1 && np < 8) ps[np++] = m;
        if (np == 1 || np == 2) {
            uint64_t u, v; int mode;
            if (np == 1) {
                mode = (ps[0] > root) ? 0 : 2;
                u = v = (mode == 0) ? lnFix(n) : lnFix(ps[0]);
            } else if (ps[1] > root) {
                uint64_t a = 0, t = n;
                while (t % ps[0] == 0) { t /= ps[0]; a++; }
                mode = 1; u = lnFix(ps[0]); v = lnFix(n) - lnFix(ps[0]) * a;
            } else {
                mode = 3; u = lnFix(ps[0]); v = lnFix(ps[1]);
            }
            uint64_t t = (u * v) << (mode & 1) >> S;
            if (mode & 1) D += t; else D -= t;
            err += (((ex + 1) * LN2UP) >> (S - 4)) + 2;
            terms++;
            prev = n;
        }
        lnlo = lnFix(n);
        thr = (A193 * sq * lnlo) >> 16;
        if (n >= 3) {
            if (D + err + n > BIAS + thr) {
                viol++; fprintf(stderr, "head clause 1 fails at n=%llu\n",
                                (unsigned long long)n);
            }
            if (D + thr < BIAS + err) {
                viol++; fprintf(stderr, "head clause 2 fails at n=%llu\n",
                                (unsigned long long)n);
            }
            double r = fabs((double)(int64_t)(D - BIAS))
                     / (double)(UINT64_C(1) << S)
                     / (sqrt((double)n) * log((double)n));
            if (r > worst) { worst = r; worst_n = n; }
        }
    }
}

int main(int argc, char **argv)
{
    uint64_t lo = argc > 1 ? strtoull(argv[1], 0, 10) : 1001;
    uint64_t hi = argc > 2 ? strtoull(argv[2], 0, 10) : 1000000;
    uint64_t L  = argc > 3 ? strtoull(argv[3], 0, 10) : 100000;

    uint64_t root = (uint64_t)sqrtl((long double)hi);
    while ((root + 1) * (root + 1) <= hi) root++;
    while (root * root > hi) root--;
    if (lo <= root) { fprintf(stderr, "LO must exceed floor(sqrt HI)=%llu\n",
                              (unsigned long long)root); return 1; }
    build_table(hi);

    head(lo - 1, root);
    fprintf(stderr, "head [1,%llu]: D=%llu err=%llu terms=%llu prev=%llu "
            "sq=%llu ex=%llu ln=%llu thr=%llu viol=%llu\n",
            (unsigned long long)(lo - 1), (unsigned long long)D,
            (unsigned long long)err, (unsigned long long)terms,
            (unsigned long long)prev, (unsigned long long)sq,
            (unsigned long long)ex, (unsigned long long)lnlo,
            (unsigned long long)thr, (unsigned long long)viol);

    uint64_t *prod = malloc(L * sizeof(uint64_t));
    uint64_t *lsum = malloc(L * sizeof(uint64_t));
    uint64_t *W    = malloc(L * sizeof(uint64_t));
    uint64_t maxstream = 0, logrounds = 0;

    for (uint64_t w = lo; w <= hi; w += L) {
        uint64_t top = w + L - 1; if (top > hi) top = hi;
        uint64_t len = top - w + 1;
        memset(prod, 0, len * sizeof(uint64_t));
        memset(lsum, 0, len * sizeof(uint64_t));
        memset(W,    0, len * sizeof(uint64_t));
        uint64_t basep = 0;
        for (long e = 0; e < tablen; e++) {
            uint64_t q = table[e].q, wt = table[e].w;
            if (table[e].first) basep = q;
            uint64_t start = (q - w % q) % q;
            for (uint64_t i = start; i < len; i += q) {
                prod[i] = (prod[i] ? prod[i] : 1) * basep;
                lsum[i] += wt;
                if (table[e].first) {
                    uint64_t d = W[i] >> 56, add = 0;
                    if (d == 0)      add += wt;
                    else if (d == 1) add += wt << WTBITS;
                    if (d < 3)       add += UINT64_C(1) << 56;
                    W[i] += add;
                }
            }
        }
        uint64_t stream = 0;
        for (uint64_t i = 0; i < len; i++) {
            uint64_t n = w + i;
            uint64_t pr = prod[i] ? prod[i] : 1;
            int big = (pr != n);
            uint64_t d = W[i] >> 56;
            uint64_t w1 = W[i] & MASKWT, w2 = (W[i] >> WTBITS) & MASKWT;
            int mode = -1;
            if (d == 0 && big)       mode = 0;
            else if (d == 1 && big)  mode = 1;
            else if (d == 1 && !big) mode = 2;
            else if (d == 2 && !big) mode = 3;
            if (mode < 0) continue;
            stream++;
            logrounds += (mode < 2) ? S : 1;
            uint64_t aux = (mode == 3) ? w2 : lsum[i];
            uint64_t lnn = (mode < 2) ? lnFix(n) : 0;
            uint64_t lq  = lnn - aux;
            uint64_t u, v;
            switch (mode) {
                case 0:  u = lq; v = lq;  break;
                case 1:  u = w1; v = lq;  break;
                case 2:  u = w1; v = w1;  break;
                default: u = w1; v = aux; break;
            }
            jump(n, mode, u, v, lnn);
        }
        if (stream > maxstream) maxstream = stream;
    }
    D += GSTEP * (hi - prev);
    if (D + err + hi > BIAS + thr) {
        viol++; fprintf(stderr, "final clause 1 fails at hi\n");
    }

    printf("lo %llu\nhi %llu\nseglen %llu\ntable %ld\n",
           (unsigned long long)lo, (unsigned long long)hi,
           (unsigned long long)L, tablen);
    printf("slot0 %llu\nslot1 %llu\nslot2 %llu\nslot3 %llu\nslot4 %llu\n"
           "slot5 %llu\nslot6 %llu\nslot7 %llu\nslot8 %llu\nslot9 %llu\n",
           (unsigned long long)D, (unsigned long long)err,
           (unsigned long long)prev, (unsigned long long)terms,
           (unsigned long long)sq, (unsigned long long)ex,
           (unsigned long long)th, (unsigned long long)lnlo,
           (unsigned long long)thr, (unsigned long long)viol);
    printf("R2star %.6f\nenclosure %.6f\nworst_ratio %.6f\nworst_n %llu\n",
           (double)(int64_t)(D - BIAS) / (double)(UINT64_C(1) << S),
           (double)err / (double)(UINT64_C(1) << S), worst,
           (unsigned long long)worst_n);
    printf("maxstream %llu\nlogrounds %llu\n",
           (unsigned long long)maxstream, (unsigned long long)logrounds);
    return 0;
}
