/* Reference for the psi residue: the fold [CH25, Lemma 9.2] reduces to.
 *
 * The reduced family (claude_math, MathExtras/NumberTheory/Reductions/
 * StepMinusLinearReductions.lean, ChirreHelfgottLemma92NatFamily) is
 *
 *   (1)  forall 1 <= n <= 1e13,      (psi(n) - n)/sqrt(n)       <= 0.79059276
 *   (2)  forall 1 <= n, n+1 <= 1e13, (psi(n) - (n+1))/sqrt(n+1) >= -sqrt(2)
 *   (3)  strict form of (2) at n = 1e13.
 *
 * psi is a step function that increases only at prime powers, so between
 * consecutive prime powers (psi(n)-n)/sqrt(n) strictly decreases: clause (1)
 * is worst immediately *after* a jump and clause (2) immediately *before* the
 * next one.  Both test sets are therefore indexed by prime powers, not by
 * integers -- 3.46e11 test points rather than 1e13 -- and both tests live in
 * the log phase, which visits exactly those points.
 *
 * THE LOGARITHM.  Per prime power q = p^k, Lambda(q) = log p is needed at
 * fixed point.  logFix below is the algorithm proved in
 * LeanCompCert/Verified/LogFixed.lean: normalise p to a 62-bit mantissa
 * (exact), then square S times, emitting one bit of log2 per round.  The
 * proved bracket is
 *
 *     2^logFix(S,p) <= p^(2^S) < 2^(logFix(S,p) + 2),
 *
 * i.e. two units in the last place, and it *multiplies*, so summing over a
 * list of prime powers gives an enclosure of 2^S*log2(prod) whose width is
 * exactly two ulps per term.  One further ulp comes from the conversion to
 * natural logarithm (a multiply by floor(2^64 * ln 2)) and one from that
 * constant's own truncation, so the per-term window used here is 4 ulps.
 *
 * THE ACCUMULATOR IS 128-BIT, AND HAS TO BE.  In residual form
 * D(n) = sum lnFix - 2^S*n the family itself bounds |D| by 2^S*sqrt(2)*sqrt(n),
 * which at n=1e13 caps a single u64 at S <= 40; the enclosure width there is
 * 4*pi*(1e13)/2^40 = 1.26 absolute, i.e. 4.0e-7 in the ratio the family prints
 * to eight decimals.  Meeting the <=1e-8 margin of 0.79059276 needs S >= 45.4.
 * See bench/results/psi_fold.md for the full table.  S = 48 with a two-word
 * accumulator gives 1.6e-9 and is what this file uses.
 *
 *   cc -O2 -o ref_psi bench/ref_psi.c -lm
 *   ./ref_psi LO HI SEGLEN
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define S        48
#define B32      UINT64_C(4294967296)
#define B29      UINT64_C(536870912)
#define B62      UINT64_C(4611686018427387904)
#define B63      UINT64_C(9223372036854775808)
/* floor(2^64 * ln 2) */
#define L2       UINT64_C(12786308645202655659)
/* floor(0.79059276 * 2^48) and ceil(sqrt(2) * 2^48) */
#define C_UP     UINT64_C(222532078708613)
#define C_DOWN   UINT64_C(398065729532861)
/* per-term enclosure width, in ulps of 2^-S */
#define ULP      4

/* floor(x^2 / 2^62) in 32-bit halves: exactly Verified/LogFixed.sq62. */
static inline uint64_t sq62(uint64_t x)
{
    uint64_t x1 = x >> 32, x0 = x & (B32 - 1);
    uint64_t hi = x1 * x1, mid = x1 * x0, lo = x0 * x0;
    uint64_t s  = (mid & (B29 - 1)) * UINT64_C(8589934592) + (lo & (B62 - 1));
    return 4 * hi + (mid >> 29) + (lo >> 62) + (s >= B62 ? 1 : 0);
}

/* floor(2^S * log2 n), to within two ulps: Verified/LogFixed.logFix. */
static uint64_t logFix(uint64_t n)
{
    int e = 63 - __builtin_clzll(n);          /* Nat.log2 n */
    uint64_t x = n << (62 - e);               /* exact: n < 2^(e+1) */
    uint64_t a = 0;
    for (int i = 0; i < S; i++) {
        uint64_t y = sq62(x);
        uint64_t b = (y >= B63) ? 1 : 0;
        x = y >> b;
        a = 2 * a + b;
    }
    return ((uint64_t)e << S) + a;
}

/* floor(2^S * ln n): one 64x64->128 multiply by floor(2^64 ln 2). */
static inline uint64_t lnFix(uint64_t n)
{
    return (uint64_t)(((unsigned __int128)logFix(n) * L2) >> 64);
}

/* floor(sqrt(n)), for the per-test thresholds. */
static uint64_t isqrt(uint64_t n)
{
    uint64_t r = (uint64_t)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

int main(int argc, char **argv)
{
    if (argc < 4) { fprintf(stderr, "usage: LO HI SEGLEN [TESTFROM]\n"); return 2; }
    uint64_t lo = strtoull(argv[1], 0, 10);
    uint64_t hi = strtoull(argv[2], 0, 10);
    uint64_t L  = strtoull(argv[3], 0, 10);
    uint64_t tf = (argc > 4) ? strtoull(argv[4], 0, 10) : lo;

    uint64_t root = 1;
    while ((root + 1) * (root + 1) <= hi) root++;
    char *isc = calloc(root + 2, 1);
    for (uint64_t d = 2; d <= root; d++)
        if (!isc[d]) for (uint64_t m = d * d; m <= root; m += d) isc[m] = 1;
    uint64_t np = 0;
    for (uint64_t d = 2; d <= root; d++) if (!isc[d]) np++;
    uint64_t *pr = malloc(np * sizeof(uint64_t));
    uint64_t k = 0;
    for (uint64_t d = 2; d <= root; d++) if (!isc[d]) pr[k++] = d;

    /* Prime powers p^j <= hi with j >= 2, in increasing order.  Each carries
     * Lambda(p^j) = log p, so its fixed-point weight is lnFix(p), not
     * lnFix(p^j).  There are 228 871 of them below 1e13 in all; they must sit
     * at their exact positions, because deferring a segment's worth to the
     * segment end biases psi by about 240 at n = 1e13 against a 0.03 budget. */
    uint64_t ppn = 0, ppcap = 1 << 12;
    uint64_t *ppv = malloc(ppcap * sizeof(uint64_t)), *ppw = malloc(ppcap * sizeof(uint64_t));
    for (uint64_t t = 0; t < np; t++) {
        unsigned __int128 q = (unsigned __int128)pr[t] * pr[t];
        while (q <= hi) {
            if (q >= 1) {
                if (ppn == ppcap) {
                    ppcap *= 2;
                    ppv = realloc(ppv, ppcap * sizeof(uint64_t));
                    ppw = realloc(ppw, ppcap * sizeof(uint64_t));
                }
                ppv[ppn] = (uint64_t)q; ppw[ppn] = lnFix(pr[t]); ppn++;
            }
            q *= pr[t];
        }
    }
    /* insertion by value */
    for (uint64_t i = 1; i < ppn; i++) {
        uint64_t v = ppv[i], w = ppw[i], j = i;
        while (j && ppv[j-1] > v) { ppv[j] = ppv[j-1]; ppw[j] = ppw[j-1]; j--; }
        ppv[j] = v; ppw[j] = w;
    }

    unsigned char *comp = malloc(L);
    /* Carry-in: the run must start at 1 for D to mean what it says. */
    __int128 D = 0;                 /* 2^S * (psi(prev) - prev), lower end */
    uint64_t prev = lo - 1;         /* psi(lo-1) = 0, so the run starts at 1 */
    uint64_t terms = 0;             /* enclosure width = ULP * terms   */
    uint64_t nprimes = 0, viol1 = 0, viol2 = 0;
    uint64_t ppi = 0;
    double worst1 = -1e9, worst2 = 1e9; uint64_t worst1n = 0, worst2n = 0;
    uint64_t s = isqrt(lo ? lo - 1 : 0), s2 = (s + 1) * (s + 1);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (uint64_t w = lo; w <= hi; w += L) {
        uint64_t top = (w + L - 1 < hi) ? w + L - 1 : hi;
        uint64_t len = top + 1 - w;
        memset(comp, 0, len);
        for (uint64_t t = 0; t < np; t++) {
            uint64_t p = pr[t];
            uint64_t first = (p - w % p) % p + w;   /* first multiple >= w */
            if (first < p * p) first = p * p;       /* never cross p itself */
            for (uint64_t m = first; m <= top; m += p) comp[m - w] = 1;
        }
        /* One pass over the window's cells; the test points are exactly the
         * primes and the prime powers, merged in increasing order. */
        for (uint64_t i = 0; i < len; i++) {
            uint64_t n = w + i;
            int isprime = (n >= 2) && !comp[i];
            int ispp = (ppi < ppn) && (ppv[ppi] == n);
            if (!isprime && !ispp) continue;

            /* s = floor(sqrt(n)), maintained incrementally */
            while (n >= s2) { s++; s2 = (s + 1) * (s + 1); }

            /* Advance the residual to n: D is now 2^S*(psi(n-1) - n). */
            D -= ((__int128)(n - prev)) << S;
            prev = n;
            /* clause (2) at n-1, just before the jump.  D is the *lower* end
             * of the enclosure, which is the safe side for a lower bound. */
            if (n >= tf && D < -(__int128)C_DOWN * (__int128)s) {
                if (viol2 < 8) fprintf(stderr, "  viol2 at n=%llu\n",
                                       (unsigned long long)n);
                viol2++;
            }
            if (n >= tf) { double r = (double)(long double)D
                         / (double)((__int128)1 << S) / sqrt((double)n);
              if (r < worst2) { worst2 = r; worst2n = n; } }
            D += (__int128)(ispp ? ppw[ppi] : lnFix(n));
            terms++;
            if (isprime) nprimes++;
            if (ispp) ppi++;
            /* clause (1) at n, after the jump: psi(n) - n <= 0.79059276*sqrt(n) */
            {
                __int128 upper = D + (__int128)(ULP * terms);
                __int128 thr = (__int128)C_UP * (__int128)s;
                if (n >= tf && upper > thr) {
                    if (viol1 < 8) fprintf(stderr, "  viol1 at n=%llu\n",
                                           (unsigned long long)n);
                    viol1++;
                }
                double r = (double)(long double)upper
                           / (double)((__int128)1 << S) / sqrt((double)n);
                if (n >= tf && r > worst1) { worst1 = r; worst1n = n; }
            }
        }
    }
    D -= ((__int128)(hi - prev)) << S;
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    uint64_t span = hi - lo + 1;

    double psi = (double)(long double)D / (double)((__int128)1 << S) + (double)hi;
    printf("range        [%llu, %llu]\n", (unsigned long long)lo, (unsigned long long)hi);
    printf("primes       %llu\n", (unsigned long long)nprimes);
    printf("primepowers  %llu\n", (unsigned long long)ppi);
    printf("terms        %llu\n", (unsigned long long)terms);
    printf("D            %lld\n", (long long)D);
    printf("psi(hi)      %.6f\n", psi);
    printf("psi(hi)-hi   %.6f\n", psi - (double)hi);
    printf("ratio        %.10f\n", (psi - (double)hi) / sqrt((double)hi));
    printf("width_abs    %.6g\n", (double)(ULP * terms) / (double)((__int128)1 << S));
    printf("width_ratio  %.6g\n",
           (double)(ULP * terms) / (double)((__int128)1 << S) / sqrt((double)hi));
    printf("worst1       %.10f at n=%llu\n", worst1, (unsigned long long)worst1n);
    printf("worst2       %.10f at n=%llu\n", worst2, (unsigned long long)worst2n);
    printf("viol1        %llu\n", (unsigned long long)viol1);
    printf("viol2        %llu\n", (unsigned long long)viol2);
    printf("secs         %.4f\n", secs);
    printf("ns/integer   %.3f\n", 1e9 * secs / (double)span);
    return (viol1 || viol2) ? 1 : 0;
}
