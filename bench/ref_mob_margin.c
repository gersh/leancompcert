/* Exact margin oracle for Platt's stronger rigorously-computed range.
 *
 *   sigma(n) = sum_{m<=n} mu(m)/m,   claim  |sigma(n)| <= 1/(2 sqrt(n+1)),
 * which is clause 1 of PlattStrongerRangeNatFamily, for 3 <= n <= 7727068586.
 *
 * The artifact accumulates the fixed-point image
 *
 *   A_S(n) = sum_{m<=n} mu(m) * round(2^S / m),   |A_S(n) - 2^S sigma(n)| <= n/2,
 *
 * and tests  |A_S(n)| + budget <= floor(2^(S-1)/ceil(sqrt(n+1))).  This program computes
 * A_92 (a reference so fine that its own rounding budget, n/2^93 = 7.8e-19, is
 * four orders below anything that matters), together with A_62 and A_78 -- the
 * two scales the artifact can actually carry -- and evaluates, at *every*
 * integer, the per-integer test each scale would run.  It therefore answers
 * three separate questions with one sweep:
 *
 *   1. the true margin  1/(2 sqrt(n+1)) - |sigma(n)|  at every n, exactly;
 *   2. the first n at which the S = 62 per-integer test fails;
 *   3. the first n at which the S = 78 per-integer test fails -- and hence
 *      whether widening the accumulator reaches Platt's stated endpoint.
 *
 * round(2^S/m) without a 128/64 division: 2^S = 2^(S-63) * 2^63, so with
 * q1 = floor(2^63/m), r1 = 2^63 mod m,
 *
 *   2^S/m = 2^(S-63) q1 + (2^(S-63) r1)/m,
 *
 * and 2^(S-63) r1 < 2^(S-63) m <= 2^(S-63+33) stays inside 64 bits for every
 * S <= 92 on this range (m < 2^33).  Two 64-bit divisions, no 128-bit one.
 *
 * The sieve is the standard segmented product decoding: cell j accumulates the
 * product of the primes p <= sqrt(N) dividing lo+j, a parity bit, and a
 * "p^2 divides" bit; mu is 0 when squarefull, and otherwise -1^(parity + [prod
 * != n]), the last term catching the one prime factor above sqrt(N).
 *
 * Two passes, both OpenMP-parallel over segments: the first accumulates each
 * segment's own delta, the second re-runs each segment from the prefix-summed
 * carry-in and evaluates the tests.  Nothing is serial but the prefix sum.
 *
 *   cc -O2 -fopenmp -o ref_mob_margin bench/ref_mob_margin.c -lm
 *   ./ref_mob_margin [N] [REPORT_LO] [REPORT_HI]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef __int128 i128;
typedef unsigned __int128 u128;

#define SEGBITS 20
#define SEGLEN  (1u << SEGBITS)

static uint64_t N;             /* last integer swept */
static uint64_t REPLO, REPHI;  /* per-integer report window */

static uint32_t *sp;           /* sieving primes <= sqrt(N) */
static uint32_t spn;

static void build_primes(uint64_t n)
{
    uint64_t r = (uint64_t)sqrtl((long double)n) + 2;
    while (r * r > n) r--;
    char *c = calloc(r + 1, 1);
    for (uint64_t i = 2; i * i <= r; i++)
        if (!c[i]) for (uint64_t j = i * i; j <= r; j += i) c[j] = 1;
    spn = 0;
    for (uint64_t i = 2; i <= r; i++) if (!c[i]) spn++;
    sp = malloc(sizeof(uint32_t) * spn);
    uint32_t k = 0;
    for (uint64_t i = 2; i <= r; i++) if (!c[i]) sp[k++] = (uint32_t)i;
    free(c);
}

/* mu over [lo, lo+len), written as -1/0/1 into out */
static void seg_mu(uint64_t lo, uint32_t len, uint64_t *prod, uint8_t *fl,
                   int8_t *out)
{
    for (uint32_t i = 0; i < len; i++) { prod[i] = 1; fl[i] = 0; }
    for (uint32_t k = 0; k < spn; k++) {
        uint64_t p = sp[k];
        uint64_t first = ((lo + p - 1) / p) * p;
        if (first < p) first = p;              /* never mark the prime 0/1 cell */
        for (uint64_t m = first; m < lo + len; m += p) {
            uint32_t i = (uint32_t)(m - lo);
            prod[i] *= p;
            fl[i] ^= 1;
        }
        uint64_t pp = p * p;
        if (pp < lo + len) {
            uint64_t f2 = ((lo + pp - 1) / pp) * pp;
            for (uint64_t m = f2; m < lo + len; m += pp) fl[(uint32_t)(m - lo)] |= 2;
        }
    }
    for (uint32_t i = 0; i < len; i++) {
        uint64_t n = lo + i;
        if (n == 0) { out[i] = 0; continue; }
        if (fl[i] & 2) { out[i] = 0; continue; }
        uint32_t par = (fl[i] & 1) ^ (prod[i] != n ? 1u : 0u);
        out[i] = par ? -1 : 1;
    }
}

/* round(2^S/m) for S in {62, 78, 92}, from one shared 2^63 division */
static inline void weights(uint64_t m, uint64_t *w62, i128 *w78, i128 *w92)
{
    const uint64_t two63 = (uint64_t)1 << 63;
    uint64_t q1 = two63 / m, r1 = two63 % m;
    /* S = 62: a single 64-bit division, round to nearest */
    *w62 = (((uint64_t)1 << 62) + m / 2) / m;
    /* S = 78 */
    { uint64_t t = r1 << 15, q2 = t / m, r2 = t % m;
      *w78 = ((i128)q1 << 15) + q2 + (2 * r2 >= m ? 1 : 0); }
    /* S = 92 */
    { uint64_t t = r1 << 29, q2 = t / m, r2 = t % m;
      *w92 = ((i128)q1 << 29) + q2 + (2 * r2 >= m ? 1 : 0); }
}

typedef struct { i128 d62, d78, d92; } Delta;

typedef struct {
    uint64_t viol62, viol78;
    uint64_t first62, first78;   /* 0 = none */
    long double minmar62, minmar78; /* min (margin / budget) ratio */
    uint64_t argmin62, argmin78;
    long double mintrue;         /* min of 1/(2 sqrt n) - |sigma| over n>=3 */
    uint64_t argmintrue;
} Stat;

int main(int argc, char **argv)
{
    N     = argc > 1 ? strtoull(argv[1], 0, 10) : 7727068600ull;
    REPLO = argc > 2 ? strtoull(argv[2], 0, 10) : 7727068500ull;
    REPHI = argc > 3 ? strtoull(argv[3], 0, 10) : N;

    build_primes(N);
    uint64_t nseg = (N + SEGLEN) / SEGLEN;   /* segments cover [0, nseg*SEGLEN) */
    fprintf(stderr, "N=%llu primes=%u segments=%llu\n",
            (unsigned long long)N, spn, (unsigned long long)nseg);

    Delta *dl = calloc(nseg, sizeof(Delta));

    /* ---- pass 1: each segment's own delta ---- */
#pragma omp parallel
    {
        uint64_t *prod = malloc(sizeof(uint64_t) * SEGLEN);
        uint8_t  *fl   = malloc(SEGLEN);
        int8_t   *mu   = malloc(SEGLEN);
#pragma omp for schedule(dynamic, 4)
        for (long long s = 0; s < (long long)nseg; s++) {
            uint64_t lo = (uint64_t)s * SEGLEN;
            uint32_t len = SEGLEN;
            if (lo + len > N + 1) len = (uint32_t)(N + 1 - lo);
            seg_mu(lo, len, prod, fl, mu);
            i128 a62 = 0, a78 = 0, a92 = 0;
            for (uint32_t i = 0; i < len; i++) {
                uint64_t n = lo + i;
                if (n == 0 || mu[i] == 0) continue;
                uint64_t w62; i128 w78, w92;
                weights(n, &w62, &w78, &w92);
                if (mu[i] > 0) { a62 += (i128)w62; a78 += w78; a92 += w92; }
                else           { a62 -= (i128)w62; a78 -= w78; a92 -= w92; }
            }
            dl[s].d62 = a62; dl[s].d78 = a78; dl[s].d92 = a92;
        }
        free(prod); free(fl); free(mu);
    }

    /* ---- prefix sum ---- */
    Delta *carry = calloc(nseg, sizeof(Delta));
    { i128 a62 = 0, a78 = 0, a92 = 0;
      for (uint64_t s = 0; s < nseg; s++) {
          carry[s].d62 = a62; carry[s].d78 = a78; carry[s].d92 = a92;
          a62 += dl[s].d62; a78 += dl[s].d78; a92 += dl[s].d92;
      } }

    /* ---- pass 2: per-integer tests ---- */
    Stat g;
    memset(&g, 0, sizeof g);
    g.minmar62 = g.minmar78 = 1e30L; g.mintrue = 1e30L;

    FILE *rep = fopen("bench/results/mob_margin_report.txt", "w");

#pragma omp parallel
    {
        uint64_t *prod = malloc(sizeof(uint64_t) * SEGLEN);
        uint8_t  *fl   = malloc(SEGLEN);
        int8_t   *mu   = malloc(SEGLEN);
        Stat l; memset(&l, 0, sizeof l);
        l.minmar62 = l.minmar78 = 1e30L; l.mintrue = 1e30L;
#pragma omp for schedule(dynamic, 4)
        for (long long s = 0; s < (long long)nseg; s++) {
            uint64_t lo = (uint64_t)s * SEGLEN;
            uint32_t len = SEGLEN;
            if (lo + len > N + 1) len = (uint32_t)(N + 1 - lo);
            seg_mu(lo, len, prod, fl, mu);
            i128 a62 = carry[s].d62, a78 = carry[s].d78, a92 = carry[s].d92;
            /* c = ceil(sqrt(n+1)) evaluated at n = lo-1, i.e. ceil(sqrt lo),
               clamped to >= 1 so the division is defined */
            uint64_t prev = lo;
            uint64_t c = (uint64_t)sqrtl((long double)prev);
            while (c && c * c > prev) c--;
            while (c * c < prev) c++;          /* now c = ceil(sqrt(lo)) */
            if (c == 0) c = 1;
            uint64_t thr = ((uint64_t)1 << 61) / c;
            for (uint32_t i = 0; i < len; i++) {
                uint64_t n = lo + i;
                if (n == 0) continue;
                if (mu[i] != 0) {
                    uint64_t w62; i128 w78, w92;
                    weights(n, &w62, &w78, &w92);
                    if (mu[i] > 0) { a62 += (i128)w62; a78 += w78; a92 += w92; }
                    else           { a62 -= (i128)w62; a78 -= w78; a92 -= w92; }
                }
                if (n >= c * c) { c++; thr = ((uint64_t)1 << 61) / c; }
                if (n < 3) continue;
                /* S = 62, per-integer: |A62| + ceil(n/2) <= floor(2^61/c) */
                i128 abs62 = a62 < 0 ? -a62 : a62;
                u128 lhs62 = (u128)abs62 + (u128)((n + 1) / 2);
                int bad62 = !(lhs62 <= (u128)thr);
                /* S = 78, shifted to scale 2^62: V = floor(A78/2^16),
                   |V| + ceil(n/2^17) + 1 <= floor(2^61/c) */
                i128 V = a78 >> 16;
                i128 absV = V < 0 ? -V : V;
                u128 lhs78 = (u128)absV + (u128)((n + 131071) >> 17) + 1;
                int bad78 = !(lhs78 <= (u128)thr);
                if (bad62) { l.viol62++; if (!l.first62 || n < l.first62) l.first62 = n; }
                if (bad78) { l.viol78++; if (!l.first78 || n < l.first78) l.first78 = n; }
                /* margins, as a ratio of the scale's own budget */
                long double sig = (long double)a92 / 4951760157141521099596496896.0L; /* 2^92 */
                long double maj = 0.5L / sqrtl((long double)(n + 1));
                long double tru = maj - (sig < 0 ? -sig : sig);
                long double b62 = (long double)n / 9223372036854775808.0L;   /* n/2^63 */
                long double b78 = (long double)n / 604462909807314587353088.0L; /* n/2^79 */
                if (tru / b62 < l.minmar62) { l.minmar62 = tru / b62; l.argmin62 = n; }
                if (tru / b78 < l.minmar78) { l.minmar78 = tru / b78; l.argmin78 = n; }
                if (tru < l.mintrue) { l.mintrue = tru; l.argmintrue = n; }
                if (bad78 && n < 7727068587ull)
#pragma omp critical
                    fprintf(stderr, "S=78 test fails at n=%llu (true margin %.6Le)\n",
                            (unsigned long long)n, tru);
                if (n >= REPLO && n <= REPHI && rep) {
#pragma omp critical
                    {
                        long double d62 = (long double)((i128)thr - (i128)lhs62);
                        long double d78 = (long double)((i128)thr - (i128)lhs78);
                        fprintf(rep,
                          "n=%llu true_margin=%.6Le maj=%.12Le |sigma|=%.12Le "
                          "s62=%s slack62=%.0Lf s78=%s slack78=%.0Lf thr=%llu "
                          "A92hi=%lld A92lo=%llu A78hi=%lld A78lo=%llu "
                          "A62=%lld\n",
                          (unsigned long long)n, tru, maj,
                          (long double)(sig < 0 ? -sig : sig),
                          bad62 ? "FAIL" : "ok", d62,
                          bad78 ? "FAIL" : "ok", d78,
                          (unsigned long long)thr,
                          (long long)(a92 >> 64), (unsigned long long)(uint64_t)a92,
                          (long long)(a78 >> 64), (unsigned long long)(uint64_t)a78,
                          (long long)a62);
                    }
                }
            }
        }
#pragma omp critical
        {
            g.viol62 += l.viol62; g.viol78 += l.viol78;
            if (l.first62 && (!g.first62 || l.first62 < g.first62)) g.first62 = l.first62;
            if (l.first78 && (!g.first78 || l.first78 < g.first78)) g.first78 = l.first78;
            if (l.minmar62 < g.minmar62) { g.minmar62 = l.minmar62; g.argmin62 = l.argmin62; }
            if (l.minmar78 < g.minmar78) { g.minmar78 = l.minmar78; g.argmin78 = l.argmin78; }
            if (l.mintrue < g.mintrue) { g.mintrue = l.mintrue; g.argmintrue = l.argmintrue; }
        }
        free(prod); free(fl); free(mu);
    }
    if (rep) fclose(rep);

    /* total accumulators at N */
    i128 t62 = carry[nseg - 1].d62 + dl[nseg - 1].d62;
    i128 t78 = carry[nseg - 1].d78 + dl[nseg - 1].d78;
    i128 t92 = carry[nseg - 1].d92 + dl[nseg - 1].d92;
    printf("A62(%llu) = %lld (low64=%llu)\n", (unsigned long long)N,
           (long long)t62, (unsigned long long)(uint64_t)t62);
    printf("A78(%llu) hi=%lld lo=%llu\n", (unsigned long long)N,
           (long long)(t78 >> 64), (unsigned long long)(uint64_t)t78);
    printf("A92(%llu) hi=%lld lo=%llu\n", (unsigned long long)N,
           (long long)(t92 >> 64), (unsigned long long)(uint64_t)t92);
    printf("per-integer violations: S=62 %llu (first %llu)   S=78 %llu (first %llu)\n",
           (unsigned long long)g.viol62, (unsigned long long)g.first62,
           (unsigned long long)g.viol78, (unsigned long long)g.first78);
    printf("min true margin / (n/2^63) = %.6Le at n=%llu\n",
           g.minmar62, (unsigned long long)g.argmin62);
    printf("min true margin / (n/2^79) = %.6Le at n=%llu\n",
           g.minmar78, (unsigned long long)g.argmin78);
    printf("min true margin = %.6Le at n=%llu\n",
           g.mintrue, (unsigned long long)g.argmintrue);
    return 0;
}
