/* Independent oracle for LeanCompCert/Ports/CDEMAbelScan.lean.
 *
 *   cc -O2 -o ref_abel bench/ref_abel.c -lm
 *   ./ref_abel W K HI [MARK] [SEG]
 *
 * MARK=1 accumulates the divisor sum by walking multiples instead of by the
 * O(HI*K) divisor loop; needed above K ~ 10^4.
 *
 * SEG is the length of the marking window, default HI (one window, which at
 * HI = 5e9 is a 20 GB int32 array).  Any SEG >= 1 gives the same numbers:
 * the multiples of each squarefree d <= K are walked window by window, at a
 * cost of one extra cursor per d per window, i.e. ceil(HI/SEG)*K extra steps,
 * which at SEG = 1e8 and HI = 5e9 is 1e7 against the 4e10 the marking already
 * costs.  A window that fits in cache also makes the marking several times
 * faster than the flat array does.
 *
 * Prints the twelve result slots the artifact stores, in the artifact's own
 * order and encoding, so the two can be compared literally:
 *
 *   slot0/1  uPos, low and high limb        slot6   tv
 *   slot2/3  uNeg, low and high limb        slot7   F(HI) as a wrapped u64
 *   slot4/5  v,    low and high limb        slot8   G(HI)
 *                                           slot9   floor(sqrt(HI))
 *                                           slot10  the divisor cursor (= K)
 *                                           slot11  violations (always 0 here)
 *
 * Nothing here is shared with the artifact.  In particular:
 *
 *   - mu is built by a linear (smallest-prime-factor) sieve, not by trial
 *     division against a table of small primes;
 *   - the reciprocal square root uses long double and a u128 fixup, which is
 *     what scripts/cdem_repro_table_fast.cpp on claude_math does, not the
 *     bisection on the exact 64-bit predicate that the artifact runs;
 *   - the accumulators are unsigned __int128, not limb pairs.
 *
 * So agreement on all twelve slots is evidence about the mathematics, not
 * about a shared implementation.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

static int8_t *mu_table(uint64_t K)
{
    uint64_t n;
    int8_t *mu = malloc((size_t)(K + 1) * sizeof(int8_t));
    uint32_t *spf = malloc((size_t)(K + 1) * sizeof(uint32_t));
    if (!mu || !spf) {
        fprintf(stderr, "out of memory\n");
        exit(2);
    }
    for (n = 0; n <= K; n++)
        spf[n] = 0;
    for (n = 2; n <= K; n++) {
        if (spf[n] == 0) {
            uint64_t m;
            for (m = n; m <= K; m += n)
                if (spf[m] == 0)
                    spf[m] = (uint32_t)n;
        }
    }
    mu[0] = 0;
    if (K >= 1)
        mu[1] = 1;
    for (n = 2; n <= K; n++) {
        uint64_t p = spf[n];
        uint64_t m = n / p;
        if (m % p == 0)
            mu[n] = 0;
        else
            mu[n] = (int8_t)(-mu[m]);
    }
    free(spf);
    return mu;
}

/* The least s with s*s*n >= W*W, by long double plus an exact u128 fixup. */
static uint64_t rsqrt_ceil(uint64_t W, uint64_t n)
{
    const u128 ww = (u128)W * W;
    uint64_t q = (uint64_t)ceill((long double)W / sqrtl((long double)n));
    if (q == 0)
        q = 1;
    while ((u128)q * q * n < ww)
        q++;
    while (q > 1 && (u128)(q - 1) * (q - 1) * n >= ww)
        q--;
    return q;
}

static void print128(const char *tag, u128 x)
{
    printf("%s %llu\n", tag, (unsigned long long)(uint64_t)x);
}

int main(int argc, char **argv)
{
    uint64_t W = argc > 1 ? strtoull(argv[1], NULL, 10) : 1000000000000000000ULL;
    uint64_t K = argc > 2 ? strtoull(argv[2], NULL, 10) : 199330;
    uint64_t HI = argc > 3 ? strtoull(argv[3], NULL, 10) : 1000000;
    int MARK = argc > 4 ? atoi(argv[4]) : 0;
    uint64_t SEG = argc > 5 ? strtoull(argv[5], NULL, 10) : 0;
    uint64_t k, d;
    int8_t *mu;
    int64_t F = 0;
    uint64_t G = 0, T = 1, tv = 0;
    u128 uPos = 0, uNeg = 0, v = 0;

    if (W == 0 || K == 0 || HI == 0) {
        fprintf(stderr, "require W, K, HI >= 1\n");
        return 2;
    }
    mu = mu_table(K);

    /* For large K the O(HI*K) divisor loop is hopeless, so delta is instead
     * accumulated by walking the multiples of each squarefree d.  This is the
     * same identity, but it is still not the artifact's algorithm: there is no
     * window, no cursor, no budget, and mu came from a linear sieve. */
    int32_t *acc = NULL;
    uint64_t seg = 0, segLo = 1, segHi = 0;
    if (MARK) {
        seg = SEG ? SEG : HI;
        if (seg > HI) seg = HI;
        acc = malloc((size_t)(seg + 1) * sizeof(int32_t));
        if (!acc) { fprintf(stderr, "out of memory\n"); exit(2); }
        segHi = 0;                       /* forces a refill at k = 1 */
    }

    for (k = 1; k <= HI; k++) {
        int64_t delta = 0;
        uint64_t g, dp, dn;
        if (MARK) {
            if (k > segHi) {             /* refill the marking window */
                uint64_t i, m;
                segLo = k;
                segHi = segLo + seg - 1;
                if (segHi > HI) segHi = HI;
                for (i = 0; i <= segHi - segLo; i++) acc[i] = 0;
                for (d = 1; d <= K; d++) {
                    if (mu[d] == 0) continue;
                    m = ((segLo + d - 1) / d) * d;
                    for (; m <= segHi; m += d)
                        acc[m - segLo] += mu[d];
                }
            }
            delta = acc[k - segLo];
        } else
            for (d = 1; d <= K; d++)
                if (k % d == 0)
                    delta += mu[d];
        F += delta;
        g = (uint64_t)(F > 1 ? F - 1 : 1 - F);
        dp = g > G ? g - G : 0;
        dn = G > g ? G - g : 0;
        tv += dp + dn;
        uPos += (u128)dp * ((W + k - 1) / k);
        uNeg += (u128)dn * (W / k);
        if (dp + dn != 0)
            v += (u128)(dp + dn) * rsqrt_ceil(W, k);
        G = g;
        while ((T + 1) * (T + 1) <= k)
            T++;
    }

    print128("slot0", uPos);
    print128("slot1", uPos >> 64);
    print128("slot2", uNeg);
    print128("slot3", uNeg >> 64);
    print128("slot4", v);
    print128("slot5", v >> 64);
    printf("slot6 %llu\n", (unsigned long long)tv);
    printf("slot7 %llu\n", (unsigned long long)(uint64_t)F);
    printf("slot8 %llu\n", (unsigned long long)G);
    printf("slot9 %llu\n", (unsigned long long)T);
    printf("slot10 %llu\n", (unsigned long long)K);
    printf("slot11 0\n");
    free(mu);
    free(acc);
    return 0;
}
