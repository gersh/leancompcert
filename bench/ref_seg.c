/* Reference for the offset segmented sieve of Ports/ArraySegSieve.
 *
 * Plain segmented Mobius sieve over [lo, hi], accumulating exactly the three
 * residues the AProgram accumulates, in exactly the same fixed-point
 * conventions:
 *
 *   M(n) = sum_{m<=n} mu(m)                        biased by 2^40
 *   Q(n) = sum_{m<=n} |mu(m)|
 *   G(n) = Q(n)*2^36 - c*n,  c = floor((6/pi^2)*2^36)   biased by 2^62
 *   T(n) = sum_{m<=n} mu(m)*round(2^62/m)          biased by 2^63
 *
 * Prints the same seven slots the hosted artifact driver prints, so the two
 * can be diffed.  This is the "how fast can this possibly go" line as well as
 * the correctness oracle.
 *
 *   cc -O2 -o ref_seg bench/ref_seg.c -lm
 *   ./ref_seg LO SEGLEN SEGCOUNT
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define CDEM_C  UINT64_C(41776432333)   /* floor((6/pi^2) * 2^36) */
#define M_BIAS  (UINT64_C(1) << 40)
#define G_BIAS  (UINT64_C(1) << 62)
#define T_BIAS  (UINT64_C(1) << 63)
#define T_SCALE (UINT64_C(1) << 62)

int main(int argc, char **argv)
{
    if (argc < 4) { fprintf(stderr, "usage: LO SEGLEN SEGCOUNT\n"); return 2; }
    uint64_t lo = strtoull(argv[1], 0, 10);
    uint64_t L  = strtoull(argv[2], 0, 10);
    uint64_t S  = strtoull(argv[3], 0, 10);
    uint64_t hi = lo + L * S - 1;

    /* sieving primes: all p with p*p <= hi */
    uint64_t root = 1;
    while ((root + 1) * (root + 1) <= hi) root++;
    char *isc = calloc(root + 2, 1);
    uint64_t np = 0;
    for (uint64_t d = 2; d <= root; d++) {
        if (!isc[d]) { np++; for (uint64_t m = d * d; m <= root; m += d) isc[m] = 1; }
    }
    uint64_t *pr = malloc(np * sizeof(uint64_t));
    uint64_t k = 0;
    for (uint64_t d = 2; d <= root; d++) if (!isc[d]) pr[k++] = d;

    uint64_t *prod = malloc(L * sizeof(uint64_t));
    uint8_t  *flag = malloc(L);

    uint64_t M = M_BIAS, Mmax = M_BIAS, Mmin = M_BIAS;
    uint64_t Q = 0;
    uint64_t G = G_BIAS, Gmax = G_BIAS, Gmin = G_BIAS;
    uint64_t T = T_BIAS, Tmax = T_BIAS, Tmin = T_BIAS;

    for (uint64_t s = 0; s < S; s++) {
        uint64_t w = lo + s * L;
        for (uint64_t i = 0; i < L; i++) { prod[i] = 0; flag[i] = 0; }
        for (uint64_t t = 0; t < np; t++) {
            uint64_t p = pr[t];
            uint64_t j = (p - w % p) % p;
            for (; j < L; j += p) {
                uint64_t n = w + j;
                prod[j] = (prod[j] ? prod[j] : 1) * p;
                flag[j] ^= 1;
                if (n % (p * p) == 0) flag[j] |= 2;
            }
        }
        for (uint64_t i = 0; i < L; i++) {
            uint64_t n = w + i;
            uint64_t pd = prod[i] ? prod[i] : 1;
            int alive = (flag[i] & 2) ? 0 : 1;
            int neg = ((flag[i] & 1) ^ (pd != n ? 1 : 0));
            uint64_t pos = alive && !neg, negv = alive && neg;
            uint64_t sf = alive;

            M = M + pos - negv;
            if (M > Mmax) Mmax = M;
            if (M < Mmin) Mmin = M;
            Q = Q + sf;
            G = G + (sf << 36) - CDEM_C;
            if (G > Gmax) Gmax = G;
            if (G < Gmin) Gmin = G;

            uint64_t q = T_SCALE / n, r = T_SCALE % n;
            uint64_t wgt = q + (2 * r >= n ? 1 : 0);
            T = T + pos * wgt - negv * wgt;
            if (T > Tmax) Tmax = T;
            if (T < Tmin) Tmin = T;
        }
    }
    printf("hi %llu\n", (unsigned long long)hi);
    printf("mertens slot0 %llu\n", (unsigned long long)M);
    printf("mertens slot1 %llu\n", (unsigned long long)Q);
    printf("mertens slot2 %llu\n", (unsigned long long)G);
    printf("mertens slot3 %llu\n", (unsigned long long)Mmax);
    printf("mertens slot4 %llu\n", (unsigned long long)Mmin);
    printf("mertens slot5 %llu\n", (unsigned long long)Gmax);
    printf("mertens slot6 %llu\n", (unsigned long long)Gmin);
    printf("mobius  slot0 %llu\n", (unsigned long long)T);
    printf("mobius  slot1 %llu\n", (unsigned long long)Tmax);
    printf("mobius  slot2 %llu\n", (unsigned long long)Tmin);
    printf("M %lld  Q %llu\n", (long long)(M - M_BIAS), (unsigned long long)Q);
    return 0;
}
