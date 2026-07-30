/*
 * Independent reference for the fixed-point exponential of
 * `Ports/ExpFixPort.lean` and `Verified/ExpFixed.lean`.
 *
 *     ref_exp P S R ROUNDS
 *
 * prints
 *
 *     viol V   mant M   rem Q
 *
 * in the artifact's own format, so the two outputs are compared bit for bit.
 *
 * The point of this file is that it does **not** use the artifact's algorithm.
 * The artifact takes each root by a restoring radix-4 digit recurrence,
 * unrolled to P+1 fixed steps; this reference seeds from `sqrtl` and corrects,
 * which is a different computation with a different rounding history.  Both
 * then apply the *same* certification — `v*v <= Z < (v+1)*(v+1)`, which is
 * `ExpFixed.expOK` — and both report the violation count, so a disagreement in
 * either the mantissa or the count is visible.
 *
 * Everything is exact 64-bit integer arithmetic.  The proved bound
 * `ExpFixed.expIter_fits_64` says that at P <= 30 the radicand and the
 * successor square stay below 2^63, so nothing here can wrap; the assertions
 * check that at run time as well.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

/* Integer square root by a floating seed and an exact integer correction.
   Deliberately unlike the artifact's digit recurrence. */
static uint64_t isqrt_seeded(uint64_t n)
{
    if (n == 0)
        return 0;
    uint64_t r = (uint64_t)sqrtl((long double)n);
    /* correct downward, then upward; at most a couple of steps either way */
    while (r > 0 && r > n / r)
        r--;
    while ((r + 1) <= n / (r + 1))
        r++;
    return r;
}

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "usage: ref_exp P S R ROUNDS\n");
        return 2;
    }
    unsigned P = (unsigned)strtoul(argv[1], NULL, 10);
    unsigned S = (unsigned)strtoul(argv[2], NULL, 10);
    uint64_t r = strtoull(argv[3], NULL, 10);
    uint64_t rounds = strtoull(argv[4], NULL, 10);
    (void)S;

    if (P > 30) {
        fprintf(stderr, "P=%u exceeds the proved word-size bound P <= 30\n", P);
        return 2;
    }

    uint64_t x = UINT64_C(1) << P;
    uint64_t viol = 0;

    for (uint64_t t = 0; t < rounds; t++) {
        uint64_t b = r & 1u;
        r >>= 1;
        uint64_t Z = (x << P) << b;
        if (Z >= (UINT64_C(1) << 63)) {
            fprintf(stderr, "radicand overflow at round %llu\n",
                    (unsigned long long)t);
            return 3;
        }
        uint64_t v = isqrt_seeded(Z);
        /* the certification, identical to the artifact's */
        if (v * v > Z)
            viol++;
        if ((v + 1) * (v + 1) <= Z)
            viol++;
        x = v;
    }

    printf("viol %llu mant %llu rem %llu\n",
           (unsigned long long)viol, (unsigned long long)x,
           (unsigned long long)r);
    return 0;
}
