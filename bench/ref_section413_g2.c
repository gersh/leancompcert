/* Independent oracle for the Helfgott §4.1.3 g2 sweep reference model
 * (LeanCompCert/Ports/Section413Sweep.lean, `g2SweepOK R checkLo N`).
 *
 * Shares no code with the emitted artifact: mu and sigma come from sieves
 * (the model recomputes them by trial division per touch), the interval
 * arithmetic is signed __int128 (the artifact uses sign-magnitude limb
 * pairs), and division is by the C `/` with explicit floor/ceil fixups
 * (the artifact uses the shift-18 + base-2^22 long division circuit).
 *
 * Also reports the magnitude maxima of every intermediate the artifact
 * guards at runtime, so the guard caps can be chosen with measured
 * headroom, and prints the final g cell and the sweep Boolean.
 *
 *   cc -O2 -o ref_g2 ref_section413_g2.c && ./ref_g2 N
 *
 * Exit status: 0 if the sweep Boolean is true, 1 otherwise.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef __int128 i128;
typedef long long i64;

static const i64 SCALE = 1000000000000000000LL; /* 10^18 */

/* floor division by a positive divisor */
static i128 floordiv(i128 a, i128 d) {
    if (a >= 0) return a / d;
    return -((-a + d - 1) / d);
}
/* ceiling division by a positive divisor */
static i128 ceildiv(i128 a, i128 d) {
    if (a >= 0) return (a + d - 1) / d;
    return -((-a) / d);
}

static i128 imin(i128 a, i128 b) { return a < b ? a : b; }
static i128 imax(i128 a, i128 b) { return a > b ? a : b; }
static i128 iabs(i128 a) { return a < 0 ? -a : a; }

typedef struct { i64 lo, hi; } Cell;

/* magnitude maxima, for cap selection */
static i128 maxW, maxWW, maxA, maxP, maxT, maxD, maxG;
static void seen(i128 *slot, i128 lo, i128 hi) {
    i128 m = imax(iabs(lo), iabs(hi));
    if (m > *slot) *slot = m;
}

/* cmul: outward-rounded interval product renormalized to SCALE */
static Cell cmul(Cell a, Cell b) {
    i128 p1 = (i128)a.lo * b.lo, p2 = (i128)a.lo * b.hi;
    i128 p3 = (i128)a.hi * b.lo, p4 = (i128)a.hi * b.hi;
    i128 lo = imin(imin(p1, p2), imin(p3, p4));
    i128 hi = imax(imax(p1, p2), imax(p3, p4));
    Cell r;
    r.lo = (i64)floordiv(lo, SCALE);
    r.hi = (i64)ceildiv(hi, SCALE);
    return r;
}

int main(int argc, char **argv) {
    long N = argc > 1 ? atol(argv[1]) : 1000000;
    long R = argc > 2 ? atol(argv[2]) : 999;
    long checkLo = argc > 3 ? atol(argv[3]) : 33;

    /* mu via smallest-prime-factor sieve; valid = trial division for
     * X < (R+2)^2, which the caller must respect (production: 10^6 < 1001^2;
     * asserted below). */
    if ((i128)N >= (i128)(R + 2) * (R + 2)) {
        fprintf(stderr, "N >= (R+2)^2: sieved mu no longer equals muZ\n");
        return 2;
    }
    int8_t *mu = malloc((N + 1) * sizeof(int8_t));
    int64_t *sigma = calloc(N + 1, sizeof(int64_t));
    uint32_t *spf = calloc(N + 1, sizeof(uint32_t));
    for (long i = 2; i <= N; i++)
        if (!spf[i])
            for (long j = i; j <= N; j += i)
                if (!spf[j]) spf[j] = (uint32_t)i;
    mu[0] = 0; if (N >= 1) mu[1] = 1;
    for (long n = 2; n <= N; n++) {
        long m = n, cnt = 0, sq = 0;
        while (m > 1) {
            long p = spf[m], e = 0;
            while (m % p == 0) { m /= p; e++; }
            if (e > 1) { sq = 1; break; }
            cnt++;
        }
        mu[n] = sq ? 0 : (cnt % 2 == 0 ? 1 : -1);
    }
    for (long d = 1; d <= N; d++)
        for (long j = d; j <= N; j += d) sigma[j] += d;

    Cell *acc = calloc(N + 1, sizeof(Cell));
    Cell g = {0, 0};
    int ok = 1;
    long firstBad = 0;

    long *divs = malloc(2400 * sizeof(long));

    for (long X = 1; X <= N; X++) {
        /* weight cell */
        Cell w = {0, 0};
        if (X % 2 == 1 && mu[X] != 0) {
            i64 s = sigma[X];
            i64 magF = SCALE / s, magC = (SCALE + s - 1) / s;
            if (mu[X] == 1) { w.lo = magF; w.hi = magC; }
            else { w.lo = -magC; w.hi = -magF; }
        }
        seen(&maxW, w.lo, w.hi);
        Cell ww = cmul(w, w);
        seen(&maxWW, ww.lo, ww.hi);

        /* divisors <= sqrt(X), ascending, with partners */
        long nd = 0;
        for (long r = 1; (i128)r * r <= X; r++)
            if (X % r == 0) {
                divs[nd++] = r;
                if (X / r != r) divs[nd++] = X / r;
            }

        Cell delta = {0, 0};
        for (long k = 0; k < nd; k++) {
            long d = divs[k];
            Cell A = acc[d];
            seen(&maxA, A.lo, A.hi);
            Cell P = cmul(A, w);
            seen(&maxP, P.lo, P.hi);
            Cell T = { 2 * P.lo + ww.lo, 2 * P.hi + ww.hi };
            seen(&maxT, T.lo, T.hi);
            Cell dT;
            if (mu[d] == 1) dT = T;
            else if (mu[d] == -1) { dT.lo = -T.hi; dT.hi = -T.lo; }
            else { dT.lo = 0; dT.hi = 0; }
            delta.lo += dT.lo; delta.hi += dT.hi;
            seen(&maxD, delta.lo, delta.hi);
            acc[d].lo = A.lo + w.lo; acc[d].hi = A.hi + w.hi;
        }
        g.lo += delta.lo; g.hi += delta.hi;
        seen(&maxG, g.lo, g.hi);

        if (X >= checkLo) {
            i128 t = (i128)10 * X;
            int pass = (i128)(-21) * SCALE <= (i128)g.lo * t
                    && (i128)g.hi * t <= (i128)21 * SCALE;
            if (!pass && ok) { ok = 0; firstBad = X; }
        }
    }

    printf("N=%ld R=%ld checkLo=%ld\n", N, R, checkLo);
    printf("ok=%d firstBad=%ld\n", ok, firstBad);
    printf("g = [%lld, %lld]\n", (long long)g.lo, (long long)g.hi);
    printf("max |w|     = %lld\n", (long long)maxW);
    printf("max |ww|    = %lld\n", (long long)maxWW);
    printf("max |acc|   = %lld\n", (long long)maxA);
    printf("max |P|     = %lld\n", (long long)maxP);
    printf("max |T|     = %lld\n", (long long)maxT);
    printf("max |delta| = %lld\n", (long long)maxD);
    printf("max |g|     = %lld\n", (long long)maxG);
    printf("2^60 = %lld  2^61 = %lld  2^62 = %lld\n",
        1152921504606846976LL, 2305843009213693952LL, 4611686018427387904LL);
    return ok ? 0 : 1;
}
