#define _POSIX_C_SOURCE 199309L
/* Benchmarks: early-exit algorithms vs verification-friendly rewrites.
   Compiled with CompCert (the deployment compiler for certified checkers). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

/* ---- 1. minFac sweep: early-exit trial division ---- */
static uint64_t minfac_early(uint64_t n) {
    if ((n & 1) == 0) return 2;
    for (uint64_t d = 3; d * d <= n; d += 2)
        if (n % d == 0) return d;
    return n;
}
static uint64_t sweep_minfac_early(uint64_t N) {
    uint64_t acc = 0;
    for (uint64_t n = 2; n <= N; n++) acc += minfac_early(n);
    return acc;
}

/* ---- 2. minFac sweep: predicated (no break; fixed d-range per n) ---- */
static uint64_t minfac_predicated(uint64_t n) {
    uint64_t found = ((n & 1) == 0) ? 2 : 0;
    for (uint64_t d = 3; d * d <= n; d += 2) {
        uint64_t hit = (n % d == 0) ? d : 0;
        uint64_t take = (found == 0) & (hit != 0);
        found = take ? hit : found;   /* branchless select in spirit */
    }
    return found == 0 ? n : found;
}
static uint64_t sweep_minfac_predicated(uint64_t N) {
    uint64_t acc = 0;
    for (uint64_t n = 2; n <= N; n++) acc += minfac_predicated(n);
    return acc;
}

/* ---- 3. minFac sweep: smallest-prime-factor sieve (fixed shape + array) ---- */
static uint64_t sweep_minfac_sieve(uint64_t N) {
    uint32_t *spf = calloc(N + 1, sizeof(uint32_t));
    if (!spf) return 0;
    for (uint64_t d = 2; d * d <= N; d++)
        if (spf[d] == 0)
            for (uint64_t m = d * d; m <= N; m += d)
                if (spf[m] == 0) spf[m] = (uint32_t)d;
    uint64_t acc = 0;
    for (uint64_t n = 2; n <= N; n++)
        acc += spf[n] ? spf[n] : n;
    free(spf);
    return acc;
}

/* ---- 4. integer sqrt: convergence loop vs fixed iteration count ---- */
static uint64_t isqrt_early(uint64_t n) {
    if (n < 2) return n;
    uint64_t x = n, y = (x + 1) / 2;
    while (y < x) { x = y; y = (x + n / x) / 2; }
    return x;
}
static uint64_t bitlen(uint64_t n) {
    uint64_t b = 0;
    while (n) { n >>= 1; b++; }
    return b;
}
static uint64_t isqrt_fixed_clean(uint64_t n) {
    if (n < 2) return n;
    uint64_t x = (uint64_t)1 << ((bitlen(n) + 1) / 2);
    for (int i = 0; i < 6; i++) x = (x + n / x) / 2;
    while (x * x > n) x--;          /* at most 1-2 corrections */
    return x;
}
static uint64_t sweep_sqrt(uint64_t N, uint64_t (*f)(uint64_t)) {
    uint64_t acc = 0;
    for (uint64_t n = 1; n <= N; n++) acc += f(n * 2654435761u % 0xFFFFFFFFFFFFull);
    return acc;
}

/* ---- 5. gcd: early-exit Euclid vs fixed-step binary gcd ---- */
static uint64_t gcd_early(uint64_t a, uint64_t b) {
    while (b) { uint64_t t = a % b; a = b; b = t; }
    return a;
}
static uint64_t gcd_fixed(uint64_t a, uint64_t b) {
    /* fixed-shape binary gcd: every round has identical structure
       (halve-or-subtract, predicated); 192 rounds cover all 64-bit pairs */
    if (a == 0) return b;
    if (b == 0) return a;
    uint64_t shift = 0;
    for (int i = 0; i < 63; i++) {
        uint64_t both_even = ((a | b) & 1) == 0;
        a = both_even ? a >> 1 : a;
        b = both_even ? b >> 1 : b;
        shift += both_even;
    }
    for (int i = 0; i < 63; i++) {          /* make b odd (discard b's twos) */
        uint64_t b_even = (b & 1) == 0;
        b = b_even ? b >> 1 : b;
    }
    for (int i = 0; i < 192; i++) {
        uint64_t live = a != 0;
        uint64_t a_even = live && ((a & 1) == 0);
        uint64_t a_half = a >> 1;
        uint64_t doswap = live && !a_even && a < b;
        uint64_t na = a_even ? a_half : (doswap ? b : a);
        uint64_t nb = doswap ? a : b;
        uint64_t dosub = live && !a_even;
        a = dosub ? na - nb : na;
        b = nb;
    }
    return b << shift;
}
static uint64_t sweep_gcd(uint64_t N, uint64_t (*f)(uint64_t, uint64_t)) {
    uint64_t acc = 0, x = 0x9E3779B97F4A7C15ull;
    for (uint64_t i = 0; i < N; i++) {
        uint64_t a = x; x = x * 6364136223846793005ull + 1442695040888963407ull;
        uint64_t b = x; x = x * 6364136223846793005ull + 1442695040888963407ull;
        acc += f(a % 1000000007, b % 998244353);
    }
    return acc;
}

/* ---- 6. early-exit fold vs poison-flag fold (bandRun shape) ---- */
static uint64_t fold_early(uint64_t N) {
    uint64_t acc = 0;
    for (uint64_t n = 1; n <= N; n++) {
        acc += (n * 2862933555777941757ull) >> 40;
        if (acc > 0x8000000000000000ull) return 0;   /* abort: never fires */
    }
    return acc;
}
static uint64_t fold_poison(uint64_t N) {
    uint64_t acc = 0, ok = 1;
    for (uint64_t n = 1; n <= N; n++) {
        acc += (n * 2862933555777941757ull) >> 40;
        ok &= (acc <= 0x8000000000000000ull);
    }
    return ok ? acc : 0;
}

static void bench(const char *name, uint64_t result, double t) {
    printf("%-28s %18llu  %8.3f s\n", name, (unsigned long long)result, t);
}

int main(void) {
    double t;
    uint64_t r;

    t = now_s(); r = sweep_minfac_early(10000000);      bench("minfac early-exit 1e7", r, now_s()-t);
    t = now_s(); r = sweep_minfac_sieve(10000000);      bench("minfac sieve      1e7", r, now_s()-t);
    t = now_s(); r = sweep_minfac_early(1000000);       bench("minfac early-exit 1e6", r, now_s()-t);
    t = now_s(); r = sweep_minfac_predicated(1000000);  bench("minfac predicated 1e6", r, now_s()-t);
    t = now_s(); r = sweep_minfac_sieve(1000000);       bench("minfac sieve      1e6", r, now_s()-t);

    t = now_s(); r = sweep_sqrt(5000000, isqrt_early);       bench("isqrt convergence 5e6", r, now_s()-t);
    t = now_s(); r = sweep_sqrt(5000000, isqrt_fixed_clean); bench("isqrt fixed-6     5e6", r, now_s()-t);

    t = now_s(); r = sweep_gcd(2000000, gcd_early);  bench("gcd euclid       2e6", r, now_s()-t);
    t = now_s(); r = sweep_gcd(2000000, gcd_fixed);  bench("gcd fixed-128    2e6", r, now_s()-t);

    t = now_s(); r = fold_early(50000000);   bench("fold early-exit  5e7", r, now_s()-t);
    t = now_s(); r = fold_poison(50000000);  bench("fold poison-flag 5e7", r, now_s()-t);
    return 0;
}
