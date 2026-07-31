/* Independent reference oracle for Helfgott Prop. 12.2.4's fixed-point table.
 *
 *     ref_p1224 row  LO HI [NOPRINT]
 *     ref_p1224 cell Q  [CELLCAP]
 *
 * The shared specification is spec.py (exact-integer Python, validated against
 * mpmath).  This file reproduces spec.py bit for bit.  It is NOT a
 * transcription of the artifact: the artifact is a straight-line branchless
 * register machine compiled through the proved fragment; this is ordinary C
 * with branches, loops and named locals, written from the Python alone.  The
 * point is that an encoding bug in the register machine -- a mux that writes
 * its destination before reading its input, a swapped operand, a shift by the
 * wrong immediate -- changes the artifact's output and not this one.
 *
 * ------------------------------------------------------------------ THE CLAIM
 * For q in range and every integer k in the window,
 *
 *   M(q,k) := (phi(q)/q) [ log k + (1-w*) log q + w* L(q) + 1.36 ]
 *             - G_q(k) - w* . 7.284 . (20000k)^{-1/3} . f1(q)   >=  0,
 *
 * every rounding taken OUTWARD in the direction that makes the claim stronger
 * (a larger window, a smaller margin).  Scales: E=26 for row reals, C=44 for
 * G_q and the margin, P=30 for the ExpFixed mantissa, S=T=24 for exponents.
 *
 * ------------------------------------------------------------- THE ROOTS
 * `isqrt_seeded` seeds from `sqrt` and `cbrt32` seeds from `cbrt`, and both
 * then correct by exact integer comparison, so the floating seed cannot leak
 * into the answer.  The artifact takes the square root by a restoring radix-4
 * digit recurrence and advances the cube root incrementally.  Different
 * computations, the same certification -- v*v <= Z < (v+1)*(v+1) and
 * t^3 <= 2^15.20000k < (t+1)^3 -- so a disagreement is visible.
 *
 * `long double` is deliberately not used: CompCert rejects it on AArch64, and
 * <math.h> cannot even be included there, so `sqrt` and `cbrt` are declared
 * directly.  Both are only seeds.
 *
 * ------------------------------------------------------- WORD SIZE, HONESTLY
 * Every arithmetic operation below is on uint64_t.  Two products legitimately
 * exceed 2^63 while still fitting an unsigned word -- they are exact here but
 * would trap a signed-64 port:
 *
 *   (a) varpi0's  K_CSIG_LO * rpow_lo(q, Y_TAU).  9021664010625817088 at
 *       q = 3299999999, which is 2^62.968 -- ONE THIRTIETH OF A BIT under
 *       2^63; 1.0494e19 at q = 6469693230 and 1.3814e19 at q = 2.2e10, both
 *       already past it.  It crosses 2^63 at about q = 3.45e9.
 *   (b) f1_factor_hi's  p*(p-1).  10889999726100001722 at p = 3299999959.
 *
 * The tightest site that must stay NARROW is B_hi's
 *   ceil(K_B_HI . f1hi / 2^E) * q,
 * which is 7851867778430969190 at q = 2.2e10: 0.297 bits below 2^63, and
 * 4.67e18 at q = 6.47e9.  spec.py's scale note ("a product of two row values
 * is < 2^62") does not cover it, because this is a row value times q itself.
 *
 * Two quantities of spec.py do NOT fit a word at all, and are staged:
 *
 *   (c) logFix's squaring step x*x with x < 2^63 -- the half-limb `sq62`,
 *       whose result may itself sit above 2^63 (that is the emitted bit).
 *   (d) rpow_hi(q, Y_1_1MOM) reaches 2^75 near q = 2^17, and v3's numerator
 *       K_T3NUM_LO << P is 5.2e21 always.  Both only ever appear as the two
 *       sides of one division, and floor(X/(m.2^e)) = floor(floor(X/2^e)/m)
 *       together with floor(A.2^s/m) = (A/m).2^s + floor((A mod m).2^s/m)
 *       keeps every operand under 2^62.  `rpow_hi` therefore returns the
 *       mantissa and the shift separately.
 *
 * lam_hi is the near miss spec.py already fixed: staged >>20 then >>40 its
 * last product is 2.56e19 at q=1, over the word; staged >>40 then >>20, which
 * is what spec.py and this file do, the two middles are 9.0e16 and 2.5e13.
 *
 * Compiled with -DP1224_DEBUG every multiply and shift is checked: the two
 * sites above are allowed to reach 2^64 and every other site asserts < 2^63.
 * The largest intermediate seen is printed on stderr.
 *
 *   gcc   -O2 -o ref_p1224 bench/ref_p1224.c -lm
 *   ccomp -O  -o ref_p1224 bench/ref_p1224.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/* <math.h> is not includable under CompCert/AArch64 (it declares long double
   prototypes), and only these two seeds are needed. */
extern double sqrt(double);
extern double cbrt(double);

/* ------------------------------------------------------------------ scales */
#define E   26
#define C   44
#define P   30
#define S   24
#define T   24

#define ONE_E   (UINT64_C(1) << E)
#define ONE_C   (UINT64_C(1) << C)
#define B62     (UINT64_C(1) << 62)
#define B63     (UINT64_C(1) << 63)

/* E-scaled literals, exactly the integers spec.py prints */
#define K_OM_LO      UINT64_C(42098195)
#define K_1MOM_LO    UINT64_C(25010668)
#define K_136_LO     UINT64_C(91268055)
#define K_CD_LO      UINT64_C(1751541)
#define K_A_HI       UINT64_C(306643258)
#define K_B_HI       UINT64_C(500118107)
#define K_CSIG_LO    UINT64_C(61190398)
#define K_V2_LO      UINT64_C(812086418)
#define K_T3NUM_LO   UINT64_C(4803288635121)
/* exponent numerators at scale 2^T */
#define Y_TAU        UINT64_C(3767890)
#define Y_TAU1MTAU   UINT64_C(4859185)
#define Y_1_1MTAU    UINT64_C(21636401)
#define Y_1_1MOM     UINT64_C(45016787)
#define Y_THIRD      UINT64_C(5592405)
#define Y_TWOTHIRD   UINT64_C(11184810)
/* ln 2 at scale 2^32, both directions */
#define L2LO32       UINT64_C(2977044471)
#define L2HI32       UINT64_C(2977044472)

#define ROOTQ_BIG    148324          /* floor(sqrt(2.2e10)) */
#define CELLCAP_DEF  UINT64_C(30000000)

/* ------------------------------------------------- word-size instrumentation
 * MUL/SHL: must stay below 2^63.        MULW: allowed to reach 2^64.
 * Both are fatal on an actual wraparound. */
#ifdef P1224_DEBUG
static uint64_t g_max, g_maxw;
static int g_max_line, g_maxw_line;

static void fatal_wrap(const char *what, uint64_t a, uint64_t b, int line)
{
    fprintf(stderr, "FATAL line %d: %s wraps the word: %llu, %llu\n",
            line, what, (unsigned long long)a, (unsigned long long)b);
    abort();
}

static uint64_t mul_ck(uint64_t a, uint64_t b, int wide, int line)
{
    uint64_t v;
    if (a != 0 && b > UINT64_MAX / a) fatal_wrap("product", a, b, line);
    v = a * b;
    if (!wide && (v >> 63) != 0) {
        fprintf(stderr, "FATAL line %d: product %llu reaches 2^63\n",
                line, (unsigned long long)v);
        abort();
    }
    if (wide) { if (v > g_maxw) { g_maxw = v; g_maxw_line = line; } }
    else      { if (v > g_max)  { g_max  = v; g_max_line  = line; } }
    return v;
}

static uint64_t shl_ck(uint64_t a, unsigned n, int line)
{
    uint64_t v;
    if (n >= 63 || (n != 0 && (a >> (63 - n)) != 0))
        fatal_wrap("shift", a, (uint64_t)n, line);
    v = a << n;
    if (v > g_max) { g_max = v; g_max_line = line; }
    return v;
}
/* logFix's normalisation, whose result is by construction in [2^62, 2^63):
   asserted, but kept out of the general maximum so it cannot mask a near miss */
static uint64_t shlm_ck(uint64_t a, unsigned n, int line)
{
    uint64_t v;
    if (n >= 63 || (n != 0 && (a >> (63 - n)) != 0))
        fatal_wrap("mantissa shift", a, (uint64_t)n, line);
    v = a << n;
    if (v < B62) {
        fprintf(stderr, "FATAL line %d: mantissa %llu below 2^62\n",
                line, (unsigned long long)v);
        abort();
    }
    return v;
}
#define MUL(a, b)   mul_ck((a), (b), 0, __LINE__)
#define MULW(a, b)  mul_ck((a), (b), 1, __LINE__)
#define SHL(a, n)   shl_ck((a), (unsigned)(n), __LINE__)
#define SHLM(a, n)  shlm_ck((a), (unsigned)(n), __LINE__)
#else
#define MUL(a, b)   ((a) * (b))
#define MULW(a, b)  ((a) * (b))
#define SHL(a, n)   ((a) << (n))
#define SHLM(a, n)  ((a) << (n))
#endif

/* ceiling division on nonnegative integers, staged so a+b-1 cannot wrap */
static uint64_t cdiv(uint64_t a, uint64_t b)
{
    return a / b + (a % b != 0);
}

/* ===================================================================
 *  LogFixed / ExpFixed
 * =================================================================== */

/* floor(x^2 / 2^62) for x < 2^63, by a half-limb split.  The result is the
   only place a value at or above 2^63 is expected: that top bit is exactly the
   bit logFix emits.  Each partial product below is < 2^63 on its own. */
static uint64_t sq62(uint64_t x)
{
    uint64_t x1 = x >> 32, x0 = x & UINT64_C(0xffffffff);
    uint64_t hi = x1 * x1, mid = x1 * x0, lo = x0 * x0;
    uint64_t carry = ((mid & UINT64_C(0x1fffffff)) * (UINT64_C(1) << 33)
                      + (lo & (B62 - 1))) >= B62;
    return 4 * hi + (mid >> 29) + (lo >> 62) + carry;
}

/* floor(2^s * log2 n), 1 <= n < 2^63: normalise to a 62-bit mantissa, then
   square s times emitting one bit per round.
   Proved bracket: 2^logFix <= n^(2^s) < 2^(logFix+2). */
static uint64_t logFix(unsigned s, uint64_t n)
{
    int ex = 63;
    uint64_t x, acc = 0;
    unsigned i;
    if (n == 0 || (n >> 63) != 0) {
        fprintf(stderr, "FATAL: logFix needs 1 <= n < 2^63, got %llu\n",
                (unsigned long long)n);
        abort();
    }
    while (((n >> ex) & 1) == 0) ex--;
    x = SHLM(n, 62 - ex);
    for (i = 0; i < s; i++) {
        uint64_t b;
        x = sq62(x);
        b = (x >= B63) ? 1 : 0;
        x >>= b;
        acc = (acc << 1) + b;
    }
    return ((uint64_t)ex << s) + acc;
}

/* Integer square root by a floating seed and an exact integer correction --
   deliberately unlike the artifact's radix-4 digit recurrence.  The seed only
   has to be within a step or two; the loops decide. */
static uint64_t isqrt_seeded(uint64_t n)
{
    uint64_t r;
    if (n == 0) return 0;
    r = (uint64_t)sqrt((double)n);
    while (r > 0 && r > n / r) r--;
    while ((r + 1) <= n / (r + 1)) r++;
    return r;
}

/* the mantissa of 2^(r/2^t) at precision 2^p, one square root per bit */
static uint64_t expIter(unsigned p, uint64_t r, unsigned t)
{
    uint64_t x = UINT64_C(1) << p;
    unsigned i;
    for (i = 0; i < t; i++) {
        uint64_t b = (r >> i) & 1;
        uint64_t z = SHL(x, b + p);
        uint64_t v = isqrt_seeded(z);
        /* the certification, identical to the artifact's */
        if (MUL(v, v) > z || MUL(v + 1, v + 1) <= z) {
            fprintf(stderr, "FATAL: isqrt certification fails at z=%llu\n",
                    (unsigned long long)z);
            abort();
        }
        x = v;
    }
    return x;
}

/* LOWER mantissa of 2^(a/2^s) at precision 2^p, times 2^(a>>s) */
static uint64_t expFix(unsigned p, unsigned s, uint64_t a)
{
    return SHL(expIter(p, a & ((UINT64_C(1) << s) - 1), s), a >> s);
}

/* UPPER, as mantissa and shift: the value is (return) << *shift, which at
   q near 2^17 and y = 1/(1-w*) is 2^75 and does not fit a word. */
static uint64_t expFixHi(unsigned p, unsigned s, uint64_t a, unsigned *shift)
{
    *shift = (unsigned)(a >> s);
    return expIter(p, a & ((UINT64_C(1) << s) - 1), s) + s;
}

/* LOWER bound on 2^P . n^(y/2^T) */
static uint64_t rpow_lo(uint64_t n, uint64_t y)
{
    return expFix(P, S, MUL(y, logFix(S, n)) >> T);
}

/* UPPER bound on 2^P . n^(y/2^T), as mantissa << *shift */
static uint64_t rpow_hi(uint64_t n, uint64_t y, unsigned *shift)
{
    return expFixHi(P, S, cdiv(MUL(y, logFix(S, n) + 2), UINT64_C(1) << T),
                    shift);
}

/* LOWER bound on 2^E . ln n */
static uint64_t ln_lo(uint64_t n)
{
    return MUL(logFix(S, n), L2LO32) >> (S + 32 - E);
}

/* UPPER bound on 2^E . ln n */
static uint64_t ln_hi(uint64_t n)
{
    return cdiv(MUL(logFix(S, n) + 2, L2HI32), UINT64_C(1) << (S + 32 - E));
}

/* ===================================================================
 *  The per-q ROW
 * =================================================================== */

/* UPPER bound at scale 2^E on (1+p^{-2/3}) . (1+(p^{1/3}+p^{2/3})/(p(p-1)))^{-1}.
   The numerator's upper bound needs p^{2/3} LOWER and the denominator's lower
   bound needs both powers LOWER, so only rpow_lo is ever used. */
static uint64_t f1_factor_hi(uint64_t p)
{
    uint64_t a13 = rpow_lo(p, Y_THIRD);
    uint64_t a23 = rpow_lo(p, Y_TWOTHIRD);
    uint64_t num = ONE_E + cdiv(UINT64_C(1) << (E + P), a23);
    uint64_t den = ONE_E + ((a13 + a23) >> (P - E)) / MULW(p, p - 1);
    return cdiv(SHL(num, E), den);
}

/* LOWER bound on varpi_0(q) at scale 2^E.  The branch is taken only when the
   enclosures PROVE the condition; 0 is a lower bound either way, so a refused
   branch is safe.  The two fixed-point powers are replaced by integer-base
   powers via x^a >= floor(x)^a (a > 0). */
static uint64_t varpi0_lo(uint64_t q, uint64_t lq_hi)
{
    uint64_t cq, w_lo, wi, u_lo, sub_hi, base_lo, bi;
    cq = MULW(K_CSIG_LO, rpow_lo(q, Y_TAU)) >> P;
    if (cq <= ONE_E + lq_hi) return 0;
    w_lo = cq - lq_hi;
    wi = w_lo >> E;
    if (wi < 1) return 0;
    u_lo = rpow_lo(wi, Y_TAU1MTAU);
    sub_hi = cdiv(SHL(lq_hi, P), u_lo);
    if (cq <= sub_hi) return 0;
    base_lo = cq - sub_hi;
    bi = base_lo >> E;
    if (bi < 1) return 0;
    return rpow_lo(bi, Y_1_1MTAU) >> (P - E);
}

/* term3 at scale 2^E, LOWER:  floor((K_T3NUM_LO << P) / rpow_hi(q,Y_1_1MOM)).
   The numerator is 5.2e21 and the denominator can be 2^75, so the division is
   staged:  floor(X/(m.2^e)) = floor(floor(X/2^e)/m), and when e < P the
   remaining floor(A.2^s/m) is split as (A/m).2^s + floor((A mod m).2^s/m).
   With m >= 2^P every operand stays under 2^62. */
static uint64_t term3_lo(uint64_t q)
{
    unsigned e;
    uint64_t m = rpow_hi(q, Y_1_1MOM, &e);
    if (m == 0) return 0;
    if (e >= P) {
        if (e - P >= 64) return 0;
        return (K_T3NUM_LO >> (e - P)) / m;
    }
    return SHL(K_T3NUM_LO / m, P - e) + SHL(K_T3NUM_LO % m, P - e) / m;
}

#define MAXPF 16

typedef struct {
    uint64_t q, phi;
    uint64_t ps[MAXPF];
    int      np;                 /* omega(q) */
    uint64_t Llo, Lhi, f1hi;
    uint64_t phi_lo, phi_hi;
    uint64_t const_lo, kap_lo, B_hi, lam_hi, varpi_lo;
    uint64_t v0, v2, v3;
    int      viol;
} Row;

/* ---------------------------------------------------- factorisation by sieve */

static unsigned char *spf_composite;   /* the smallest-prime-factor sieve */
static uint32_t      *primes;
static int            nprimes;
static uint64_t       g_factor_incomplete;

static void build_spf(void)
{
    long n = ROOTQ_BIG, i, j;
    spf_composite = (unsigned char *)calloc((size_t)n + 1, 1);
    primes = (uint32_t *)malloc(sizeof(uint32_t) * 14000);
    nprimes = 0;
    for (i = 2; i <= n; i++) {
        if (spf_composite[i]) continue;
        primes[nprimes++] = (uint32_t)i;
        for (j = i * i; j <= n; j += i) spf_composite[j] = 1;
    }
}

/* distinct primes and Euler phi of q <= 2.2e10.  Every prime up to
   floor(sqrt(2.2e10)) = 148324 is tried, so at most one prime factor can be
   left over and it is the large cofactor. */
static void factor(uint64_t q, Row *r)
{
    uint64_t m = q, phi = 1;
    int i = 0;
    r->np = 0;
    if (q <= 1) { r->phi = 1; return; }
    for (i = 0; i < nprimes; i++) {
        uint64_t p = primes[i];
        if (MUL(p, p) > m) break;
        if (m % p == 0) {
            uint64_t f = p - 1;
            m /= p;
            while (m % p == 0) { m /= p; f = MUL(f, p); }
            r->ps[r->np++] = p;
            phi = MUL(phi, f);
        }
    }
    if (m > 1) {
        if (i >= nprimes && m > (uint64_t)ROOTQ_BIG * ROOTQ_BIG)
            g_factor_incomplete++;    /* only reachable above 2.2e10 */
        r->ps[r->np++] = m;
        phi = MUL(phi, m - 1);
    }
    r->phi = phi;
}

static void row(uint64_t q, Row *r)
{
    uint64_t lq_lo, lq_hi, R;
    int i;

    memset(r, 0, sizeof(*r));
    r->q = q;
    factor(q, r);

    /* L(q) = sum_{p|q} log p / p, both directions */
    for (i = 0; i < r->np; i++) {
        uint64_t p = r->ps[i];
        r->Llo += ln_lo(p) / p;
        r->Lhi += cdiv(ln_hi(p), p);
    }
    /* f1(q), UPPER */
    r->f1hi = ONE_E;
    for (i = 0; i < r->np; i++)
        r->f1hi = (MUL(r->f1hi, f1_factor_hi(r->ps[i])) + ONE_E - 1) >> E;
    /* phi/q, both directions */
    r->phi_lo = SHL(r->phi, E) / q;
    r->phi_hi = cdiv(SHL(r->phi, E), q);
    /* the k-independent part of the bracket, LOWER */
    lq_lo = ln_lo(q);
    lq_hi = ln_hi(q);
    r->const_lo = (MUL(K_1MOM_LO, lq_lo) >> E) + (MUL(K_OM_LO, r->Llo) >> E)
                  + K_136_LO;
    /* kappa* LOWER: log q lower, L upper, c_Delta lower */
    r->kap_lo = K_CD_LO;
    if (lq_lo > r->Lhi)
        r->kap_lo += MUL(K_1MOM_LO, lq_lo - r->Lhi) >> E;
    /* B(q) = (q/phi) . 7.284(1+beta*) . f1(q), UPPER */
    r->B_hi = cdiv(MUL(cdiv(MUL(K_B_HI, r->f1hi), ONE_E), q), r->phi);
    /* lambda_hi = ceil((B/kappa*)^3), staged >>40 THEN >>20; the other order
       overflows the word at q=1.  R <= 3.0e8, R*R <= 9.0e16,
       ceil(R*R/2^40).R <= 2.5e13. */
    R = cdiv(SHL(r->B_hi, 20), r->kap_lo);
    r->lam_hi = cdiv(MUL(cdiv(MUL(R, R), UINT64_C(1) << 40), R),
                     UINT64_C(1) << 20) + 1;
    /* varpi(q) LOWER = the max of three lower bounds */
    r->v2 = (K_V2_LO > lq_hi) ? K_V2_LO - lq_hi : 0;
    r->v3 = (q < (UINT64_C(1) << 17)) ? term3_lo(q) : 0;
    r->v0 = varpi0_lo(q, lq_hi);
    r->varpi_lo = r->v0;
    if (r->v2 > r->varpi_lo) r->varpi_lo = r->v2;
    if (r->v3 > r->varpi_lo) r->varpi_lo = r->v3;

    /* the row's own certification: the outward directions must be ordered and
       the window must be well defined.  Every one of these is expected to
       hold, so `viol` is expected to be 0 on every range. */
    r->viol = 0;
    if (r->Llo > r->Lhi)       r->viol = 1;
    if (r->phi_lo > r->phi_hi) r->viol = 1;
    if (lq_lo > lq_hi)         r->viol = 1;
    if (r->kap_lo == 0)        r->viol = 1;
    if (r->lam_hi == 0)        r->viol = 1;
}

/* ===================================================================
 *  The per-cell margin
 * =================================================================== */

/* floor(2^5 . (20000k)^{1/3}) -- what the artifact carries in a register and
   advances by the certified comparison t^3 <= 2^15 . 20000 k.  Here the seed
   comes from `cbrt` and the correction is exact: a different computation,
   certified the same way. */
static uint64_t cbrt32(uint64_t k)
{
    uint64_t n = SHL(MUL(UINT64_C(20000), k), 15);
    uint64_t t = (uint64_t)cbrt((double)n);
    while (t > 0 && MUL(MUL(t, t), t) > n) t--;
    while (MUL(MUL(t + 1, t + 1), t + 1) <= n) t++;
    return t;
}

/* the integer margin at scale 2^C; >= 0 is the artifact's test.  Returned as
   an unsigned word whose two's-complement reading is the signed value. */
static uint64_t cell_margin(const Row *r, uint64_t k, uint64_t Gq_hi)
{
    uint64_t lk_lo = ln_lo(k);
    uint64_t brk_lo = lk_lo + r->const_lo;
    uint64_t pos = SHL(MUL(r->phi_lo, brk_lo) >> E, C - E);
    uint64_t t = cbrt32(k);
    uint64_t af = cdiv(MUL(K_A_HI, r->f1hi), ONE_E);
    uint64_t env_hi = cdiv(SHL(af, 5), t);
    return pos - Gq_hi - SHL(env_hi, C - E);
}

/* ------------------------------------------------- G_q by a segmented sieve */

#define BLK 524288

/* UPPER bound on 2^C . G_q(k):  sum over squarefree r <= k coprime to q of
   ceil(2^C / phi(r)).  Each term overshoots by < 1 ulp.  The block sieve
   strips every prime up to sqrt(top), so a leftover cofactor is prime. */
typedef struct {
    uint32_t rem[BLK], ph[BLK];
    unsigned char sf[BLK], ex[BLK];
} Sieve;

static Sieve *sieve;

static void cell_run(const Row *r, uint64_t k0, uint64_t kmax,
                     uint64_t *cells, uint64_t *minmargin,
                     uint64_t *summargin, uint64_t *viol)
{
    uint64_t acc = 0, lo, top;
    *cells = 0; *summargin = 0; *viol = 0; *minmargin = 0;
    if (kmax <= 1) return;
    top = kmax - 1;                       /* the last r that G_q needs */
    if (sieve == NULL) sieve = (Sieve *)malloc(sizeof(Sieve));
    for (lo = 1; lo <= top; lo += BLK) {
        uint64_t hi = lo + BLK - 1, len, i;
        int j;
        if (hi > top) hi = top;
        len = hi - lo + 1;
        for (i = 0; i < len; i++) {
            sieve->rem[i] = (uint32_t)(lo + i);
            sieve->ph[i] = 1;
            sieve->sf[i] = 1;
            sieve->ex[i] = 0;
        }
        for (j = 0; j < nprimes; j++) {
            uint64_t p = primes[j], m, start;
            if (p * p > hi) break;
            start = (lo % p == 0) ? lo : lo + (p - lo % p);
            for (m = start; m <= hi; m += p) {
                uint64_t idx = m - lo;
                int e = 0;
                while (sieve->rem[idx] % p == 0) {
                    sieve->rem[idx] /= (uint32_t)p;
                    e++;
                }
                if (e >= 2) sieve->sf[idx] = 0;
                sieve->ph[idx] *= (uint32_t)(p - 1);
            }
        }
        /* strike out the r sharing a prime with q */
        for (j = 0; j < r->np; j++) {
            uint64_t p = r->ps[j], m, start;
            if (p > hi) continue;
            start = (lo % p == 0) ? lo : lo + (p - lo % p);
            for (m = start; m <= hi; m += p) sieve->ex[m - lo] = 1;
        }
        for (i = 0; i < len; i++) {
            uint64_t k = lo + i, ph = sieve->ph[i];
            if (sieve->rem[i] > 1) ph *= (uint64_t)sieve->rem[i] - 1;
            if (sieve->sf[i] && !sieve->ex[i]) acc += cdiv(ONE_C, ph);
            if (k >= k0 && k < kmax) {
                uint64_t m = cell_margin(r, k, acc);
                if (*cells == 0 || (int64_t)m < (int64_t)*minmargin)
                    *minmargin = m;
                (*cells)++;
                *summargin += m;
                if ((int64_t)m < 0) (*viol)++;
            }
        }
    }
}

/* =================================================================== main */

static void print_row(const Row *r)
{
    printf("%llu %llu %d %llu %llu %llu %llu %llu %llu %llu %llu\n",
           (unsigned long long)r->q, (unsigned long long)r->phi, r->np,
           (unsigned long long)r->Llo, (unsigned long long)r->Lhi,
           (unsigned long long)r->f1hi, (unsigned long long)r->phi_lo,
           (unsigned long long)r->const_lo, (unsigned long long)r->kap_lo,
           (unsigned long long)r->varpi_lo, (unsigned long long)r->lam_hi);
}

int main(int argc, char **argv)
{
    Row r;
    if (argc < 3) {
        fprintf(stderr, "usage: ref_p1224 row LO HI [NOPRINT]\n"
                        "       ref_p1224 cell Q [CELLCAP]\n");
        return 2;
    }
    build_spf();

    if (strcmp(argv[1], "row") == 0) {
        uint64_t lo = strtoull(argv[2], NULL, 10);
        uint64_t hi = (argc > 3) ? strtoull(argv[3], NULL, 10) : lo + 1;
        int quiet = (argc > 4 && strtoull(argv[4], NULL, 10) != 0);
        uint64_t q, viol = 0, s_q = 0, s_cells = 0, s_varpi = 0, s_lam = 0;
        uint64_t s_f1 = 0, s_phi = 0, s_const = 0, s_kap = 0, nonempty = 0;
        if (lo < 1) lo = 1;
        for (q = lo; q < hi; q++) {
            uint64_t k0;
            row(q, &r);
            if (!quiet) print_row(&r);
            k0 = (r.varpi_lo >> E) + 1;
            viol    += (uint64_t)r.viol;
            s_q     += q;
            s_cells += (r.lam_hi > k0) ? r.lam_hi - k0 : 0;
            s_varpi += r.varpi_lo;
            s_lam   += r.lam_hi;
            s_f1    += r.f1hi;
            s_phi   += r.phi_lo;
            s_const += r.const_lo;
            s_kap   += r.kap_lo;
            if (r.lam_hi > k0) nonempty++;
        }
        printf("SUM %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu\n",
               (unsigned long long)viol, (unsigned long long)s_q,
               (unsigned long long)s_cells, (unsigned long long)s_varpi,
               (unsigned long long)s_lam, (unsigned long long)s_f1,
               (unsigned long long)s_phi, (unsigned long long)s_const,
               (unsigned long long)s_kap, (unsigned long long)nonempty);
    } else if (strcmp(argv[1], "cell") == 0) {
        uint64_t q = strtoull(argv[2], NULL, 10);
        uint64_t cap = (argc > 3) ? strtoull(argv[3], NULL, 10) : CELLCAP_DEF;
        uint64_t k0, kmax, cells, minm, summ, viol;
        row(q, &r);
        k0 = (r.varpi_lo >> E) + 1;
        kmax = r.lam_hi;
        if (kmax > k0 + cap) kmax = k0 + cap;
        cell_run(&r, k0, kmax, &cells, &minm, &summ, &viol);
        printf("%llu %llu %llu %llu %lld %llu %llu\n",
               (unsigned long long)q, (unsigned long long)k0,
               (unsigned long long)kmax, (unsigned long long)cells,
               (long long)(int64_t)minm, (unsigned long long)summ,
               (unsigned long long)viol);
    } else {
        fprintf(stderr, "unknown mode %s\n", argv[1]);
        return 2;
    }

    if (g_factor_incomplete)
        fprintf(stderr, "WARNING: %llu q had an uncertified large cofactor\n",
                (unsigned long long)g_factor_incomplete);
#ifdef P1224_DEBUG
    {
        int b1 = 0, b2 = 0;
        uint64_t t;
        for (t = g_max;  t; t >>= 1) b1++;
        for (t = g_maxw; t; t >>= 1) b2++;
        fprintf(stderr, "debug: largest narrow intermediate %llu (%d bits, "
                        "%.3f bits below 2^63, line %d); largest wide %llu (%d bits, line %d)\n",
                (unsigned long long)g_max, b1,
                g_max ? 63.0 - (double)b1 + 1.0
                        - (double)(g_max - (UINT64_C(1) << (b1 - 1)))
                          / (double)(UINT64_C(1) << (b1 - 1)) : 63.0,
                g_max_line, (unsigned long long)g_maxw, b2, g_maxw_line);
    }
#endif
    return 0;
}
