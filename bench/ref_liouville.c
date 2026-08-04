/* Reference model for the Liouville little-sum sweep scalar port.
 *
 * Mirrors, in exact u64 arithmetic, the per-round register semantics the
 * Reflect program will have, so that the design can be checked before any
 * Lean is written.  Structured as the nested (candidate, round) loop the flat
 * index decodes to; the operation sequence is identical.
 *
 * WHY THIS FILE EXISTS.  bench/liouville_band_bridge_check.py established
 *   (C)  L(N+1)*2^20 <= L_j*2^SC
 * exhaustively, and the design read (C) as licensing "tableless certificate
 * implies the atom's per-band thresholds".  It does not: (C) says the per-N
 * log bound is SHARPER than the band's, so the tableless threshold
 * floor(99*2^(50+SC)/(1000*L(N+1))) is LARGER than T_j -- at all 3991082
 * candidates, by up to 2.6%.  The implication needs the reverse inequality.
 * What replaces it: the 65-entry table is not data at all, it is the orbit of
 * a two-line integer recurrence (see bench/liouville_band_ladder_check.py),
 * so the machine can carry the band's own L_j in a register and the bridge
 * becomes an exact 65-step check instead of an inequality.
 *
 *   cc -O2 -o /tmp/ref_liouville bench/ref_liouville.c && /tmp/ref_liouville
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t u64;

#define LO      1u
#define LEN     3999999u
#define EXTRA   21u
#define DSMALL  157u
#define DBIG    2000u
#define ROUNDS  (EXTRA * DSMALL + (DBIG - DSMALL))   /* 5140 */

#define PL      (1ULL << 50)
#define BIAS    (1ULL << 62)
#define ACLO    (BIAS - (1ULL << 56))
#define ACHI    (BIAS + (1ULL << 56))
#define GLO     (BIAS - (1ULL << 55))
#define GHI     (BIAS + (1ULL << 55))

#define NLO     8918u
#define NHI     4000000u
#define E0      9442u
#define LB0     9603098u

#define SH      20
#define ASHCAP  (1ULL << 25)
#define LBCAP   (1ULL << 25)
#define RHS     (99ULL << 50)

/* ---- an independent lambda, by a smallest-prime-factor sieve ---- */
static unsigned char *lam_sieve(unsigned n)
{
    unsigned *spf = malloc((size_t)(n + 1) * sizeof(unsigned));
    unsigned char *par = malloc((size_t)(n + 1));
    unsigned i, m;
    for (i = 0; i <= n; i++) spf[i] = i;
    for (i = 2; (u64)i * i <= n; i++)
        if (spf[i] == i)
            for (m = i * i; m <= n; m += i)
                if (spf[m] == m) spf[m] = i;
    par[0] = 0;
    if (n >= 1) par[1] = 0;
    for (m = 2; m <= n; m++) par[m] = par[m / spf[m]] ^ 1;
    free(spf);
    return par;
}

int main(void)
{
    unsigned char *ref = lam_sieve(NHI);
    clock_t t0 = clock();

    u64 bad = 0, acc = BIAS, res = 0, par = 0, Lb = LB0, E = E0;
    unsigned long long parity_bad = 0, first_parity_bad = 0;
    u64 maxlhs = 0, maxAsh = 0, maxabs = 0, maxinc = 0, maxLbRaw = 0;
    double worst = 0.0; unsigned worst_at = 0;
    u64 ell_1e6 = 0;

    for (unsigned i = 0; i < LEN; i++) {
        unsigned n = LO + i;
        for (unsigned q = 0; q < ROUNDS; q++) {
            u64 first = (q == 0), last = (q == ROUNDS - 1);

            /* divisor decode: two phases on the flat round index */
            u64 qs = q / EXTRA;
            u64 d1 = qs + 2;
            u64 d2 = (q >= EXTRA * DSMALL ? q - EXTRA * DSMALL : 0)
                     + (DSMALL + 2);
            u64 ph = (q < EXTRA * DSMALL);
            u64 d  = ph * d1 + (1 - ph) * d2;

            /* strip one round */
            u64 resIn = first ? (u64)n : res;
            u64 parIn = first ? 0 : par;
            u64 qd = resIn / d;
            u64 rd = resIn - qd * d;
            u64 hit = (rd == 0);
            u64 resN = hit ? qd : resIn;
            u64 parN = 1 - (parIn == hit);
            res = resN; par = parN;

            /* the completely-multiplicative sign, meaningful on the last round */
            u64 corr = 1 - (resN == 1);
            u64 sgn  = 1 - (parN == corr);

            /* accumulate at scale 2^50, biased at 2^62 */
            u64 pn   = PL / n;
            u64 accC = acc < ACLO ? ACLO : (acc > ACHI ? ACHI : acc);
            u64 t    = accC + (1 - sgn) * pn;
            u64 accN = t - sgn * pn;
            u64 accP = last * accN + (1 - last) * acc;
            acc = accP;

            /* |S| and the atom's A = |ellLval n| + n */
            u64 u1 = accP > BIAS ? accP - BIAS : 0;
            u64 u2 = accP < BIAS ? BIAS - accP : 0;
            u64 absS = u1 + u2;
            u64 A = absS + n;
            u64 Ash = (A + ((1ULL << SH) - 1)) >> SH;
            u64 gsh = (Ash > ASHCAP);
            u64 AshC = gsh * ASHCAP + (1 - gsh) * Ash;
            u64 gash = 1 - gsh;

            /* the band ladder, tableless */
            u64 wr  = E / 10 + 1;
            u64 rem = NHI - E;
            u64 gwr = (wr > rem);
            u64 w   = gwr * rem + (1 - gwr) * wr;
            u64 num = (1ULL << 20) * w + E - 1;
            u64 inc = num / E;
            u64 isB = (n == E);
            u64 adv = last * isB;
            u64 LbRaw = Lb + adv * inc;
            u64 glb = (LbRaw <= LBCAP);
            u64 LbC = glb * LbRaw + (1 - glb) * LBCAP;
            Lb = LbC;
            E  = E + adv * w;

            /* the band test, only on [NLO, NHI) */
            u64 post = (n >= NLO);
            u64 prod = AshC * LbC;
            u64 lhs  = 1000ULL * prod;
            u64 gok  = (lhs <= RHS);
            u64 gacc = (accP >= GLO) * (accP <= GHI);
            u64 rowOK = gacc * glb * (1 - post * (1 - gash * gok));
            bad |= last * (1 - rowOK);

            if (last) {
                if (sgn != ref[n]) {
                    parity_bad++;
                    if (parity_bad == 1) first_parity_bad = n;
                }
                if (absS > maxabs) maxabs = absS;
                if (inc > maxinc) maxinc = inc;
                if (LbRaw > maxLbRaw) maxLbRaw = LbRaw;
                if (post) {
                    if (Ash > maxAsh) maxAsh = Ash;
                    if (lhs > maxlhs) maxlhs = lhs;
                    double r = (double)lhs / (double)RHS;
                    if (r > worst) { worst = r; worst_at = n; }
                }
                if (n == 1000000u) ell_1e6 = absS;
            }
        }
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("bad                 = %llu\n", (unsigned long long)bad);
    printf("parity mismatches   = %llu (first at n=%llu)\n",
           parity_bad, first_parity_bad);
    printf("|ellLval 10^6|      = %llu   (Lean records 916977218216)\n",
           (unsigned long long)ell_1e6);
    printf("final Lb            = %llu   (want 16256727)\n",
           (unsigned long long)Lb);
    printf("final E             = %llu   (want 4000000)\n",
           (unsigned long long)E);
    printf("max |ellLval|       = %llu\n", (unsigned long long)maxabs);
    printf("max Ash             = %llu  (cap %llu)\n",
           (unsigned long long)maxAsh, (unsigned long long)ASHCAP);
    printf("max LbRaw           = %llu  (cap %llu)\n",
           (unsigned long long)maxLbRaw, (unsigned long long)LBCAP);
    printf("max inc             = %llu\n", (unsigned long long)maxinc);
    printf("max LHS             = %llu  (RHS %llu)\n",
           (unsigned long long)maxlhs, (unsigned long long)RHS);
    printf("worst LHS/RHS       = %.9f at n=%u\n", worst, worst_at);
    printf("loopCount           = %llu\n",
           (unsigned long long)LEN * ROUNDS);
    printf("wall (this ref)     = %.1f s\n", secs);
    free(ref);
    return bad != 0;
}
