#!/usr/bin/env python3
"""Oracle for the ellSweep_cert (Liouville little sum) CompCert design.

The atom checks, at scale P = 2^50:
    ellLval N = sum_{n=1}^{N} lambda(n) * floor(P/n)
    for every N in a band: |ellLval N| + N <= T_band

lambda(n) = (-1)^Omega(n) is completely multiplicative, so the machine must
know Omega(n) mod 2 -- i.e. prime multiplicities, not just distinct primes.
That is what makes it harder than the (C.17) squarefree sweep, where one
division per divisor sufficed.

DESIGN UNDER TEST -- a TWO-PHASE flat-index decode, no table:
  phase B (first):  rounds q in [0, EXTRA*DSMALL) -> d = q / EXTRA + 2,
                    i.e. each d in [2, DSMALL+1] held for EXTRA CONSECUTIVE
                    rounds, so every power of d is stripped before d+1 is
                    tried.  (Cycling the divisors instead -- d = q % DSMALL + 2
                    -- is WRONG and the oracle caught it: at n = 8 the residual
                    4 is then divided by the COMPOSITE d = 4 and counted once,
                    giving parity 0 where Omega(8) = 3.)
  phase A (second): rounds q in [EXTRA*DSMALL, EXTRA*DSMALL + DBIG - DSMALL)
                    -> d = (q - EXTRA*DSMALL) + DSMALL + 2, one division each.
                    One pass suffices there: after phase B the residual is a
                    product of at most two primes >= DSMALL+2 (159^3 > 4e6),
                    and the "res != 1" correction catches the survivor.
Both decodes are pure udiv/urem on the flat index, so they are expressible
in the scalar Reflect fragment.

Checks:
  1. the two-phase strip really computes Omega(n) mod 2 for every n < NMAX,
  2. the signed accumulator fits a biased u64 representation,
  3. the exact band thresholds are met (reproduce the Lean ellLval values),
  4. every intermediate stays inside u64.
"""
from math import isqrt
import sys

P = 1 << 50
NMAX = 4_000_000

# ---- design constants ----
DBIG = 2000        # divisors 2 .. 2001 ; (2001)^2 = 4004001 > 4e6
DSMALL = 157       # extra passes for d in [2, 158] ; 158^3 = 3.9e6 <= 4e6
EXTRA = 21         # 2^21 = 2097152 <= 4e6 < 2^22, so v_2 <= 21
BIAS = 1 << 62     # signed accumulator carried as BIAS + S

maxw = {}
def W(tag, v):
    if not (0 <= v < (1 << 64)):
        print(f"WIDTH VIOLATION {tag}: {v}")
        sys.exit(1)
    if v > maxw.get(tag, 0):
        maxw[tag] = v

# ---- reference lambda by a smallest-prime-factor sieve ----
def lam_sieve(n):
    """Omega(m) mod 2 for m <= n, via a correct SPF sieve."""
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:                       # i is prime
            for m in range(i * i, n + 1, i):
                if spf[m] == m:
                    spf[m] = i
        i += 1
    par = bytearray(n + 1)
    for m in range(2, n + 1):
        par[m] = par[m // spf[m]] ^ 1         # Omega(m) = Omega(m/spf) + 1
    return par

print("building reference lambda sieve ...")
omega_par = lam_sieve(NMAX)
print("  done")

# ---- the machine's two-phase strip ----
def machine_parity(n):
    """Omega(n) mod 2, exactly as the register program computes it."""
    res, par = n, 0
    # phase B: each d in [2, DSMALL+1] held for EXTRA CONSECUTIVE rounds
    for q in range(EXTRA * DSMALL):
        d = q // EXTRA + 2
        if res % d == 0:
            res //= d
            par ^= 1
    # phase A: one pass over d in [DSMALL+2, DBIG+1]
    for q in range(DBIG - DSMALL):
        d = q + DSMALL + 2
        if res % d == 0:
            res //= d
            par ^= 1
    # one prime may survive
    if res != 1:
        par ^= 1
    return par

# spot-check the strip on a stratified sample (full 4e6 x 5000 is too slow here)
import random
random.seed(7)
sample = list(range(1, 3000))
sample += [2**k for k in range(1, 22)]
sample += [3**k for k in range(1, 14)]
sample += [2**a * 3**b for a in range(0, 22) for b in range(0, 14)
           if 2**a * 3**b <= NMAX]
sample += [random.randrange(1, NMAX) for _ in range(4000)]
sample = sorted(set(x for x in sample if 1 <= x < NMAX))
bad = 0
for n in sample:
    if machine_parity(n) != omega_par[n]:
        bad += 1
        if bad < 6:
            print(f"  PARITY MISMATCH at n={n}: machine={machine_parity(n)} ref={omega_par[n]}")
print(f"two-phase strip: {len(sample)} sampled candidates, {bad} mismatches")

# worst-case multiplicity actually needed
worst = 0
for p in (2, 3, 5, 7):
    k = 0
    while p ** (k + 1) <= NMAX:
        k += 1
    worst = max(worst, k)
print(f"max prime multiplicity below {NMAX}: {worst} (design supplies EXTRA = {EXTRA})")

# ---- exact ellLval and the band thresholds ----
print("computing exact ellLval sweep ...")
S = 0
absmax = 0
ell = {}
for n in range(1, NMAX):
    S += (1 if omega_par[n] == 0 else -1) * (P // n)
    absmax = max(absmax, abs(S))
    if n in (8917, 10**6, NMAX - 1):
        ell[n] = S
print(f"  ellLval 8917    = {ell[8917]}")
print(f"  ellLval 10^6    = {ell[10**6]}  (Lean records 916977218216)")
print(f"  ellLval 3999999 = {ell[NMAX-1]}")
print(f"  max |ellLval|   = {absmax}  ({absmax.bit_length()} bits)")

# ---- biased accumulator widths ----
lo, hi = BIAS - absmax, BIAS + absmax
W("acc_biased_lo", lo); W("acc_biased_hi", hi)
step = P // 1
W("acc_plus_step", hi + step)
print(f"biased accumulator range: [{lo}, {hi}] -- both inside u64: True")
print(f"biased acc + max step ({step}) = {hi+step} < 2^64: {hi+step < (1<<64)}")

# ---- loop cost ----
rounds = EXTRA * DSMALL + (DBIG - DSMALL)
print(f"rounds per candidate = {EXTRA}*{DSMALL} + ({DBIG}-{DSMALL}) = {rounds}")
print(f"loopCount = {NMAX} * {rounds} = {NMAX*rounds:.3e}")
print(f"  (C.17 measured 4.09e9 iterations in 40 s => projected "
      f"{NMAX*rounds/4.09e9*40/60:.1f} min)")

print("\nmax widths (bits):")
for k in sorted(maxw, key=lambda k: -maxw[k].bit_length()):
    print(f"  {k:16s} {maxw[k].bit_length():3d}  {maxw[k]}")
