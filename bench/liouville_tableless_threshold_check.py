#!/usr/bin/env python3
"""Oracle 2 for ellSweep_cert: can the 65-entry BAND TABLE be removed?

The atom's checker compares |ellLval N| + N against a per-band threshold T_j
read from a 65-entry list.  A scalar `Reflect.Program` has no table, so the
threshold must become a function the machine can carry in registers.

REPLACEMENT UNDER TEST -- a per-candidate log recurrence, no table:

    log(n+1) <= log(n) + 1/n      (concavity)

so an integer accumulator at binary scale SC with

    L(n+1) = L(n) + ceil(2^SC / n),      L(8918) = ceil(2^SC * log 8918)

satisfies  L(n) >= 2^SC * log(n)  for every n, by induction -- one division
per candidate, no table, and the Lean side's existing anchor
`Real.log 8918 <= 9541486/2^20` seeds it.

The atom then needs, for N in [8918, 4e6):
    |ell(N)| * log(N+1) <= 99/1000
and since |ell(N)| <= (|ellLval N| + N)/2^50 and log(N+1) <= L(N+1)/2^SC:
    (|ellLval N| + N) * L(N+1) * 1000 <= 99 * 2^(50+SC)            (*)

That product is ~2^97, far past u64, so the machine tests the SHIFTED form
    ceil((|ellLval N| + N) / 2^SH) * L(N+1) * 1000 <= 99 * 2^(50+SC-SH)
which implies (*) because ceil(x/2^SH) >= x/2^SH.

Checks: the accumulated slack against the knife-edge, and every width.
"""
from math import log, isqrt
import sys

P = 1 << 50
NLO, NHI = 8918, 4_000_000       # the atom's banded range [NLO, NHI)
ANCHOR20 = 9541486               # Lean: log 8918 <= 9541486 / 2^20

def sieve_parity(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for m in range(i * i, n + 1, i):
                if spf[m] == m:
                    spf[m] = i
        i += 1
    par = bytearray(n + 1)
    for m in range(2, n + 1):
        par[m] = par[m // spf[m]] ^ 1
    return par

print("sieving lambda ...")
par = sieve_parity(NHI)
print("  done")

def run(SC, SH, verbose=False):
    """Return (ok, min_slack_ratio, worst_n, widths)."""
    L = -(-ANCHOR20 * (1 << SC) // (1 << 20))       # ceil(anchor * 2^(SC-20))
    assert L >= (1 << SC) * log(8918)
    RHS = 99 * (1 << (50 + SC - SH))
    S = 0
    for n in range(1, NLO):                          # prefix, builds ellLval
        S += (1 if par[n] == 0 else -1) * (P // n)
    ok = True
    worst = (2.0, 0)
    maxlhs = 0
    maxL = 0
    for N in range(NLO, NHI):
        S += (1 if par[N] == 0 else -1) * (P // N)
        # L is advanced to cover log(N+1)
        L += -(-(1 << SC) // N)                      # ceil(2^SC / N)
        A = abs(S) + N
        Ash = -(-A // (1 << SH))                     # ceil(A / 2^SH)
        lhs = Ash * L * 1000
        maxlhs = max(maxlhs, lhs)
        maxL = max(maxL, L)
        if lhs > RHS:
            ok = False
            if verbose and worst[1] == 0:
                print(f"    FAIL at N={N}: lhs/rhs = {lhs/RHS:.6f}")
        r = lhs / RHS
        if r < 2.0 and r > worst[0] if False else False:
            pass
        if r > worst[0] if worst[1] == 0 and False else False:
            pass
        if worst[1] == 0 or r > worst[0]:
            worst = (r, N)
    return ok, worst, maxlhs, maxL

# the true knife-edge, for reference
S = 0
for n in range(1, NLO):
    S += (1 if par[n] == 0 else -1) * (P // n)
knife = (0.0, 0)
for N in range(NLO, NHI):
    S += (1 if par[N] == 0 else -1) * (P // N)
    r = (abs(S) / P) * log(N + 1) / 0.099
    if r > knife[0]:
        knife = (r, N)
print(f"exact knife-edge: ratio {knife[0]:.6f} at N = {knife[1]}")

for SC, SH in [(30, 25), (31, 26), (29, 24), (28, 23), (27, 22), (32, 27)]:
    ok, worst, maxlhs, maxL = run(SC, SH)
    print(f"SC={SC} SH={SH}: pass={ok}  worst lhs/rhs = {worst[0]:.6f} at N={worst[1]}")
    print(f"    max LHS = {maxlhs} ({maxlhs.bit_length()} bits), "
          f"max L = {maxL} ({maxL.bit_length()} bits), "
          f"RHS = {99*(1<<(50+SC-SH))} ({(99*(1<<(50+SC-SH))).bit_length()} bits)")
