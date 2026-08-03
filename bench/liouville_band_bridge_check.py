#!/usr/bin/env python3
"""Oracle 3 -- the DECISIVE check for keeping the atom's statement unchanged.

`ellSweep_cert` is a Boolean about `ladderRun ellBands`, so the 65-entry band
table cannot be dropped: it is part of the statement.  The plan is therefore

    artifact certifies the TABLELESS bound
        (|ellLval N| + N) * L(N+1) * 1000 <= 99 * 2^(50+SC)          (A)
    Lean derives the PER-BAND bound
        |ellLval N| + N <= T_j                                        (B)
    and (B) for every N drives `bandRun`/`ladderRun` to `true` by induction.

(A) => (B) needs exactly one comparison, for every N in every band j:

        L(N+1) * 2^20 <= L_j * 2^SC                                   (C)

i.e. the artifact's per-N fixed-point log bound must be at least as SHARP as
the band's coarse one.  If (C) fails anywhere the whole route is dead, so it
is checked here exhaustively over all 3 991 082 candidates BEFORE any Lean.
"""
from math import log
import sys
sys.path.insert(0, '.')
from liouville_bands import ellBands

P = 1 << 50
NLO = 8918
ANCHOR20 = 9541486
SC, SH = 30, 25

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

NHI = NLO + sum(b[0] for b in ellBands)
print(f"range [{NLO}, {NHI})  ({NHI - NLO} candidates, {len(ellBands)} bands)")
par = sieve_parity(NHI)

# ---- (C): is the per-N recurrence at least as sharp as every band's L_j? ----
L = -(-ANCHOR20 * (1 << SC) // (1 << 20))
S = 0
for n in range(1, NLO):
    S += (1 if par[n] == 0 else -1) * (P // n)

badC = 0; worstC = 0.0; worstCat = None
badB = 0; worstB = 0.0; worstBat = None
n = NLO
for (w, T, Lj) in ellBands:
    for _ in range(w):
        S += (1 if par[n] == 0 else -1) * (P // n)
        L += -(-(1 << SC) // n)                       # ceil(2^SC / n)
        # (C)
        lhsC, rhsC = L * (1 << 20), Lj * (1 << SC)
        if lhsC > rhsC:
            badC += 1
            if badC < 4:
                print(f"  (C) FAILS at n={n}: L*2^20={lhsC} > L_j*2^SC={rhsC}")
        r = lhsC / rhsC
        if r > worstC: worstC, worstCat = r, n
        # (B) the band bound the atom actually needs
        A = abs(S) + n
        if A > T:
            badB += 1
            if badB < 4:
                print(f"  (B) FAILS at n={n}: |ellLval|+n={A} > T={T}")
        rb = A / T
        if rb > worstB: worstB, worstBat = rb, n
        n += 1

print(f"(C) sharper-than-band : {badC} failures; worst ratio {worstC:.6f} at n={worstCat}")
print(f"(B) atom's band bound : {badB} failures; worst ratio {worstB:.6f} at n={worstBat}")
print("=> route viable" if badC == 0 and badB == 0 else "=> ROUTE DEAD")
