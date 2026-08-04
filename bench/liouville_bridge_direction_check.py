#!/usr/bin/env python3
"""Independent check of the DIRECTION of bridge fact (C).

Claim under test (from the banked design):
    (A)  A(N) * L(N+1) * 1000 <= 99 * 2^(50+SC)        [artifact certifies]
    (C)  L(N+1) * 2^20 <= L_j * 2^SC                    [checked exhaustively]
    ==>  (B)  A(N) <= T_j                               [what the atom needs]

Algebra says (A) gives A <= 99*2^(50+SC)/(1000*L), and (B) needs
A*1000*L_j <= 99*2^70, so the implication needs  L_j * 2^SC <= L * 2^20,
i.e. the REVERSE of (C).  Test directly: is the artifact's per-N threshold
    Ttl(N) = floor(99*2^(50+SC) / (1000*L(N+1)))
ever LARGER than the band threshold T_j?  If so, (A) does not imply (B).
"""
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
print(f"range [{NLO}, {NHI})")
par = sieve_parity(NHI)

L = -(-ANCHOR20 * (1 << SC) // (1 << 20))
S = 0
for n in range(1, NLO):
    S += (1 if par[n] == 0 else -1) * (P // n)

n = NLO
worst_excess = 0.0; worst_at = None; n_excess = 0
worst_shortfall = 1e9; short_at = None
first_bad = None
for (w, T, Lj) in ellBands:
    for _ in range(w):
        S += (1 if par[n] == 0 else -1) * (P // n)
        L += -(-(1 << SC) // n)
        A = abs(S) + n
        # the artifact's own per-N threshold, exactly as (A) states it
        Ttl = 99 * (1 << (50 + SC)) // (1000 * L)
        if Ttl > T:
            n_excess += 1
            if first_bad is None:
                first_bad = (n, Ttl, T, A)
            r = Ttl / T
            if r > worst_excess:
                worst_excess, worst_at = r, n
        else:
            r = Ttl / T
            if r < worst_shortfall:
                worst_shortfall, short_at = r, n
        n += 1

print(f"N where the tableless threshold EXCEEDS the band threshold: {n_excess}"
      f" of {NHI-NLO}")
if first_bad:
    print(f"  first at n={first_bad[0]}: Ttl={first_bad[1]} > T={first_bad[2]}"
          f"  (A={first_bad[3]})")
    print(f"  worst Ttl/T = {worst_excess:.9f} at n={worst_at}")
print("VERDICT: (A)+(C) => (B) is "
      + ("INVALID (tableless bound is strictly weaker)" if n_excess
         else "plausible"))
