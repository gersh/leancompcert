#!/usr/bin/env python3
"""Oracle for the per-integer `Sum mu(m)/m` residue of `plattstronglive`.

`bench/ref_mob_margin.c` is the oracle for the *mathematics* -- it sweeps to
7.7e9 and reports the true margin against 1/(2 sqrt n).  This is the oracle for
the *arithmetic*: it reproduces, in exactly the residue's fixed point, the four
result slots and the violation count an artifact over [1, N] must print.

    A(n)  = sum_{m<=n} mu(m) * round(2^(63+k)/m)          k = mobWideBits = 15
    U     = 2^(64+k) + A(n)                               two limbs, mod 2^128
    V     = floor(A(n) / 2^(k+1))                         scale 2^62
    c     = ceil(sqrt (n+1))
    fail  <=>  |V| + ceil(n / 2^(k+2)) + 1  >  floor(2^61 / c)

    python3 bench/ref_moblive.py [N] [K]
    lake env lean --run bench/ArraySegEmit.lean plattstronglive 1 N 1 lv.c -

The violation count and all four slots must agree.  Small ranges only -- it is
O(N) memory and pure Python.
"""
import math
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
K = int(sys.argv[2]) if len(sys.argv) > 2 else 15

mu = [1] * (N + 1)
alive = [True] * (N + 1)
primes = []
for i in range(2, N + 1):
    if alive[i]:
        primes.append(i)
        mu[i] = -1
    for p in primes:
        if i * p > N:
            break
        alive[i * p] = False
        if i % p == 0:
            mu[i * p] = 0
            break
        mu[i * p] = -mu[i]

A = 0
c = 1
csq = 1
viol = 0
first = None
for n in range(1, N + 1):
    if mu[n]:
        A += mu[n] * ((2 ** (63 + K) + n // 2) // n)
    if n >= csq:
        c += 1
        csq = csq + 2 * c - 1
    V = A >> (K + 1)          # Python's >> is a floor shift for negatives too
    lhs = abs(V) + -(-n // 2 ** (K + 2)) + 1
    if lhs > 2 ** 61 // c:
        viol += 1
        if first is None:
            first = n

U = (2 ** (64 + K) + A) % 2 ** 128
print("violations %d" % viol)
print("slot0 %d" % (U % 2 ** 64))
print("slot1 %d" % (U >> 64))
print("slot2 %d" % c)
print("slot3 %d" % csq)
if first is not None:
    print("first failing n: %d" % first)
