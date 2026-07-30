#!/usr/bin/env python3
"""Oracle for the per-integer Mertens / CDEM tests of `mertenslive`.

`bench/ref_seg.c` is the oracle for the accumulators; this is the oracle for
the four clauses the per-integer residue tests, in exactly the residue's
arithmetic:

    s     = floor(sqrt(n))                 maintained incrementally there
    thrM  = (floor(0.571*2^32) * s) >> 32  Hurst, rounded down to a dyadic
    thrG  = floor(b*2^36) * s              CDEM, likewise
    clauses:  M > thrM,  M < -thrM,  G > thrG,  G < c + n + 1 - thrG
    with     G = Q*2^36 - c*n,  c = floor((6/pi^2)*2^36) = 41776432333

It sieves mu directly, so nothing about the artifact's sieve is assumed.
Small ranges only -- it is O(N) memory and pure Python.

    python3 bench/ref_live.py [N] [bNum] [bDen]
    lake env lean --run bench/ArraySegEmit.lean mertenslive 1 N 1 lv.c -

The two violation counts, M, Q and floor(sqrt(N)) must agree.
"""
import math
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
bNum = int(sys.argv[2]) if len(sys.argv) > 2 else 755
bDen = int(sys.argv[3]) if len(sys.argv) > 3 else 10000

CDEM_C = 41776432333          # floor((6/pi^2) * 2^36), as the artifact carries it
CDEM_SCALE = 36
HURST_A = 571 * 2 ** 32 // 1000
CDEM_B = bNum * 2 ** CDEM_SCALE // bDen

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

M = Q = viol = 0
for n in range(1, N + 1):
    M += mu[n]
    Q += abs(mu[n])
    s = math.isqrt(n)
    thrM = (HURST_A * s) >> 32
    thrG = CDEM_B * s
    G = Q * 2 ** CDEM_SCALE - CDEM_C * n
    viol += (M > thrM) + (M < -thrM) + (G > thrG) + (G < CDEM_C + n + 1 - thrG)

print("violations %d" % viol)
print("slot0 %d" % ((1 << 40) + M))
print("slot1 %d" % Q)
print("slot2 %d" % ((1 << 62) + G))
print("slot3 %d" % math.isqrt(N))
