/* Reference timing model for the CeDyadicFold body.  NOT the artifact:
   a hand-written mirror of `ceRound`, used only to size the run. */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
int main(int argc, char **argv) {
  u64 lo = 20001, R = 2501, up = 0, lfx = 12786308640407511063ULL;
  u64 len = (argc > 1) ? strtoull(argv[1], 0, 10) : 100000;
  u64 acc = 0, ok = 1, pk = 16384, kk = 14, cf = 0;
  u64 qA = 0, rA = 0, qB = 0, rB = 0, q0 = 0, r0 = 0, fA = 0, fB = 0;
  u64 total = len * R;
  for (u64 idx = 0; idx < total; idx++) {
    u64 q = idx / R, rr = idx - q * R, n = lo + q;
    u64 first = (rr == 0), last = (rr == R - 1);
    u64 pk2 = pk * 2, dob = first * (pk2 <= n);
    pk = dob ? pk2 : pk; kk = kk + dob;
    u64 C = n * (n - 1);
    u64 d = first ? 2 : 2 * rr + 1;
    u64 n2 = n * n, p2 = pk * pk, np = n * pk;
    u64 U = n2 - p2, V = 4 * p2 - n2;
    u64 numA = up ? U : 3 * U;
    u64 denA = up ? 2 * np : n2 + 4 * np + p2;
    u64 numB = up ? 3 * V : V;
    u64 denB = up ? 4 * p2 + 8 * np + n2 : 4 * np;
    u64 act = (1 <= rr) & (rr <= 8), isq = (rr == 9), isf = (rr == 10);
    u64 qA0 = first ? 0 : qA, rA0 = first ? numA : rA;
    u64 qB0 = first ? 0 : qB, rB0 = first ? numB : rB;
    u64 cf0 = first ? 0 : cf;
    u64 FA = qA0 + up * (rA0 != 0), FB = qB0 + (1 - up) * (rB0 != 0);
    u64 a1 = (kk + 1) * r0, ge = (a1 <= FB), cb = ge ^ up;
    u64 uA = act ? rA0 * 256 : (isq ? lfx : (isf ? kk * r0 + FA + up * (C - 1) : 0));
    u64 vA = act ? denA : C;
    u64 uB = act ? rB0 * 256 : (isf ? (ge ? FB - a1 : a1 - FB) + cb * (C - 1) : 0);
    u64 vB = act ? denB : C;
    u64 wA = uA / vA, zA = uA - wA * vA;
    u64 wB = uB / vB, zB = uB - wB * vB;
    u64 td = n / d;
    cf = cf0 | (n - td * d == 0);
    qA = act ? qA0 * 256 + wA : qA0; rA = act ? zA : rA0;
    qB = act ? qB0 * 256 + wB : qB0; rB = act ? zB : rB0;
    q0 = isq ? wA : q0; r0 = isq ? zA : r0;
    fA = isf ? wA : fA; fB = isf ? wB : fB;
    u64 FA2 = qA + up * (rA != 0), FB2 = qB + (1 - up) * (rB != 0);
    (void)FA2;
    u64 a1b = (kk + 1) * r0, ge2 = (a1b <= FB2);
    u64 tA = kk * q0 + fA, base = (kk + 1) * q0;
    u64 tB = ge2 ? (fB <= base ? base - fB : tA) : base + fB;
    u64 t = up ? (tA < tB ? tA : tB) : (tA > tB ? tA : tB);
    u64 ct = last * (cf == 0) * t;
    u64 na = acc + ct; ok = ok * (na >= acc); acc = na;
  }
  printf("len=%llu acc=%llu ok=%llu\n", len, acc, ok);
  return 0;
}
