# Compiled finite even-Goldbach witness verification

Target: the finite binary-Goldbach input used by Helfgott--Platt, namely every
even integer from `4` through `4·10^18`.  The primary computation is Oliveira
e Silva--Herzog--Pardi, *Math. Comp.* 83 (2014), Algorithm 1.4.  It uses
independent intervals of `10^12` integers, a segmented Eratosthenes sieve, a
small-prime scan, and a fallback search for any row not covered by the fast
scan.

## Proved checker

`LeanCompCert/Ports/TGEvenGoldbach.lean` implements a separate fail-closed
consumer.  Four caller-owned array planes contain `p`, `q`, and the compiled
primality bits for `p` and `q`.  One constant-size rolled array loop checks:

```text
p <= n,  q = n - p,  primeBit(p) = 1,  primeBit(q) = 1
```

for `n = evenLo + 2*k`.  Invalid rows OR one into a monotone verdict bit.
`covers_of_rolled_receipts` consumes two actual rolled-CompCert receipts:

1. the fail-safe audit receipt, which proves the partial array program had a
   source execution; and
2. the ordinary zero receipt, which identifies that execution's verdict.

Together with the prime-bit semantics supplied by preceding compiled sieve or
certificate stages, zero implies a prime-pair decomposition for every row.
The proof is symbolic in `count`; Lean does not scan rows or test primality.
Fresh axiom prints are `[propext, Classical.choice, Quot.sound]` for the full
receipt theorem and `[propext, Quot.sound]` before the fail-safe audit wrapper.

Proof-only source check under a 64 GiB virtual-memory cap and one Lean worker:
`0.79 s`, `0.59 GiB` peak RSS.  The Lake target builds in about `0.9 s` after
its dependencies are present.  No source-scale computation was run.

## Receipt-check benchmark

`bench/TGEvenGoldbachEmit.lean` emits the ordinary verifier, its fail-safe
audit, and a synthetic timing harness.  The synthetic rows exercise the same
four loads and arithmetic but are not evidence for Goldbach.  On this aarch64
host, with `10,000,000` rows (`320 MB`) and five repetitions:

| CompCert artifact | CPU seconds / 50,000,000 rows | ns/row |
| --- | ---: | ---: |
| ordinary zero checker | 0.072439 | 1.448780 |
| fail-safe audit | 0.070809 | 1.416180 |
| both required receipts | 0.143248 | **2.864960** |

The emitted translation unit is constant-size (about 4 KB with both
functions); `ccomp -O2` took `0.03 s` and 17 MB RSS.  The run used about
`313 MB` RSS.  Shards of `10^8` rows would use `3.2 GB` for these four simple
planes and remain comfortably below the repository's 64 GiB cap.

There are approximately `2·10^18` even rows through `4·10^18`.  At the
measured combined rate, checking both receipts costs

```text
2.864960 ns/row * 2·10^18 rows = 5.72992·10^9 CPU seconds
                                    = about 181.6 core-years.
```

This is the checker cost, not the whole computation.  It parallelizes by
independent intervals and would ideally take about 66.3 days on 1,000 cores.

## Whole-route estimate

The cited 2014 computation reports roughly **770 one-core CPU-years** for its
complete optimized producer/checking campaign.  Reusing a producer at that
rate and adding the two proof-carrying receipt scans gives a first
paper-faithful estimate of about **952 core-years**.  This is the best estimate
for the intended optimized route until its dedicated bitset sieve has been
ported and benchmarked through CompCert.

There is already a proved correctness route for prime masks through
`RS62SegmentedPrimeMask`, built on the general 111-instruction segmented
array core.  As a correctness-first fallback, its measured `17.70 ns` per
loop iteration and an estimated `3.5` mark iterations per odd integer near
`4·10^18` project roughly **3,900 core-years** for mask production, before
the 181.6-year receipt scan.  That is deliberately labelled an order estimate:
the production-scale prime count, mark budget, and dedicated Goldbach memory
layout have not yet been benchmarked.  Porting Algorithm 1.4's packed
prime-bit sieve is therefore the important performance task; the proved
witness consumer is already cheap relative to either producer estimate.

## Reproduction

The benchmark is intentionally small:

```bash
lake env lean --run bench/TGEvenGoldbachEmit.lean \
  10000000 5 /tmp/tg_even_goldbach.c
ccomp -O2 /tmp/tg_even_goldbach.c -o /tmp/tg_even_goldbach
/tmp/tg_even_goldbach
```

It does not execute, sample, or claim any part of the `4·10^18` campaign.
