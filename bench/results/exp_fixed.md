# The fixed-point exponential as a compiled artifact — what it costs

All numbers: single core, `/usr/bin/time`, elapsed seconds, best of two runs.
`gcc` is `gcc -O2`; `ccomp` is CompCert `-O`.  Every artifact in the agreement
table below is emitted from `Ports/ExpFixPort.expProgram` by
`bench/ExpFixEmit.lean`, and is compared against `bench/ref_exp.c`, an
independent plain-C reference that takes its roots by a floating seed plus an
exact integer correction rather than by the artifact's digit recurrence.

## What is being computed

`expFix P S a` is the mantissa of `2 ^ (a / 2^S)` at precision `P`, and
`Verified/ExpFixed.lean` proves the two-sided integer bracket

```
expFix P S a ^ (2^S)  ≤  2 ^ (P·2^S + a)  ≤  expFixHi P S a ^ (2^S),
      expFixHi P S a  =  expFix P S a + S · 2^(a / 2^S)
```

— a fixed-point enclosure of width exactly `S` ulps, one per round.
`rpow_bracket` composes it with `LogFixed` to bracket `n ^ (Y / 2^T)`.

The artifact's loop body is one round: two instructions to take the next
exponent bit, two to form the radicand `x · 2^P · 2^b`, two to initialise the
root loop, `7·(P+1)` for the restoring radix-4 square root, and eight to
certify the root against `ExpFixed.expOK`'s two comparisons.  At `P = 30` that
is **231 instructions and no division of any width**.

The root's digit recurrence is *not* proved.  The eight certifying
instructions are what carry the soundness: `ExpFixed.expOK_sound` says a run
whose comparisons all pass is `expIter`, so `expFix_bracket` applies to it.
The artifact returns the violation count, and every run below returns `0`.

## Agreement

`P = 30` throughout — the proved word-size bound (`ExpFixed.expIter_fits_64`:
at `P ≤ 30` the radicand and the successor square are below `2^63`).  Four
sizes, three independent producers, bit for bit:

| `S` | exponent `R` | `2^(R/2^S)` | gcc | ccomp | `ref_exp.c` | Lean kernel |
| --- | --- | --- | --- | --- | --- | --- |
| 16 | 40503 | `2^0.61804…` | 1647951608 | 1647951608 | 1647951608 | — |
| 24 | 8388608 | `√2` | 1518500249 | 1518500249 | 1518500249 | 1518500249 |
| 24 | 9814955 | `2^(log₂3−1)` | 1610673474 | 1610673474 | 1610673474 | 1610673474 |
| 28 | 164707077 | `2^0.61354…` | 1642881953 | 1642881953 | 1642881953 | — |

Violation count `0` in all twelve runs.  The two exact floors are
`⌊2³⁰√2⌋ = 1518500249` — hit on the nose — and `⌊2³⁰·2^(9814955/2²⁴)⌋ =
1610673475`, hit one ulp low against a budget of `S = 24`.

The "Lean kernel" column is `Ports/ExpFixPort.Check`, which evaluates
`(expProgram …).denote` in the kernel; `Verified/ExpFixed.Check` certifies the
same values for `expFrac` — which is written with `Nat.sqrt` and does not
reduce — through `expOK_sound` and a twenty-four-entry transcript.  So the
digit recurrence, `Nat.sqrt`, `gcc`, `ccomp` and an independent C reference all
produce the same integers.

## Cost

`P = 30`, `S = 24`, exponent `9814955`, loop count varied.  After round `S` the
exponent register is empty and every later round recomputes `2^P`; the body is
branch-free and its instruction count is data-independent, so the cost per
round is unchanged, which the linearity below confirms.

| rounds | instructions | gcc (s) | ccomp (s) | gcc ns/round | ccomp ns/round |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 6 000 000 | 1.386·10⁹ | 0.29 | 0.34 | 48.3 | 56.7 |
| 12 000 000 | 2.772·10⁹ | 0.59 | 0.66 | 49.2 | 55.0 |
| 24 000 000 | 5.544·10⁹ | 1.13 | 1.28 | 47.1 | 53.3 |

So **`≈ 48 ns` per round under gcc and `≈ 54 ns` under ccomp**, i.e. `0.21` and
`0.23 ns` per instruction.  That is about `1.8×` the `0.1244 ns/instruction`
calibrated for the segmented sieve in `array_seg_folds.md`, and the reason is
visible in the body: the digit recurrence is a serial dependency chain — every
iteration's compare feeds the next iteration's add — so there is little for the
machine to overlap.

At `S = 24` rounds one exponential therefore costs

| | gcc | ccomp |
| --- | ---: | ---: |
| `expFix` (24 rounds) | **1.13 µs** | **1.28 µs** |
| `logFix` (24 rounds × 21 instructions, at the sieve's calibration) | 0.06 µs | 0.06 µs |
| `rpow = exp ∘ log` | **1.19 µs** | **1.34 µs** |

## Where the precision goes

The bracket's width is `S` ulps at precision `P`, i.e. a relative enclosure
width of `S · 2^(−P)` (`expFix_rel_width`).  At `P = 30`, `S = 24` that is
`2.2 · 10^(−8)`.  Through `rpow` the logarithm's own two-ulp window enters
multiplied by the exponent `Y`, which is the term `rpowHiA` carries explicitly.

Raising `P` is cheap in instructions (`7` per bit) and free in rounds, but
`P = 30` is the wall for a pure-`u64` artifact: `P = 31` still fits the
radicand in 64 bits but lets `(v+1)²` reach exactly `2^64`, and the certifying
comparison would wrap.  Above that the round needs the wide product of
`Verified/MulWide.lean`, which roughly triples the certification cost and
leaves the digit recurrence needing a two-limb remainder.

## What this does not measure

This is the exponential alone.  It is not a port of any cite family; in
particular it is not the Helfgott Prop 12.2.4 large-sieve table, which needs
totients, prime-factor products and a `G_q` accumulation on top.  See
`docs/` for the projection.
