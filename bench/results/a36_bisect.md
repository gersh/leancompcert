# `interval_bisect` in fixed point: where the wall actually was

The `interval_bisect` family in `claude_math` — 112 call sites across the
Helfgott Appendix A / Theorem 3.1 development — is the largest block of
certificates that does not go through Lean's kernel.  The received explanation
is leaf count.  It is not.

The representative measured here is
`MathExtras/Analysis/HelfgottThm31/C1Bound/A36Bisection.lean`,
`lowBranch_nonneg_mid_low_hi`: for every real `ρ ∈ [1, 6.2]`,

```
0 ≤ 8·υ²·(υ − 1) + 8·υ·Y·ρ − (υ + 2)·Y²·ρ²
```

with `j = √(1 + ρ²)`, `υ = √((1 + j)/2)`, `x = ρ/(2υ(υ + j))`,
`Y = √(1 + x²) − x`.  It is discharged at **depth 8** — 256 leaves — by
`native_decide`.  Two hundred and fifty-six leaves is nothing.  The kernel
still cannot do it: the file reached 13.2 GB at 22 minutes without finishing.

The cost is not the leaves, it is the numbers.  `interval_bisect`'s kernel is
exact `ℚ`, and `sqrtTight_enclose_interval` is a Newton iteration on rationals:
each step squares the denominator, and there are three nested roots per leaf.
By the last leaf the numerators are tens of thousands of bits, and every
comparison drags them through the kernel.

## Change the representation, and the wall is gone

Everything below is `2⁻²⁴` fixed point: `Nat` mantissas, outward rounding
proved in `Verified/Dyadic.lean` and `Verified/DyadicBisect.lean`, largest
intermediate product `2^61.4` — one machine word, at every depth, forever.

| depth | leaves | kernel `decide +kernel` | kernel peak RSS | artifact run | artifact exe |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 256 | **1.01 s** | 0.64 GB | 0.0014 s | 3 704 B |
| 10 | 1 024 | 4.58 s | 1.4 GB | — | — |
| 12 | 4 096 | 21.4 s | 4.3 GB | 0.0024 s | 3 712 B |
| 14 | 16 384 | 90.7 s | 16.3 GB | — | — |
| 16 | 65 536 | (≈ 6 min, ≈ 65 GB — not run) | | 0.0129 s | 3 712 B |
| 20 | 1 048 576 | out of reach | | 0.199 s | 3 712 B |
| 24 | 16 777 216 | out of reach | | 3.02 s | 3 720 B |
| 28 | 268 435 456 | out of reach | | 48.17 s | 3 720 B |

(`user` time throughout; kernel column is `lean` on the sweep alone, artifact
column is CompCert-compiled freestanding, `bench/a36_bisect.sh`.)

**Depth 8 goes from "13.2 GB, unfinished at 22 minutes" to "1.01 s, 0.64 GB,
`decide +kernel`, and `#print axioms` reports no axioms at all."**  That is the
result.  The artifact path is not needed for this certificate, and the trust
downgrade it would cost — an attested binary instead of a kernel proof — does
not have to be paid.

## Where each path runs out

The kernel's cost is a clean factor of four per level of depth, in time and in
memory alike, and memory binds first: depth 14 is 16 GB.  Call the kernel's
reach **2·10⁴ leaves**.

The artifact's cost is `leaves × body`, at a measured **179.5 ns per leaf**
(depth 20/24/28: 189.3, 180.1, 179.5 — the depth-8 and depth-12 figures are
process startup, not work).  The emitted C is 20.7 kB and the freestanding
binary 3.7 kB *at every depth*, because emission is rolled: only the loop bound
in the `while` changes.  CompCert compiles it in 73–80 ms regardless.

So the two paths do not compete; they partition the family:

* every site at depth ≤ 14 — which, by the depth histogram of the 112 sites, is
  **all of them**, the deepest recorded `depth :=` being 12 — is now a kernel
  certificate;
* the deep outliers that are *not* uniform-depth `interval_bisect` — the
  adaptive `A2.cert_lower`, 377 817 leaf cells at maximum depth 31 — are the
  artifact's, and the artifact does 2³¹ uniform leaves in about six minutes.

## Precision is not delicately tuned

The residual's true minimum on `[1, 6.2]` is `2.8678`, attained at the right
endpoint.  The depth-8 fixed-point enclosure proves `≥ 2.0673`.  The gap is
interval *dependency*, not rounding, and the evidence is that precision barely
moves it:

| precision | margin at depth 8 |
| --- | --- |
| `2⁻²⁰` | 2.0668 |
| `2⁻²⁴` | 2.0674 |
| `2⁻²⁶` | 2.0674 |
| `2⁻²⁸` | 2.0674 |

Depth is what moves it (depth 6: −0.33, i.e. the certificate fails; depth 8:
+2.067; depth 12: +2.818) — which is exactly why the source file chose 8, and
why the fixed-point form needs no more depth than the rational one.  Nothing
here was tuned to make the certificate pass.

## Every rounding is outward

| quantity | rounding | direction |
| --- | --- | --- |
| cell left endpoint | floor | left, enlarging the cell |
| cell right endpoint | ceiling | right, enlarging the cell |
| product lower / upper | floor / ceiling | apart |
| quotient lower / upper | floor / ceiling | apart |
| root lower / upper | `Nat.sqrt` / `Nat.sqrt + 1` | apart |
| the residual test | `B.hi ≤ A.lo` | the *upper* bound of the subtrahend against the *lower* bound of the sum |

An inward rounding anywhere would shrink the enclosure and could let a false
claim pass.  Each direction is a separate named theorem
(`Dyadic.mulLo_le`, `mulHi_ge`, `divLo_le`, `divHi_ge`,
`DyadicBisect.sqrtI_lo_sq_le`, `sqrtI_lt_hi_sq`, `Grid.loM_mul_le`,
`Grid.le_hiM_mul`) so a reviewer can check the direction without reading a
definition.

## The three roots are checked, not computed

A fixed-shape register program cannot run `Nat.sqrt`'s data-dependent clamp, so
the artifact does ten Heron steps from `2²⁸` and then *verifies* the two
squared inequalities (`DyadicBisect.sqrtOK`).  Nothing is proved about the
iteration; soundness is `sqrtOK_encloses`, which consumes the check alone.
Eight steps suffice for every radicand here; ten is what ships.  A bad root
makes the artifact report failure, never a wrong answer.

## What is proved, and what is not

Proved, `#print axioms` within `{propext, Classical.choice, Quot.sound}` and
usually far less:

* `A36Bisect.sweep_ok` — all 256 leaves pass, `decide +kernel`. **No axioms.**
* `A36Bisect.leaf_sound`, `j_encloses`, `v_encloses`, `w_encloses` — the four
  inequalities each passing leaf exports, `∀`-quantified over the index.
* `A36Bisect.cells_chain` / `cells_cover` — the grid has no gaps, at every
  depth.
* `A36BisectProgram.programAt_wf` — the fragment obligation, at every depth
  from one proof, so `Program.evalCC_compile` applies and the emitted CCIR
  computes `Program.denote` exactly.

Not proved, and named as such:

* **The analytic step.**  From "the mantissa interval `B` lies below `A`" to
  "`0 ≤ 8υ²(υ−1) + …` for real `ρ`" needs `Real.sqrt` monotonicity and ordered
  field arithmetic, and this package has no Mathlib.  The interface that step
  consumes is the four exported inequalities plus the generic transfer lemmas,
  all already cross-multiplied and quantified over enclosed mantissas.  It is
  one lemma per kernel *shape*, not one per site.
* **The body/`leafOK` simulation.**  That the 472-instruction loop body's `Nat`
  denotation equals `A36Bisect.leafOK` at every index.  `FoldBridge` exists for
  exactly this and it needs a no-overflow invariant on the mod-2⁶⁴ arithmetic
  (true — the largest product is `2^61.4` — but not proved).  Until it is, the
  deep-depth rows of the table above are **measurements, not theorems**.
