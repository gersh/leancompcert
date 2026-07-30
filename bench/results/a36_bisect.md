# `interval_bisect` in fixed point: where the wall actually was

The `interval_bisect` family in `claude_math` — 143 independent kernel
evaluations across the Helfgott Appendix A / Theorem 3.1 development, the
Corollary C.13 certificate, and the ext SII margin grid — is the largest block
of certificates that does not go through Lean's kernel.  The received
explanation is leaf count.  It is not.

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
| 8 | 256 | **1.06 s** | 0.64 GB | 0.0010 s | 3 744 B |
| 10 | 1 024 | 5.21 s | 1.4 GB | — | — |
| 12 | 4 096 | 19.8 s | 4.4 GB | 0.0019 s | 3 744 B |
| 14 | 16 384 | 101.6 s | 16.6 GB | — | — |
| 16 | 65 536 | (≈ 6 min, ≈ 65 GB — not run) | | 0.0126 s | 3 744 B |
| 20 | 1 048 576 | out of reach | | 0.188 s | 3 744 B |
| 24 | 16 777 216 | out of reach | | 2.989 s | 3 760 B |
| 28 | 268 435 456 | out of reach | | 47.73 s | 3 760 B |
| 31 | 2 147 483 648 | out of reach | | 382.4 s | 3 768 B |

(`user` time throughout; kernel column is `lean` on the sweep alone, artifact
column is CompCert-compiled freestanding, `bench/a36_bisect.sh`, shipped
476-instruction body.  Every artifact row exits `0`: every leaf passes its
three root checks, its two ordering checks and its residual comparison.)

**Depth 8 goes from "13.2 GB, unfinished at 22 minutes" to "1.06 s, 0.64 GB,
`decide +kernel`, and `#print axioms` reports no axioms at all."**  That is the
result.  The artifact path is not needed for this certificate, and the trust
downgrade it would cost — an attested binary instead of a kernel proof — does
not have to be paid.

## Where each path runs out

The kernel's cost is a clean factor of four per level of depth, in time and in
memory alike, and memory binds first: depth 14 is 16.6 GB.  Call the kernel's
reach **2·10⁴ leaves**.

The artifact's cost is `leaves × body`, at a measured **177.8 ns per leaf**
(depth 20/24/28/31: 179.5, 178.2, 177.8, 178.1 — the depth-8 and depth-12
figures are process startup, not work).  The emitted C is 20.9 kB and the
freestanding binary 3.7 kB *at every depth*, because emission is rolled: only
the loop bound in the `while` changes.  CompCert compiles it in 54–80 ms
regardless.

So the two paths do not compete; they partition the family:

* every uniform-depth `interval_bisect` site is at depth ≤ 14 — the modal depth
  is 4–5, the maximum anywhere is 14 (`H1FiniteClaim`), and the whole family is
  about 2·10⁴ leaf cells in total.  **All of it is inside the kernel's reach**
  once the arithmetic is fixed point;
* the deep outliers that are *not* uniform-depth `interval_bisect` — the
  adaptive `A2.cert_lower`, 377 817 leaf cells at maximum depth 31 — are the
  artifact's.  Measured: 2³¹ uniform leaves, 382.4 s, exit 0.

## What the rest of the family would cost

A survey of all 143 sites (kernels, depths, primitives):

| primitive set | sites | ported by |
| --- | ---: | --- |
| √ and ÷ only | 24 | this file, verbatim |
| + log | ~116 | a fixed-point `log` |
| + exp | 13 | a fixed-point `exp` |
| all four | 8 | both |
| trig / arctan / arccos | **0** | — |

The count that matters is not 143 but **19**: that is how many *distinct kernel
functions* there are, and six of them (`corC13MarginKernel`, `mkA`, `mkB`,
`mkC`, `res2K`, `sqrtBranchKernel`) serve 128 of the 143 sites.  The A29 / A36 /
A32 / A33 group additionally shares one `j`/`υ`/`Y`/`x` sub-kernel layer, which
is exactly what `A36Bisect.leafDataAt` already is.  So the port is roughly
nineteen kernel rewrites and nineteen soundness re-proofs, not one hundred and
forty-three — and the two missing primitives are `log` and `exp`, both of which
already exist in this package's neighbourhood (`Verified/LogFixed.lean` computes
`⌊2^S·log₂ n⌋` to two ulps).

Two things make this less speculative than it sounds. First, `claude_math`
already caps denominators inside exact ℚ in three places (`rdPos 128` in
`A33Tight`, `roundOut 48` in the C.13 kernel, `roundOut 80/90` in A.33) —
the development has been drifting toward fixed point on its own. Second, there
is already a complete Q24 fixed-point reimplementation of the largest kernel
family, `ext/helfgott_certificates/HelfgottCertificates/SIIMarginFixed/`,
discharged by plain `decide`. Its recorded cost is 16–31 s and 2.3–3.5 GiB
**per leaf**, against 4 ms per leaf here; its kernel carries a 12-term `log`
that this one does not, so the two are not directly comparable, but a factor of
several thousand per leaf is not explained by the logarithm alone, and it is
worth finding out where it goes before porting the remaining kernels.

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
| the divisor | checked nonzero | `divHi` at `0` would return `0`, i.e. inward |
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
* `A36Bisect.leaf_sound`, `j_encloses`, `v_encloses`, `w_encloses`,
  `differences_exact` — the six inequalities each passing leaf exports,
  `∀`-quantified over the index.
* `A36Bisect.cells_chain` / `cells_cover` — the grid has no gaps, at every
  depth.
* `A36BisectProgram.programAt_wf` — the fragment obligation, at every depth
  from one proof, so `Program.evalCC_compile` applies and the emitted CCIR
  computes `Program.denote` exactly.

Not proved, and named as such:

* **The analytic step.**  From "the mantissa interval `B` lies below `A`" to
  "`0 ≤ 8υ²(υ−1) + …` for real `ρ`" needs `Real.sqrt` monotonicity and ordered
  field arithmetic, and this package has no Mathlib.  The interface that step
  consumes is the six exported inequalities plus the generic transfer lemmas,
  all already cross-multiplied and quantified over enclosed mantissas.  It is
  one lemma per kernel *shape*, not one per site.
* **The body/`leafOK` simulation.**  That the 476-instruction loop body's `Nat`
  denotation equals `A36Bisect.leafOK` at every index.  `FoldBridge` exists for
  exactly this and it needs a no-overflow invariant on the mod-2⁶⁴ arithmetic
  (true — the largest product is `2^61.4` — but not proved).  Until it is, the
  deep-depth rows of the table above are **measurements, not theorems**.
