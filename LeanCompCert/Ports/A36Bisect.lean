import LeanCompCert.Verified.DyadicBisect

/-!
# Helfgott A.36, low branch: an `interval_bisect` certificate in fixed point

The source certificate is `claude_math`
`MathExtras/Analysis/HelfgottThm31/C1Bound/A36Bisection.lean`, theorem
`lowBranch_nonneg_mid_low_hi`.  It asserts, for every real `ρ ∈ [1, 6.2]`,

```
0 ≤ 8·υ²·(υ − 1) + 8·υ·Y·ρ − (υ + 2)·Y²·ρ²
```

with `j = √(1 + ρ²)`, `υ = √((1 + j)/2)`, `x = ρ / (2υ(υ + j))`,
`Y = √(1 + x²) − x`, and discharges it by

```
interval_bisect_lower_bound_of_subset_on … (depth := 8) (c := 0) (by native_decide)
```

i.e. by asking whether `0 ≤ (interval_bisect (lowBranchKernel 4) 1 (62/10) 8).lo`.
That question is a **rational** computation: the kernel is exact `ℚ` interval
arithmetic with a Newton square root, so every one of the 2⁸ leaves carries
numerators and denominators whose bit length doubles at each nested root.  It is
the reason the family does not go through Lean's kernel: it is 256 leaves, not
a large number, and it still does not finish.

## What this file changes

Nothing about the mathematics; only the number representation.  Every quantity
is a `Nat` mantissa at the static precision `2⁻²⁴`, every operation rounds
**outward** (`Verified/Dyadic.lean`, `Verified/DyadicBisect.lean`), and the
whole leaf is therefore a bounded-width computation: the largest intermediate
product is `2^61.4`, so the entire certificate fits in machine words and never
grows.

The cost of that is precision, and the certificate has room for it: the true
minimum of the residual on `[1, 6.2]` is `2.87` (attained at the right
endpoint), and the depth-8 fixed-point enclosure proves `≥ 2.067`.  The
enclosure is limited by interval *dependency*, not by rounding — at `p = 20`
the margin is `2.0668` and at `p = 28` it is `2.0674` — so the precision is not
delicately tuned, and the same depth the source file chose is the depth that
works.

## The three roots are guessed and checked, not computed

`Nat.sqrt`'s clamp loop is data-dependent, which a fixed-shape register program
cannot have.  Instead each root is produced by a fixed 10-step Newton iteration
from `2²⁸` — about which **nothing is proved** — and then *verified* by
`DyadicBisect.sqrtOK`, one multiply and one comparison per side.  Soundness
rests on the check alone (`sqrtOK_encloses`), so the iteration is free to be
any shape at all; if it ever returned a wrong root the leaf would report
failure rather than a wrong answer.

## What is proved here

* `sweep_ok` — all 256 leaves pass, **by `decide +kernel`**: no
  `native_decide`, no compiler, no runtime.  This is the headline: the
  fixed-point form of the certificate is not merely artifact-sized, it is
  *kernel*-sized, which the rational form is not.
* `leaf_sound` — for every leaf index below `2^depth`, the seven checked
  inequalities hold; stated `∀`-quantified over the index, with no dependence
  on the depth.
* `cells_chain`, `cells_cover` — the 256 cells have no gaps.

## What is not proved here

That the fixed-point residual bound is the analytic statement: the step from
"the mantissa interval `bI i` lies below `aI i`" to "`0 ≤ 8υ²(υ−1) + …` for
real `ρ`" needs `Real.sqrt` monotonicity and the ordered-field arithmetic of
`ℝ`, and this package does not depend on Mathlib.  The interface that step
consumes is exactly the seven exported inequalities plus the generic transfer
lemmas `Dyadic.mul_encloses` / `div_encloses` / `add_encloses` /
`sub_encloses` and `DyadicBisect.sqrtOK_encloses`, each of which is already
stated cross-multiplied and quantified over all enclosed mantissas.  See the
module docstring of `Verified/DyadicBisect.lean`.
-/

namespace LeanCompCert.Ports.A36Bisect

open LeanCompCert.Verified.Dyadic
open LeanCompCert.Verified.DyadicBisect

set_option maxRecDepth 100000

/-! ## Configuration -/

/-- Binary precision: mantissas denote multiples of `2⁻²⁴`. -/
def prec : Nat := 24

/-- `2^prec`, written once. -/
def scale : Nat := 2 ^ prec

/-- The bisection depth the source certificate uses. -/
def depth : Nat := 8

/-- Leaf count `2^depth`. -/
def leaves : Nat := 2 ^ depth

/-- The grid of `[1, 31/5]` in `2^d` steps: grid point `i` is
`(5·2^d + 26·i)/(5·2^d)`, which is `1` at `i = 0` and `31/5` at `i = 2^d`.
At `d = 8` the denominator is `1280`, the depth the source certificate uses. -/
def gridAt (d : Nat) : Grid := { den := 5 * 2 ^ d, base := 5 * 2 ^ d, step := 26 }

/-- The shipped grid. -/
def grid : Grid := gridAt depth

/-- Intervals at this file's precision. -/
abbrev I : Type := DInt prec

/-- The degenerate interval holding the integer `k`. -/
def kC (k : Nat) : I := constD prec k

/-! ## The checked square root -/

/-- Newton steps.  Eight suffice for every radicand this certificate meets;
ten is the shipped figure.  No property of this function is used. -/
def newtonSteps : Nat := 10

/-- Newton start: above every root here (the largest is `2^25.4`). -/
def newtonStart : Nat := 2 ^ 28

/-- Fixed-shape Heron iteration.  Unproved by design — see `sqrtOK`. -/
def newton (n : Nat) : Nat :=
  (List.range newtonSteps).foldl (fun x _ => (x + n / x) / 2) newtonStart

/-- The guessed root interval, with two ulps of slack on each side so the
iteration has room to be off; `sqrtOK` decides whether it was. -/
def sqrtGuess (x : I) : I :=
  ⟨newton (x.lo * scale) - 2, newton (x.hi * scale) + 2⟩

/-! ## One leaf

Bound in a single structure so the kernel evaluates the chain once and the
theorems below can name each stage.
-/

/-- The enclosure chain on one cell. -/
structure Leaf where
  /-- the cell `[ρ⁻, ρ⁺]` itself -/
  cell : I
  /-- `1 + ρ²`, the radicand of `j` -/
  rad1 : I
  /-- `j = √(1 + ρ²)` -/
  j : I
  /-- `(1 + j)/2`, the radicand of `υ` -/
  rad2 : I
  /-- `υ = √((1 + j)/2)` -/
  v : I
  /-- `2υ(υ + j)` -/
  den : I
  /-- `x = ρ / (2υ(υ + j))` -/
  x : I
  /-- `1 + x²`, the radicand of `Y`'s root -/
  rad3 : I
  /-- `√(1 + x²)` -/
  w : I
  /-- `Y = √(1 + x²) − x` -/
  y : I
  /-- `A = 8υ²(υ − 1) + 8υYρ` -/
  a : I
  /-- `B = (υ + 2)Y²ρ²` -/
  b : I

/-- Evaluate the chain on cell `i` of the depth-`d` grid.  Only the cell
depends on `d`; every later stage is the same fixed-width computation, which
is why deepening costs leaves and nothing else. -/
def leafDataAt (d i : Nat) : Leaf :=
  let cell : I := (gridAt d).cell prec i
  let rr : I := cell.mul cell
  let rad1 : I := (kC 1).add rr
  let j : I := sqrtGuess rad1
  let rad2 : I := ((kC 1).add j).div (kC 2)
  let v : I := sqrtGuess rad2
  let den : I := ((kC 2).mul v).mul (v.add j)
  let x : I := cell.div den
  let rad3 : I := (kC 1).add (x.mul x)
  let w : I := sqrtGuess rad3
  let y : I := w.sub x
  let a : I := (((kC 8).mul (v.mul v)).mul (v.sub (kC 1))).add
    ((((kC 8).mul v).mul y).mul cell)
  let b : I := (((v.add (kC 2)).mul (y.mul y)).mul rr)
  { cell, rad1, j, rad2, v, den, x, rad3, w, y, a, b }

/-- The chain on cell `i` at the shipped depth. -/
def leafData (i : Nat) : Leaf := leafDataAt depth i

/-- The leaf test at depth `d`: the three root checks, the divisor check, the
two ordering checks that make the differences exact, and the residual's lower
bound.

The divisor check is the side condition of `Dyadic.DInt.div_encloses`: at
`den.lo = 0` the ceiling division would return `0` and the enclosure's upper
endpoint would collapse to something *tighter* than the truth, which is the one
direction that could let a false claim pass.  `2υ(υ + j)` is bounded below by
`2` for real reasons, but the leaf checks it rather than inheriting it.

The ordering checks are the reason no nonnegativity assumption is needed
anywhere.  `Nat` subtraction truncates at zero, so an interval difference whose
operands overlap would report a lower endpoint of `0` where the true value is
negative — sound only if the quantity is known nonnegative in advance.  Here
`υ ≥ 1` and `√(1 + x²) ≥ x` are both true, but rather than assume them the leaf
*checks* `(kC 1).hi ≤ v.lo` and `x.hi ≤ w.lo`, which is exactly the hypothesis
of `Dyadic.DInt.sub_no_truncation`: the difference is then the exact one and
`sub_encloses` needs no side condition. -/
def leafOKAt (d i : Nat) : Bool :=
  let L := leafDataAt d i
  sqrtOK L.rad1 L.j.lo L.j.hi &&
  sqrtOK L.rad2 L.v.lo L.v.hi &&
  sqrtOK L.rad3 L.w.lo L.w.hi &&
  decide (0 < L.den.lo) &&
  decide ((kC 1).hi ≤ L.v.lo) &&
  decide (L.x.hi ≤ L.w.lo) &&
  decide (L.b.hi ≤ L.a.lo)

/-- The leaf test at the shipped depth. -/
def leafOK (i : Nat) : Bool := leafOKAt depth i

/-! ## The sweep, in the kernel -/

/--
**The certificate.**  Every one of the `2⁸` cells of `[1, 6.2]` passes, checked
by Lean's kernel.  `#print axioms` on this theorem reports the base trio and
nothing else — in particular no `Lean.ofReduceBool`, which is what the source
file's `native_decide` carries.
-/
theorem sweep_ok : allBelow leaves leafOK = true := by
  decide +kernel

/-- The `∀`-form, which is what a consumer quotes.  Size-independent: the
statement mentions `leaves`, not `256`. -/
theorem leaf_passes (i : Nat) (hi : i < leaves) : leafOK i = true :=
  (allBelow_iff leaves leafOK).mp sweep_ok i hi

/-! ## What each passing leaf gives

Unpacked into the seven separate inequalities, each in the cross-multiplied form
the generic transfer lemmas of `Verified/DyadicBisect.lean` consume.  Nothing
below re-runs the computation.
-/

/-- Unpacking, at every depth: a passing leaf is exactly the seven
inequalities. -/
theorem leafOKAt_sound (d i : Nat) (h : leafOKAt d i = true) :
    sqrtOK (leafDataAt d i).rad1 (leafDataAt d i).j.lo (leafDataAt d i).j.hi = true ∧
    sqrtOK (leafDataAt d i).rad2 (leafDataAt d i).v.lo (leafDataAt d i).v.hi = true ∧
    sqrtOK (leafDataAt d i).rad3 (leafDataAt d i).w.lo (leafDataAt d i).w.hi = true ∧
    0 < (leafDataAt d i).den.lo ∧
    (kC 1).hi ≤ (leafDataAt d i).v.lo ∧
    (leafDataAt d i).x.hi ≤ (leafDataAt d i).w.lo ∧
    (leafDataAt d i).b.hi ≤ (leafDataAt d i).a.lo := by
  simp only [leafOKAt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The three roots are verified and the residual's lower bound holds, for
every cell.  This is the whole interface. -/
theorem leaf_sound (i : Nat) (hi : i < leaves) :
    sqrtOK (leafData i).rad1 (leafData i).j.lo (leafData i).j.hi = true ∧
    sqrtOK (leafData i).rad2 (leafData i).v.lo (leafData i).v.hi = true ∧
    sqrtOK (leafData i).rad3 (leafData i).w.lo (leafData i).w.hi = true ∧
    0 < (leafData i).den.lo ∧
    (kC 1).hi ≤ (leafData i).v.lo ∧
    (leafData i).x.hi ≤ (leafData i).w.lo ∧
    (leafData i).b.hi ≤ (leafData i).a.lo :=
  leafOKAt_sound depth i (leaf_passes i hi)

/-- The divisor interval is positive, so `Dyadic.DInt.div_encloses` applies to
`x = ρ / (2υ(υ + j))` with no hypothesis left over. -/
theorem den_pos (i : Nat) (hi : i < leaves) : (leafData i).den.lo ≠ 0 :=
  by have h := (leaf_sound i hi).2.2.2.1; omega

/-- Both interval differences are *exact*: the checked ordering is the
hypothesis of `Dyadic.DInt.sub_no_truncation`, so `υ − 1` and `√(1 + x²) − x`
lose nothing at the bottom and need no nonnegativity assumption. -/
theorem differences_exact (i : Nat) (hi : i < leaves) {a b : Nat}
    (ha : (leafData i).w.mem a) (hb : (leafData i).x.mem b) :
    b + (a - b) = a :=
  DInt.sub_no_truncation ha hb (leaf_sound i hi).2.2.2.2.2.1

/-- Consequence of the first check, in enclosure form: for every mantissa `m`
of `1 + ρ²` inside `rad1`, the root's mantissa is bracketed by `j`. -/
theorem j_encloses (i : Nat) (hi : i < leaves) {m : Nat}
    (hm : (leafData i).rad1.mem m) :
    (leafData i).j.lo * (leafData i).j.lo ≤ m * 2 ^ prec ∧
      m * 2 ^ prec < (leafData i).j.hi * (leafData i).j.hi :=
  sqrtOK_encloses (leaf_sound i hi).1 hm

/-- Same for `υ`. -/
theorem v_encloses (i : Nat) (hi : i < leaves) {m : Nat}
    (hm : (leafData i).rad2.mem m) :
    (leafData i).v.lo * (leafData i).v.lo ≤ m * 2 ^ prec ∧
      m * 2 ^ prec < (leafData i).v.hi * (leafData i).v.hi :=
  sqrtOK_encloses (leaf_sound i hi).2.1 hm

/-- Same for `√(1 + x²)`. -/
theorem w_encloses (i : Nat) (hi : i < leaves) {m : Nat}
    (hm : (leafData i).rad3.mem m) :
    (leafData i).w.lo * (leafData i).w.lo ≤ m * 2 ^ prec ∧
      m * 2 ^ prec < (leafData i).w.hi * (leafData i).w.hi :=
  sqrtOK_encloses (leaf_sound i hi).2.2.1 hm

/-! ## The cells have no gaps -/

/-- Consecutive cells overlap. -/
theorem grid_den_pos (d : Nat) : 0 < (gridAt d).den :=
  Nat.mul_pos (by decide) (Nat.two_pow_pos d)

theorem cells_chain (d i : Nat) :
    (gridAt d).loM prec (i + 1) ≤ (gridAt d).hiM prec i :=
  Grid.chain (grid_den_pos d) i

/-- Every cell is nonempty. -/
theorem cells_wf (d i : Nat) : ((gridAt d).cell prec i).WF :=
  Grid.cell_wf (grid_den_pos d) i

/-- Every mantissa between the first cell's left end and cell `n`'s right end
lies in some cell at or below `n`: the depth-`d` grid has no gaps, at every
`d` at once. -/
theorem cells_cover (d n m : Nat)
    (h0 : (gridAt d).loM prec 0 ≤ m) (h1 : m ≤ (gridAt d).hiM prec n) :
    ∃ i, i ≤ n ∧ (gridAt d).loM prec i ≤ m ∧ m ≤ (gridAt d).hiM prec i :=
  chain_cover _ _ (cells_chain d) n m h0 h1

end LeanCompCert.Ports.A36Bisect
