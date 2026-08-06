import LeanCompCert.Ports.A36Bisect

/-!
# Helfgott Appendix A.34: fixed-width interval-verifier model

This is the bounded-word replacement for the exact-rational adaptive
certificate in `claude_math`'s `AppendixAProven/A34.lean`.  It checks the
equivalent nonnegative inequality

```
  (υ² - υ) ≤ ρ · Υ · ((29888/100000) · W - 1/2)
```

on an outward-rounded uniform cover of `[1/10, 36]`.  All arithmetic is on
natural mantissas at one static binary precision.  Every subtraction whose
real meaning matters has an explicit ordering check, every division has an
explicit positive-lower-endpoint check, and every square root is represented
by a bracket whose squared inequalities are checked by the eventual compiled
program.

The model and physical program use the same fixed-shape Newton guesser, but
their acceptance predicate checks every result with `sqrtOK`.  Thus no
property of the guesser is part of the soundness boundary: an inaccurate
guess can only reject a row.
-/

namespace LeanCompCert.Ports.A34Bisect

open LeanCompCert.Verified.Dyadic
open LeanCompCert.Verified.DyadicBisect
open LeanCompCert.Ports.A36Bisect (sqrtGuess)

/-- Static mantissa precision.  At `p = 24` the largest squared intermediate
in the shipped range remains below `2^64`. -/
def prec : Nat := 24

def scale : Nat := 2 ^ prec

/-- Uniform depth used by the production checker.  The smallest comfortably
passing value is selected by the benchmark runner before this is finalized. -/
def depth : Nat := 20

def leaves : Nat := 2 ^ depth

/-- Grid point `i` is `(2^d + 359*i)/(10*2^d)`, hence the endpoints are
exactly `1/10` and `36`. -/
def gridAt (d : Nat) : Grid :=
  { den := 10 * 2 ^ d, base := 2 ^ d, step := 359 }

def grid : Grid := gridAt depth

abbrev I : Type := DInt prec

def kC (k : Nat) : I := constD prec k

/-- Outward dyadic enclosure of a nonnegative rational constant. -/
def qC (num den : Nat) : I :=
  ⟨num * scale / den, (num * scale + den - 1) / den⟩

/-- Every intermediate of one verifier row, named so the soundness bridge and
the physical-program simulation can share the same stage boundaries. -/
structure Leaf where
  cell : I
  radJ : I
  j : I
  radV : I
  v : I
  den : I
  x : I
  radY : I
  sy : I
  y : I
  radW : I
  w : I
  vv : I
  lhs : I
  cw : I
  t : I
  rhs : I

def leafDataAt (d i : Nat) : Leaf :=
  let cell := (gridAt d).cell prec i
  let radJ := (kC 1).add (cell.mul cell)
  let j := sqrtGuess radJ
  let radV := ((kC 1).add j).div (kC 2)
  let v := sqrtGuess radV
  let den := ((kC 2).mul v).mul (v.add j)
  let x := cell.div den
  let radY := (kC 1).add (x.mul x)
  let sy := sqrtGuess radY
  let y := sy.sub x
  let radW := ((kC 1).add j).add ((kC 2).mul v)
  let w := sqrtGuess radW
  let vv := v.mul v
  let lhs := vv.sub v
  let cw := (qC 29888 100000).mul w
  let t := cw.sub (qC 1 2)
  let rhs := (cell.mul y).mul t
  { cell, radJ, j, radV, v, den, x, radY, sy, y, radW, w, vv, lhs, cw, t, rhs }

def leafData (i : Nat) : Leaf := leafDataAt depth i

/-- Fail-closed row predicate.  Besides the terminal inequality it checks all
side conditions needed to interpret `Nat` subtraction and division as the
corresponding nonnegative real operations. -/
def leafOKAt (d i : Nat) : Bool :=
  let L := leafDataAt d i
  sqrtOK L.radJ L.j.lo L.j.hi &&
  sqrtOK L.radV L.v.lo L.v.hi &&
  sqrtOK L.radY L.sy.lo L.sy.hi &&
  sqrtOK L.radW L.w.lo L.w.hi &&
  decide (0 < L.den.lo) &&
  decide (L.x.hi ≤ L.sy.lo) &&
  decide (L.v.hi ≤ L.vv.lo) &&
  decide ((qC 1 2).hi ≤ L.cw.lo) &&
  decide (L.lhs.hi ≤ L.rhs.lo)

def leafOK (i : Nat) : Bool := leafOKAt depth i

/-- A passing row exposes exactly the four checked root brackets, the divisor
guard, the three exact-subtraction guards, and the terminal inequality. -/
theorem leafOKAt_sound (d i : Nat) (h : leafOKAt d i = true) :
    let L := leafDataAt d i
    sqrtOK L.radJ L.j.lo L.j.hi = true ∧
    sqrtOK L.radV L.v.lo L.v.hi = true ∧
    sqrtOK L.radY L.sy.lo L.sy.hi = true ∧
    sqrtOK L.radW L.w.lo L.w.hi = true ∧
    0 < L.den.lo ∧ L.x.hi ≤ L.sy.lo ∧ L.v.hi ≤ L.vv.lo ∧
    (qC 1 2).hi ≤ L.cw.lo ∧ L.lhs.hi ≤ L.rhs.lo := by
  simp only [leafOKAt, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa only [and_assoc] using h

def sweepOKAt (d : Nat) : Bool := allBelow (2 ^ d) (leafOKAt d)

def sweepOK : Bool := sweepOKAt depth

/-- A shard of the production sweep.  Keeping this separate from `allBelow`
lets downstream certificate files kernel-check bounded blocks independently,
so peak memory is controlled by the shard size rather than by all `2^20`
rows at once. -/
def shardOK (start count : Nat) : Bool :=
  (List.range' start count).all leafOK

theorem shardOK_iff (start count : Nat) :
    shardOK start count = true ↔
      ∀ i, start ≤ i → i < start + count → leafOK i = true := by
  simp only [shardOK, List.all_eq_true, List.mem_range']
  constructor
  · intro h i hlo hhi
    have hj : i - start < count := by omega
    exact h i ⟨i - start, hj, by omega⟩
  · intro h i hi
    obtain ⟨j, hj, hij⟩ := hi
    subst i
    exact h (start + 1 * j) (by omega) (by omega)

/-- Adaptive verifier rooted at cell `(d,i)`.  A passing cell closes the
whole interval immediately; only a failing enclosure is split into its two
children.  `fuel` bounds the maximum additional depth. -/
def adaptiveOKAt : Nat → Nat → Nat → Bool
  | 0, d, i => leafOKAt d i
  | fuel + 1, d, i =>
      leafOKAt d i ||
        (adaptiveOKAt fuel (d + 1) (2 * i) &&
          adaptiveOKAt fuel (d + 1) (2 * i + 1))

/-- Production adaptive tree over the single depth-zero cell `[1/10,36]`. -/
def adaptiveOK : Bool := adaptiveOKAt depth 0 0

theorem grid_den_pos (d : Nat) : 0 < (gridAt d).den :=
  Nat.mul_pos (by decide) (Nat.two_pow_pos d)

theorem cells_chain (d i : Nat) :
    (gridAt d).loM prec (i + 1) ≤ (gridAt d).hiM prec i :=
  Grid.chain (grid_den_pos d) i

theorem cells_wf (d i : Nat) : ((gridAt d).cell prec i).WF :=
  Grid.cell_wf (grid_den_pos d) i

theorem cells_cover (d n m : Nat)
    (h0 : (gridAt d).loM prec 0 ≤ m) (h1 : m ≤ (gridAt d).hiM prec n) :
    ∃ i, i ≤ n ∧ (gridAt d).loM prec i ≤ m ∧
      m ≤ (gridAt d).hiM prec i :=
  chain_cover _ _ (cells_chain d) n m h0 h1

end LeanCompCert.Ports.A34Bisect
