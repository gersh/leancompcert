import LeanCompCert.Verified.DyadicBisect

/-!
# Helfgott A.29 middle ranges in bounded-width dyadic arithmetic

The source proof used exact rational interval arithmetic on two depth-seven
grids.  Nested Newton fractions make that representation expensive even though
there are only 128 cells.  This port evaluates the same analytic expression
with outward dyadic rounding at precision `2^-20`.

All stored mantissas are below `2^23`; every product used by `DInt.mul` and
`sqrtI` is therefore below `2^46`.  Thus this is also within the unsigned
64-bit fragment used by LeanCompCert.  At this size the fixed-width certificate
is kernel-sized, so no physical-run axiom is needed.
-/

namespace LeanCompCert.Ports.A29Bisect

open LeanCompCert.Verified.Dyadic
open LeanCompCert.Verified.DyadicBisect

def prec : Nat := 20
def depth : Nat := 7
def leaves : Nat := 2 ^ depth
def scale : Nat := 2 ^ prec

abbrev I : Type := DInt prec

def ratC (n d : Nat) : I :=
  ⟨n * scale / d, (n * scale + d - 1) / d⟩

def kC (n : Nat) : I := ratC n 1

/-- The uniform grid on `[aNum/aDen,bNum/bDen]`. -/
def grid (aNum aDen bNum bDen : Nat) : Grid := {
  den := aDen * bDen * leaves
  base := aNum * bDen * leaves
  step := bNum * aDen - aNum * bDen
}

structure Cfg where
  aNum : Nat
  aDen : Nat
  bNum : Nat
  bDen : Nat

def midLowCfg : Cfg := ⟨29, 100, 3, 4⟩
def midPeakLowCfg : Cfg := ⟨3, 4, 6, 5⟩

def Cfg.cell (c : Cfg) (i : Nat) : I :=
  (grid c.aNum c.aDen c.bNum c.bDen).cell prec i

structure Leaf where
  cell : I
  rr : I
  radJ : I
  j : I
  radV : I
  v : I
  den : I
  x : I
  radY : I
  w : I
  y : I
  invV : I
  vSq : I
  invVSq : I
  ySq : I
  c0 : I
  radK : I
  k : I
  jp1 : I
  invJp1 : I
  pos : I
  neg : I

/-- Outward fixed-point evaluation of the rearranged A.29 residual.

`pos - neg` is

`0.43(1+Y^2)Kρ + 0.43ρ
 - (0.43ρY^2 + 0.43ρ/υ + 0.86ρ^2Y/(j+1) + (1+2c₀^2))`.
-/
def leafData (c : Cfg) (i : Nat) : Leaf :=
  let cell := c.cell i
  let rr := cell.mul cell
  let radJ := (kC 1).add rr
  let j := sqrtI radJ
  let radV := ((kC 1).add j).div (kC 2)
  let v := sqrtI radV
  let den := ((kC 2).mul v).mul (v.add j)
  let x := cell.div den
  let radY := (kC 1).add (x.mul x)
  let w := sqrtI radY
  let y := w.sub x
  let invV := (kC 1).div v
  let vSq := v.mul v
  let invVSq := (kC 1).div vSq
  let ySq := y.mul y
  let c0 := ((kC 2).sub invV).add (((kC 1).add invV).mul ySq) |>.add
    ((cell.mul y).mul invVSq)
  let radK := ((((kC 8).mul j).mul v).mul (v.add (kC 1)))
  let k := sqrtI radK
  let jp1 := j.add (kC 1)
  let invJp1 := (kC 1).div jp1
  let pos := (((ratC 43 100).mul ((kC 1).add ySq)).mul k).add
    ((ratC 43 100).mul cell)
  let neg := ((((ratC 43 100).mul cell).mul ySq).add
      (((ratC 43 100).mul cell).mul invV)).add
      ((((ratC 86 100).mul rr).mul y).mul invJp1) |>.add c0
  { cell, rr, radJ, j, radV, v, den, x, radY, w, y, invV, vSq,
    invVSq, ySq, c0, radK, k, jp1, invJp1, pos, neg }

/-- Every potentially unsound truncated subtraction/division is guarded, and
the final positive lower endpoint dominates the negative upper endpoint. -/
def leafOK (c : Cfg) (i : Nat) : Bool :=
  let L := leafData c i
  decide (0 < L.den.lo) &&
  decide (L.x.hi ≤ L.w.lo) &&
  decide (0 < L.v.lo) &&
  decide (L.invV.hi ≤ (kC 2).lo) &&
  decide (0 < L.vSq.lo) &&
  decide (0 < L.jp1.lo) &&
  decide (L.neg.hi ≤ L.pos.lo)

theorem leafOK_sound (c : Cfg) (i : Nat) (h : leafOK c i = true) :
    0 < (leafData c i).den.lo ∧
    (leafData c i).x.hi ≤ (leafData c i).w.lo ∧
    0 < (leafData c i).v.lo ∧
    (leafData c i).invV.hi ≤ (kC 2).lo ∧
    0 < (leafData c i).vSq.lo ∧
    0 < (leafData c i).jp1.lo ∧
    (leafData c i).neg.hi ≤ (leafData c i).pos.lo := by
  simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

def sweepOK (c : Cfg) : Bool := allBelow leaves (leafOK c)

theorem midLow_sweep_ok : sweepOK midLowCfg = true := by
  decide +kernel

theorem midPeakLow_sweep_ok : sweepOK midPeakLowCfg = true := by
  decide +kernel

theorem leaf_passes (c : Cfg) (h : sweepOK c = true) (i : Nat) (hi : i < leaves) :
    leafOK c i = true :=
  (allBelow_iff leaves (leafOK c)).mp h i hi

end LeanCompCert.Ports.A29Bisect
