import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Limb

/-!
# Compiled fixed-width row check for the CH25 Lemma A.7 transcript

The retained transcript uses positive mantissas of at most 192 bits.  This
module gives the machine-local part of its replacement checker: three input
limbs are compared with a four-limb strict upper threshold, and the remaining
finite parser/geometry guards are evaluated with word operations.  Large
transcript evaluation belongs to the emitted CompCert program; the theorems
below are uniform in the row values.
-/

namespace LeanCompCert.Ports.A7BoundaryRow

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

abbrev B : Nat := M

/-- A little-endian four-word value. -/
structure Limbs4 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  deriving Repr, DecidableEq

def Limbs4.val (x : Limbs4) : Nat :=
  x.l0 + B * (x.l1 + B * (x.l2 + B * x.l3))

def Limbs4.WF (x : Limbs4) : Prop :=
  x.l0 < B ∧ x.l1 < B ∧ x.l2 < B ∧ x.l3 < B

/-- Borrow recurrence used by the emitted comparison.  For word inputs and a
zero/one incoming borrow this is the borrow bit of `x - y - borrow`. -/
def borrowStep (x y borrow : Nat) : Nat :=
  (if x < y then 1 else 0) + ((if x = y then 1 else 0) * borrow)

def borrow4 (x y : Limbs4) : Nat :=
  let b0 := borrowStep x.l0 y.l0 0
  let b1 := borrowStep x.l1 y.l1 b0
  let b2 := borrowStep x.l2 y.l2 b1
  borrowStep x.l3 y.l3 b2

theorem borrowStep_eq_sbb_borrow (x y borrow : Nat)
    (hx : x < B) (hy : y < B) (hb : borrow ≤ 1) :
    borrowStep x y borrow =
      (LeanCompCert.Verified.Limb.sbbStep x y borrow).2 := by
  unfold borrowStep LeanCompCert.Verified.Limb.sbbStep
  by_cases hxy : x < y
  · have hsum : x < y + borrow := by omega
    have hne : x ≠ y := Nat.ne_of_lt hxy
    simp [hxy, hsum, hne]
  · have hyx : y ≤ x := Nat.le_of_not_gt hxy
    by_cases heq : x = y
    · subst x
      cases borrow with
      | zero => simp
      | succ borrow =>
          have hb0 : borrow = 0 := by omega
          subst borrow
          simp
    · have hylt : y < x := Nat.lt_of_le_of_ne hyx (Ne.symm heq)
      have hsum : ¬ x < y + borrow := by omega
      simp [hxy, heq, hsum]

private theorem borrowStep_le_one (x y borrow : Nat) (hb : borrow ≤ 1) :
    borrowStep x y borrow ≤ 1 := by
  unfold borrowStep
  by_cases hlt : x < y
  · have hne : x ≠ y := Nat.ne_of_lt hlt
    simp [hlt, hne]
  · by_cases heq : x = y
    · simp [hlt, heq, hb]
    · simp [hlt, heq]

theorem borrow4_le_one (x y : Limbs4) : borrow4 x y ≤ 1 := by
  apply borrowStep_le_one
  apply borrowStep_le_one
  apply borrowStep_le_one
  exact borrowStep_le_one _ _ _ (by omega)

theorem borrow4_eq_limbBorrow (x y : Limbs4) (hx : x.WF) (hy : y.WF) :
    borrow4 x y =
      (LeanCompCert.Verified.Limb.sbb
        [x.l0, x.l1, x.l2, x.l3]
        [y.l0, y.l1, y.l2, y.l3] 0).2 := by
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  have hb0 : borrowStep x.l0 y.l0 0 ≤ 1 := borrowStep_le_one _ _ _ (by omega)
  have hb1 : borrowStep x.l1 y.l1 (borrowStep x.l0 y.l0 0) ≤ 1 :=
    borrowStep_le_one _ _ _ hb0
  have hb2 : borrowStep x.l2 y.l2
      (borrowStep x.l1 y.l1 (borrowStep x.l0 y.l0 0)) ≤ 1 :=
    borrowStep_le_one _ _ _ hb1
  let b0 := borrowStep x.l0 y.l0 0
  let b1 := borrowStep x.l1 y.l1 b0
  let b2 := borrowStep x.l2 y.l2 b1
  have he0 : b0 = (LeanCompCert.Verified.Limb.sbbStep x.l0 y.l0 0).2 :=
    borrowStep_eq_sbb_borrow x.l0 y.l0 0 hx0 hy0 (by omega)
  have he1 : b1 = (LeanCompCert.Verified.Limb.sbbStep x.l1 y.l1
      (LeanCompCert.Verified.Limb.sbbStep x.l0 y.l0 0).2).2 := by
    rw [show b1 = borrowStep x.l1 y.l1 b0 by rfl, he0]
    exact borrowStep_eq_sbb_borrow _ _ _ hx1 hy1 (by
      simpa [← he0] using hb0)
  have he2 : b2 = (LeanCompCert.Verified.Limb.sbbStep x.l2 y.l2
      (LeanCompCert.Verified.Limb.sbbStep x.l1 y.l1
        (LeanCompCert.Verified.Limb.sbbStep x.l0 y.l0 0).2).2).2 := by
    rw [show b2 = borrowStep x.l2 y.l2 b1 by rfl, he1]
    exact borrowStep_eq_sbb_borrow _ _ _ hx2 hy2 (by
      simpa [← he1] using hb1)
  have he3 : borrowStep x.l3 y.l3 b2 =
      (LeanCompCert.Verified.Limb.sbbStep x.l3 y.l3
        (LeanCompCert.Verified.Limb.sbbStep x.l2 y.l2
          (LeanCompCert.Verified.Limb.sbbStep x.l1 y.l1
            (LeanCompCert.Verified.Limb.sbbStep x.l0 y.l0 0).2).2).2).2 := by
    rw [he2]
    exact borrowStep_eq_sbb_borrow _ _ _ hx3 hy3 (by
      simpa [← he2] using hb2)
  simpa [borrow4, b0, b1, b2, LeanCompCert.Verified.Limb.sbb] using he3

theorem borrow4_eq_one_iff_lt (x y : Limbs4) (hx : x.WF) (hy : y.WF) :
    borrow4 x y = 1 ↔ x.val < y.val := by
  rw [borrow4_eq_limbBorrow x y hx hy]
  have h := LeanCompCert.Verified.Limb.lt_iff
    [x.l0, x.l1, x.l2, x.l3] [y.l0, y.l1, y.l2, y.l3]
    rfl
    (by simpa [LeanCompCert.Verified.Limb.Limbs.WF, Limbs4.WF, B, M] using hx)
    (by simpa [LeanCompCert.Verified.Limb.Limbs.WF, Limbs4.WF, B, M] using hy)
  simpa [LeanCompCert.Verified.Limb.isLt, Limbs4.val,
    LeanCompCert.Verified.Limb.Limbs.val, B, M] using h

/-! ## Literal instruction block -/

def rX0 : Nat := 0
def rX1 : Nat := 1
def rX2 : Nat := 2
def rY0 : Nat := 3
def rY1 : Nat := 4
def rY2 : Nat := 5
def rY3 : Nat := 6
def rBorrow : Nat := 7
def rLt : Nat := 8
def rEq : Nat := 9
def rEqBorrow : Nat := 10

def borrowLimbBody (rx ry : Nat) : List AInstr :=
  [ .scalar (.binop rLt .lt (.reg rx) (.reg ry))
  , .scalar (.binop rEq .eq (.reg rx) (.reg ry))
  , .scalar (.binop rEqBorrow .mul (.reg rEq) (.reg rBorrow))
  , .scalar (.binop rBorrow .add (.reg rLt) (.reg rEqBorrow)) ]

/-- Four-word strict comparison.  The fourth input word is the literal zero,
because retained A.7 mantissas occupy at most three words. -/
def compareBody : List AInstr :=
  [ .scalar (.mov rBorrow (.lit 0)) ] ++
    borrowLimbBody rX0 rY0 ++
    borrowLimbBody rX1 rY1 ++
    borrowLimbBody rX2 rY2 ++
    borrowLimbBody 11 rY3

/-- Exact denotation of the literal four-word comparison block. -/
theorem compareBody_run (k : Nat) (s : AState)
    (hx0 : s.regs rX0 < M) (hx1 : s.regs rX1 < M)
    (hx2 : s.regs rX2 < M)
    (hy0 : s.regs rY0 < M) (hy1 : s.regs rY1 < M)
    (hy2 : s.regs rY2 < M) (hy3 : s.regs rY3 < M)
    (hzero : s.regs 11 = 0) :
    (arun k s compareBody).regs rBorrow =
      borrow4
        { l0 := s.regs rX0, l1 := s.regs rX1,
          l2 := s.regs rX2, l3 := 0 }
        { l0 := s.regs rY0, l1 := s.regs rY1,
          l2 := s.regs rY2, l3 := s.regs rY3 } := by
  let x : Limbs4 :=
    { l0 := s.regs rX0, l1 := s.regs rX1,
      l2 := s.regs rX2, l3 := 0 }
  let y : Limbs4 :=
    { l0 := s.regs rY0, l1 := s.regs rY1,
      l2 := s.regs rY2, l3 := s.regs rY3 }
  have hbM : borrow4 x y < M :=
    Nat.lt_of_le_of_lt (borrow4_le_one x y) (by decide)
  change (arun k s compareBody).regs rBorrow = borrow4 x y
  calc
    _ = borrow4 x y % M := by
      simp [compareBody, borrowLimbBody, arun, astep, AState.writeReg,
        sdest, sval, denoteOperand, denoteOp, borrow4, borrowStep, hzero,
        rX0, rX1, rX2, rY0, rY1, rY2, rY3,
        rBorrow, rLt, rEq, rEqBorrow, x, y]
      rfl
    _ = borrow4 x y := Nat.mod_eq_of_lt hbM

theorem compareBody_run_eq_one_iff (k : Nat) (s : AState)
    (hx0 : s.regs rX0 < M) (hx1 : s.regs rX1 < M)
    (hx2 : s.regs rX2 < M)
    (hy0 : s.regs rY0 < M) (hy1 : s.regs rY1 < M)
    (hy2 : s.regs rY2 < M) (hy3 : s.regs rY3 < M)
    (hzero : s.regs 11 = 0) :
    (arun k s compareBody).regs rBorrow = 1 ↔
      Limbs4.val
        { l0 := s.regs rX0, l1 := s.regs rX1,
          l2 := s.regs rX2, l3 := 0 } <
      Limbs4.val
        { l0 := s.regs rY0, l1 := s.regs rY1,
          l2 := s.regs rY2, l3 := s.regs rY3 } := by
  rw [compareBody_run k s hx0 hx1 hx2 hy0 hy1 hy2 hy3 hzero]
  apply borrow4_eq_one_iff_lt
  · exact ⟨hx0, hx1, hx2, by simp [B, M]⟩
  · exact ⟨hy0, hy1, hy2, hy3⟩

#print axioms borrow4_eq_one_iff_lt
#print axioms compareBody_run
#print axioms compareBody_run_eq_one_iff

end LeanCompCert.Ports.A7BoundaryRow
