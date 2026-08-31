import LeanCompCert.Ports.DirichletLadderExternalSafetyReference

/-! Constant-size projections of the non-counter fields of `refStep`.

Keeping these projections opaque to downstream proofs prevents Lean from
re-elaborating the 25-element violation list when only a copied state field is
needed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert.Ports.DirichletLadder

theorem refStep_prevTag (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevTag = words.getD (recW * idx) 0 := by rfl

theorem refStep_prevBlk (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevBlk = words.getD (recW * idx + 1) 0 := by rfl

theorem refStep_prevUpper (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevUpper = words.getD (recW * idx + 4) 0 := by rfl

theorem refStep_prevBit (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevBit =
      (words.getD (recW * idx + 5) 0 >>> 63) % 2 := by rfl

theorem refStep_firstBit (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).firstBit =
      if words.getD (recW * idx) 0 == st.prevTag then st.firstBit
      else words.getD (recW * idx + 5) 0 % 2 := by rfl

theorem refStep_trI0 (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).trI0 =
      if words.getD (recW * idx) 0 == st.prevTag then st.trI1 else 0 := by rfl

theorem refStep_sj0 (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).sj0 =
      if words.getD (recW * idx) 0 == st.prevTag then st.sj1 else 0 := by rfl

theorem refStep_trI1 (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).trI1 =
      bitCount (transWord (words.getD (recW * idx + 5) 0)) := by rfl

theorem refStep_sj1 (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).sj1 =
      bitMoment (transWord (words.getD (recW * idx + 5) 0)) := by rfl

theorem refStep_prevLast (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevLast = words.getD (recW * idx + 7) 0 := by rfl

theorem refStep_prevConj (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevConj = words.getD (recW * idx + 11) 0 := by rfl

theorem refStep_prevDig (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (refStep c words st idx).prevDig = words.getD (recW * idx + 12) 0 := by rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety
