import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.RegFrame

/-!
# Register framing for mixed scalar/array instruction blocks

`RegFrame` provides a cheap Boolean write test for scalar blocks.  Array
programs also contain loads and stores: loads write one scalar register while
stores write no scalar register.  This module supplies the corresponding test
and framing theorem for `AInstr`, still inspecting only destination indices.
-/

namespace LeanCompCert.Verified.ArrayRegFrame

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

/-- Does one mixed instruction write scalar register `r`? -/
def instrWrites (r : Nat) : AInstr → Bool
  | .scalar i => decide (sdest i = r)
  | .load dest _ => decide (dest = r)
  | .store _ _ => false

/-- Does a mixed instruction block write scalar register `r`? -/
def writes (r : Nat) (l : List AInstr) : Bool :=
  l.any (instrWrites r)

@[simp] theorem writes_nil (r : Nat) : writes r [] = false := rfl

@[simp] theorem writes_cons (r : Nat) (i : AInstr) (l : List AInstr) :
    writes r (i :: l) = (instrWrites r i || writes r l) := rfl

theorem astep_frame (k r : Nat) (s : AState) (i : AInstr)
    (h : instrWrites r i = false) :
    (astep k s i).regs r = s.regs r := by
  cases i with
  | scalar i =>
      have hne : sdest i ≠ r := of_decide_eq_false h
      simp [astep, AState.writeReg, hne.symm]
  | load dest idx =>
      have hne : dest ≠ r := of_decide_eq_false h
      simp [astep, AState.writeReg, hne.symm]
  | store idx src => rfl

/-- A mixed block which does not write `r` preserves that register. -/
theorem arun_frame (k r : Nat) (l : List AInstr)
    (h : writes r l = false) (s : AState) :
    (arun k s l).regs r = s.regs r := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
      rw [writes_cons, Bool.or_eq_false_iff] at h
      rw [arun_cons, ih h.2, astep_frame k r s i h.1]

end LeanCompCert.Verified.ArrayRegFrame
