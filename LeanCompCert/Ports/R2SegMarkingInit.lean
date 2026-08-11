import LeanCompCert.Ports.R2SegMarkingRoundPosition

/-! # Initial marking position of the emitted `R₂*` program -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

/-- A literal array store uses only registers 90 and 91 as scratch. -/
theorem r2_storeLit_regs_frame (idx cell value r : Nat) (s : AState)
    (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun idx s (storeLit cell value)).regs r = s.regs r := by
  simp [storeLit, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, hr90, hr91]

/-- An arbitrary emitted table initialization frames every non-scratch
register, independently of the table's finite length. -/
theorem r2_storeLits_regs_frame (idx r : Nat) (s : AState)
    (l : List (Nat × Nat)) (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun idx s (storeLits l)).regs r = s.regs r := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun idx (arun idx s (storeLit x.1 x.2))
        (storeLits xs)).regs r = _
      rw [ih, r2_storeLit_regs_frame idx x.1 x.2 r s hr90 hr91]

/-- The explicit seed block preserves round zero and installs `lo`. -/
theorem seedList_mark_position_run (c : R2Cfg) (seed : R2Seed) (s : AState)
    (hr : s.regs rR = 0) (hloM : c.lo < M) :
    let out := arun 0 s (seedRegs (c.seedList seed))
    out.regs rR = 0 ∧ out.regs rW = c.lo := by
  have hr5 : s.regs 5 = 0 := by simpa [rR] using hr
  simp [R2Cfg.seedList, seedRegs, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, rR, rW, rD, rErr, rPrev, rTerms,
    rSq, rSq2, rEx, rTh, rLn, rThr, hr5,
    Nat.mod_eq_of_lt hloM]

/-- The emitted initializer starts the schedule at round zero and seeds the
first window base with `lo`. -/
theorem init_mark_position_run (c : R2Cfg) (seed : R2Seed)
    (hloM : c.lo < M) :
    let out := arun 0 initialAState (c.init seed)
    out.regs rR = 0 ∧ out.regs rW = c.lo := by
  let stored := arun 0 initialAState (storeLits c.tableCells)
  have hsR : stored.regs rR = 0 := by
    rw [r2_storeLits_regs_frame 0 rR initialAState c.tableCells
      (by decide) (by decide)]
    rfl
  have hs := seedList_mark_position_run c seed stored hsR hloM
  rw [R2Cfg.init, arun_append]
  exact hs

#print axioms r2_storeLit_regs_frame
#print axioms r2_storeLits_regs_frame
#print axioms seedList_mark_position_run
#print axioms init_mark_position_run

end LeanCompCert.Ports.R2SegSieve
