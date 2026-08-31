import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveState
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyMonotone

/-! Reusable decoded flag-9 state extracted from a literal body run. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private def storeFree : AInstr → Bool
  | .store _ _ => false
  | _ => true

private theorem arun_arr_frame (idx : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all storeFree = true → (arun idx s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [storeFree] at h

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxHeartbeats 1000000 in
theorem historicalBody_flag9Core_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    HistoricalFlag9Core words idx st
      (arun idx
        (arun idx
          (arun idx
            (arun idx before (historicalLoad c)) (historicalEarly c))
          (historicalDerived c))
        (historicalFlag9 c)) := by
  let loaded := arun idx before (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  let derived := arun idx early (historicalDerived c)
  have hloaded := historicalLoad_loaded c words idx before hrel.array_eq hstatic hidx
  change HistoricalLoaded c words idx before loaded at hloaded
  have hword := arun_word idx (historicalLoad c) before hrel.regs_word
    hrel.array_word
  have prevLastBefore : before.regs rPrevLast ≤ 1 := by
    have h := congrArg RefState.prevLast hrel.state_eq
    have heq : before.regs rPrevLast = st.prevLast := by
      simpa [refStateOf] using h
    rw [heq]
    exact hrel.previous_last_bit
  have prevBlkBefore : before.regs rPrevBlk + 1 < M := by
    have h := congrArg RefState.prevBlk hrel.state_eq
    have heq : before.regs rPrevBlk = st.prevBlk := by
      simpa [refStateOf] using h
    rw [heq]
    exact hrel.previous_blk_succ_word
  have violBefore : before.regs rViol = st.viol := by
    have h := congrArg RefState.viol hrel.state_eq
    simpa [refStateOf] using h
  have earlyZero := historicalEarly_zero_of_body_zero c words idx
    (before.regs rViol) before rfl hrel.array_eq hrel.regs_word hrel.array_word
    hstatic hidx hsafe prevLastBefore prevBlkBefore (by
      simp only [ViolationBudget] at hbudget
      have hv := hrel.viol_bound
      rw [violBefore]
      omega) hbodyZero
  change early.regs rViol = 0 at earlyZero
  have arrayEarly : HistoricalArrayMatches c words early := by
    have heq : early.arr = loaded.arr := by
      dsimp [early]
      exact arun_arr_frame idx (historicalEarly c) loaded (by rfl)
    constructor
    · intro k hk; rw [heq]; exact hloaded.array_eq.record_cells k hk
    · intro v hv; rw [heq]; exact hloaded.array_eq.table_cells v hv
  have core := historicalFlag9_core c words idx before loaded early derived st
    rfl rfl hloaded hrel.state_eq arrayEarly hstatic
    (by rw [← hloaded.bits_eq]; exact hword.1 26)
    hrel.previous_sign_bit hstat (by
      have hd : derived.regs rViol = early.regs rViol := by
        dsimp [derived]
        exact frame (idx := idx) (r := rViol) (l := historicalDerived c) (by rfl)
      rw [hd, earlyZero]
      exact one_lt_M)
  simpa only [loaded, early, derived] using core

end LeanCompCert.Ports.DirichletLadderExternalSafety
