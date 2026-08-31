import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsMain

/-! Flags 10--15 and 17 follow from the literal body zero result. -/

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
theorem historicalBody_main_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures (referenceMainConditions c words st idx) := by
  let loaded := arun idx before (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  let derived := arun idx early (historicalDerived c)
  let s9 := arun idx derived (historicalFlag9 c)
  have hloaded := historicalLoad_loaded c words idx before hrel.array_eq hstatic hidx
  change HistoricalLoaded c words idx before loaded at hloaded
  have loadedWord := arun_word idx (historicalLoad c) before hrel.regs_word
    hrel.array_word
  have earlyWord := arun_word idx (historicalEarly c) loaded loadedWord.1
    loadedWord.2
  have derivedWord := arun_word idx (historicalDerived c) early earlyWord.1
    earlyWord.2
  have s9Word := arun_word idx (historicalFlag9 c) derived derivedWord.1
    derivedWord.2
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
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := hsafe.2.1
    have hs := hsafe.2.2.1
    simp only [wordsArray_apply] at hlo hs
    have pair : maxPinnedUpper + maxPinnedUpper < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hs) pair
  have hstat := stat_le_of_historicalEarly_zero c words idx before loaded st
    hloaded hrel.state_eq loadedWord.1 hrel.previous_last_bit
    hrel.previous_blk_succ_word hslot (by
      simp only [ViolationBudget] at hbudget
      have hv := hrel.viol_bound
      omega) earlyZero
  have hbitsEarly : early.regs 26 = words.getD (recW * idx + 5) 0 := by
    dsimp [early]
    rw [frame (idx := idx) (r := 26) (l := historicalEarly c) (by rfl)]
    exact hloaded.bits_eq
  have arrayEarly : HistoricalArrayMatches c words early := by
    have heq : early.arr = loaded.arr := by
      dsimp [early]
      exact arun_arr_frame idx (historicalEarly c) loaded (by rfl)
    constructor
    · intro k hk; rw [heq]; exact hloaded.array_eq.record_cells k hk
    · intro v hv; rw [heq]; exact hloaded.array_eq.table_cells v hv
  have core := historicalFlag9_core c words idx before loaded early derived st
    rfl rfl hloaded hrel.state_eq arrayEarly hstatic
    (by rw [← hloaded.bits_eq]; exact loadedWord.1 26)
    hrel.previous_sign_bit hstat (by
      have dz : derived.regs rViol = 0 := by
        dsimp [derived]
        rw [frame (idx := idx) (r := rViol) (l := historicalDerived c) (by rfl),
          earlyZero]
      rw [dz]
      exact one_lt_M)
  change HistoricalFlag9Core words idx st s9 at core
  have cuts := historicalFlag9_main_zero_of_body_zero c idx before earlyZero
    hbodyZero
  change s9.regs rViol = 0 ∧
    (arun idx derived (historicalMainFlags c)).regs rViol = 0 at cuts
  have mainZero :
      (arun idx s9 (historicalMainAfterFlag9Counter c)).regs rViol = 0 := by
    rw [historicalMainFlags_eq_flag9_counter_tail, arun_append] at cuts
    exact cuts.2
  have gate : s9.regs 48 ≤ 1 := by
    rw [core.isLastGate]
    split <;> omega
  have zeros := historicalMain_counterZeros c idx s9 cuts.1 gate mainZero
  have upperBound : words.getD (recW * idx + 4) 0 ≤ maxPinnedUpper := by
    simpa only [wordsArray_apply] using hsafe.2.2.2.1
  have hencBound : words.getD (recW * idx + 9) 0 ≤ hExpect := by
    simpa only [wordsArray_apply] using hsafe.2.2.2.2.1
  exact historicalMain_noFailures c words st idx s9 core zeros cuts.1 s9Word.1
    hrel.trI0_bound hrel.sj0_bound hrel.first_sign_bit upperBound hencBound

end LeanCompCert.Ports.DirichletLadderExternalSafety
