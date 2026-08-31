import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsFlag9
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterZeroFlag9

/-! Flag 9 is discharged from the literal body result, without an extra
trusted acceptance premise. -/

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
theorem historicalBody_flag9_noFailure_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).drop 8 |>.take 1) := by
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
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := hsafe.2.1
    have hs := hsafe.2.2.1
    simp only [wordsArray_apply] at hlo hs
    have pair : maxPinnedUpper + maxPinnedUpper < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hs) pair
  have hstat := stat_le_of_historicalEarly_zero c words idx before loaded st
    hloaded hrel.state_eq hword.1 hrel.previous_last_bit
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
  have d := historicalDerived_result c words idx
    (words.getD (recW * idx + 5) 0) early hbitsEarly (by
      rw [← hloaded.bits_eq]
      exact hword.1 26) arrayEarly hstatic
  change HistoricalDerivedLoaded (words.getD (recW * idx + 5) 0) derived ∧
    HistoricalArrayMatches c words derived at d
  have regDerived (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalDerived c) = false) : derived.regs r = early.regs r := by
    dsimp [derived]
    exact frame h
  have prevTagLoaded : loaded.regs rPrevTag = st.prevTag := by
    have h := congrArg RefState.prevTag (hloaded.ref_state.trans hrel.state_eq)
    simpa [refStateOf] using h
  have gates := historicalEarly_gate_values c idx
    (words.getD (recW * idx) 0) st.prevTag
    (words.getD (recW * idx + 7) 0) loaded hloaded.tag_eq prevTagLoaded
    hloaded.isLast_eq
  change early.regs 33 =
      (if words.getD (recW * idx) 0 == st.prevTag then 1 else 0) ∧ _ at gates
  have prevBitDerived : derived.regs rPrevBit = st.prevBit := by
    rw [regDerived rPrevBit (by rfl)]
    dsimp [early]
    rw [frame (idx := idx) (r := rPrevBit) (l := historicalEarly c) (by rfl)]
    have h := congrArg RefState.prevBit (hloaded.ref_state.trans hrel.state_eq)
    simpa [refStateOf] using h
  have derivedZero : derived.regs rViol = 0 := by
    rw [regDerived rViol (by rfl), earlyZero]
  have flag9Zero := historicalFlag9_zero_of_body_zero c idx before earlyZero
    hbodyZero
  change (arun idx derived (historicalFlag9 c)).regs rViol = 0 at flag9Zero
  apply historicalFlag9_noFailure_of_zero c words idx derived st
  · exact (regDerived 26 (by rfl)).trans hbitsEarly
  · rw [regDerived 24 (by rfl)]
    dsimp [early]
    rw [frame (idx := idx) (r := 24) (l := historicalEarly c) (by rfl)]
    exact hloaded.slots_eq
  · rw [regDerived 27 (by rfl)]
    dsimp [early]
    rw [frame (idx := idx) (r := 27) (l := historicalEarly c) (by rfl)]
    exact hloaded.stat_eq
  · exact (regDerived 33 (by rfl)).trans gates.1
  · exact prevBitDerived
  · exact d.1.trI
  · rw [← hloaded.bits_eq]
    exact hword.1 26
  · exact hrel.previous_sign_bit
  · exact hstat
  · exact derivedZero
  · exact flag9Zero

end LeanCompCert.Ports.DirichletLadderExternalSafety
