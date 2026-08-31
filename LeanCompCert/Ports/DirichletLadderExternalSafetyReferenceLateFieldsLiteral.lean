import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag9CoreLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLateOutputZeroLiteral

/-! Decoded fields and array identity at the literal late-flag input. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag9Output (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx
    (arun idx
      (arun idx
        (arun idx before (historicalLoad c)) (historicalEarly c))
      (historicalDerived c))
    (historicalFlag9 c)

theorem historicalMiddleOutput_eq_flag9_tail
    (c : Cfg) (idx : Nat) (before : AState) :
    historicalMiddleOutput c idx before =
      arun idx
        (arun idx (historicalFlag9Output c idx before)
          (historicalMainAfterFlag9Counter c))
        (historicalMiddleFlags c) := by
  unfold historicalMiddleOutput historicalMainOutput historicalEarlyOutput
    historicalLoadedOutput historicalFlag9Output
  rw [historicalMainFlags_eq_flag9_counter_tail]
  simp only [arun_append]

theorem historicalMiddleOutput_frame_from_flag9
    (c : Cfg) (idx r : Nat) (before : AState)
    (hm : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalMainAfterFlag9Counter c) = false)
    (ha : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightPrefixA c) = false)
    (hb : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightPrefixB c) = false)
    (hf : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightFlag c) = false)
    (hc : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalCoverageBlock c) = false)
    (ho : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalOvershootBlock c) = false) :
    (historicalMiddleOutput c idx before).regs r =
      (historicalFlag9Output c idx before).regs r := by
  rw [historicalMiddleOutput_eq_flag9_tail,
    historicalMiddleFrame c idx r _ ha hb hf hc ho,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r
      (historicalMainAfterFlag9Counter c) hm]

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

theorem historicalFlag9Output_arr_eq_before
    (c : Cfg) (idx : Nat) (before : AState) :
    (historicalFlag9Output c idx before).arr = before.arr := by
  unfold historicalFlag9Output
  rw [arun_arr_frame idx (historicalFlag9 c) _ (by rfl),
    arun_arr_frame idx (historicalDerived c) _ (by rfl),
    arun_arr_frame idx (historicalEarly c) _ (by rfl),
    arun_arr_frame idx (historicalLoad c) _ (by rfl)]

theorem historicalMiddleOutput_arr_eq_flag9
    (c : Cfg) (idx : Nat) (before : AState) :
    (historicalMiddleOutput c idx before).arr =
      (historicalFlag9Output c idx before).arr := by
  rw [historicalMiddleOutput_eq_flag9_tail,
    historicalMiddleFlags_eq_frame_parts]
  simp only [historicalMainAfterFlag9Counter, arun_append]
  repeat rw [arun_arr_frame idx _ _ (by rfl)]

theorem historicalMiddleOutput_arr_eq_before
    (c : Cfg) (idx : Nat) (before : AState) :
    (historicalMiddleOutput c idx before).arr = before.arr := by
  rw [historicalMiddleOutput_arr_eq_flag9,
    historicalFlag9Output_arr_eq_before]

structure HistoricalLateFields (c : Cfg) (words : List Nat) (idx : Nat)
    (st : RefState) (before : AState) : Prop where
  conj : (historicalMiddleOutput c idx before).regs 32 =
    words.getD (recW * idx + 11) 0
  same : (historicalMiddleOutput c idx before).regs 33 =
    if words.getD (recW * idx) 0 == st.prevTag then 1 else 0
  fresh : (historicalMiddleOutput c idx before).regs 34 =
    if !(words.getD (recW * idx) 0 == st.prevTag) then 1 else 0
  isLastGate : (historicalMiddleOutput c idx before).regs 48 =
    if words.getD (recW * idx + 7) 0 == 1 then 1 else 0
  uElem : (historicalMiddleOutput c idx before).regs 29 =
    words.getD (recW * idx + 8) 0
  henc : (historicalMiddleOutput c idx before).regs 30 =
    words.getD (recW * idx + 9) 0
  prevConj : (historicalMiddleOutput c idx before).regs rPrevConj = st.prevConj
  recordCells : ∀ k, k < c.tblBase →
    (historicalMiddleOutput c idx before).arr k = words.getD k 0

set_option maxHeartbeats 1000000 in
theorem historicalLateFields_of_body_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    HistoricalLateFields c words idx st before := by
  have core := historicalBody_flag9Core_of_zero c words idx before st hidx
    hstatic hsafe hbudget hrel hstat hbodyZero
  change HistoricalFlag9Core words idx st
    (historicalFlag9Output c idx before) at core
  refine {
    conj := ?_
    same := ?_
    fresh := ?_
    isLastGate := ?_
    uElem := ?_
    henc := ?_
    prevConj := ?_
    recordCells := ?_ }
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 32 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.cj
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 33 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.same
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 34 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.fresh
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 48 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.isLastGate
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 29 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.uElem
  · rw [historicalMiddleOutput_frame_from_flag9 c idx 30 before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.henc
  · rw [historicalMiddleOutput_frame_from_flag9 c idx rPrevConj before
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact core.oldConj
  · intro k hk
    rw [historicalMiddleOutput_arr_eq_before]
    exact hrel.array_eq.record_cells k hk

end LeanCompCert.Ports.DirichletLadderExternalSafety
