import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag9CoreLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLateFieldsLiteral

/-! Decoded record fields at the source height-prefix input. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalMainOutput_eq_flag9_tail
    (c : Cfg) (idx : Nat) (before : AState) :
    historicalMainOutput c idx before =
      arun idx (historicalFlag9Output c idx before)
        (historicalMainAfterFlag9Counter c) := by
  unfold historicalMainOutput historicalFlag9Output historicalEarlyOutput
    historicalLoadedOutput
  rw [historicalMainFlags_eq_flag9_counter_tail]
  simp only [arun_append]

theorem historicalMainOutput_frame_from_flag9
    (c : Cfg) (idx r : Nat) (before : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalMainAfterFlag9Counter c) = false) :
    (historicalMainOutput c idx before).regs r =
      (historicalFlag9Output c idx before).regs r := by
  rw [historicalMainOutput_eq_flag9_tail,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r
      (historicalMainAfterFlag9Counter c) h]

structure HistoricalHeightInputFields (c : Cfg) (words : List Nat) (idx : Nat)
    (st : RefState) (before : AState) : Prop where
  tag : (historicalMainOutput c idx before).regs 21 =
    words.getD (recW * idx) 0
  blk : (historicalMainOutput c idx before).regs 22 =
    words.getD (recW * idx + 1) 0
  tqNum : (historicalMainOutput c idx before).regs 31 =
    words.getD (recW * idx + 10) 0
  isLastGate : (historicalMainOutput c idx before).regs 48 =
    if words.getD (recW * idx + 7) 0 == 1 then 1 else 0

theorem historicalHeightInputFields_of_body_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    HistoricalHeightInputFields c words idx st before := by
  have core := historicalBody_flag9Core_of_zero c words idx before st hidx
    hstatic hsafe hbudget hrel hstat hbodyZero
  change HistoricalFlag9Core words idx st (historicalFlag9Output c idx before)
    at core
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [historicalMainOutput_frame_from_flag9 c idx 21 before (by rfl)]
    exact core.tag
  · rw [historicalMainOutput_frame_from_flag9 c idx 22 before (by rfl)]
    exact core.blk
  · rw [historicalMainOutput_frame_from_flag9 c idx 31 before (by rfl)]
    exact core.tqNum
  · rw [historicalMainOutput_frame_from_flag9 c idx 48 before (by rfl)]
    exact core.isLastGate

end LeanCompCert.Ports.DirichletLadderExternalSafety
