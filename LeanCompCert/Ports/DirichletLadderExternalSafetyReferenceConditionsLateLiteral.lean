import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsLate21_23Literal
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsLate24_25Literal

/-! Exact literal-source discharge of reference flags 21--25. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem referenceConditions_drop20
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (referenceConditions c words st idx).drop 20 =
      [ (words.getD (recW * idx) 0 == st.prevTag) &&
          words.getD (recW * idx + 11) 0 != st.prevConj
      , !(words.getD (recW * idx + 7) 0 == 1) &&
          words.getD (recW * idx + 8) 0 != 0
      , !(words.getD (recW * idx + 7) 0 == 1) &&
          words.getD (recW * idx + 9) 0 != 0
      , !(words.getD (recW * idx) 0 == st.prevTag) &&
          !(recW * words.getD (recW * idx + 11) 0 + 11 < c.tblBase)
      , !(words.getD (recW * idx) 0 == st.prevTag) &&
          (recW * words.getD (recW * idx + 11) 0 + 11 < c.tblBase) &&
          words.getD
            (recW * words.getD (recW * idx + 11) 0 + 11) 0 != idx ] := by
  rfl

set_option maxHeartbeats 1000000 in
theorem historicalBody_drop20_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).drop 20) := by
  have fields := historicalLateFields_of_body_zero c words idx before st hidx
    hstatic hsafe hbudget hrel hstat hbodyZero
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
  have earlyZeroNamed :
      (historicalEarlyOutput c idx before).regs rViol = 0 := by
    simpa only [historicalEarlyOutput, historicalLoadedOutput] using earlyZero
  have mid := historicalMiddle_zero_gates_of_body_zero c idx before
    earlyZeroNamed hbodyZero
  have zeros := historicalLate_counterZeros_of_body_zero c idx before
    earlyZeroNamed hbodyZero
  have hconjRecords : words.getD (recW * idx + 11) 0 < c.records := by
    simpa only [wordsArray_apply] using hsafe.2.2.2.2.2.2.2.2
  have first := historicalLate_conditions21_23_false c words idx before st
    fields zeros
  have last := historicalLate_conditions24_25_false c words idx before st
    hidx hstatic hconjRecords fields mid.zero zeros
  rw [referenceConditions_drop20]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact first.1
  · exact first.2.1
  · exact first.2.2
  · exact last.1
  · exact last.2

end LeanCompCert.Ports.DirichletLadderExternalSafety
