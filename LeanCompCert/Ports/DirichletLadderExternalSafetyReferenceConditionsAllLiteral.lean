import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsFirst17Literal
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditions18_20Literal
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsLateLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositivePipeline

/-! All 25 reference failures and the exact positive reference state. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem NoFailures.of_take_drop {conditions : List Bool} (n : Nat)
    (ht : NoFailures (conditions.take n))
    (hd : NoFailures (conditions.drop n)) : NoFailures conditions := by
  rw [show conditions = conditions.take n ++ conditions.drop n by
    exact (List.take_append_drop n conditions).symm]
  intro b hb
  rw [List.mem_append] at hb
  exact hb.elim (ht b) (hd b)

theorem stat_le_of_reference_take17_noFailures
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat)
    (h : NoFailures ((referenceConditions c words st idx).take 17)) :
    words.getD (recW * idx + 6) 0 ≤ maxStat := by
  have hf : (words.getD (recW * idx + 6) 0 > maxStat : Bool) = false :=
    h _ (by simp [referenceConditions])
  exact Nat.le_of_not_gt (of_decide_eq_false hf)

set_option maxHeartbeats 1000000 in
theorem historicalBody_all_noFailures_sourceCfg
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (hwords : ∀ k, words.getD k 0 < M)
    (hidx : idx < records)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hsafe : RecordSafe (sourceCfg records termDigest) (wordsArray words) idx)
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hrel : HistoricalLoopRel (sourceCfg records termDigest) words idx before st)
    (hbodyZero : (arun idx before
      (sourceCfg records termDigest).bodyBlock).regs rViol = 0) :
    NoFailures (referenceConditions (sourceCfg records termDigest)
      words st idx) := by
  let c := sourceCfg records termDigest
  have h17 := historicalBody_take17_noFailures_of_zero c words idx before st
    hidx hstatic hsafe hbudget hrel hbodyZero
  have hstat := stat_le_of_reference_take17_noFailures c words st idx h17
  have hmid := historicalBody_flags18_20_noFailures_sourceCfg records termDigest
    words idx before st hwords hidx hstatic hsafe hbudget hrel hstat hbodyZero
  have hlate := historicalBody_drop20_noFailures_of_zero c words idx before st
    hidx hstatic hsafe hbudget hrel hstat hbodyZero
  have hdrop3 : NoFailures
      (((referenceConditions c words st idx).drop 17).drop 3) := by
    simpa only [List.drop_drop] using hlate
  have htail : NoFailures ((referenceConditions c words st idx).drop 17) :=
    NoFailures.of_take_drop 3 hmid hdrop3
  exact NoFailures.of_take_drop 17 h17 htail

theorem historicalBody_refStep_viol_zero_sourceCfg
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (hwords : ∀ k, words.getD k 0 < M)
    (hidx : idx < records)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hsafe : RecordSafe (sourceCfg records termDigest) (wordsArray words) idx)
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hrel : HistoricalLoopRel (sourceCfg records termDigest) words idx before st)
    (hbodyZero : (arun idx before
      (sourceCfg records termDigest).bodyBlock).regs rViol = 0) :
    (refStep (sourceCfg records termDigest) words st idx).viol = 0 := by
  let c := sourceCfg records termDigest
  have hNoWrap : before.regs rViol + 25 < M := by
    have hv := hrel.viol_bound
    have heq := congrArg RefState.viol hrel.state_eq
    have hs : before.regs rViol = st.viol := by simpa [refStateOf] using heq
    simp only [ViolationBudget, sourceCfg] at hbudget
    rw [hs]
    change st.viol ≤ 25 * idx at hv
    omega
  have bm := historicalBody_machine_bounds c words idx (before.regs rViol)
    before rfl hrel.array_eq hrel.regs_word hrel.array_word hstatic hidx hsafe
    (by
      have h := congrArg RefState.prevLast hrel.state_eq
      have heq : before.regs rPrevLast = st.prevLast := by
        simpa [refStateOf] using h
      rw [heq]
      exact hrel.previous_last_bit)
    (by
      have h := congrArg RefState.prevBlk hrel.state_eq
      have heq : before.regs rPrevBlk = st.prevBlk := by
        simpa [refStateOf] using h
      rw [heq]
      exact hrel.previous_blk_succ_word)
    hNoWrap
  have beforeZero : before.regs rViol = 0 := by
    rw [hbodyZero] at bm
    omega
  have stZero : st.viol = 0 := by
    have h := congrArg RefState.viol hrel.state_eq
    simpa [refStateOf, beforeZero] using h.symm
  exact refStep_viol_zero_of_noFailures c words st idx stZero
    (historicalBody_all_noFailures_sourceCfg records termDigest words idx before
      st hwords hidx hstatic hsafe hbudget hrel hbodyZero)

theorem historicalBody_refState_of_zero_sourceCfg
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (hwords : ∀ k, words.getD k 0 < M)
    (hidx : idx < records)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hsafe : RecordSafe (sourceCfg records termDigest) (wordsArray words) idx)
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hrel : HistoricalLoopRel (sourceCfg records termDigest) words idx before st)
    (hbodyZero : (arun idx before
      (sourceCfg records termDigest).bodyBlock).regs rViol = 0) :
    refStateOf (arun idx before (sourceCfg records termDigest).bodyBlock) =
      refStep (sourceCfg records termDigest) words st idx := by
  have h17 := historicalBody_take17_noFailures_of_zero
    (sourceCfg records termDigest) words idx before st hidx hstatic hsafe hbudget
    hrel hbodyZero
  have hstat := stat_le_of_reference_take17_noFailures
    (sourceCfg records termDigest) words st idx h17
  apply historicalBody_refState_of_zero_and_refViol_zero
    (sourceCfg records termDigest) words idx before st hidx hstatic hsafe hbudget
    hrel hstat hbodyZero
  exact historicalBody_refStep_viol_zero_sourceCfg records termDigest words idx
    before st hwords hidx hstatic hsafe hbudget hrel hbodyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety
