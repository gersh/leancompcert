import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsAllLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptanceTelescope

/-! Acceptance-directed composition of the literal historical source with the
independent list reference.  This file never evaluates a record: a zero sticky
counter at the literal body output supplies all 25 reference conditions. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem refState_reg_viol {s : AState} {st : RefState}
    (h : refStateOf s = st) : s.regs rViol = st.viol := by
  simpa [refStateOf] using congrArg RefState.viol h

private theorem refState_reg_prevLast {s : AState} {st : RefState}
    (h : refStateOf s = st) : s.regs rPrevLast = st.prevLast := by
  simpa [refStateOf] using congrArg RefState.prevLast h

private theorem refState_reg_prevBlk {s : AState} {st : RefState}
    (h : refStateOf s = st) : s.regs rPrevBlk = st.prevBlk := by
  simpa [refStateOf] using congrArg RefState.prevBlk h

/-- One literal source step preserves the full reference relation whenever its
sticky output is zero.  The zero output is later obtained from final signed
acceptance by monotonicity, not assumed by the public whole-run theorem. -/
theorem historicalBody_loopRel_of_zero_sourceCfg
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
    HistoricalLoopRel (sourceCfg records termDigest) words (idx + 1)
      (arun idx before (sourceCfg records termDigest).bodyBlock)
      (refStep (sourceCfg records termDigest) words st idx) := by
  let c := sourceCfg records termDigest
  let out := arun idx before c.bodyBlock
  have hstate : refStateOf out = refStep c words st idx := by
    exact historicalBody_refState_of_zero_sourceCfg records termDigest words idx
      before st hwords hidx hstatic hsafe hbudget hrel hbodyZero
  have hinv : HistoricalMachineInv c words idx before := {
    array_eq := hrel.array_eq
    viol_bound := by
      rw [refState_reg_viol hrel.state_eq]
      exact hrel.viol_bound
    previous_last_bit := by
      rw [refState_reg_prevLast hrel.state_eq]
      exact hrel.previous_last_bit
    previous_blk_succ_word := by
      rw [refState_reg_prevBlk hrel.state_eq]
      exact hrel.previous_blk_succ_word
    regs_word := hrel.regs_word
    array_word := hrel.array_word }
  have houtInv : HistoricalMachineInv c words (idx + 1) out :=
    historicalMachineInv_step c words idx before hstatic hbudget hidx hsafe hinv
  refine {
    state_eq := hstate
    array_eq := houtInv.array_eq
    viol_bound := ?_
    previous_last_bit := ?_
    previous_sign_bit := ?_
    first_sign_bit := ?_
    trI0_bound := ?_
    sj0_bound := ?_
    trI1_bound := ?_
    sj1_bound := ?_
    previous_blk_succ_word := ?_
    regs_word := houtInv.regs_word
    array_word := houtInv.array_word }
  · have hz := historicalBody_refStep_viol_zero_sourceCfg records termDigest
      words idx before st hwords hidx hstatic hsafe hbudget hrel hbodyZero
    rw [hz]
    omega
  · have heq : out.regs rPrevLast = (refStep c words st idx).prevLast :=
      refState_reg_prevLast hstate
    rw [← heq]
    exact houtInv.previous_last_bit
  · rw [refStep_prevBit]
    have hm := Nat.mod_lt (words.getD (recW * idx + 5) 0 >>> 63)
      (by decide : 0 < 2)
    omega
  · rw [refStep_firstBit]
    split
    · exact hrel.first_sign_bit
    · have hm := Nat.mod_lt (words.getD (recW * idx + 5) 0)
        (by decide : 0 < 2)
      omega
  · rw [refStep_trI0]
    split
    · exact hrel.trI1_bound
    · omega
  · rw [refStep_sj0]
    split
    · exact hrel.sj1_bound
    · omega
  · rw [refStep_trI1]
    exact bitCount_transWord_le _
  · rw [refStep_sj1]
    exact bitMoment_transWord_le _
  · have heq : out.regs rPrevBlk = (refStep c words st idx).prevBlk :=
      refState_reg_prevBlk hstate
    rw [← heq]
    exact houtInv.previous_blk_succ_word

/-- Every accepted literal source prefix is exactly related to the independent
reference fold.  Final acceptance supplies every intermediate zero through
the proved monotonicity of the sticky source counter. -/
theorem historicalLoopRel_range_of_hardenedMachineAccepts_sourceCfg
    (records termDigest : Nat) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hterm : termDigest < M)
    (hsafe : AllRecordsSafe (sourceCfg records termDigest) (wordsArray words))
    (haccept : HardenedMachineAccepts (sourceCfg records termDigest)
      (wordsArray words))
    (n : Nat) (hn : n ≤ records) :
    HistoricalLoopRel (sourceCfg records termDigest) words n
      (historicalStateAt (sourceCfg records termDigest) words n)
      ((List.range n).foldl
        (refStep (sourceCfg records termDigest) words) refInit) := by
  let c := sourceCfg records termDigest
  induction n with
  | zero =>
      simpa [historicalStateAt] using
        historical_symbolicEntry_loopRel c words hstatic.array_word hwords
  | succ n ih =>
      have hnlt : n < records := by omega
      have hprev := ih (by omega)
      have hloopZero :=
        historicalLoop_counter_zero_of_hardenedMachineAccepts c words hwords
          hstatic hbudget (by change termDigest < M; exact hterm) hsafe haccept
      change (historicalStateAt c words records).regs rViol = 0 at hloopZero
      have hmono := historicalStateAt_counter_mono c words hwords hstatic
        hbudget hsafe (n + 1) records (by omega) (Nat.le_refl _)
      have hbodyZero :
          (arun n (historicalStateAt c words n) c.bodyBlock).regs rViol = 0 := by
        rw [← historicalStateAt_succ]
        rw [hloopZero] at hmono
        omega
      have hstep := historicalBody_loopRel_of_zero_sourceCfg records termDigest
        words n (historicalStateAt c words n)
        ((List.range n).foldl (refStep c words) refInit)
        hwords hnlt hstatic (hsafe n hnlt) hbudget hprev hbodyZero
      simpa [c, historicalStateAt_succ, List.range_succ,
        List.foldl_append] using hstep

end LeanCompCert.Ports.DirichletLadderExternalSafety
