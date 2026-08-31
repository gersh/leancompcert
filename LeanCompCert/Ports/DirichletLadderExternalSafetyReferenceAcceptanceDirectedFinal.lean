import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptanceDirectedComposition

/-! Final source/epilogue projection for the acceptance-directed historical
Dirichlet ladder refinement. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

/-- On an accepted production-shaped run, the literal historical source final
counter is definitionally the independent reference violation count. -/
theorem historicalReferenceAgreement_of_hardenedMachineAccepts_sourceCfg
    (records termDigest : Nat) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hterm : termDigest < M)
    (haccept : HardenedMachineAccepts (sourceCfg records termDigest)
      (wordsArray words)) :
    HistoricalReferenceAgreement (sourceCfg records termDigest) words := by
  let c := sourceCfg records termDigest
  let sm := historicalStateAt c words records
  let st := (List.range records).foldl (refStep c words) refInit
  have hsafe : AllRecordsSafe c (wordsArray words) :=
    allRecordsSafe_of_words_hardenedMachineAccepts c words hwords hstatic haccept
  have hrel : HistoricalLoopRel c words records sm st := by
    simpa [c, sm, st] using
      historicalLoopRel_range_of_hardenedMachineAccepts_sourceCfg records
        termDigest words hwords hstatic hbudget hterm hsafe haccept records
        (Nat.le_refl _)
  have hv : sm.regs rViol = st.viol := by
    have h := congrArg RefState.viol hrel.state_eq
    simpa [refStateOf] using h
  have hl : sm.regs rPrevLast = st.prevLast := by
    have h := congrArg RefState.prevLast hrel.state_eq
    simpa [refStateOf] using h
  have hd : sm.regs rPrevDig = st.prevDig := by
    have h := congrArg RefState.prevDig hrel.state_eq
    simpa [refStateOf] using h
  have hwrap : st.viol + 2 < M := by
    have hb := hrel.viol_bound
    simp only [ViolationBudget, sourceCfg] at hbudget
    omega
  have hep := historicalEpilogue_result c st.viol st.prevLast st.prevDig sm
    hv hl hd (by change termDigest < M; exact hterm) hwrap
  unfold HistoricalReferenceAgreement
  change (arun 0 sm c.epilogueBlock).regs rViol = refViolations c words
  rw [hep]
  rfl

/-- Complete finite source theorem: paired signed acceptance of the literal
historical and sticky programs implies that the independent list reference has
zero violations.  No analytic sign, Turing, GRH, or roster premise occurs in
this machine/reference theorem. -/
theorem refViolations_eq_zero_of_hardenedMachineAccepts_sourceCfg
    (records termDigest : Nat) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hterm : termDigest < M)
    (haccept : HardenedMachineAccepts (sourceCfg records termDigest)
      (wordsArray words)) :
    refViolations (sourceCfg records termDigest) words = 0 := by
  apply refViolations_eq_zero_of_hardenedMachineAccepts
    (sourceCfg records termDigest) words hwords hstatic hbudget haccept
  exact historicalReferenceAgreement_of_hardenedMachineAccepts_sourceCfg
    records termDigest words hwords hstatic hbudget hterm haccept

end LeanCompCert.Ports.DirichletLadderExternalSafety
