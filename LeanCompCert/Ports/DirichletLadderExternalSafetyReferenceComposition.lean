import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceEpilogue

/-! Low-memory fold telescope for the historical/reference simulation.

The only remaining local obligation is `HistoricalBodyStep`: one composition
of the already split source slices.  This module proves that such a step
theorem is sufficient for the whole record fold and terminal checks; it does
not postulate that obligation or hide any record evidence.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def HistoricalBodyStep (c : Cfg) (words : List Nat) : Prop :=
  ∀ idx s st, idx < c.records → RecordSafe c (wordsArray words) idx →
    HistoricalLoopRel c words idx s st →
    HistoricalLoopRel c words (idx + 1)
      (arun idx s c.bodyBlock) (refStep c words st idx)

theorem historicalLoopRel_range
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hsafe : AllRecordsSafe c (wordsArray words))
    (hstep : HistoricalBodyStep c words) (n : Nat) (hn : n ≤ c.records) :
    HistoricalLoopRel c words n
      ((List.range n).foldl
        (fun state index => arun index state c.bodyBlock)
        (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
          c (wordsArray words)))
      ((List.range n).foldl (refStep c words) refInit) := by
  induction n with
  | zero =>
      simpa using historical_symbolicEntry_loopRel c words hstatic.array_word hwords
  | succ n ih =>
      have hnlt : n < c.records := by omega
      have hprev := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      simpa [Nat.add_comm] using
        hstep n _ _ hnlt (hsafe n hnlt) hprev

theorem historicalReferenceAgreement_of_bodyStep
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hsafe : AllRecordsSafe c (wordsArray words))
    (hbudget : ViolationBudget c) (hterm : c.termDigest < M)
    (hstep : HistoricalBodyStep c words) :
    HistoricalReferenceAgreement c words := by
  let sm := (List.range c.records).foldl
    (fun state index => arun index state c.bodyBlock)
    (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
      c (wordsArray words))
  let st := (List.range c.records).foldl (refStep c words) refInit
  have hrel : HistoricalLoopRel c words c.records sm st := by
    simpa [sm, st] using historicalLoopRel_range c words hwords hstatic hsafe hstep
      c.records (Nat.le_refl _)
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
    simp only [ViolationBudget] at hbudget
    omega
  have hep := historicalEpilogue_result c st.viol st.prevLast st.prevDig sm
    hv hl hd hterm hwrap
  unfold HistoricalReferenceAgreement
  change
    (arun 0 sm c.epilogueBlock).regs rViol = refViolations c words
  rw [hep]
  rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety
