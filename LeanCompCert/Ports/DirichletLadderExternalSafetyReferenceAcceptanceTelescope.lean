import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMachineInvariant

/-! Acceptance-directed counter telescope for the literal historical run. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem maxPinnedUpper_pair_word' :
    maxPinnedUpper + maxPinnedUpper < M := by decide

def historicalStateAt (c : Cfg) (words : List Nat) (n : Nat) : AState :=
  (List.range n).foldl
    (fun state index => arun index state c.bodyBlock)
    (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
      c (wordsArray words))

theorem historicalStateAt_succ (c : Cfg) (words : List Nat) (n : Nat) :
    historicalStateAt c words (n + 1) =
      arun n (historicalStateAt c words n) c.bodyBlock := by
  simp only [historicalStateAt, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem historicalStateAt_inv
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hsafe : AllRecordsSafe c (wordsArray words))
    (n : Nat) (hn : n ≤ c.records) :
    HistoricalMachineInv c words n (historicalStateAt c words n) := by
  exact historicalMachineInv_range c words hwords hstatic hbudget hsafe n hn

theorem historicalStateAt_counter_mono
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hsafe : AllRecordsSafe c (wordsArray words))
    (m n : Nat) (hmn : m ≤ n) (hn : n ≤ c.records) :
    (historicalStateAt c words m).regs rViol ≤
      (historicalStateAt c words n).regs rViol := by
  induction n with
  | zero =>
      have : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases heq : m = n + 1
      · subst m
        exact Nat.le_refl _
      · have hmn' : m ≤ n := by omega
        have hprev := ih hmn' (by omega)
        have hinv := historicalStateAt_inv c words hwords hstatic hbudget
          hsafe n (by omega)
        have hstep := historicalBody_machine_bounds c words n
          ((historicalStateAt c words n).regs rViol)
          (historicalStateAt c words n) rfl hinv.array_eq hinv.regs_word
          hinv.array_word hstatic (by omega) (hsafe n (by omega))
          hinv.previous_last_bit hinv.previous_blk_succ_word (by
            simp only [ViolationBudget] at hbudget
            have hv := hinv.viol_bound
            omega)
        rw [historicalStateAt_succ]
        exact Nat.le_trans hprev hstep.1

theorem historicalLoop_counter_zero_of_hardenedMachineAccepts
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hterm : c.termDigest < M)
    (hsafe : AllRecordsSafe c (wordsArray words))
    (haccept : HardenedMachineAccepts c (wordsArray words)) :
    (historicalStateAt c words c.records).regs rViol = 0 := by
  let loop := historicalStateAt c words c.records
  have loop_eq : loop = historicalStateAt c words c.records := rfl
  have hinv := historicalStateAt_inv c words hwords hstatic hbudget hsafe
    c.records (Nat.le_refl _)
  rw [← loop_eq] at hinv
  have hep := historicalEpilogue_result c (loop.regs rViol)
    (loop.regs rPrevLast) (loop.regs rPrevDig) loop rfl rfl rfl hterm (by
      simp only [ViolationBudget] at hbudget
      have hv := hinv.viol_bound
      omega)
  have hfinal := haccept.1
  unfold LeanCompCert.Ports.DirichletLadderExternalDenotation.MachineAccepts at hfinal
  change (arun 0
    (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicLoop
      c (wordsArray words)) c.epilogueBlock).regs rViol = 0 at hfinal
  have symbolicLoop_eq :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicLoop
        c (wordsArray words) = loop := by
    simp only [LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicLoop,
      historicalStateAt, loop]
  rw [symbolicLoop_eq, hep] at hfinal
  have hmono := bumps_ge
    [loop.regs rPrevLast != 1, loop.regs rPrevDig != c.termDigest]
    (loop.regs rViol)
  simp [bumps] at hmono
  rw [← loop_eq]
  omega

theorem stat_le_of_hardenedMachineAccepts_at
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hterm : c.termDigest < M)
    (hsafe : AllRecordsSafe c (wordsArray words))
    (haccept : HardenedMachineAccepts c (wordsArray words))
    (idx : Nat) (hidx : idx < c.records) :
    words.getD (recW * idx + 6) 0 ≤ maxStat := by
  let before := historicalStateAt c words idx
  let loaded := arun idx before (historicalLoad c)
  have before_eq : before = historicalStateAt c words idx := rfl
  have loaded_eq : loaded = arun idx before (historicalLoad c) := rfl
  have hinv := historicalStateAt_inv c words hwords hstatic hbudget hsafe idx
    (by omega)
  rw [← before_eq] at hinv
  have hloopZero := historicalLoop_counter_zero_of_hardenedMachineAccepts c
    words hwords hstatic hbudget hterm hsafe haccept
  have hmono := historicalStateAt_counter_mono c words hwords hstatic hbudget
    hsafe (idx + 1) c.records (by omega) (Nat.le_refl _)
  have hnextZero : (arun idx before c.bodyBlock).regs rViol = 0 := by
    rw [← historicalStateAt_succ]
    omega
  have hearlyZero := historicalEarly_zero_of_body_zero c words idx
    (before.regs rViol) before rfl hinv.array_eq hinv.regs_word
    hinv.array_word hstatic hidx (hsafe idx hidx) hinv.previous_last_bit
    hinv.previous_blk_succ_word (by
      simp only [ViolationBudget] at hbudget
      have hv := hinv.viol_bound
      omega) hnextZero
  rw [← loaded_eq] at hearlyZero
  have hloaded := historicalLoad_loaded c words idx before hinv.array_eq
    hstatic hidx
  change HistoricalLoaded c words idx before loaded at hloaded
  let st := refStateOf before
  have hwordLoaded := arun_word idx (historicalLoad c) before hinv.regs_word
    hinv.array_word
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := (hsafe idx hidx).2.1
    have hslots := (hsafe idx hidx).2.2.1
    simp only [wordsArray_apply] at hlo hslots
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hslots)
      maxPinnedUpper_pair_word'
  apply stat_le_of_historicalEarly_zero c words idx before loaded st hloaded rfl
    hwordLoaded.1
  · simpa [st, refStateOf] using hinv.previous_last_bit
  · simpa [st, refStateOf] using hinv.previous_blk_succ_word
  · exact hslot
  · simp only [ViolationBudget] at hbudget
    have hv := hinv.viol_bound
    simpa [st, refStateOf] using (show before.regs rViol + 8 < M by omega)
  · exact hearlyZero

theorem all_stats_le_of_hardenedMachineAccepts
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hterm : c.termDigest < M)
    (haccept : HardenedMachineAccepts c (wordsArray words)) :
    ∀ idx, idx < c.records → words.getD (recW * idx + 6) 0 ≤ maxStat := by
  have hsafe := allRecordsSafe_of_words_hardenedMachineAccepts c words hwords
    hstatic haccept
  intro idx hidx
  exact stat_le_of_hardenedMachineAccepts_at c words hwords hstatic hbudget
    hterm hsafe haccept idx hidx

end LeanCompCert.Ports.DirichletLadderExternalSafety
