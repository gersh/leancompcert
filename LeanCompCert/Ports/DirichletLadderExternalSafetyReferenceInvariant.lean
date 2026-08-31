import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBits

/-! Loop relation for the historical ladder/reference simulation. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalArrayMatches (c : Cfg) (words : List Nat)
    (s : AState) : Prop where
  record_cells : ∀ k, k < c.tblBase → s.arr k = words.getD k 0
  table_cells : ∀ v, v < 256 → s.arr (c.tblBase + v) = tblEntry v

/-- Inductive relation at loop index `idx`.  The violation bound is exactly
the prefix of `ViolationBudget`; no analytic record truth occurs here. -/
structure HistoricalLoopRel (c : Cfg) (words : List Nat) (idx : Nat)
    (s : AState) (st : RefState) : Prop where
  state_eq : refStateOf s = st
  array_eq : HistoricalArrayMatches c words s
  viol_bound : st.viol ≤ 25 * idx
  previous_last_bit : st.prevLast ≤ 1
  previous_sign_bit : st.prevBit ≤ 1
  first_sign_bit : st.firstBit ≤ 1
  trI0_bound : st.trI0 ≤ 64
  sj0_bound : st.sj0 ≤ 2240
  trI1_bound : st.trI1 ≤ 64
  sj1_bound : st.sj1 ≤ 2240
  previous_blk_succ_word : st.prevBlk + 1 < M
  regs_word : ∀ j, s.regs j < M
  array_word : ∀ j, s.arr j < M

set_option maxRecDepth 10000 in
theorem historical_symbolicEntry_loopRel
    (c : Cfg) (words : List Nat) (hlen : c.arrayLen < M)
    (hwords : ∀ k, words.getD k 0 < M) :
    HistoricalLoopRel c words 0
      (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
        c (wordsArray words)) refInit := by
  refine {
    state_eq := historical_symbolicEntry_refState c words
    array_eq := ?_
    viol_bound := by simp [refInit]
    previous_last_bit := by simp [refInit]
    previous_sign_bit := by simp [refInit]
    first_sign_bit := by simp [refInit]
    trI0_bound := by simp [refInit]
    sj0_bound := by simp [refInit]
    trI1_bound := by simp [refInit]
    sj1_bound := by simp [refInit]
    previous_blk_succ_word := by simp [refInit, M]
    regs_word := ?_
    array_word := ?_ }
  constructor
  · intro k hk
    exact historical_symbolicEntry_record_cell c words k hlen hk
  · intro v hv
    exact historical_symbolicEntry_table_cell c words v hlen hv
  · exact (arun_word 0 c.initBlock
      (LeanCompCert.Verified.ArrayState.initialAStateWithArray
        (wordsArray words))
      (by intro j; simp [LeanCompCert.Verified.ArrayState.initialAStateWithArray,
        initialState, M])
      (by intro j; simpa [LeanCompCert.Verified.ArrayState.initialAStateWithArray,
        wordsArray] using hwords j)).1
  · exact (arun_word 0 c.initBlock
      (LeanCompCert.Verified.ArrayState.initialAStateWithArray
        (wordsArray words))
      (by intro j; simp [LeanCompCert.Verified.ArrayState.initialAStateWithArray,
        initialState, M])
      (by intro j; simpa [LeanCompCert.Verified.ArrayState.initialAStateWithArray,
        wordsArray] using hwords j)).2

end LeanCompCert.Ports.DirichletLadderExternalSafety
