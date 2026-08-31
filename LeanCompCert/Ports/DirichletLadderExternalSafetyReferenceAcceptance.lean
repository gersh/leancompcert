import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag9

/-! Consequences obtained from the historical machine's own zero result.
These are semantic facts extracted from executed flags, not external evidence. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem bumps_ge (conditions : List Bool) (n : Nat) :
    n ≤ bumps conditions n := by
  induction conditions generalizing n with
  | nil => simp [bumps]
  | cons condition rest ih =>
      rw [show bumps (condition :: rest) n =
        bumps rest (bump condition n) by rfl]
      exact Nat.le_trans (by cases condition <;> simp [bump]) (ih _)

theorem bumps_pos_of_true_mem (conditions : List Bool) (n : Nat)
    (hmem : true ∈ conditions) : 0 < bumps conditions n := by
  induction conditions generalizing n with
  | nil => simp at hmem
  | cons condition rest ih =>
      rw [show bumps (condition :: rest) n =
        bumps rest (bump condition n) by rfl]
      rw [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst condition
        have hge := bumps_ge rest (bump true n)
        simp [bump] at hge ⊢
        omega
      · exact ih (bump condition n) htail

theorem stat_le_of_earlyConditions_zero
    (words : List Nat) (st : RefState) (idx : Nat)
    (hzero : bumps (earlyConditions words st idx) st.viol = 0) :
    words.getD (recW * idx + 6) 0 ≤ maxStat := by
  apply Nat.le_of_not_gt
  intro hgt
  have hgt' : maxStat < words.getD (recW * idx + 6) 0 := hgt
  have hb : (words.getD (recW * idx + 6) 0 > maxStat : Bool) = true :=
    decide_eq_true hgt'
  have hmem : true ∈ earlyConditions words st idx := by
    simp only [earlyConditions, List.mem_cons, List.mem_singleton,
      Bool.decide_coe]
    right; right; right; right; right; right; right
    left
    exact hb.symm
  have hpos := bumps_pos_of_true_mem _ st.viol hmem
  omega

theorem stat_le_of_historicalEarly_zero
    (c : Cfg) (words : List Nat) (idx : Nat)
    (before loaded : AState) (st : RefState)
    (hloaded : HistoricalLoaded c words idx before loaded)
    (hbefore : refStateOf before = st)
    (hword : ∀ j, loaded.regs j < M)
    (hprevLast : st.prevLast ≤ 1)
    (hprevBlk : st.prevBlk + 1 < M)
    (hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M)
    (hNoWrap : st.viol + 8 < M)
    (hzero : (arun idx loaded (historicalEarly c)).regs rViol = 0) :
    words.getD (recW * idx + 6) 0 ≤ maxStat := by
  have hdenote := historicalEarly_viol c words idx before loaded st hloaded
    hbefore hword hprevLast hprevBlk hslot hNoWrap
  rw [hdenote] at hzero
  exact stat_le_of_earlyConditions_zero words st idx hzero

end LeanCompCert.Ports.DirichletLadderExternalSafety
