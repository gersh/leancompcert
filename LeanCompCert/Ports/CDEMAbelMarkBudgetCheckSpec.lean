import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckFold

/-!
# Source specification of the rolled CDEM Abel marking-budget checker

This file re-blocks the flat `len * rounds` machine loop into one block per
divisor.  It never evaluates the production fold.  The result is expressed
as a short source recursion with one node per divisor, suitable for rewriting
against the production `muCodeFor` theorem in the consuming project.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.BlockedFold

theorem gstep_round (n r : Nat) (hr : r < rounds) (a : Abs)
    (hacc : a.acc < M) :
    gstep (n * rounds + r) a =
      (let t := MertensCDEM.trialStep (r + 2)
        (if r = 0 then ⟨2 + n, 0, 0⟩ else a.t)
      if r + 1 = rounds then
        ⟨(a.acc + allowanceOf (2 + n) t) % M, t⟩
      else ⟨a.acc, t⟩) := by
  obtain ⟨hdiv, hmod⟩ := MertensCDEM.index_decode trialCfg n r hr
  simp only [trialCfg] at hdiv hmod
  unfold gstep accumulated divided reset
  rw [hdiv, hmod]
  by_cases hlast : r + 1 = rounds
  · have hq : r = rounds - 1 := by omega
    simp [rounds, hlast, hq]
  · have hq : ¬ r = rounds - 1 := by omega
    have hq' : r ≠ 444 := by simpa [rounds] using hq
    by_cases hr0 : r = 0 <;>
      simp [rounds, hq', hr0, Nat.mod_eq_of_lt hacc]

def trialPrefix (X k : Nat) : MertensCDEM.Trial :=
  (List.range k).foldl
    (fun t q => MertensCDEM.trialStep (q + 2) t) ⟨X, 0, 0⟩

theorem trialPrefix_full (X R : Nat) :
    trialPrefix X R = MertensCDEM.trialRun X R := rfl

theorem block_prefix (n : Nat) (a : Abs) (hacc : a.acc < M) :
    ∀ k, k < rounds →
      (List.range (k + 1)).foldl
          (fun x r => gstep (n * rounds + r) x) a =
        (let t := trialPrefix (2 + n) (k + 1)
        if k + 1 = rounds then
          ⟨(a.acc + allowanceOf (2 + n) t) % M, t⟩
        else ⟨a.acc, t⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons,
        List.foldl_nil, gstep_round n 0 hk a hacc]
      simp only [trialPrefix, show (List.range 1) = [0] from rfl,
        List.foldl_cons, List.foldl_nil, if_pos rfl]
      rfl
  | succ k ih =>
      intro hk
      have hklt : k < rounds := by omega
      have hkne : ¬ (k + 1 = rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt]
      rw [if_neg hkne]
      rw [gstep_round n (k + 1) hk ⟨a.acc, trialPrefix (2 + n) (k + 1)⟩
        hacc]
      have hne0 : ¬ (k + 1 = 0) := by omega
      simp only [if_neg hne0, trialPrefix, List.range_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_spec (n : Nat) (a : Abs) (hacc : a.acc < M) :
    block rounds (fun x i => gstep i x) a n =
      (let t := MertensCDEM.trialRun (2 + n) rounds
      ⟨(a.acc + allowanceOf (2 + n) t) % M, t⟩) := by
  have h := block_prefix n a hacc (rounds - 1) (by decide)
  rw [show rounds - 1 + 1 = rounds from by decide] at h
  rw [block_eq_shift, h]
  simp only [trialPrefix_full, if_pos]

/-- The accumulated machine word after `n` complete divisor blocks. -/
def budgetAtMod : Nat → Nat
  | 0 => seed
  | n + 1 =>
      (budgetAtMod n + allowanceOf (2 + n)
        (MertensCDEM.trialRun (2 + n) rounds)) % M

theorem budgetAtMod_lt : ∀ n, budgetAtMod n < M
  | 0 => by decide
  | _ + 1 => Nat.mod_lt _ M_pos

theorem fold_blocks : ∀ n,
    ((List.range n).foldl
      (block rounds (fun x i => gstep i x)) (obs entry)).acc = budgetAtMod n
  | 0 => by
      have hseed : seed < M := by decide
      simp [budgetAtMod, obs, entry, RegState.set, initialState,
        Nat.mod_eq_of_lt hseed]
  | n + 1 => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        block_spec n _ (by rw [fold_blocks n]; exact budgetAtMod_lt n),
        fold_blocks n, budgetAtMod]

theorem value_eq_budgetAtMod :
    ((List.range program.loopCount).foldl
      (fun a index => gstep index a) (obs entry)).acc = budgetAtMod len := by
  change ((List.range (len * rounds)).foldl
    (fun a index => gstep index a) (obs entry)).acc = budgetAtMod len
  rw [foldl_range_mul len rounds (fun a index => gstep index a) (obs entry)]
  exact fold_blocks len

theorem program_denote_budgetAtMod :
    program.denote = some (budgetAtMod len) := by
  rw [program_denote_raw, value_eq_budgetAtMod]

/-- The unbounded-Nat source sum computed by the checker before word
normalisation. -/
def budgetAt : Nat → Nat
  | 0 => seed
  | n + 1 => budgetAt n + allowanceOf (2 + n)
      (MertensCDEM.trialRun (2 + n) rounds)

theorem allowanceOf_le (d : Nat) (t : MertensCDEM.Trial)
    (hsq : t.sq ≤ 1) : allowanceOf d t ≤ segLen + 2 := by
  have hdiv : segLen / d ≤ segLen := Nat.div_le_self _ _
  rcases (show t.sq = 0 ∨ t.sq = 1 by omega) with h | h <;>
    simp [allowanceOf, h] <;> split <;> omega

theorem budgetAt_le : ∀ n, budgetAt n ≤ seed + n * (segLen + 2)
  | 0 => by simp [budgetAt]
  | n + 1 => by
      rw [budgetAt]
      have hprev := budgetAt_le n
      have hallow := allowanceOf_le (2 + n)
        (MertensCDEM.trialRun (2 + n) rounds)
        (MertensCDEM.trialRun_bits (2 + n) rounds).1
      calc
        budgetAt n + allowanceOf (2 + n)
            (MertensCDEM.trialRun (2 + n) rounds) ≤
            (seed + n * (segLen + 2)) + (segLen + 2) :=
          Nat.add_le_add hprev hallow
        _ = seed + (n + 1) * (segLen + 2) := by
          rw [Nat.add_mul]
          omega

theorem budgetAt_len_lt_M : budgetAt len < M := by
  have h := budgetAt_le len
  exact Nat.lt_of_le_of_lt h (by decide)

theorem budgetAtMod_eq : ∀ n, budgetAtMod n = budgetAt n % M
  | 0 => by
      have hseed : seed < M := by decide
      simp [budgetAtMod, budgetAt, Nat.mod_eq_of_lt hseed]
  | n + 1 => by
      rw [budgetAtMod, budgetAt, budgetAtMod_eq n, Nat.mod_add_mod]

end LeanCompCert.Ports.CDEMAbelMarkBudgetCheck
