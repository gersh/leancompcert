/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.ListFold

/-!
# Verified non-wrapping fixed-point sums

This port checks a list of nonnegative integer upper bounds.  The input words
are the indices of an `LProgram`; its body performs `acc := acc + word`, and
output zero means that the final sum is at most `bound`.

Callers may attach any rational scale and normalization to the words.  The
machine theorem deliberately exposes only the exact integer sum, while the
caller proves that each source term lies below its corresponding word.
-/

namespace LeanCompCert.Ports.FixedPointSum

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ListFold

/-- Exact fold computed by the machine when addition does not wrap. -/
def run (seed : Nat) (words : List Nat) : Nat :=
  words.foldl Nat.add seed

/-- Executable per-prefix word-safety check. -/
def safeB (accumulator : Nat) : List Nat → Bool
  | [] => true
  | word :: rest =>
      decide (accumulator + word < M) && safeB (accumulator + word) rest

/-- Per-prefix word-safety, in proposition form. -/
def Safe (accumulator : Nat) (words : List Nat) : Prop :=
  safeB accumulator words = true

instance safeDecidable (accumulator words) :
    Decidable (Safe accumulator words) := by
  unfold Safe
  infer_instance

@[simp] theorem safe_nil (accumulator : Nat) : Safe accumulator [] := rfl

theorem safe_cons_iff (accumulator word : Nat) (rest : List Nat) :
    Safe accumulator (word :: rest) ↔
      accumulator + word < M ∧ Safe (accumulator + word) rest := by
  simp [Safe, safeB, Bool.and_eq_true, decide_eq_true_eq]

structure Admissible (seed bound : Nat) (words : List Nat) : Prop where
  seedLt : seed < M
  boundLt : bound < M
  wordsLt : ∀ word ∈ words, word < M
  safe : Safe seed words

def initInstrs (seed : Nat) : List Instr :=
  [.mov 1 (.lit seed)]

def bodyInstrs : List Instr :=
  [.binop 1 .add (.reg 1) .idx]

def epilogueInstrs (bound : Nat) : List Instr :=
  [.binop 0 .gt (.reg 1) (.lit bound)]

/-- The list-driven checker.  Output zero means `run ≤ bound`. -/
def sumProgram (seed bound : Nat) (words : List Nat) : LProgram := {
  regCount := 2
  indices := words
  init := initInstrs seed
  body := bodyInstrs
  epilogue := epilogueInstrs bound
  output := 0
}

theorem sumProgram_wf (seed bound : Nat) (words : List Nat) :
    (sumProgram seed bound words).WF := by
  refine ⟨show (0 : Nat) < 2 by decide, ?_, ?_, ?_⟩
  · intro instr hinstr
    simp only [sumProgram, initInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (1 : Nat) < 2 by decide, trivial⟩
  · intro instr hinstr
    simp only [sumProgram, bodyInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (1 : Nat) < 2 by decide,
      show (1 : Nat) < 2 by decide, trivial⟩
  · intro instr hinstr
    simp only [sumProgram, epilogueInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (0 : Nat) < 2 by decide,
      show (1 : Nat) < 2 by decide, trivial⟩

private theorem body_denote (accumulator word : Nat) (s : RegState)
    (hacc : s 1 = accumulator) (hwordLt : word < M)
    (hsafe : accumulator + word < M) :
    ∃ s', denoteInstrs word s bodyInstrs = some s' ∧
      s' 1 = accumulator + word := by
  let s' := s.set 1 (accumulator + word)
  refine ⟨s', ?_, ?_⟩
  · simp [bodyInstrs, denoteInstrs, denoteInstr, denoteOp,
      denoteOperand, hacc, Nat.mod_eq_of_lt hwordLt,
      Nat.mod_eq_of_lt hsafe, s']
  · simp [s', RegState.set]

private theorem fold_denote (words : List Nat) (accumulator : Nat)
    (s : RegState) (hacc : s 1 = accumulator)
    (hwordsLt : ∀ word ∈ words, word < M)
    (hsafe : Safe accumulator words) :
    ∃ s', words.foldlM
        (fun state word => denoteInstrs word state bodyInstrs) s = some s' ∧
      s' 1 = run accumulator words := by
  induction words generalizing accumulator s with
  | nil => exact ⟨s, rfl, hacc⟩
  | cons word rest ih =>
      rw [safe_cons_iff] at hsafe
      rcases hsafe with ⟨hhead, hrest⟩
      have hwordLt := hwordsLt word (by simp)
      have hrestLt : ∀ w ∈ rest, w < M := fun w hw =>
        hwordsLt w (by simp [hw])
      obtain ⟨s1, hs1, hs1acc⟩ :=
        body_denote accumulator word s hacc hwordLt hhead
      obtain ⟨s2, hs2, hs2acc⟩ :=
        ih (accumulator + word) s1 hs1acc hrestLt hrest
      refine ⟨s2, ?_, ?_⟩
      · simp only [List.foldlM_cons, hs1]
        exact hs2
      · change s2 1 = List.foldl Nat.add (accumulator + word) rest
        exact hs2acc

private theorem init_denote (seed : Nat) (hseed : seed < M) :
    ∃ s, denoteInstrs 0 initialState (initInstrs seed) = some s ∧
      s 1 = seed := by
  let s := initialState.set 1 seed
  refine ⟨s, ?_, ?_⟩
  · simp [initInstrs, denoteInstrs, denoteInstr, denoteOperand,
      Nat.mod_eq_of_lt hseed, s]
  · simp [s, RegState.set]

private theorem epilogue_denote (bound accumulator : Nat) (s : RegState)
    (hacc : s 1 = accumulator) (hbound : bound < M) :
    ∃ s', denoteInstrs 0 s (epilogueInstrs bound) = some s' ∧
      s' 0 = if accumulator > bound then 1 else 0 := by
  let s' := s.set 0 (if accumulator > bound then 1 else 0)
  refine ⟨s', ?_, ?_⟩
  · simp [epilogueInstrs, denoteInstrs, denoteInstr, denoteOp,
      denoteOperand, hacc, Nat.mod_eq_of_lt hbound, s']
  · simp [s', RegState.set]

/-- The program denotes the non-wrapping integer-sum verdict. -/
theorem sumProgram_denote (seed bound : Nat) (words : List Nat)
    (hadm : Admissible seed bound words) :
    (sumProgram seed bound words).denote =
      some (if run seed words > bound then 1 else 0) := by
  obtain ⟨s0, hs0, hs0acc⟩ := init_denote seed hadm.seedLt
  obtain ⟨s1, hs1, hs1acc⟩ :=
    fold_denote words seed s0 hs0acc hadm.wordsLt hadm.safe
  obtain ⟨s2, hs2, hs2out⟩ :=
    epilogue_denote bound (run seed words) s1 hs1acc hadm.boundLt
  change (do
    let state ← denoteInstrs 0 initialState (initInstrs seed)
    let state ← words.foldlM
      (fun state word => denoteInstrs word state bodyInstrs) state
    let state ← denoteInstrs 0 state (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs0]
  change (do
    let state ← words.foldlM
      (fun state word => denoteInstrs word state bodyInstrs) s0
    let state ← denoteInstrs 0 state (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs1]
  change (do
    let state ← denoteInstrs 0 s1 (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs2]
  exact congrArg some hs2out

/-- Packaged compiled computation for a concrete sum. -/
def sumComputation (name : String) (seed bound : Nat)
    (words : List Nat) : LeanCompCert.Verified.Computation :=
  (sumProgram seed bound words).toComputation name
    (sumProgram_wf seed bound words)

/-- An admitted zero result implies the exact integer sum bound. -/
theorem bound_of_returns_zero (name : String) (seed bound : Nat)
    (words : List Nat) (hadm : Admissible seed bound words)
    (hrun : (sumComputation name seed bound words).Returns
      ((0 : Nat) : Int)) :
    run seed words ≤ bound := by
  have hden : (sumProgram seed bound words).denote = some 0 :=
    ((LProgram.toComputation_returns
      (sumProgram seed bound words) name
      (sumProgram_wf seed bound words) 0)).mp hrun
  rw [sumProgram_denote seed bound words hadm] at hden
  split at hden <;> simp_all

end LeanCompCert.Ports.FixedPointSum
