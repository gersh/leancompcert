/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.ListFold

/-!
# Verified list-wide word bounds

The compiled loop compares every supplied word with one common bound and
counts violations.  Output zero therefore means every word is at most the
bound.  This is useful for outward interval tables: Lean certifies the exact
meaning of each word once, while generated code executes the entire table.
-/

namespace LeanCompCert.Ports.WordBounds

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ListFold

def violation (bound word : Nat) : Nat := if word > bound then 1 else 0

def run (bound : Nat) (words : List Nat) : Nat :=
  (words.map (violation bound)).sum

def safeB (bound accumulator : Nat) : List Nat → Bool
  | [] => true
  | word :: rest =>
      decide (accumulator + violation bound word < M) &&
        safeB bound (accumulator + violation bound word) rest

def Safe (bound accumulator : Nat) (words : List Nat) : Prop :=
  safeB bound accumulator words = true

instance safeDecidable (bound accumulator words) :
    Decidable (Safe bound accumulator words) := by
  unfold Safe
  infer_instance

@[simp] theorem safe_nil (bound accumulator : Nat) :
    Safe bound accumulator [] := rfl

theorem safe_cons_iff (bound accumulator word : Nat) (rest : List Nat) :
    Safe bound accumulator (word :: rest) ↔
      accumulator + violation bound word < M ∧
        Safe bound (accumulator + violation bound word) rest := by
  simp [Safe, safeB, Bool.and_eq_true, decide_eq_true_eq]

structure Admissible (bound : Nat) (words : List Nat) : Prop where
  boundLt : bound < M
  wordsLt : ∀ word ∈ words, word < M
  safe : Safe bound 0 words

def initInstrs : List Instr := [.mov 1 (.lit 0)]

def bodyInstrs (bound : Nat) : List Instr :=
  [ .binop 2 .gt .idx (.lit bound)
  , .binop 1 .add (.reg 1) (.reg 2) ]

def boundsProgram (bound : Nat) (words : List Nat) : LProgram := {
  regCount := 3
  indices := words
  init := initInstrs
  body := bodyInstrs bound
  epilogue := []
  output := 1
}

theorem boundsProgram_wf (bound : Nat) (words : List Nat) :
    (boundsProgram bound words).WF := by
  refine ⟨show (1 : Nat) < 3 by decide, ?_, ?_, ?_⟩
  · intro instr hinstr
    simp only [boundsProgram, initInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (1 : Nat) < 3 by decide, trivial⟩
  · intro instr hinstr
    simp only [boundsProgram, bodyInstrs] at hinstr
    rcases List.mem_cons.mp hinstr with rfl | hinstr
    · exact ⟨show (2 : Nat) < 3 by decide, trivial, trivial⟩
    · rcases List.mem_singleton.mp hinstr with rfl
      exact ⟨show (1 : Nat) < 3 by decide,
        show (1 : Nat) < 3 by decide, show (2 : Nat) < 3 by decide⟩
  · intro instr hinstr
    simp only [boundsProgram, List.not_mem_nil] at hinstr

private theorem body_denote (bound accumulator word : Nat) (s : RegState)
    (hacc : s 1 = accumulator) (hbound : bound < M)
    (hword : word < M)
    (hsafe : accumulator + violation bound word < M) :
    ∃ s', denoteInstrs word s (bodyInstrs bound) = some s' ∧
      s' 1 = accumulator + violation bound word := by
  let flag := violation bound word
  have hflag : flag < M := by
    unfold flag violation
    split <;> simp [M]
  let s2 := s.set 2 flag
  let s1 := s2.set 1 (accumulator + flag)
  have hs21 : s2 1 = accumulator := by
    simp [s2, RegState.set, hacc]
  have hs22 : s2 2 = flag := by
    simp [s2, RegState.set]
  have hfirst :
      denoteInstr word s (.binop 2 .gt .idx (.lit bound)) = some s2 := by
    simp [denoteInstr, denoteOp, denoteOperand, Nat.mod_eq_of_lt hword,
      Nat.mod_eq_of_lt hbound, s2, flag, violation]
  have hsecond :
      denoteInstr word s2 (.binop 1 .add (.reg 1) (.reg 2)) = some s1 := by
    simp [denoteInstr, denoteOp, denoteOperand, hs21, hs22,
      Nat.mod_eq_of_lt hsafe, s1, flag]
  refine ⟨s1, ?_, ?_⟩
  · simp [bodyInstrs, denoteInstrs, hfirst, hsecond]
  · simp [s1, s2, RegState.set, flag]

private theorem fold_denote (bound : Nat) (words : List Nat)
    (accumulator : Nat) (s : RegState) (hacc : s 1 = accumulator)
    (hbound : bound < M) (hwords : ∀ word ∈ words, word < M)
    (hsafe : Safe bound accumulator words) :
    ∃ s', words.foldlM
        (fun state word => denoteInstrs word state (bodyInstrs bound)) s =
        some s' ∧ s' 1 = accumulator + run bound words := by
  induction words generalizing accumulator s with
  | nil => exact ⟨s, rfl, by simpa [run] using hacc⟩
  | cons word rest ih =>
      rw [safe_cons_iff] at hsafe
      rcases hsafe with ⟨hhead, hrest⟩
      have hword := hwords word (by simp)
      have hrestWords : ∀ w ∈ rest, w < M := fun w hw =>
        hwords w (by simp [hw])
      obtain ⟨s1, hs1, hs1acc⟩ :=
        body_denote bound accumulator word s hacc hbound hword hhead
      obtain ⟨s2, hs2, hs2acc⟩ :=
        ih (accumulator + violation bound word) s1 hs1acc
          hrestWords hrest
      refine ⟨s2, ?_, ?_⟩
      · simp only [List.foldlM_cons, hs1]
        exact hs2
      · simpa only [run, List.map_cons, List.sum_cons, Nat.add_assoc]
          using hs2acc

private theorem init_denote :
    ∃ s, denoteInstrs 0 initialState initInstrs = some s ∧ s 1 = 0 := by
  let s := initialState.set 1 0
  refine ⟨s, ?_, ?_⟩ <;> simp [initInstrs, denoteInstrs, denoteInstr,
    denoteOperand, s, RegState.set]

theorem boundsProgram_denote (bound : Nat) (words : List Nat)
    (hadm : Admissible bound words) :
    (boundsProgram bound words).denote = some (run bound words) := by
  obtain ⟨s0, hs0, hs0acc⟩ := init_denote
  obtain ⟨s1, hs1, hs1acc⟩ :=
    fold_denote bound words 0 s0 hs0acc hadm.boundLt hadm.wordsLt hadm.safe
  change (do
    let state ← denoteInstrs 0 initialState initInstrs
    let state ← words.foldlM
      (fun state word => denoteInstrs word state (bodyInstrs bound)) state
    pure (state 1)) = _
  rw [hs0]
  change (do
    let state ← words.foldlM
      (fun state word => denoteInstrs word state (bodyInstrs bound)) s0
    pure (state 1)) = _
  rw [hs1]
  simpa using congrArg some hs1acc

def boundsComputation (name : String) (bound : Nat)
    (words : List Nat) : LeanCompCert.Verified.Computation :=
  (boundsProgram bound words).toComputation name
    (boundsProgram_wf bound words)

private theorem run_eq_zero_iff (bound : Nat) : ∀ words : List Nat,
    run bound words = 0 ↔ ∀ word ∈ words, word ≤ bound
  | [] => by simp [run]
  | word :: rest => by
      change violation bound word + run bound rest = 0 ↔
        ∀ w ∈ word :: rest, w ≤ bound
      rw [Nat.add_eq_zero_iff, run_eq_zero_iff bound rest]
      simp only [List.mem_cons]
      unfold violation
      by_cases h : word > bound
      · have hn : ¬ word ≤ bound := Nat.not_le_of_lt h
        simp [h, hn]
      · simp [h, Nat.le_of_not_gt h]

/-- An admitted zero result proves the bound for every runtime word. -/
theorem all_le_of_returns_zero (name : String) (bound : Nat)
    (words : List Nat) (hadm : Admissible bound words)
    (hrun : (boundsComputation name bound words).Returns
      ((0 : Nat) : Int)) :
    ∀ word ∈ words, word ≤ bound := by
  have hden : (boundsProgram bound words).denote = some 0 :=
    ((LProgram.toComputation_returns
      (boundsProgram bound words) name
      (boundsProgram_wf bound words) 0)).mp hrun
  rw [boundsProgram_denote bound words hadm] at hden
  have hzero : run bound words = 0 := by simpa using Option.some.inj hden
  exact (run_eq_zero_iff bound words).mp hzero

end LeanCompCert.Ports.WordBounds
