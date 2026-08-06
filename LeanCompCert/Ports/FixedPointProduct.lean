/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Dyadic
import LeanCompCert.Verified.ListFold

/-!
# Verified upward-rounded fixed-point products

This port checks products of positive rational upper bounds without ever
materialising their large common denominator.  Each input word `w` represents
an upper factor `w / scale`; the machine updates

`acc := ceil(acc * w / scale)`

and accepts when the final accumulator is at most `bound`.  The input words
are the indices of an `LProgram`, so a caller can hoist an expensive exact
factor table once, prove its pointwise meaning in Lean, and compile the small
integer product itself.

`Safe` records precisely the no-wrap condition needed at every multiplication
and addition.  It is recursive and decidable, so concrete campaigns discharge
it by kernel computation without evaluating a CCIR trace.
-/

namespace LeanCompCert.Ports.FixedPointProduct

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ListFold

/-- One upward-rounded fixed-point multiplication. -/
def step (scale accumulator word : Nat) : Nat :=
  (accumulator * word + scale - 1) / scale

/-- Exact fold computed by the machine when arithmetic does not wrap. -/
def run (scale seed : Nat) (words : List Nat) : Nat :=
  words.foldl (step scale) seed

/-- Executable per-prefix word-safety check. -/
def safeB (scale : Nat) (accumulator : Nat) : List Nat → Bool
  | [] => true
  | word :: rest =>
      decide (accumulator * word + scale - 1 < M) &&
        safeB scale (step scale accumulator word) rest

/-- Per-prefix word-safety, in proposition form. -/
def Safe (scale accumulator : Nat) (words : List Nat) : Prop :=
  safeB scale accumulator words = true

instance safeDecidable (scale accumulator words) :
    Decidable (Safe scale accumulator words) := by
  unfold Safe
  infer_instance

@[simp] theorem safe_nil (scale accumulator : Nat) :
    Safe scale accumulator [] := rfl

theorem safe_cons_iff (scale accumulator word : Nat) (rest : List Nat) :
    Safe scale accumulator (word :: rest) ↔
      accumulator * word + scale - 1 < M ∧
        Safe scale (step scale accumulator word) rest := by
  simp [Safe, safeB, Bool.and_eq_true, decide_eq_true_eq]

structure Admissible (scale seed bound : Nat) (words : List Nat) : Prop where
  scalePos : 0 < scale
  scaleLt : scale < M
  seedLt : seed < M
  boundLt : bound < M
  wordsLt : ∀ word ∈ words, word < M
  safe : Safe scale seed words

def initInstrs (seed : Nat) : List Instr :=
  [.mov 1 (.lit seed)]

def bodyInstrs (scale : Nat) : List Instr :=
  [ .binop 2 .mul (.reg 1) .idx
  , .binop 3 .add (.reg 2) (.lit (scale - 1))
  , .binop 1 .udiv (.reg 3) (.lit scale) ]

def epilogueInstrs (bound : Nat) : List Instr :=
  [.binop 0 .gt (.reg 1) (.lit bound)]

/-- The list-driven checker.  Output zero means `run ≤ bound`. -/
def productProgram (scale seed bound : Nat) (words : List Nat) : LProgram := {
  regCount := 4
  indices := words
  init := initInstrs seed
  body := bodyInstrs scale
  epilogue := epilogueInstrs bound
  output := 0
}

theorem productProgram_wf (scale seed bound : Nat) (words : List Nat) :
    (productProgram scale seed bound words).WF := by
  refine ⟨show (0 : Nat) < 4 by decide, ?_, ?_, ?_⟩
  · intro instr hinstr
    simp only [productProgram, initInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (1 : Nat) < 4 by decide, trivial⟩
  · intro instr hinstr
    simp only [productProgram, bodyInstrs] at hinstr
    rcases List.mem_cons.mp hinstr with rfl | hinstr
    · exact ⟨show (2 : Nat) < 4 by decide,
        show (1 : Nat) < 4 by decide, trivial⟩
    · rcases List.mem_cons.mp hinstr with rfl | hinstr
      · exact ⟨show (3 : Nat) < 4 by decide,
          show (2 : Nat) < 4 by decide, trivial⟩
      · rcases List.mem_singleton.mp hinstr with rfl
        exact ⟨show (1 : Nat) < 4 by decide,
          show (3 : Nat) < 4 by decide, trivial⟩
  · intro instr hinstr
    simp only [productProgram, epilogueInstrs, List.mem_singleton] at hinstr
    subst instr
    exact ⟨show (0 : Nat) < 4 by decide,
      show (1 : Nat) < 4 by decide, trivial⟩

private theorem body_denote (scale accumulator word : Nat) (s : RegState)
    (hacc : s 1 = accumulator) (hscalePos : 0 < scale)
    (hscaleLt : scale < M) (hwordLt : word < M)
    (hsafe : accumulator * word + scale - 1 < M) :
    ∃ s', denoteInstrs word s (bodyInstrs scale) = some s' ∧
      s' 1 = step scale accumulator word := by
  have hprodLt : accumulator * word < M := by omega
  have haddLt : accumulator * word + (scale - 1) < M := by omega
  have hscalePredLt : scale - 1 < M := by omega
  have hscaleNe : scale % M ≠ 0 := by
    rw [Nat.mod_eq_of_lt hscaleLt]
    omega
  have hscaleZero : scale ≠ 0 := by omega
  have hquotLe := Nat.div_le_self (accumulator * word + (scale - 1)) scale
  have hquotLt : (accumulator * word + (scale - 1)) / scale < M := by omega
  have haddEq : accumulator * word + scale - 1 =
      accumulator * word + (scale - 1) := by omega
  let s2 := s.set 2 (accumulator * word)
  let s3 := s2.set 3 (accumulator * word + (scale - 1))
  let s1 := s3.set 1 ((accumulator * word + (scale - 1)) / scale)
  refine ⟨s1, ?_, ?_⟩
  · simp [bodyInstrs, denoteInstrs, denoteInstr, denoteOp,
      denoteOperand, hacc, Nat.mod_eq_of_lt hwordLt,
      Nat.mod_eq_of_lt hprodLt, Nat.mod_eq_of_lt hscaleLt,
      Nat.mod_eq_of_lt hscalePredLt, Nat.mod_eq_of_lt haddLt,
      Nat.mod_eq_of_lt hquotLt, hscaleZero,
      s2, s3, s1, RegState.set]
  · simp only [s1, RegState.set, if_pos, step]
    rw [haddEq]

private theorem fold_denote (scale : Nat) (words : List Nat)
    (accumulator : Nat) (s : RegState) (hacc : s 1 = accumulator)
    (hscalePos : 0 < scale) (hscaleLt : scale < M)
    (hwordsLt : ∀ word ∈ words, word < M)
    (hsafe : Safe scale accumulator words) :
    ∃ s', words.foldlM
        (fun state word => denoteInstrs word state (bodyInstrs scale)) s =
        some s' ∧ s' 1 = run scale accumulator words := by
  induction words generalizing accumulator s with
  | nil =>
      exact ⟨s, rfl, hacc⟩
  | cons word rest ih =>
      rw [safe_cons_iff] at hsafe
      rcases hsafe with ⟨hhead, hrest⟩
      have hwordLt := hwordsLt word (by simp)
      have hrestLt : ∀ w ∈ rest, w < M := fun w hw =>
        hwordsLt w (by simp [hw])
      obtain ⟨s1, hs1, hs1acc⟩ :=
        body_denote scale accumulator word s hacc hscalePos hscaleLt hwordLt hhead
      obtain ⟨s2, hs2, hs2acc⟩ :=
        ih (step scale accumulator word) s1 hs1acc hrestLt hrest
      refine ⟨s2, ?_, ?_⟩
      · simp only [List.foldlM_cons, hs1]
        exact hs2
      · simpa only [run, List.foldl_cons] using hs2acc

private theorem init_denote (seed : Nat) (hseed : seed < M) :
    ∃ s, denoteInstrs 0 initialState (initInstrs seed) = some s ∧ s 1 = seed := by
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

/-- The program denotes the non-wrapping upward-rounded product verdict. -/
theorem productProgram_denote (scale seed bound : Nat) (words : List Nat)
    (hadm : Admissible scale seed bound words) :
    (productProgram scale seed bound words).denote =
      some (if run scale seed words > bound then 1 else 0) := by
  obtain ⟨s0, hs0, hs0acc⟩ := init_denote seed hadm.seedLt
  obtain ⟨s1, hs1, hs1acc⟩ :=
    fold_denote scale words seed s0 hs0acc hadm.scalePos hadm.scaleLt
      hadm.wordsLt hadm.safe
  obtain ⟨s2, hs2, hs2out⟩ :=
    epilogue_denote bound (run scale seed words) s1 hs1acc hadm.boundLt
  change (do
    let state ← denoteInstrs 0 initialState (initInstrs seed)
    let state ← words.foldlM
      (fun state word => denoteInstrs word state (bodyInstrs scale)) state
    let state ← denoteInstrs 0 state (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs0]
  change (do
    let state ← words.foldlM
      (fun state word => denoteInstrs word state (bodyInstrs scale)) s0
    let state ← denoteInstrs 0 state (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs1]
  change (do
    let state ← denoteInstrs 0 s1 (epilogueInstrs bound)
    pure (state 0)) = _
  rw [hs2]
  exact congrArg some hs2out

/-- Packaged compiled computation for a concrete product. -/
def productComputation (name : String) (scale seed bound : Nat)
    (words : List Nat) : LeanCompCert.Verified.Computation :=
  (productProgram scale seed bound words).toComputation name
    (productProgram_wf scale seed bound words)

/-- An admitted zero result implies the exact integer product bound. -/
theorem bound_of_returns_zero (name : String) (scale seed bound : Nat)
    (words : List Nat) (hadm : Admissible scale seed bound words)
    (hrun : (productComputation name scale seed bound words).Returns
      ((0 : Nat) : Int)) :
    run scale seed words ≤ bound := by
  have hden : (productProgram scale seed bound words).denote = some 0 :=
    ((LProgram.toComputation_returns
      (productProgram scale seed bound words) name
      (productProgram_wf scale seed bound words) 0)).mp hrun
  rw [productProgram_denote scale seed bound words hadm] at hden
  split at hden <;> simp_all

end LeanCompCert.Ports.FixedPointProduct
