/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.WordBounds

/-!
# Total verified list-wide word bounds

`WordBounds` exposes the simplest compiler theorem when every source word is
already known to fit one machine word.  This wrapper makes that side condition
computational instead of trusted: an out-of-range source word is replaced by
`bound + 1`, so the compiled comparison necessarily rejects it.  Consequently
the only static hypotheses are that the bound and the list length fit in one
word; no proposition about the untrusted input values is needed.
-/

namespace LeanCompCert.Ports.TotalWordBounds

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.WordBounds

/-- Normalize a mathematical input to a machine word, mapping overflow to a
deliberate bound violation. -/
def checkedWord (bound word : Nat) : Nat :=
  if word < M then word else bound + 1

def checkedWords (bound : Nat) (words : List Nat) : List Nat :=
  words.map (checkedWord bound)

theorem checkedWord_lt_M {bound word : Nat} (hbound : bound + 1 < M) :
    checkedWord bound word < M := by
  unfold checkedWord
  split <;> omega

theorem checkedWord_le_iff {bound word : Nat} (hbound : bound + 1 < M) :
    checkedWord bound word ≤ bound ↔ word ≤ bound := by
  unfold checkedWord
  split
  case isTrue hword => rfl
  case isFalse hword =>
    have hboundM : bound < M := by omega
    have hnle : ¬ word ≤ bound := by omega
    constructor <;> omega

private theorem violation_le_one (bound word : Nat) :
    violation bound word ≤ 1 := by
  unfold violation
  split <;> omega

/-- A violation accumulator cannot wrap when the remaining list length fits
above it.  This proof is independent of the input values. -/
theorem safe_of_accumulator_add_length_lt (bound accumulator : Nat) :
    ∀ words : List Nat, accumulator + words.length < M →
      Safe bound accumulator words
  | [], _ => by simp
  | word :: rest, hlen => by
      rw [safe_cons_iff]
      constructor
      · have hv := violation_le_one bound word
        simp only [List.length_cons] at hlen
        omega
      · apply safe_of_accumulator_add_length_lt
        have hv := violation_le_one bound word
        simp only [List.length_cons] at hlen
        omega

theorem checkedWords_admissible (bound : Nat) (words : List Nat)
    (hbound : bound + 1 < M) (hlen : words.length < M) :
    Admissible bound (checkedWords bound words) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro word hword
    simp only [checkedWords, List.mem_map] at hword
    obtain ⟨source, _, rfl⟩ := hword
    exact checkedWord_lt_M hbound
  · apply safe_of_accumulator_add_length_lt
    simpa [checkedWords] using hlen

def boundsProgram (bound : Nat) (words : List Nat) :
    LeanCompCert.Verified.ListFold.LProgram :=
  WordBounds.boundsProgram bound (checkedWords bound words)

def boundsComputation (name : String) (bound : Nat) (words : List Nat) :
    LeanCompCert.Verified.Computation :=
  WordBounds.boundsComputation name bound (checkedWords bound words)

/-- A compiled zero result proves the mathematical bound for every source
word, including rejecting any source word at least `2^64`. -/
theorem all_le_of_returns_zero (name : String) (bound : Nat)
    (words : List Nat) (hbound : bound + 1 < M)
    (hlen : words.length < M)
    (hrun : (boundsComputation name bound words).Returns
      ((0 : Nat) : Int)) :
    ∀ word ∈ words, word ≤ bound := by
  have hall := WordBounds.all_le_of_returns_zero name bound
    (checkedWords bound words) (checkedWords_admissible bound words hbound hlen)
    hrun
  intro word hword
  have hchecked : checkedWord bound word ≤ bound := by
    apply hall (checkedWord bound word)
    exact List.mem_map_of_mem hword
  exact (checkedWord_le_iff hbound).mp hchecked

end LeanCompCert.Ports.TotalWordBounds
