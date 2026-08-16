/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.InstrBlock

/-!
# Composing straight-line blocks

Every emitted block is proved the same way: run a block, then another, and
argue that the second did not disturb what the first computed, or that the
first did not disturb what the second reads.  That argument has been written
out by hand at each site.  This module names it.

`spec_append_of_preserves` is the lemma: the earlier block computed the answer
and the later one leaves it alone.

★ It is about the **frame**, and the frame is the part that is easy to leave
implicit and wrong.  A block that computes the right value into `r` proves
nothing about `r` after a longer program unless something rules out a later
write, and `Preserves` is that something.

⚠ The *other* direction needs no frame at all.  Transporting a fact about `l₂`
from the post-`l₁` state to the composite is just `srun_append` — I first
stated it as `reads_append_of_preserves` carrying a `Preserves l₁ r`
hypothesis, and the proof never used it.  A lemma named `_of_preserves` whose
frame is decorative is worse than no lemma, so it is gone.

⚠ `Preserves l r` is a statement about **destinations only**.  A block can read
`r` freely and still preserve it; that asymmetry is the whole point, and
conflating the two would make the predicate far too strong to hold anywhere.
-/

namespace LeanCompCert.Verified.BlockCompose

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-- `l` never writes `r`. -/
def Preserves (l : List Instr) (r : Nat) : Prop := ∀ i ∈ l, sdest i ≠ r

theorem preserves_nil (r : Nat) : Preserves [] r := by
  intro i hi; cases hi

theorem preserves_cons {i : Instr} {l : List Instr} {r : Nat}
    (hi : sdest i ≠ r) (hl : Preserves l r) : Preserves (i :: l) r := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hi
  · exact hl j hj

theorem preserves_append {l₁ l₂ : List Instr} {r : Nat}
    (h₁ : Preserves l₁ r) (h₂ : Preserves l₂ r) : Preserves (l₁ ++ l₂) r := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact h₁ i h
  · exact h₂ i h

/-- A preserved register keeps its value. -/
theorem srun_preserves (k : Nat) (s : RegState) {l : List Instr} {r : Nat}
    (h : Preserves l r) : srun k s l r = s r :=
  srun_untouched k r l h s

/-- **The first direction.**  `l₁` computed `v` into `r`, and `l₂` does not
write `r`, so the composite still holds `v`. -/
theorem spec_append_of_preserves (k : Nat) (s : RegState)
    {l₁ l₂ : List Instr} {r v : Nat}
    (h₁ : srun k s l₁ r = v) (h₂ : Preserves l₂ r) :
    srun k s (l₁ ++ l₂) r = v := by
  rw [srun_append, srun_preserves k _ h₂, h₁]

/-- Two blocks, each computing into its own register, compose. -/
theorem pair_append (k : Nat) (s : RegState)
    {l₁ l₂ : List Instr} {r₁ r₂ v₁ v₂ : Nat}
    (h₁ : srun k s l₁ r₁ = v₁) (hp : Preserves l₂ r₁)
    (h₂ : srun k (srun k s l₁) l₂ r₂ = v₂) :
    srun k s (l₁ ++ l₂) r₁ = v₁ ∧ srun k s (l₁ ++ l₂) r₂ = v₂ := by
  constructor
  · exact spec_append_of_preserves k s h₁ hp
  · rw [srun_append]; exact h₂

/-! ## Discharging `Preserves`

⚠ The frame proofs in this development have blown up twice, both times for the
same reason: unfolding a block that contains `++` inside a membership
hypothesis.  `preserves_append` is the cure — split at the `++` and never let
`simp` see the concatenation. -/

/-- A singleton block preserves everything it does not write. -/
theorem preserves_singleton {i : Instr} {r : Nat} (h : sdest i ≠ r) :
    Preserves [i] r :=
  preserves_cons h (preserves_nil r)

#print axioms srun_preserves
#print axioms spec_append_of_preserves
#print axioms pair_append
#print axioms preserves_append

end LeanCompCert.Verified.BlockCompose
