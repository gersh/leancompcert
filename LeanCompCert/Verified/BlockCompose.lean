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

/-! ## The register footprint

★ The frames above are stated one register at a time, and in an assembly that
is the wrong granularity: wiring five blocks needs each one checked against
every earlier one's outputs, which is quadratically many `≠` hypotheses.

`Writes` replaces all of them with a single **computable list**.  For a block
with concrete register numbers `Writes l` reduces to a literal by `rfl`, so
every frame obligation becomes a decidable membership test — and `decide` on
`r ∉ [310, 311, 340]` is cheap where deciding sixty inequalities was not. -/

/-- The registers a block writes, in order. -/
def Writes : List Instr → List Nat
  | [] => []
  | i :: l => sdest i :: Writes l

@[simp] theorem writes_nil : Writes [] = [] := rfl

@[simp] theorem writes_cons (i : Instr) (l : List Instr) :
    Writes (i :: l) = sdest i :: Writes l := rfl

/-- ★ The footprint of a concatenation is the concatenation of footprints,
which is what makes the whole scheme compositional. -/
@[simp] theorem writes_append : ∀ (l₁ l₂ : List Instr),
    Writes (l₁ ++ l₂) = Writes l₁ ++ Writes l₂
  | [], _ => rfl
  | i :: l, l₂ => by
      show sdest i :: Writes (l ++ l₂) = sdest i :: (Writes l ++ Writes l₂)
      rw [writes_append l l₂]

/-- **A register outside the footprint is preserved.**  This is the bridge
from the decidable test to the frame. -/
theorem preserves_of_not_mem {l : List Instr} {r : Nat} (h : r ∉ Writes l) :
    Preserves l r := by
  induction l with
  | nil => intro i hi; cases hi
  | cons j l ih =>
      have h1 : r ≠ sdest j := fun hc => h (List.mem_cons.mpr (Or.inl hc))
      have h2 : r ∉ Writes l := fun hc => h (List.mem_cons.mpr (Or.inr hc))
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact fun hEq => h1 hEq.symm
      · exact ih h2 i hi'

/-- A register outside the footprint keeps its value. -/
theorem srun_outside (k : Nat) (s : RegState) {l : List Instr} {r : Nat}
    (h : r ∉ Writes l) : srun k s l r = s r :=
  srun_preserves k s (preserves_of_not_mem h)

/-- **The composition lemma, footprint form.**  Everything a caller has to
supply is one membership test. -/
theorem spec_append_of_not_mem (k : Nat) (s : RegState)
    {l₁ l₂ : List Instr} {r v : Nat}
    (h₁ : srun k s l₁ r = v) (h₂ : r ∉ Writes l₂) :
    srun k s (l₁ ++ l₂) r = v :=
  spec_append_of_preserves k s h₁ (preserves_of_not_mem h₂)

/-! ### Decomposing a chain

⚠ Decomposing an assembled block by `show` and definitional unfolding times
out the kernel once the block is a few hundred instructions long — it forces
the whole `++` chain open.  These make the split syntactic, which is
instant. -/

theorem srun_append3 (k : Nat) (s : RegState) (l₁ l₂ l₃ : List Instr) :
    srun k s (l₁ ++ l₂ ++ l₃) = srun k (srun k (srun k s l₁) l₂) l₃ := by
  rw [srun_append, srun_append]

theorem srun_append4 (k : Nat) (s : RegState) (l₁ l₂ l₃ l₄ : List Instr) :
    srun k s (l₁ ++ l₂ ++ l₃ ++ l₄)
      = srun k (srun k (srun k (srun k s l₁) l₂) l₃) l₄ := by
  rw [srun_append, srun_append, srun_append]

theorem srun_append5 (k : Nat) (s : RegState) (l₁ l₂ l₃ l₄ l₅ : List Instr) :
    srun k s (l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅)
      = srun k (srun k (srun k (srun k (srun k s l₁) l₂) l₃) l₄) l₅ := by
  rw [srun_append, srun_append, srun_append, srun_append]

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
#print axioms writes_append
#print axioms preserves_of_not_mem
#print axioms spec_append_of_not_mem

end LeanCompCert.Verified.BlockCompose
