/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.TwosComplement

/-!
# The accumulator fold, in two's complement

`MainSumFold` bounds a sample of the main sum with a sign-magnitude
accumulator.  The mathematics there is right, but `TwosComplement` shows the
representation is wrong for emission: sign-magnitude addition is nineteen
instructions and `.add` is one.  This is the same fold re-fronted so the proved
object matches the code that will be emitted.

## Three sums, deliberately kept apart

⚠ There are **three** quantities here and collapsing any two of them is the
mistake to avoid:

* `tcSum` — what the machine computes, a `Nat` register value;
* `computedSum` — the exact signed sum of the *computed* terms;
* `exactSum` — the sum of the *exact* terms, which is what is wanted.

`tcSum_val` relates the first two: the accumulation is exact, so the machine
loses nothing.  `sum_error` relates the second two: the terms themselves are
only approximate, and that is where all the error lives.

★ Splitting them is what makes the bound linear.  Because the accumulation
contributes nothing, `M` terms contribute exactly `M` terms' worth of error.

## The obligation that is new

⚠ Sign-magnitude addition can only overflow the register.  Two's complement
addition can silently **wrap into the wrong sign**, which is worse: the result
is a perfectly valid register value.  `PartialsInRange` rules that out, and it
is stated at every suffix — a run of large positive terms followed by large
negative ones has a small total and can still wrap in the middle, so bounding
only the total would be unsound.
-/

namespace LeanCompCert.Verified.TwosComplementFold

open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.TwosComplement

/-- The accumulator: each step is one modular add, which is what `.add` does.
The pairs are (computed term, exact term). -/
def tcSum : List (Nat × Int) → Nat
  | [] => 0
  | p :: ps => (p.1 + tcSum ps) % B64

/-- The exact signed sum of the **computed** terms. -/
def computedSum : List (Nat × Int) → Int
  | [] => 0
  | p :: ps => tcVal p.1 + computedSum ps

/-- The sum of the **exact** terms — what the fold is approximating. -/
def exactSum : List (Nat × Int) → Int
  | [] => 0
  | p :: ps => p.2 + exactSum ps

/-- The accumulator is always a register value. -/
theorem tcSum_lt : ∀ ps : List (Nat × Int), tcSum ps < B64
  | [] => by decide
  | _ :: _ => Nat.mod_lt _ (by decide)

/-- Every partial sum stays inside signed range.

⚠ At every suffix, because that is where wrapping happens. -/
def PartialsInRange : List (Nat × Int) → Prop
  | [] => True
  | p :: ps => PartialsInRange ps ∧
      -(H : Int) ≤ tcVal p.1 + computedSum ps ∧
      tcVal p.1 + computedSum ps < (H : Int)

/-- ★ `PartialsInRange` is **decidable**, which is what lets a certificate
checker verify it by running rather than a proof supplying it. -/
instance decidablePartialsInRange : ∀ ps : List (Nat × Int),
    Decidable (PartialsInRange ps)
  | [] => isTrue trivial
  | p :: ps =>
      have : Decidable (PartialsInRange ps) := decidablePartialsInRange ps
      inferInstanceAs (Decidable (PartialsInRange ps ∧ _ ∧ _))

/-- **The accumulation is exact.**  Every `.add` is the signed sum, so the
machine loses nothing relative to the computed terms. -/
theorem tcSum_val : ∀ ps : List (Nat × Int), (∀ p ∈ ps, p.1 < B64) →
    PartialsInRange ps → tcVal (tcSum ps) = computedSum ps
  | [], _, _ => by
      show tcVal 0 = 0
      rw [tcVal_of_lt (by decide)]
      rfl
  | p :: ps, hb, hp => by
      have hbs : ∀ q ∈ ps, q.1 < B64 := fun q hq => hb q (by simp [hq])
      have ihv : tcVal (tcSum ps) = computedSum ps := tcSum_val ps hbs hp.1
      show tcVal ((p.1 + tcSum ps) % B64) = tcVal p.1 + computedSum ps
      rw [tcAdd_val p.1 (tcSum ps) (hb p (by simp)) (tcSum_lt ps)
        (by rw [ihv]; exact ⟨hp.2.1, hp.2.2⟩), ihv]

/-- The inductive step, over abstract variables.

⚠ Abstract on purpose; `omega` with `B64` in scope has produced terms the
kernel could not check elsewhere in this chain. -/
private theorem step_bound (a b c d : Int) (u v : Nat)
    (h1 : (a - b).natAbs ≤ u) (h2 : (c - d).natAbs ≤ v) :
    ((a + c) - (b + d)).natAbs ≤ u + v := by
  omega

private theorem succ_arith (n u : Nat) : (n + 1) * u = u + n * u := by
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **The computed terms sum to within `M·u` of the exact terms.**

Linear in the number of terms, because the accumulation contributes nothing —
this statement is about the terms alone. -/
theorem sum_error (u : Nat) : ∀ ps : List (Nat × Int),
    (∀ p ∈ ps, (tcVal p.1 - p.2).natAbs ≤ u) →
    (computedSum ps - exactSum ps).natAbs ≤ ps.length * u
  | [], _ => by
      show ((0 : Int) - 0).natAbs ≤ 0 * u
      simp
  | p :: ps, he => by
      have hps : ∀ q ∈ ps, (tcVal q.1 - q.2).natAbs ≤ u :=
        fun q hq => he q (by simp [hq])
      have ih := sum_error u ps hps
      have hp := he p (by simp)
      show (tcVal p.1 + computedSum ps - (p.2 + exactSum ps)).natAbs
        ≤ (ps.length + 1) * u
      rw [succ_arith]
      exact step_bound (tcVal p.1) p.2 (computedSum ps) (exactSum ps)
        u (ps.length * u) hp ih

/-- **The whole sample bound**: what the machine holds is within `M·u` of the
exact sum. -/
theorem tcSum_error (u : Nat) (ps : List (Nat × Int))
    (hb : ∀ p ∈ ps, p.1 < B64) (hp : PartialsInRange ps)
    (he : ∀ p ∈ ps, (tcVal p.1 - p.2).natAbs ≤ u) :
    (tcVal (tcSum ps) - exactSum ps).natAbs ≤ ps.length * u := by
  rw [tcSum_val ps hb hp]
  exact sum_error u ps he

/-! ## Checks -/

/-- The empty accumulator is zero. -/
example : tcSum [] = 0 := rfl

/-- ⚠ Wrapping is real, and it is why `PartialsInRange` exists: two positive
in-range terms accumulate to a **negative** register value. -/
example : tcVal (tcSum [(H - 1, 0), (1, 0)]) = -(H : Int) := by decide

/-- And that assignment does *not* satisfy `PartialsInRange`, so `tcSum_val`
never applies to it. -/
example : ¬ (tcVal (H - 1) + computedSum [((1 : Nat), (0 : Int))] < (H : Int)) := by
  decide

#print axioms tcSum_val
#print axioms sum_error
#print axioms tcSum_error

end LeanCompCert.Verified.TwosComplementFold
