import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Verified.Segment
import LeanCompCert.Verified.ListFold

/-!
# The RS62 anchor ladder as a segmentable, word-safe fold

`MathExtras.RS62Ladder.loopE` is the largest fold family in the
ternary-goldbach development — 140 of the 221 `native_decide` atoms that need
chunking. It is a fuel-driven recursion:

```lean
def loopE : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, SL, SU => (SL, SU)
  | f+1, n, SL, SU =>
      if isP n then loopE f (n+1) (SL + incL (n-1)) (SU + incU (n-1))
      else loopE f (n+1) SL SU
```

reproduced below with the primality test abstracted as a parameter `p`
(`Nat.minFac`, which `isP` uses, is not available to this package, and nothing
in the fold's algebra depends on which predicate the guard tests —
instantiating `p := isP` recovers the original definition literally).

Three results, all `∀`-quantified and independent of the fuel:

* `loopE_eq_foldl` — the recursion **is** a `List.foldl` over `List.range'`.
  This is the door: every generic lever in this package that acts on folds
  now acts on `loopE`.
* `loopE_of_chain` — **the segmentation theorem**. A contiguous chain of
  independently checked segments computes the whole run. Unlike the
  development's own `loopE_append`, which composes two runs at a time and
  nests, this consumes a flat list of `k` segments in one step, and its own
  cost does not depend on what the segments computed.
* `loopE_eq_word` — the run may be computed entirely with
  `incLWord`/`incUWord`, whose intermediates all fit in a machine word
  (`RS62Increments`). This is what makes the fold expressible in the proved
  `u64` fragment at all; in the source form the per-step numerator is a
  106-bit number.

## What this buys

Chunking is the whole cost of migrating this family: the measured law for
`loopE` in the Lean kernel is `rss ≈ 0.0314 · n^1.182 MB`, which caps one
`decide` at about 37 400 iterations under an 8 GB budget, against segments
that are currently 1–5 million iterations long. `loopE_of_chain` is the
recombination lemma that re-segmentation needs, proved once for every
segmentation of every atom.

The guard hoist (`ListFold.foldl_guard`) applies verbatim as well, and is
recorded here as `loopE_eq_filter_foldl`: the trial-division primality test
leaves the loop body entirely, at the price of a one-time certificate that a
supplied list really is the primes in the window.
-/

namespace LeanCompCert.Ports.RS62

open LeanCompCert.Verified

/-! ## The fold -/

/--
The RS62 anchor fold, with the primality guard abstracted.

At `p := MathExtras.RS62Ladder.isP` this is `MathExtras.RS62Ladder.loopE`
character for character.
-/
def loopE (p : Nat → Bool) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, SL, SU => (SL, SU)
  | f+1, n, SL, SU =>
      if p n then loopE p f (n+1) (SL + incL (n-1)) (SU + incU (n-1))
      else loopE p f (n+1) SL SU

/-- The unguarded ladder step on the pair state. -/
def stepRef (a : Nat × Nat) (k : Nat) : Nat × Nat :=
  (a.1 + incL (k - 1), a.2 + incU (k - 1))

/-- The same step with the word-safe increments. -/
def stepWord (a : Nat × Nat) (k : Nat) : Nat × Nat :=
  (a.1 + incLWord (k - 1), a.2 + incUWord (k - 1))

/-- The guarded step, which is what the fold actually iterates. -/
def stepGuarded (p : Nat → Bool) (a : Nat × Nat) (k : Nat) : Nat × Nat :=
  if p k then stepRef a k else a

/-! ## The fold form -/

/--
**The recursion is a fold.** `loopE` run with fuel `f` from `n` is the
`List.foldl` of its guarded step over the contiguous index window
`[n, n + f)`.

Everything else in this file — and every generic fold lever in the package —
goes through this equation.
-/
theorem loopE_eq_foldl (p : Nat → Bool) :
    ∀ (f n SL SU : Nat),
      loopE p f n SL SU =
        (List.range' n f).foldl (stepGuarded p) (SL, SU) := by
  intro f
  induction f with
  | zero => intro n SL SU; rfl
  | succ f ih =>
      intro n SL SU
      show (if p n then loopE p f (n + 1) (SL + incL (n - 1)) (SU + incU (n - 1))
            else loopE p f (n + 1) SL SU) = _
      rw [show List.range' n (f + 1) = n :: List.range' (n + 1) f from rfl,
        List.foldl_cons]
      by_cases hp : p n = true
      · rw [if_pos hp, ih (n + 1) _ _]
        show _ = (List.range' (n + 1) f).foldl (stepGuarded p)
          (stepGuarded p (SL, SU) n)
        rw [show stepGuarded p (SL, SU) n = (SL + incL (n - 1), SU + incU (n - 1))
          from by simp only [stepGuarded, hp, if_pos, stepRef]]
      · simp only [Bool.not_eq_true] at hp
        rw [if_neg (by simp [hp]), ih (n + 1) _ _]
        show _ = (List.range' (n + 1) f).foldl (stepGuarded p)
          (stepGuarded p (SL, SU) n)
        rw [show stepGuarded p (SL, SU) n = (SL, SU) from by
          simp only [stepGuarded, hp, Bool.false_eq_true, if_false]]

/-! ## Segmentation -/

/-- A segment obligation for the ladder is itself a `loopE` run: the shape a
certificate already has. -/
theorem seg_ok_iff (p : Nat → Bool) (sg : Segment.Seg (Nat × Nat)) :
    Segment.Seg.Ok (stepGuarded p) sg ↔
      loopE p sg.len sg.start sg.entry.1 sg.entry.2 = sg.exit := by
  unfold Segment.Seg.Ok
  rw [loopE_eq_foldl]

/--
**The segmentation theorem.**

A contiguous chain of independently verified segments computes the whole
ladder run. Each `hOk sg` is exactly the certificate
`loopE p sg.len sg.start sg.entry.1 sg.entry.2 = sg.exit`, so an existing
`native_decide` atom is already in the right shape — it just has to be split
finer.

Recombination performs no fold evaluation, so the kernel frees the memory of
each segment before the next one is checked. That is the whole point: the
measured wall for this family is memory inside one `decide`, not total time.
-/
theorem loopE_of_chain (p : Nat → Bool)
    (segs : List (Segment.Seg (Nat × Nat))) (n f : Nat)
    (init final : Nat × Nat)
    (hOk : ∀ sg ∈ segs,
      loopE p sg.len sg.start sg.entry.1 sg.entry.2 = sg.exit)
    (hChain : Segment.Chain n f init final segs = true) :
    loopE p f n init.1 init.2 = final := by
  rw [loopE_eq_foldl]
  have hOk' : ∀ sg ∈ segs, Segment.Seg.Ok (stepGuarded p) sg :=
    fun sg hsg => (seg_ok_iff p sg).mpr (hOk sg hsg)
  exact Segment.foldl_range'_of_chain (stepGuarded p) segs n f init final
    hOk' hChain

/-! ## Guard hoisting -/

/--
The trial-division primality test leaves the loop body: the ladder is a fold
over the primes in the window.

The remaining obligation — that a supplied list really is
`(List.range' n f).filter p` — is `ListFold.Certifies`, proved once and shared
by every segment with the same window.
-/
theorem loopE_eq_filter_foldl (p : Nat → Bool) (f n SL SU : Nat) :
    loopE p f n SL SU =
      ((List.range' n f).filter p).foldl stepRef (SL, SU) := by
  rw [loopE_eq_foldl]
  exact ListFold.foldl_guard p stepRef (SL, SU) (List.range' n f)

/-- With a certified index list, the ladder is an unguarded fold over that
list — the shape the register fragment executes. -/
theorem loopE_of_certifies (p : Nat → Bool) (f n SL SU : Nat)
    (primes : List Nat)
    (hcert : ListFold.Certifies p id (List.range' n f) primes) :
    loopE p f n SL SU = primes.foldl stepRef (SL, SU) := by
  rw [loopE_eq_foldl]
  exact ListFold.foldl_of_certifies_id hcert stepRef (SL, SU)

/-! ## The word-safe form -/

/-- The word-safe step agrees with the source step at every index the ladder
visits (`3 ≤ k`, i.e. `2 ≤ k − 1`). -/
theorem stepWord_eq_stepRef (a : Nat × Nat) (k : Nat) (hk : 3 ≤ k) :
    stepWord a k = stepRef a k := by
  unfold stepWord stepRef
  rw [incL_eq_wordSafe (k - 1) (by omega), incU_eq_wordSafe (k - 1) (by omega)]

/-- A fold agrees with a fold whose step differs only off the index list. -/
private theorem foldl_congr_of_mem {α : Type _} (Q : Nat → Prop)
    (f g : α → Nat → α) (hStep : ∀ acc k, Q k → f acc k = g acc k) :
    ∀ (l : List Nat), (∀ k ∈ l, Q k) → ∀ init : α,
      l.foldl f init = l.foldl g init := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons k rest ih =>
      intro hQ init
      rw [List.foldl_cons, List.foldl_cons,
        hStep init k (hQ k (by simp)),
        ih (fun x hx => hQ x (by simp [hx])) (g init k)]

/--
**The ladder is computable in 64-bit arithmetic.**

Over any window starting at `3` or above, the run may be computed with
`incLWord`/`incUWord`, whose every intermediate is below `2⁵¹`
(`RS62Increments.incLWord_intermediate_lt`). In the source form the per-step
numerator reaches 106 bits at ladder scale, so this is the equation that
brings the family inside the proved `u64` fragment.
-/
theorem loopE_eq_word (p : Nat → Bool) (f n SL SU : Nat) (hn : 3 ≤ n)
    (primes : List Nat)
    (hcert : ListFold.Certifies p id (List.range' n f) primes) :
    loopE p f n SL SU = primes.foldl stepWord (SL, SU) := by
  rw [loopE_of_certifies p f n SL SU primes hcert]
  refine (foldl_congr_of_mem (fun k => 3 ≤ k) stepWord stepRef
    (fun acc k hk => stepWord_eq_stepRef acc k hk) primes ?_ (SL, SU)).symm
  intro k hk
  have hmem : k ∈ (List.range' n f).filter p := by
    rw [hcert] at hk
    simpa using hk
  have := (List.mem_filter.mp hmem).1
  have hrange := List.mem_range'.mp this
  omega

/-! ## Sanity checks

`p` is instantiated by a toy guard; the algebra is what is being checked, and
it is independent of the guard.
-/

private def toyP (k : Nat) : Bool := decide (k % 2 = 1)

-- The fold form really is the recursion.
example : loopE toyP 8 101 0 0
    = (List.range' 101 8).foldl (stepGuarded toyP) (0, 0) :=
  loopE_eq_foldl toyP 8 101 0 0

-- Two independently checked halves recombine into the whole run, with the
-- recombination itself performing no fold evaluation.
example :
    loopE toyP 8 101 0 0 = loopE toyP 4 105 (loopE toyP 4 101 0 0).1
      (loopE toyP 4 101 0 0).2 :=
  loopE_of_chain toyP
    [{ start := 101, len := 4, entry := (0, 0)
     , exit := loopE toyP 4 101 0 0 },
     { start := 105, len := 4, entry := loopE toyP 4 101 0 0
     , exit := loopE toyP 4 105 (loopE toyP 4 101 0 0).1
                 (loopE toyP 4 101 0 0).2 }]
    101 8 (0, 0) _ (by intro sg hsg; simp at hsg; cases hsg <;> simp_all)
    (by decide)

end LeanCompCert.Ports.RS62
