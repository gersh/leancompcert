/-!
# Segmenting a fold into independently-checked blocks

The measured wall for kernel-checked folds is **memory, not time**: inside a
single `decide` the kernel retains every intermediate, so peak RSS grows
linearly with reduction steps and is released only when the command ends.
Nothing about packing the *state* helps, because the steps of a fold are
inherently sequential.

The lever that does help is to cut the fold into segments that are checked by
**separate** `decide`s, so the kernel frees between them, and to recombine the
segment results by a proved lemma whose own cost does not scale with the
segment contents. This is the same move that took a 16-way split of one
compilation unit from 88 GB to 12.8 GB.

This module supplies that lemma once, generically, for any `List.foldl` over a
contiguous range. Nothing here is specific to a certificate, an accumulator
type, or a step function.

## What a caller does

1. Pick segment boundaries. Each segment is a `Seg`: a start index, a length,
   the accumulator value entering it, and the accumulator value leaving it.
2. Discharge `Seg.Ok f sg` for each segment — one `decide +kernel` each, and
   they are independent, so they can live in different commands, different
   files, or different processes.
3. Apply `foldl_range'_of_chain`. The chain hypothesis is a `List.Chain'`-style
   contiguity check that is decidable and constant-cost in the segment
   *contents*; it only inspects the boundary values.

The recombination is free in the measured sense of §3 of the cost model: it
performs no fold evaluation at all.

## Main results

* `foldl_range'_split` — the two-way split, the primitive move.
* `Seg.Ok`, `Chain` — the segment record and its contiguity predicate.
* `foldl_range'_of_chain` — **the composition theorem**: a contiguous chain of
  verified segments computes the whole fold.
* `foldl_range_of_chain` — the same for `List.range n`, which is what a
  `Reflect.Program`'s loop actually ranges over.
-/

namespace LeanCompCert.Verified.Segment

/-! ## The primitive split -/

/-- `List.range' s (a + b)` is the concatenation of its two halves. -/
theorem range'_split (s a b : Nat) :
    List.range' s (a + b) = List.range' s a ++ List.range' (s + a) b :=
  List.range'_append_1.symm

/--
**The two-way split.** Folding over a contiguous range of length `a + b` is
folding over the first `a` indices and then, from that value, over the next
`b`. Each half can be checked on its own.
-/
theorem foldl_range'_split {α : Type _} (f : α → Nat → α) (init : α)
    (s a b : Nat) :
    (List.range' s (a + b)).foldl f init =
      (List.range' (s + a) b).foldl f ((List.range' s a).foldl f init) := by
  rw [range'_split, List.foldl_append]

/-- The same split for `List.range`, the index list of a `Reflect.Program`. -/
theorem foldl_range_split {α : Type _} (f : α → Nat → α) (init : α)
    (a b : Nat) :
    (List.range (a + b)).foldl f init =
      (List.range' a b).foldl f ((List.range a).foldl f init) := by
  rw [List.range_eq_range', foldl_range'_split, Nat.zero_add,
    ← List.range_eq_range']

/-! ## Chains of segments -/

/--
One segment of a fold: the indices `[start, start + len)`, the accumulator
value `entry` on the way in, and the value `exit` claimed on the way out.

`entry` and `exit` are data, not proofs — they are the numbers a caller pastes
between the independent chunk checks.
-/
structure Seg (α : Type _) where
  start : Nat
  len : Nat
  entry : α
  exit : α
  deriving Repr

/-- The segment's own obligation: folding it really does carry `entry` to
`exit`. This is the one `decide +kernel` per segment, and its cost is the
segment's length — which is exactly the quantity the caller chose. -/
def Seg.Ok {α : Type _} (f : α → Nat → α) (sg : Seg α) : Prop :=
  (List.range' sg.start sg.len).foldl f sg.entry = sg.exit

instance {α : Type _} [DecidableEq α] (f : α → Nat → α) (sg : Seg α) :
    Decidable (Seg.Ok f sg) := by
  unfold Seg.Ok; infer_instance

/-- The index just past a segment. -/
def Seg.stop {α : Type _} (sg : Seg α) : Nat := sg.start + sg.len

/--
A list of segments tiles `[start, start + total)` and carries `init` to
`final`, each segment's exit being the next one's entry.

`Bool`-valued on purpose: the recombination check must itself be cheap in the
kernel, and a `Bool` recursion over the boundary data reduces without ever
touching a `Decidable` instance whose unfolding could drag in the accumulator
type's structure.
-/
def Chain {α : Type _} [DecidableEq α] (start total : Nat) (init final : α) :
    List (Seg α) → Bool
  | [] => (total == 0) && decide (init = final)
  | sg :: rest =>
      (sg.start == start) && decide (sg.entry = init) && (sg.len ≤ total) &&
        Chain sg.stop (total - sg.len) sg.exit final rest

/--
**The composition theorem.**

Given a contiguous chain of segments, each individually verified, the fold over
the whole range `[start, start + total)` carries `init` to `final`.

No hypothesis mentions the segment contents beyond `Seg.Ok`, and the proof
performs no fold evaluation: recombination is independent of how much work the
segments did. Checking `n` elements in `k` segments therefore costs `k` peak
memory footprints of `n / k` elements each instead of one footprint of `n`.
-/
theorem foldl_range'_of_chain {α : Type _} [DecidableEq α] (f : α → Nat → α) :
    ∀ (segs : List (Seg α)) (start total : Nat) (init final : α),
      (∀ sg ∈ segs, Seg.Ok f sg) →
      Chain start total init final segs = true →
      (List.range' start total).foldl f init = final := by
  intro segs
  induction segs with
  | nil =>
      intro start total init final _ hChain
      simp only [Chain, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hChain
      obtain ⟨rfl, rfl⟩ := hChain
      rfl
  | cons sg rest ih =>
      intro start total init final hOk hChain
      simp only [Chain, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        at hChain
      obtain ⟨⟨⟨hStart, hEntry⟩, hLen⟩, hRest⟩ := hChain
      have hSeg : Seg.Ok f sg := hOk sg (by simp)
      have hRestOk : ∀ x ∈ rest, Seg.Ok f x := fun x hx => hOk x (by simp [hx])
      have hTotal : total = sg.len + (total - sg.len) := by omega
      subst hStart
      subst hEntry
      rw [hTotal, foldl_range'_split, hSeg]
      exact ih sg.stop (total - sg.len) sg.exit final hRestOk hRest

/-- The `List.range n` form: what a `Reflect.Program`'s loop folds over. -/
theorem foldl_range_of_chain {α : Type _} [DecidableEq α] (f : α → Nat → α)
    (segs : List (Seg α)) (total : Nat) (init final : α)
    (hOk : ∀ sg ∈ segs, Seg.Ok f sg)
    (hChain : Chain 0 total init final segs = true) :
    (List.range total).foldl f init = final := by
  rw [List.range_eq_range']
  exact foldl_range'_of_chain f segs 0 total init final hOk hChain

/-! ## Sanity checks -/

-- A two-way split, recombined from independently checked halves.
example :
    (List.range 20).foldl (fun acc i => acc + i * i) 0 = 2470 :=
  foldl_range_of_chain _
    [{ start := 0, len := 10, entry := 0, exit := 285 },
     { start := 10, len := 10, entry := 285, exit := 2470 }]
    20 0 2470 (by decide) (by decide)

-- The chain check really does force contiguity: a gap is rejected, so a wrong
-- recombination cannot be assembled.
example :
    Chain 0 20 (0 : Nat) 2470
      [{ start := 0, len := 10, entry := 0, exit := 285 },
       { start := 11, len := 10, entry := 285, exit := 2470 }] = false := by
  decide

-- …and so is a mismatched hand-off value.
example :
    Chain 0 20 (0 : Nat) 2470
      [{ start := 0, len := 10, entry := 0, exit := 285 },
       { start := 10, len := 10, entry := 286, exit := 2470 }] = false := by
  decide

end LeanCompCert.Verified.Segment
