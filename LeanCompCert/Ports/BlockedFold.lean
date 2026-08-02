import LeanCompCert.Verified.Segment

/-!
# Re-blocking a flat loop into candidate × round

A `Reflect.Program` has one loop, of a statically fixed length.  A source
development that scans `F` candidates, spending `B` rounds on each, therefore
has to be flattened into a single loop of `F · B` iterations, with the
candidate and the round *decoded from the index*.  That is what
`Ports/RS62LadderProgram.lean` does, and its docstring names the missing step
plainly:

> What is missing is the re-blocking between the two index spaces (`f · B`
> flat rounds against `f` candidates) …

This module supplies it, once, for every fold and every step function.

## The statement

`foldl_range_mul` says that folding a step `g` over `List.range (F * B)` is
folding, over `List.range F`, the *block* step that runs `g` at
`q·B, q·B+1, …, q·B+B−1`.  Nothing about `g` is assumed: it is a pure
re-association of the same `F · B` applications in the same order, so the
equation holds for every step function and every accumulator type.

`block_eq_shift` re-indexes one block by its *round number* `r ∈ [0, B)`,
which is the form in which a per-candidate argument is usually written.

## Why this is the load-bearing lemma

The flat program's denotation is a fold over `List.range (F * B)`
(`Verified/FoldBridge.lean`).  The source recursion is a fold over the
candidates (`Ports/RS62LoopE.lean`'s `loopE_eq_foldl`).  Neither side can be
moved to the other without this equation, and once it is available the
remaining work is entirely about **one block** — a statement whose size does
not grow with `F`.

Nothing here evaluates a fold, so the cost of using it is independent of `F`
and `B`, and the proofs below contain no `decide`.
-/

namespace LeanCompCert.Ports.BlockedFold

open LeanCompCert.Verified

/-- One block of `B` rounds, at candidate `q`: the flat indices
`q·B, q·B+1, …, q·B+B−1`, folded in order. -/
def block {α : Type _} (B : Nat) (g : α → Nat → α) (a : α) (q : Nat) : α :=
  (List.range' (q * B) B).foldl g a

/-- `List.range' s (n + 1)` peels its **last** element, matching
`List.range_succ`. -/
theorem range'_succ_right (s n : Nat) :
    List.range' s (n + 1) = List.range' s n ++ [s + n] :=
  List.range'_1_concat

/--
Folding over a contiguous window is folding over `[0, n)` with the start
added back at each index.  Proved by peeling the **last** element of both
lists, which is why `range'_succ_right` is stated in that direction.
-/
theorem foldl_range'_shift {α : Type _} (g : α → Nat → α) :
    ∀ (n s : Nat) (a : α),
      (List.range' s n).foldl g a =
        (List.range n).foldl (fun x r => g x (s + r)) a := by
  intro n
  induction n with
  | zero => intro s a; rfl
  | succ n ih =>
      intro s a
      rw [range'_succ_right, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih s a]

/--
**Re-indexing one block by its round number.**

The block at candidate `q` is the fold of `g` at `q·B + r` over the rounds
`r ∈ [0, B)`.  This is the shape in which a per-candidate invariant is stated:
`r` is what the program's `urem` decodes.
-/
theorem block_eq_shift {α : Type _} (B : Nat) (g : α → Nat → α) (a : α)
    (q : Nat) :
    block B g a q = (List.range B).foldl (fun x r => g x (q * B + r)) a :=
  foldl_range'_shift g B (q * B) a

/--
**The re-blocking equation.**

Folding `g` over the flat index space `[0, F·B)` is folding the block step
over the candidate space `[0, F)`.  A re-association of the same applications
in the same order; no hypothesis on `g`, `F` or `B`, and no fold evaluated.
-/
theorem foldl_range_mul {α : Type _} (F B : Nat) (g : α → Nat → α) (init : α) :
    (List.range (F * B)).foldl g init =
      (List.range F).foldl (block B g) init := by
  induction F generalizing init with
  | zero => simp
  | succ F ih =>
      rw [Nat.succ_mul, Segment.foldl_range_split g init (F * B) B,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih init]
      rfl

end LeanCompCert.Ports.BlockedFold
