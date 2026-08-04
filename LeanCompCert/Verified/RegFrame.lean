import LeanCompCert.Verified.InstrBlock

/-!
# Reading one register through a long straight-line block

`Verified/InstrBlock.lean` gives a block its total meaning `srun`, and
`srun_untouched` says a register the block never writes keeps its value.  That
is the right fact, but in the form it is stated it does not compose through a
real port body:

* its hypothesis is `∀ i ∈ l, sdest i ≠ r`, a `Prop` over a list, so a port
  has to produce a membership proof rather than run a decision procedure; and
* the register a port needs to read is almost never *untouched*.  It is
  written once, early, and read much later — the weighted-moment sweep of
  `Ports/RamareWM217.lean` sets its trial divisor `rD` in the decode block and
  divides by it five instructions later, and its candidate `rN` in the same
  decode block and divides by it a hundred instructions later.

Pushed through `simp`, that read costs one `RegState.set` layer per
intervening instruction, and each layer drags the arithmetic of an unrelated
instruction into the normal form.  For the sweep above that is what trips
`(kernel) deep recursion detected`: the intervening instructions are the ones
carrying `2⁴⁸`-scale literals, and `simp` normalising `(reg ⊕ literal) % M`
unary-unfolds the literal (`Nat.add`/`Nat.mul` recurse on their **second**
argument).  Growing the simp set makes this strictly worse.

This module is the framing layer that removes the need for any of it.

## What it provides

* `writes r l : Bool` — "does this block write register `r`", a decidable
  test that inspects only `sdest`, i.e. only register *indices*.  Every side
  condition below is discharged by `by decide`, and the decision never looks
  inside an operand, so a block full of `2⁴⁸`-scale literals costs the same as
  an empty one.
* `srun_frame` — a block that does not write `r` leaves `r` alone.
* `srun_frame_append` — the same fact used as a *suffix* eraser: the value of
  `r` after `xs ++ ys` is its value after `xs`, whenever `ys` does not write
  it.
* `srun_read_write` — **the composition lemma the ports were missing**: the
  value of `r` after a block equals `sval` of the *last instruction that
  writes it*, evaluated at the state its own prefix reaches.  Everything after
  that write is framed away by one decidable check, and everything before it
  stays packaged as `srun k s xs` — an opaque term, not a tower of `set`s.

The resulting discipline, which `Verified/BlockDefined.lean` builds on: state
threading is *always* `srun k s prefix`, never nested `RegState.set`; a
register read is *always* `srun_read_write` followed by a value lemma about
one `denoteOp`.  No unrelated instruction's arithmetic ever enters the goal.
-/

namespace LeanCompCert.Verified.RegFrame

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## The decidable write test -/

/-- **Does this block write register `r`?**  Decidable, and it inspects only
destination indices — never an operand, so the cost is the block's length and
not the size of the constants in it. -/
def writes (r : Nat) (l : List Instr) : Bool :=
  l.any (fun i => decide (sdest i = r))

@[simp] theorem writes_nil (r : Nat) : writes r [] = false := rfl

@[simp] theorem writes_cons (r : Nat) (i : Instr) (l : List Instr) :
    writes r (i :: l) = (decide (sdest i = r) || writes r l) := rfl

theorem writes_append (r : Nat) (xs ys : List Instr) :
    writes r (xs ++ ys) = (writes r xs || writes r ys) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      show (decide (sdest i = r) || writes r (xs ++ ys)) = _
      rw [ih]
      show _ = ((decide (sdest i = r) || writes r xs) || writes r ys)
      rw [Bool.or_assoc]

theorem writes_append_left {r : Nat} {xs ys : List Instr}
    (h : writes r (xs ++ ys) = false) : writes r xs = false := by
  rw [writes_append, Bool.or_eq_false_iff] at h
  exact h.1

theorem writes_append_right {r : Nat} {xs ys : List Instr}
    (h : writes r (xs ++ ys) = false) : writes r ys = false := by
  rw [writes_append, Bool.or_eq_false_iff] at h
  exact h.2

/-- The Boolean test, unpacked into the membership form `srun_untouched`
wants. -/
theorem sdest_ne_of_not_writes {r : Nat} {l : List Instr}
    (h : writes r l = false) : ∀ i ∈ l, sdest i ≠ r := by
  induction l with
  | nil => intro i hi; cases hi
  | cons a l ih =>
      rw [writes_cons, Bool.or_eq_false_iff] at h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact of_decide_eq_false h.1
      · exact ih h.2 i hi

/-! ## Framing -/

/--
**A block that does not write `r` leaves `r` alone.**

`srun_untouched` with a decidable hypothesis: the side condition is
`by decide` on register indices.
-/
theorem srun_frame (k r : Nat) (l : List Instr) (h : writes r l = false)
    (s : RegState) : srun k s l r = s r :=
  srun_untouched k r l (sdest_ne_of_not_writes h) s

/--
**Erasing a suffix.**  The value of `r` after `xs ++ ys` is its value after
`xs` alone, provided `ys` does not write `r`.  This is the form a port uses to
walk backwards from a read to the write that produced it.
-/
theorem srun_frame_append (k r : Nat) (xs ys : List Instr)
    (h : writes r ys = false) (s : RegState) :
    srun k s (xs ++ ys) r = srun k s xs r := by
  rw [srun_append]
  exact srun_frame k r ys h _

/--
**Read after write — the composition lemma.**

If the block factors as `xs ++ i :: ys` with `i` writing `r` and `ys` not
writing it, then reading `r` at the end of the block is exactly `sval` of `i`
at the state `xs` reaches.  Both side conditions are decidable and mention
only register indices.

The point is what does *not* appear: the instructions of `ys` are erased by a
`decide`, and those of `xs` stay inside the opaque term `srun k s xs`.  A
`2⁴⁸`-scale literal in either one is never normalised, so it cannot unfold.
-/
theorem srun_read_write (k r : Nat) (xs : List Instr) (i : Instr)
    (ys : List Instr) (hi : sdest i = r) (hys : writes r ys = false)
    (s : RegState) :
    srun k s (xs ++ i :: ys) r = sval k (srun k s xs) i := by
  rw [srun_append, srun_cons, srun_frame k r ys hys]
  show (if r = sdest i then sval k (srun k s xs) i else srun k s xs r) = _
  rw [if_pos hi.symm]

/--
The common special case of `srun_read_write`: the last instruction of the
block is the write.
-/
theorem srun_read_last (k r : Nat) (xs : List Instr) (i : Instr)
    (hi : sdest i = r) (s : RegState) :
    srun k s (xs ++ [i]) r = sval k (srun k s xs) i :=
  srun_read_write k r xs i [] hi rfl s

/--
The other special case: the write is the block's first instruction, so the
prefix is empty and the state is the entry state itself.
-/
theorem srun_read_head (k r : Nat) (i : Instr) (ys : List Instr)
    (hi : sdest i = r) (hys : writes r ys = false) (s : RegState) :
    srun k s (i :: ys) r = sval k s i :=
  srun_read_write k r [] i ys hi hys s

/-! ## Bounds carried through a block

`srun_lt_of_lt` already says every register stays a word.  These two are the
convenient packagings: a block preserves "every register is a word", and a
register read out of a block is a word.
-/

theorem srun_regs_lt (k : Nat) (l : List Instr) (s : RegState)
    (hs : ∀ j, s j < M) (j : Nat) : srun k s l j < M :=
  srun_lt_of_lt k l s hs j

end LeanCompCert.Verified.RegFrame
