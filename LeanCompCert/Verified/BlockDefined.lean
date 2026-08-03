import LeanCompCert.Verified.RegFrame

/-!
# Definedness of a block without putting its constants into the normal form

A straight-line block is defined when each of its `udiv`/`urem` has a nonzero
divisor *at the state that instruction executes in* (`InstrBlock.SAllDefined`).
For a real port body that is a handful of side conditions inside a hundred and
some instructions, and the obvious way to get at them — unfold `SAllDefined`,
`srun`, `sval`, `denoteOp`, `denoteOperand` in one `simp` — does not scale.
It fails in two distinct ways, both measured on `Ports/RamareWM217.lean`:

1. **The state grows a layer per instruction.**  Reading the divisor register
   means peeling one `RegState.set` for every intervening instruction, and
   each peel drags that instruction's arithmetic into the goal even though
   nothing depends on it.
2. **The dragged-in arithmetic contains the program's constants.**  A
   fixed-point ladder carries `2⁴⁸`-scale literals, and `simp` normalising
   `(reg ⊕ literal) % M` unary-unfolds them, because the kernel's `Nat.add`
   and `Nat.mul` recurse on their **second** argument.  Unfolding one such
   block inside `simp` reports `(kernel) deep recursion detected` outright.

Reordering the program's operands would dodge (2), but only by changing the
program — which invalidates any measured run of the emitted C.  The fix has to
be proof-side, and it is a discipline rather than a tactic:

> **Never normalise an instruction you did not ask about.**
>
> * Thread state as `srun k s prefix`, an opaque term — never as a tower of
>   `RegState.set`.  `sAllDefined_stage` is the only way this module lets you
>   advance, and it hands you exactly that form.
> * Retire whole division-free stages with `sAllDefined_of_noDiv`, whose
>   hypothesis is a `Bool` computed from *opcodes only*.
> * Read a divisor with `RegFrame.srun_read_write`, whose side conditions are
>   `Bool`s computed from *register indices only*.
> * Turn the one `denoteOp` you actually care about into a value with the
>   lemmas below, each stated for **variable** operands under a numeric
>   hypothesis.  A literal enters the proof only as the subject of a `<`
>   comparison, where it is one GMP call and no unfolding.
>
> Under this discipline the size of a port's constants is irrelevant to the
> cost of its definedness proof, and no `simp` set ever has to grow.

## What the trigger actually is, and what does not fix it

Three things were measured while this module was being written, and two of
them contradict the folklore:

* **It is not only `simp`.**  A plain `show`/`rfl` detonates the same way: in
  `Ports/RamareWM217.lean` a `show 2 ≤ srun k s.regs (wmPre c) rN` — one
  structure projection away from the goal — reported `maximum recursion depth`
  because `isDefEq` walked into the 137-instruction run.  Any tactic that
  forces `whnf` into a `% M`-saturated term is enough; `simp` is merely the
  most common one.  The fix is the same either way: keep the state a
  *variable* (see `wmBody_post_defined` there) so there is nothing to walk
  into.
* **Do not raise `maxRecDepth` to cope.**  It converts a clean error into a
  slower one, and at large settings a failing check has been observed to abort
  the process outright rather than report.
* **Operand order is not the whole story.**  The "big numeral in second
  position unary-unfolds" rule is real, but it is not the only mechanism and
  reordering is not available to a port whose emitted C has already been
  compiled and run — changing the program changes the artifact.  This module
  exists so that the fix never has to touch the program.

A complementary technique, used on other ports in this package where the
*arithmetic itself* is the subject (encoding proofs, not definedness proofs):
parameterise each block by its constants as ordinary variables and bridge back
to the concrete block by `rfl`.  The numeral then never enters the goal at
all, and the program — hence the emitted C and its hash — is unchanged.  The
two approaches compose: use the parameterised form when the value matters, and
this module when only definedness does.

Everything here is generic: it mentions no port, no configuration, and no
constant.
-/

namespace LeanCompCert.Verified.BlockDefined

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame

/-! ## Operands and instruction values, without unfolding

These are all `rfl`, and that is the point: a port rewrites with them by name
instead of putting `denoteOperand`/`sval` into a simp set, so unfolding stops
exactly where it was asked to.
-/

@[simp] theorem denoteOperand_reg (k : Nat) (s : RegState) (j : Nat) :
    denoteOperand k s (.reg j) = s j := rfl

theorem denoteOperand_lit (k : Nat) (s : RegState) (v : Nat) :
    denoteOperand k s (.lit v) = v % M := rfl

theorem denoteOperand_idx (k : Nat) (s : RegState) :
    denoteOperand k s .idx = k % M := rfl

/-- A literal below the word size denotes itself.  The hypothesis is the *only*
place the literal appears, and it is discharged by one comparison. -/
theorem denoteOperand_lit_of_lt (k : Nat) (s : RegState) {v : Nat} (h : v < M) :
    denoteOperand k s (.lit v) = v :=
  Nat.mod_eq_of_lt h

theorem denoteOperand_idx_of_lt (k : Nat) (s : RegState) (h : k < M) :
    denoteOperand k s .idx = k :=
  Nat.mod_eq_of_lt h

theorem sval_mov (k : Nat) (s : RegState) (d : Nat) (src : Operand) :
    sval k s (.mov d src) = denoteOperand k s src := rfl

theorem sval_binop (k : Nat) (s : RegState) (d : Nat) (op : Op) (l r : Operand) :
    sval k s (.binop d op l r) =
      (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).getD 0 := rfl

/-- The shape a port uses: having computed the one `denoteOp` it cares about,
read the instruction's value off it. -/
theorem sval_binop_of_eq {k : Nat} {s : RegState} {d : Nat} {op : Op}
    {l r : Operand} {v : Nat}
    (h : denoteOp op (denoteOperand k s l) (denoteOperand k s r) = some v) :
    sval k s (.binop d op l r) = v := by
  rw [sval_binop, h]
  rfl

/--
**Evaluating one instruction, in three independent steps.**

The two operands are resolved separately — typically by `RegFrame.srun_frame`
on the left and `denoteOperand_lit_of_lt` on the right — and only then is the
operation applied, through one of the `denoteOp_*_of_*` lemmas below.  Because
each argument is named (`a`, `b`) before the operation is touched, the
program's constants appear only inside `hr` and inside the numeric side
condition of the operation lemma.  They are never rewritten *under* a `% M`,
which is the rewrite that unary-unfolds them.
-/
theorem sval_binop_val {k : Nat} {s : RegState} {d : Nat} {op : Op}
    {l r : Operand} {a b v : Nat}
    (hl : denoteOperand k s l = a) (hr : denoteOperand k s r = b)
    (h : denoteOp op a b = some v) :
    sval k s (.binop d op l r) = v := by
  rw [sval_binop, hl, hr, h]
  rfl

/-- The same, for a `mov`. -/
theorem sval_mov_val {k : Nat} {s : RegState} {d : Nat} {src : Operand} {a : Nat}
    (h : denoteOperand k s src = a) : sval k s (.mov d src) = a := h

@[simp] theorem sdest_mov (d : Nat) (src : Operand) : sdest (.mov d src) = d := rfl

@[simp] theorem sdest_binop (d : Nat) (op : Op) (l r : Operand) :
    sdest (.binop d op l r) = d := rfl

/-! ## `denoteOp` as a value, for variable operands

Each lemma below removes the machine's `% M` under a bound the port already
has.  None of them mentions a constant, so instantiating one at a
`2⁴⁸`-scale literal costs a single comparison.
-/

theorem denoteOp_add_of_lt {a b : Nat} (h : a + b < M) :
    denoteOp .add a b = some (a + b) := by
  show some ((a + b) % M) = _
  rw [Nat.mod_eq_of_lt h]

theorem denoteOp_mul_of_lt {a b : Nat} (h : a * b < M) :
    denoteOp .mul a b = some (a * b) := by
  show some ((a * b) % M) = _
  rw [Nat.mod_eq_of_lt h]

/-- Machine subtraction is `a + (M − b)` reduced mod `M`; below the word size
and above the subtrahend it is ordinary `Nat` subtraction.  Stating it here
once is what keeps `M − literal` out of every port's goals. -/
theorem denoteOp_sub_of_le {a b : Nat} (hb : b ≤ a) (ha : a < M) :
    denoteOp .sub a b = some (a - b) := by
  show some ((a + (M - b)) % M) = _
  have hbM : b ≤ M := Nat.le_trans hb (Nat.le_of_lt ha)
  have hsplit : a + (M - b) = M + (a - b) := by omega
  rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem denoteOp_udiv_of_ne {a b : Nat} (hb : b ≠ 0) (ha : a < M) :
    denoteOp .udiv a b = some (a / b) := by
  show (if b = 0 then none else some ((a / b) % M)) = _
  rw [if_neg hb, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem denoteOp_urem_of_ne {a b : Nat} (hb : b ≠ 0) (ha : a < M) :
    denoteOp .urem a b = some (a % b) := by
  show (if b = 0 then none else some ((a % b) % M)) = _
  rw [if_neg hb, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha)]

theorem denoteOp_lshr_of_lt {a n : Nat} (ha : a < M) :
    denoteOp .lshr a n = some (a >>> n) := by
  show some ((a >>> n) % M) = _
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a _) ha)]

theorem denoteOp_eq_val (a b : Nat) :
    denoteOp .eq a b = some (if a = b then 1 else 0) := rfl

theorem denoteOp_ne_val (a b : Nat) :
    denoteOp .ne a b = some (if a ≠ b then 1 else 0) := rfl

theorem denoteOp_lt_val (a b : Nat) :
    denoteOp .lt a b = some (if a < b then 1 else 0) := rfl

theorem denoteOp_le_val (a b : Nat) :
    denoteOp .le a b = some (if a ≤ b then 1 else 0) := rfl

theorem denoteOp_gt_val (a b : Nat) :
    denoteOp .gt a b = some (if a > b then 1 else 0) := rfl

theorem denoteOp_ge_val (a b : Nat) :
    denoteOp .ge a b = some (if a ≥ b then 1 else 0) := rfl

/-! ## Branchless flags, at instruction level

Every port in this package materialises a condition as a `0`/`1` register.
`Verified/ArrayFoldBridge.lean` has the algebra of those flags once they are
already `if … then 1 else 0`; what is missing, and what a framing proof needs,
is the fact one step earlier: a *comparison instruction writes a flag*, and a
*product of flags is a flag*, whatever the operands are.  With those two, a
gate register can be case-split without evaluating anything that feeds it.
-/

/-- A register holds a machine flag. -/
def IsBit (v : Nat) : Prop := v = 0 ∨ v = 1

theorem isBit_zero : IsBit 0 := Or.inl rfl

theorem isBit_one : IsBit 1 := Or.inr rfl

theorem isBit_ite (p : Prop) [Decidable p] : IsBit (if p then 1 else 0) := by
  by_cases h : p
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

theorem sval_eq_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .eq l r)) := by
  show IsBit ((denoteOp .eq (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_eq_val]
  exact isBit_ite _

theorem sval_ne_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .ne l r)) := by
  show IsBit ((denoteOp .ne (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_ne_val]
  exact isBit_ite _

theorem sval_lt_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .lt l r)) := by
  show IsBit ((denoteOp .lt (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_lt_val]
  exact isBit_ite _

theorem sval_le_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .le l r)) := by
  show IsBit ((denoteOp .le (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_le_val]
  exact isBit_ite _

theorem sval_gt_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .gt l r)) := by
  show IsBit ((denoteOp .gt (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_gt_val]
  exact isBit_ite _

theorem sval_ge_isBit (k : Nat) (s : RegState) (d : Nat) (l r : Operand) :
    IsBit (sval k s (.binop d .ge l r)) := by
  show IsBit ((denoteOp .ge (denoteOperand k s l) (denoteOperand k s r)).getD 0)
  rw [denoteOp_ge_val]
  exact isBit_ite _

/-- **A product of flags is a flag** — how a port combines conditions.  Neither
operand is evaluated: the two `IsBit` facts are all that is used. -/
theorem sval_mul_isBit {k : Nat} {s : RegState} {d : Nat} {l r : Operand}
    (hl : IsBit (denoteOperand k s l)) (hr : IsBit (denoteOperand k s r)) :
    IsBit (sval k s (.binop d .mul l r)) := by
  rw [sval_binop]
  rcases hl with h | h <;> rcases hr with h' | h' <;> rw [h, h']
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Definedness of one instruction -/

theorem sDefined_mov (k : Nat) (s : RegState) (d : Nat) (src : Operand) :
    SDefined k s (.mov d src) := trivial

/-- A division-free instruction is defined in every state. -/
theorem sDefined_of_noDiv {k : Nat} {s : RegState} {i : Instr}
    (h : NoDivI i = true) : SDefined k s i := by
  cases i with
  | mov d src => exact trivial
  | binop d op l r =>
      have hops : op ≠ Op.udiv ∧ op ≠ Op.urem := by
        simp only [NoDivI, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        exact h
      show (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).isSome = true
      cases op <;> first
        | rfl
        | (exact absurd rfl hops.1)
        | (exact absurd rfl hops.2)

/-- **A division is defined exactly when its divisor operand is nonzero.**
The divisor is read with `RegFrame.srun_read_write`; nothing else about the
state is needed. -/
theorem sDefined_udiv {k : Nat} {s : RegState} {d : Nat} {l r : Operand}
    (h : denoteOperand k s r ≠ 0) : SDefined k s (.binop d .udiv l r) := by
  show (denoteOp .udiv (denoteOperand k s l) (denoteOperand k s r)).isSome = true
  show ((if denoteOperand k s r = 0 then none
    else some ((denoteOperand k s l / denoteOperand k s r) % M)).isSome) = true
  rw [if_neg h]
  rfl

theorem sDefined_urem {k : Nat} {s : RegState} {d : Nat} {l r : Operand}
    (h : denoteOperand k s r ≠ 0) : SDefined k s (.binop d .urem l r) := by
  show (denoteOp .urem (denoteOperand k s l) (denoteOperand k s r)).isSome = true
  show ((if denoteOperand k s r = 0 then none
    else some ((denoteOperand k s l % denoteOperand k s r) % M)).isSome) = true
  rw [if_neg h]
  rfl

/-! ## Definedness of a block, one stage at a time -/

@[simp] theorem sAllDefined_nil (k : Nat) (s : RegState) :
    SAllDefined k s ([] : List Instr) := trivial

/-- The recursion step, with the continuation state written as `srun` of the
prefix rather than as a `RegState.set`.  This is the shape every lemma in this
module produces and consumes. -/
theorem sAllDefined_cons {k : Nat} {s : RegState} {i : Instr} {rest : List Instr}
    (hi : SDefined k s i) (hrest : SAllDefined k (srun k s [i]) rest) :
    SAllDefined k s (i :: rest) := ⟨hi, hrest⟩

theorem srun_snoc (k : Nat) (s : RegState) (xs : List Instr) (i : Instr) :
    srun k s (xs ++ [i]) =
      RegState.set (srun k s xs) (sdest i) (sval k (srun k s xs) i) := by
  rw [srun_append]
  rfl

/--
**A division-free block is defined in every state.**

The scalar counterpart of `ArrayScalarBlock.allDefined_lift_of_noDiv`.  Its
hypothesis is a `Bool` computed from opcodes alone, so `by decide` discharges
it for a block of any length carrying constants of any size.
-/
theorem sAllDefined_of_noDiv (k : Nat) :
    ∀ (l : List Instr) (s : RegState), l.all NoDivI = true → SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro s _; trivial
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      exact ⟨sDefined_of_noDiv h.1, ih _ h.2⟩

/--
**Splitting a block at one instruction.**

`SAllDefined_append` in the state form this module keeps: the tail's obligation
is read at `srun k s (xs ++ [i])`, so a port can keep applying this lemma and
never sees a `RegState.set`.
-/
theorem sAllDefined_split {k : Nat} {s : RegState} {xs : List Instr} {i : Instr}
    {ys : List Instr} (hxs : SAllDefined k s xs)
    (hi : SDefined k (srun k s xs) i)
    (hys : SAllDefined k (srun k s (xs ++ [i])) ys) :
    SAllDefined k s (xs ++ i :: ys) := by
  rw [SAllDefined_append]
  refine ⟨hxs, hi, ?_⟩
  rw [srun_snoc] at hys
  exact hys

/--
**The stage combinator — the workhorse.**

A body is `division-free prefix`, then one partial instruction, then the rest.
`hxs` is `by decide`; `hi` is one divisor-nonzero fact, read with
`RegFrame.srun_read_write`; `hys` is the same lemma again on the remainder.
A hundred-instruction body with three divisions costs three applications and
three arithmetic facts — and no instruction outside those three is ever
unfolded.
-/
theorem sAllDefined_stage {k : Nat} {s : RegState} {xs : List Instr} {i : Instr}
    {ys : List Instr} (hxs : xs.all NoDivI = true)
    (hi : SDefined k (srun k s xs) i)
    (hys : SAllDefined k (srun k s (xs ++ [i])) ys) :
    SAllDefined k s (xs ++ i :: ys) :=
  sAllDefined_split (sAllDefined_of_noDiv k xs s hxs) hi hys

/-- Appending a division-free tail to a defined block. -/
theorem sAllDefined_append_noDiv {k : Nat} {s : RegState} {xs ys : List Instr}
    (hxs : SAllDefined k s xs) (hys : ys.all NoDivI = true) :
    SAllDefined k s (xs ++ ys) :=
  (SAllDefined_append k xs ys s).mpr ⟨hxs, sAllDefined_of_noDiv k ys _ hys⟩

/-- Concatenating two defined blocks, with the second read at the state the
first reaches. -/
theorem sAllDefined_append {k : Nat} {s : RegState} {xs ys : List Instr}
    (hxs : SAllDefined k s xs) (hys : SAllDefined k (srun k s xs) ys) :
    SAllDefined k s (xs ++ ys) :=
  (SAllDefined_append k xs ys s).mpr ⟨hxs, hys⟩

end LeanCompCert.Verified.BlockDefined
