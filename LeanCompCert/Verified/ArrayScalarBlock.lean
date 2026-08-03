import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Scalar blocks inside the array machine

`Verified/ArrayFoldBridge.lean` gives the array machine its own total
straight-line meaning (`astep`, `arun`, `ADefined`, `AllDefined`).
`Verified/InstrBlock.lean` gives the *scalar* machine the same thing
(`sval`, `srun`, `SDefined`, `SAllDefined`), and every scalar port in the
package — `Ports/MertensCDEM.lean`, `Ports/SingSeriesC17.lean`,
`Ports/RS62MertensFirst.lean` — is proved against it, together with the
accumulated library of gating lemmas (`one_sub_bit`, `bit_mul_val`,
`ite_ite_and`, …) that make those `simp only` calls close.

A real array port is almost never *mostly* array instructions.  It is a long
scalar computation with a handful of `load`/`store` punctuating it: the
Möbius sieve's sixty-instruction body has five array instructions, and the
weighted-moment sweep of `Ports/RamareWM217.lean` has **one** in a body of
137.  Without this module each of those ports re-derives the scalar theory
inside `AState`, which is where `Ports/ArrayMobiusDenotation.lean` stalled:

> the one-shot `simp only` that works for `ArraySieveCount`'s 23-instruction
> body produces, for this one, a term in which the post-store array is
> inlined at eight separate read sites, so the printed goal is ~57 kB and the
> normal forms of the two sides no longer line up syntactically.

The array is inlined at every read site because the *scalar* instructions are
being pushed through `astep`, which carries the array along. They do not need
to be. This module says so once:

```text
arun k s (lift xs) = ⟨srun k s.regs xs, s.arr⟩
```

A block of scalar instructions moves the register file exactly as the scalar
machine does and **does not touch the array at all**. So a port cuts its body
at the array instructions, lifts each scalar stage with `arun_lift`, and
proves it with the ordinary scalar library against a variable `RegState` —
paying, as `AllDefined_append` intends, for one stage at a time and never
carrying the array through a scalar `simp`.

`allDefined_lift_of_noDiv` is the other half: a division-free scalar block is
defined in the array machine unconditionally, so the definedness obligation
survives only at the genuinely partial instructions (`udiv`/`urem` and the
array accesses themselves).
-/

namespace LeanCompCert.Verified.ArrayScalarBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- A scalar block, as array instructions. -/
def lift (xs : List Instr) : List AInstr := xs.map AInstr.scalar

@[simp] theorem lift_nil : lift [] = [] := rfl

@[simp] theorem lift_cons (i : Instr) (xs : List Instr) :
    lift (i :: xs) = .scalar i :: lift xs := rfl

theorem lift_append (xs ys : List Instr) :
    lift (xs ++ ys) = lift xs ++ lift ys :=
  List.map_append ..

theorem mem_lift {a : AInstr} {xs : List Instr} (h : a ∈ lift xs) :
    ∃ i ∈ xs, a = .scalar i := by
  obtain ⟨i, hi, hEq⟩ := List.mem_map.mp h
  exact ⟨i, hi, hEq.symm⟩

/-! ## The array is untouched, and the registers move scalar-wise -/

/--
**A scalar block does not touch the array.**

The register file moves exactly as `InstrBlock.srun` says, and `arr` is
returned unchanged — so a port may reason about a scalar stage entirely in
the scalar machine, with the existing library, and re-attach the array
afterwards.
-/
theorem arun_lift (k : Nat) : ∀ (xs : List Instr) (s : AState),
    arun k s (lift xs) = ⟨InstrBlock.srun k s.regs xs, s.arr⟩ := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons i rest ih =>
      intro s
      show arun k (astep k s (.scalar i)) (lift rest) = _
      rw [ih]
      rfl

theorem arun_lift_regs (k : Nat) (xs : List Instr) (s : AState) :
    (arun k s (lift xs)).regs = InstrBlock.srun k s.regs xs := by
  rw [arun_lift]

theorem arun_lift_arr (k : Nat) (xs : List Instr) (s : AState) :
    (arun k s (lift xs)).arr = s.arr := by
  rw [arun_lift]

/-! ## Definedness -/

/-- Definedness of a lifted block is scalar definedness of the block. -/
theorem allDefined_lift (len k : Nat) : ∀ (xs : List Instr) (s : AState),
    AllDefined len k s (lift xs) ↔ InstrBlock.SAllDefined k s.regs xs := by
  intro xs
  induction xs with
  | nil => intro s; exact Iff.rfl
  | cons i rest ih =>
      intro s
      have harr : (astep k s (.scalar i)).regs =
          RegState.set s.regs (InstrBlock.sdest i)
            (InstrBlock.sval k s.regs i) := rfl
      have hdef : ADefined len k s (.scalar i) ↔ InstrBlock.SDefined k s.regs i := by
        cases i with
        | mov d src => exact Iff.rfl
        | binop d op l r => exact Iff.rfl
      show ADefined len k s (.scalar i) ∧
        AllDefined len k (astep k s (.scalar i)) (lift rest) ↔ _
      rw [hdef, ih (astep k s (.scalar i)), harr]
      exact Iff.rfl

/--
**A division-free scalar block is defined in the array machine, always.**

This is the lemma that removes definedness as a per-port obligation for the
overwhelming majority of a body's instructions: only `udiv`/`urem` and the
array accesses can fail, so only those need a side condition.
-/
theorem allDefined_lift_of_noDiv (len k : Nat) :
    ∀ (xs : List Instr) (s : AState), xs.all InstrBlock.NoDivI = true →
      AllDefined len k s (lift xs) := by
  intro xs
  induction xs with
  | nil => intro s _; trivial
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, ih _ h.2⟩
      cases i with
      | mov d src => exact trivial
      | binop d op l r =>
          have hops : op ≠ Op.udiv ∧ op ≠ Op.urem := by
            simp only [InstrBlock.NoDivI, Bool.and_eq_true, bne_iff_ne,
              ne_eq] at h
            exact h.1
          show (denoteOp op (denoteOperand k s.regs l)
            (denoteOperand k s.regs r)).isSome = true
          cases op <;> first
            | rfl
            | (exact absurd rfl hops.1)
            | (exact absurd rfl hops.2)

end LeanCompCert.Verified.ArrayScalarBlock
