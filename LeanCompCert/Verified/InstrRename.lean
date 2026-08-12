import LeanCompCert.Verified.InstrBlock

/-!
# Injective register relocation for straight-line blocks

Production programs allocate scratch registers globally, while the small
verified scalar ports normally number their registers from zero.  This file
proves once that an injective relocation of every register in a block
preserves its exact `srun` semantics.
-/

namespace LeanCompCert.Verified.InstrRename

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

def renameOperand (f : Nat → Nat) : Operand → Operand
  | .reg r => .reg (f r)
  | .lit v => .lit v
  | .idx => .idx

def renameInstr (f : Nat → Nat) : Instr → Instr
  | .mov d src => .mov (f d) (renameOperand f src)
  | .binop d op lhs rhs =>
      .binop (f d) op (renameOperand f lhs) (renameOperand f rhs)

@[simp] theorem sdest_renameInstr (f : Nat → Nat) (i : Instr) :
    sdest (renameInstr f i) = f (sdest i) := by
  cases i <;> rfl

private theorem denoteOperand_rename (k : Nat) (f : Nat → Nat)
    (s t : RegState) (h : ∀ r, t (f r) = s r) (o : Operand) :
    denoteOperand k t (renameOperand f o) = denoteOperand k s o := by
  cases o with
  | reg r => exact h r
  | lit v => rfl
  | idx => rfl

private theorem sval_rename (k : Nat) (f : Nat → Nat)
    (s t : RegState) (h : ∀ r, t (f r) = s r) (i : Instr) :
    sval k t (renameInstr f i) = sval k s i := by
  cases i with
  | mov d src => exact denoteOperand_rename k f s t h src
  | binop d op lhs rhs =>
      simp only [renameInstr, sval]
      rw [denoteOperand_rename k f s t h lhs,
        denoteOperand_rename k f s t h rhs]

private theorem set_related (f : Nat → Nat) (hf : Function.Injective f)
    (s t : RegState) (h : ∀ r, t (f r) = s r) (d value : Nat) :
    ∀ r, (t.set (f d) value) (f r) = (s.set d value) r := by
  intro r
  by_cases hr : r = d
  · subst r
    simp [RegState.set]
  · have hfr : f r ≠ f d := fun hEq => hr (hf hEq)
    simp [RegState.set, hr, hfr, h r]

/-- Executing an injectively relocated block and reading relocated register
`f r` gives exactly the original execution at register `r`. -/
theorem srun_rename (k : Nat) (f : Nat → Nat) (hf : Function.Injective f) :
    ∀ (xs : List Instr) (s t : RegState),
      (∀ r, t (f r) = s r) → ∀ r,
        srun k t (xs.map (renameInstr f)) (f r) = srun k s xs r := by
  intro xs
  induction xs with
  | nil =>
      intro s t h r
      exact h r
  | cons i rest ih =>
      intro s t h r
      simp only [List.map_cons, srun_cons]
      apply ih
      intro q
      rw [sdest_renameInstr, sval_rename k f s t h i]
      exact set_related f hf s t h (sdest i) (sval k s i) q

#print axioms srun_rename

end LeanCompCert.Verified.InstrRename
