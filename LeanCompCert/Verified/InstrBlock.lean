import LeanCompCert.Verified.Reflect

/-!
# Total straight-line blocks at the instruction level

`Verified/Straight.lean` composes *expressions*, which is convenient but
costs four instructions per operation (two operand moves, the operation,
and a move to the destination).  At the scale Montgomery exponentiation
needs — tens of thousands of operations in one loop body — that factor is
the difference between a 1.6 MB artifact and a 6 MB one.

This module is the same composition idea one level down: a block is a plain
`List Instr`, and `srun` is its *total* `Nat`-level meaning.  Totality is
again bought by excluding `udiv`/`urem`, which Montgomery arithmetic never
uses.  One operation costs exactly one instruction, and the whole layer is
five short lemmas.
-/

namespace LeanCompCert.Verified.InstrBlock

open LeanCompCert.Verified.Reflect

/-- The register an instruction writes. -/
def sdest : Instr → Nat
  | .mov d _ => d
  | .binop d _ _ _ => d

/-- The value an instruction writes, junk (`0`) on division by zero. -/
def sval (k : Nat) (s : RegState) : Instr → Nat
  | .mov _ src => denoteOperand k s src
  | .binop _ op l r =>
      (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).getD 0

/-- The instruction uses no division. -/
def NoDivI : Instr → Bool
  | .mov _ _ => true
  | .binop _ op _ _ => (op != Op.udiv) && (op != Op.urem)

/-- The total `Nat`-level meaning of a straight-line block. -/
def srun (k : Nat) (s : RegState) : List Instr → RegState
  | [] => s
  | i :: rest => srun k (s.set (sdest i) (sval k s i)) rest

theorem srun_nil (k : Nat) (s : RegState) : srun k s [] = s := rfl

theorem srun_cons (k : Nat) (s : RegState) (i : Instr) (rest : List Instr) :
    srun k s (i :: rest) = srun k (s.set (sdest i) (sval k s i)) rest := rfl

/-- Away from `udiv`/`urem`, `denoteOp` never fails. -/
private theorem denoteOp_isSome (op : Op) (h1 : op ≠ Op.udiv)
    (h2 : op ≠ Op.urem) (a b : Nat) :
    denoteOp op a b = some ((denoteOp op a b).getD 0) := by
  cases op
  case udiv => exact absurd rfl h1
  case urem => exact absurd rfl h2
  all_goals rfl

private theorem noDivI_binop {d : Nat} {op : Op} {l r : Operand}
    (h : NoDivI (.binop d op l r) = true) :
    op ≠ Op.udiv ∧ op ≠ Op.urem := by
  revert h
  cases op <;> simp [NoDivI]

/-- One division-free instruction always steps, to the `srun` state. -/
theorem denoteInstr_eq (k : Nat) (s : RegState) (i : Instr)
    (h : NoDivI i = true) :
    denoteInstr k s i = some (s.set (sdest i) (sval k s i)) := by
  cases i with
  | mov d src => rfl
  | binop d op l r =>
      obtain ⟨h1, h2⟩ := noDivI_binop h
      show (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).bind
          (fun result => some (s.set d result)) = _
      rw [denoteOp_isSome op h1 h2]
      rfl

/--
**Block correctness.**  A division-free straight-line block always runs to
completion, and lands exactly in the state the total function `srun`
describes.  No approximation, no frame condition: `srun` *is* the state.
-/
theorem srun_correct (k : Nat) :
    ∀ (l : List Instr), (∀ i ∈ l, NoDivI i = true) →
      ∀ s : RegState, denoteInstrs k s l = some (srun k s l) := by
  intro l
  induction l with
  | nil => intro _ s; rfl
  | cons i rest ih =>
      intro h s
      show (denoteInstr k s i).bind (fun s' => denoteInstrs k s' rest) = _
      rw [denoteInstr_eq k s i (h i (by simp))]
      exact ih (fun j hj => h j (by simp [hj])) _

theorem srun_append (k : Nat) :
    ∀ (l₁ l₂ : List Instr) (s : RegState),
      srun k s (l₁ ++ l₂) = srun k (srun k s l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ s; rfl
  | cons i rest ih => intro l₂ s; exact ih l₂ _

/-- Registers the block never writes keep their value. -/
theorem srun_untouched (k : Nat) (r : Nat) :
    ∀ (l : List Instr), (∀ i ∈ l, sdest i ≠ r) →
      ∀ s : RegState, srun k s l r = s r := by
  intro l
  induction l with
  | nil => intro _ s; rfl
  | cons i rest ih =>
      intro h s
      rw [srun_cons, ih (fun j hj => h j (by simp [hj]))]
      show (if r = sdest i then sval k s i else s r) = s r
      rw [if_neg (Ne.symm (h i (by simp)))]

/-- Every register stays a `u64`. -/
theorem srun_lt (k : Nat) :
    ∀ (l : List Instr), (∀ i ∈ l, NoDivI i = true) →
      ∀ s : RegState, (∀ j, s j < M) → ∀ j, srun k s l j < M := by
  intro l
  induction l with
  | nil => intro _ s hs j; exact hs j
  | cons i rest ih =>
      intro h s hs j
      refine ih (fun x hx => h x (by simp [hx])) _ ?_ j
      intro j'
      by_cases hEq : j' = sdest i
      · subst hEq
        simp only [RegState.set, if_pos rfl]
        cases i with
        | mov d src =>
            show denoteOperand k s src < M
            cases src with
            | reg i' => exact hs i'
            | lit v => exact Nat.mod_lt _ M_pos
            | idx => exact Nat.mod_lt _ M_pos
        | binop d op l' r' =>
            obtain ⟨h1, h2⟩ := noDivI_binop (h (Instr.binop d op l' r') (by simp))
            show (denoteOp op (denoteOperand k s l') (denoteOperand k s r')).getD 0 < M
            exact denoteOp_lt op _ _ _ (denoteOp_isSome op h1 h2 _ _)
      · simp only [RegState.set, if_neg hEq]
        exact hs j'

/-- Well-formedness of a block, decidable and block-sized. -/
def BlockWF (regCount : Nat) (l : List Instr) : Prop :=
  ∀ i ∈ l, i.WF regCount

/-! ## Blocks that divide

`srun_correct` buys totality by excluding `udiv`/`urem`, which is right for
Montgomery arithmetic and wrong for anything that decodes a flat loop index
into a candidate and a round, or that trial-divides.  Those blocks *are*
partial, at exactly the points where a divisor could be zero.

This section is the scalar counterpart of
`Verified/ArrayFoldBridge.lean`'s `ADefined`/`AllDefined`: a per-instruction
definedness predicate read **at the state that instruction executes in**, and
the resulting `denoteInstrs = some (srun …)`.  `srun` is already total for
every operation (`sval` reads a failing `denoteOp` through `Option.getD`), so
nothing but the hypothesis changes.
-/

/-- "This instruction is defined in this state": the only way to fail is a
`udiv`/`urem` whose divisor is zero. -/
def SDefined (k : Nat) (s : RegState) : Instr → Prop
  | .mov _ _ => True
  | .binop _ op l r =>
      (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).isSome = true

/-- Every instruction of the block is defined at the state it executes in.
The recursion is the point: the guard on instruction `j` is read in the state
the first `j` instructions have reached. -/
def SAllDefined (k : Nat) : RegState → List Instr → Prop
  | _, [] => True
  | s, i :: rest => SDefined k s i ∧ SAllDefined k (s.set (sdest i) (sval k s i)) rest

/-- One defined instruction denotes its total meaning. -/
theorem denoteInstr_eq_of_defined (k : Nat) (s : RegState) (i : Instr)
    (h : SDefined k s i) :
    denoteInstr k s i = some (s.set (sdest i) (sval k s i)) := by
  cases i with
  | mov d src => rfl
  | binop d op l r =>
      simp only [SDefined] at h
      cases hv : denoteOp op (denoteOperand k s l) (denoteOperand k s r) with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          show (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).bind
            (fun result => some (s.set d result)) = _
          rw [hv]
          simp only [sdest, sval, hv, Option.getD_some, Option.bind_some]

/--
**Block correctness, with division.**  A straight-line block all of whose
partial operations are defined where they execute runs to completion and
lands exactly in the state `srun` describes.
-/
theorem denoteInstrs_eq_srun (k : Nat) :
    ∀ (l : List Instr) (s : RegState), SAllDefined k s l →
      denoteInstrs k s l = some (srun k s l) := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      show (denoteInstr k s i).bind (fun s' => denoteInstrs k s' rest) = _
      rw [denoteInstr_eq_of_defined k s i h.1]
      exact ih _ h.2

/-- Definedness splits along a block boundary, at the state the second block
starts in.  A port that would otherwise pay a term quadratic in the block
length cuts the body into named stages and pays for one stage at a time. -/
theorem SAllDefined_append (k : Nat) :
    ∀ (xs ys : List Instr) (s : RegState),
      SAllDefined k s (xs ++ ys) ↔
        (SAllDefined k s xs ∧ SAllDefined k (srun k s xs) ys) := by
  intro xs
  induction xs with
  | nil => intro ys s; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons i rest ih =>
      intro ys s
      show (SDefined k s i ∧ SAllDefined k _ (rest ++ ys)) ↔ _
      rw [ih ys (s.set (sdest i) (sval k s i))]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- Every register stays a `u64`, for blocks that divide as well.  `denoteOp`
reduces every result modulo `M`, so this needs no hypothesis at all beyond the
starting state. -/
theorem srun_lt_of_lt (k : Nat) :
    ∀ (l : List Instr) (s : RegState), (∀ j, s j < M) → ∀ j, srun k s l j < M := by
  intro l
  induction l with
  | nil => intro s hs j; exact hs j
  | cons i rest ih =>
      intro s hs j
      refine ih _ ?_ j
      intro j'
      by_cases hEq : j' = sdest i
      · subst hEq
        simp only [RegState.set, if_pos rfl]
        cases i with
        | mov d src =>
            show denoteOperand k s src < M
            cases src with
            | reg i' => exact hs i'
            | lit v => exact Nat.mod_lt _ M_pos
            | idx => exact Nat.mod_lt _ M_pos
        | binop d op l' r' =>
            show (denoteOp op (denoteOperand k s l') (denoteOperand k s r')).getD 0 < M
            cases hv : denoteOp op (denoteOperand k s l') (denoteOperand k s r') with
            | none => simpa [hv] using M_pos
            | some v => exact denoteOp_lt op _ _ _ hv
      · simp only [RegState.set, if_neg hEq]
        exact hs j'

end LeanCompCert.Verified.InstrBlock
