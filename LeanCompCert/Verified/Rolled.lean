import LeanCompCert.Verified.Package

/-!
# M4 — Rolled loops in emission

`foldTrace` unrolling keeps the theorems honest at any size, but emitted C
must not be gigabytes at 10⁷ iterations. This module adds the counted
rolled form: the loop index lives in a dedicated counter register, the
body is compiled **once** with `.idx` mapped to that register's C
variable, and the emitted function is a single `while` loop.

The semantics never changes: `foldTrace` remains the meaning of a
`Program`. The proved correspondence core is `evalOperand_var_eq_lit`:
under an environment where the counter register holds `k`, the
variable-index operand evaluates exactly as iteration `k`'s literal
operand. Lifting this through statements and the loop induction to a full
rolled-model ≡ unrolled-model theorem is the remaining M4 proof; until
then the rolled form is an emission choice for the independent native
check, while every theorem consumers use flows through the unrolled
trace.
-/

namespace LeanCompCert.Verified.Reflect

open LeanCompCert
open LeanCompCert.Proof

/-- The counter register: one past the program's registers. -/
def counterReg (p : Program) : Nat := p.regCount

/-- Compile an operand with the loop index as the counter variable. -/
def compileOperandVar (p : Program) : Operand → CCIR.Operand
  | .reg i => .local ⟨i + 1⟩
  | .lit value => .uintLit .u64 value
  | .idx => .local ⟨counterReg p + 1⟩

def compileInstrVar (p : Program) : Instr → List StraightInstruction
  | .mov dest src => [.assign (regLocal dest) (compileOperandVar p src)]
  | .binop dest op lhs rhs =>
      match op.arithmetic?, op.comparison? with
      | some arith, _ =>
          [.binary (regLocal dest) arith
            (compileOperandVar p lhs) (compileOperandVar p rhs)]
      | none, some comparison =>
          [.compare scratchLocal comparison
            (compileOperandVar p lhs) (compileOperandVar p rhs),
           .cast (regLocal dest) (.local ⟨0⟩)]
      | none, none => []

def compileInstrsVar (p : Program) (instrs : List Instr) :
    List StraightInstruction :=
  instrs.flatMap (compileInstrVar p)

/--
**Variable/literal correspondence** (the M4 proof core): compiling an
operand against the counter variable evaluates, in any environment where
the counter holds `k` (normalized), exactly as compiling it against the
literal `k`.
-/
theorem evalOperand_var_eq_lit (p : Program) (k : Nat)
    (env : Proof.CCEnv)
    (hCounter : env ⟨counterReg p + 1⟩ = some ((k % M : Nat) : Int))
    (operand : Operand) :
    Proof.evalOperand env
        (compileOperandVar p operand) =
      Proof.evalOperand env (compileOperand k operand) := by
  cases operand with
  | reg i => rfl
  | lit value => rfl
  | idx =>
      show env ⟨counterReg p + 1⟩ =
        Proof.normalizeCC .u64 ((k : Nat) : Int)
      rw [hCounter, normalizeCC_u64_natCast]

/-- The counter-increment instruction, shared by rolled and augmented
unrolled traces. -/
def incInstr (p : Program) : StraightInstruction :=
  .binary (regLocal (counterReg p)) .add
    (.local ⟨counterReg p + 1⟩) (.uintLit .u64 1)

/-- Register writes below the counter preserve the counter's value. -/
private theorem set_preserves_counter (p : Program) (env : Proof.CCEnv)
    (id : CCIR.LocalId) (value : Int)
    (hNe : id ≠ ⟨counterReg p + 1⟩) :
    (Proof.CCEnv.set env id value) ⟨counterReg p + 1⟩ =
      env ⟨counterReg p + 1⟩ := by
  simp only [Proof.CCEnv.set]
  rw [if_neg]
  intro h
  exact hNe (h ▸ rfl)

private theorem regLocal_ne_counter (p : Program) (d : Nat)
    (hd : d < p.regCount) :
    (regLocal d).id ≠ (⟨counterReg p + 1⟩ : CCIR.LocalId) := by
  intro h
  have : d + 1 = counterReg p + 1 := congrArg CCIR.LocalId.value h
  unfold counterReg at this
  omega

private theorem scratch_ne_counter (p : Program) :
    (⟨0⟩ : CCIR.LocalId) ≠ (⟨counterReg p + 1⟩ : CCIR.LocalId) := by
  intro h
  exact Nat.noConfusion (congrArg CCIR.LocalId.value h)

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    (Option.bind (some a) f) = f a := rfl

private theorem obind_none {α β : Type _} (f : α → Option β) :
    (Option.bind (none : Option α) f) = none := rfl

private theorem mbind_some {α β : Type _} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

private theorem obind_pure {α β : Type _} (a : α) (f : α → Option β) :
    (Option.bind (pure a : Option α) f) = f a := rfl

private theorem mbind_none {α β : Type _} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl

/-- Literal-index compiled sequences never write the counter register:
their destinations lie strictly below it. -/
theorem lit_preserves_counter (p : Program) (k : Nat) :
    ∀ (instrs : List Instr), (∀ i ∈ instrs, i.WF p.regCount) →
    ∀ (env envOut : Proof.CCEnv),
      Proof.evalCCSequence env (compileInstrs k instrs) = some envOut →
      envOut ⟨counterReg p + 1⟩ = env ⟨counterReg p + 1⟩ := by
  intro instrs
  induction instrs with
  | nil =>
      intro _ env envOut hOut
      injection hOut with h
      rw [← h]
  | cons instr rest ih =>
      intro hWF env envOut hOut
      have hInstrWF := hWF instr (by simp)
      have hRestWF : ∀ i ∈ rest, i.WF p.regCount := fun i hi =>
        hWF i (by simp [hi])
      cases instr with
      | mov dest src =>
          obtain ⟨hDest, _⟩ := hInstrWF
          replace hOut :
              (Proof.evalCCAssignStep env (regLocal dest)
                (compileOperand k src)).bind
                (fun env => Proof.evalCCSequence env
                  (compileInstrs k rest)) = some envOut := hOut
          unfold Proof.evalCCAssignStep at hOut
          cases hVal : Proof.evalOperand env (compileOperand k src) with
          | none =>
              rw [hVal, mbind_none, obind_none] at hOut
              simp at hOut
          | some value =>
              rw [hVal, mbind_some, obind_pure] at hOut
              rw [ih hRestWF _ envOut hOut,
                set_preserves_counter p env _ value
                  (regLocal_ne_counter p dest hDest)]
      | binop dest op lhs rhs =>
          obtain ⟨hDest, _, _⟩ := hInstrWF
          cases hArith : op.arithmetic? with
          | some arith =>
              replace hOut :
                  (Proof.evalCCBinaryStep env (regLocal dest) arith
                    (compileOperand k lhs) (compileOperand k rhs)).bind
                    (fun env => Proof.evalCCSequence env
                      (compileInstrs k rest)) = some envOut := by
                rw [← hOut]
                show _ = Proof.evalCCSequence env
                  (compileInstrs k (.binop dest op lhs rhs :: rest))
                show _ = Proof.evalCCSequence env
                  ((compileInstr k (.binop dest op lhs rhs)) ++
                    compileInstrs k rest)
                rw [show compileInstr k (.binop dest op lhs rhs) =
                  [.binary (regLocal dest) arith
                    (compileOperand k lhs) (compileOperand k rhs)] from by
                    show (match op.arithmetic?, op.comparison? with
                      | some arith, _ =>
                          [StraightInstruction.binary (regLocal dest) arith
                            (compileOperand k lhs) (compileOperand k rhs)]
                      | none, some comparison =>
                          [StraightInstruction.compare scratchLocal
                            comparison (compileOperand k lhs)
                            (compileOperand k rhs),
                           StraightInstruction.cast (regLocal dest)
                            (.local ⟨0⟩)]
                      | none, none => []) = _
                    rw [hArith]]
                rfl
              unfold Proof.evalCCBinaryStep at hOut
              cases hL : Proof.evalOperand env (compileOperand k lhs) with
              | none =>
                  rw [hL, mbind_none, obind_none] at hOut
                  simp at hOut
              | some lv =>
                  rw [hL, mbind_some] at hOut
                  cases hR : Proof.evalOperand env
                      (compileOperand k rhs) with
                  | none =>
                      rw [hR, mbind_none, obind_none] at hOut
                      simp at hOut
                  | some rv =>
                      rw [hR, mbind_some] at hOut
                      cases hres : Proof.evalCCBinary
                          (regLocal dest).type arith lv rv with
                      | none =>
                          rw [hres, mbind_none, obind_none] at hOut
                          simp at hOut
                      | some value =>
                          rw [hres, mbind_some, obind_pure] at hOut
                          rw [ih hRestWF _ envOut hOut,
                            set_preserves_counter p env _ value
                              (regLocal_ne_counter p dest hDest)]
          | none =>
              cases hCmp : op.comparison? with
              | none =>
                  exfalso
                  cases op <;> simp [Op.arithmetic?] at hArith <;>
                    simp [Op.comparison?] at hCmp
              | some cmp =>
                  replace hOut :
                      (Proof.evalCCComparisonStep env scratchLocal cmp
                        (compileOperand k lhs)
                        (compileOperand k rhs)).bind
                        (fun env =>
                          (Proof.evalCCCastStep env (regLocal dest)
                            (.local ⟨0⟩)).bind
                            (fun env => Proof.evalCCSequence env
                              (compileInstrs k rest))) = some envOut := by
                    rw [← hOut]
                    show _ = Proof.evalCCSequence env
                      ((compileInstr k (.binop dest op lhs rhs)) ++
                        compileInstrs k rest)
                    rw [show compileInstr k (.binop dest op lhs rhs) =
                      [.compare scratchLocal cmp
                        (compileOperand k lhs) (compileOperand k rhs),
                       .cast (regLocal dest) (.local ⟨0⟩)] from by
                        show (match op.arithmetic?, op.comparison? with
                          | some arith, _ =>
                              [StraightInstruction.binary (regLocal dest)
                                arith (compileOperand k lhs)
                                (compileOperand k rhs)]
                          | none, some comparison =>
                              [StraightInstruction.compare scratchLocal
                                comparison (compileOperand k lhs)
                                (compileOperand k rhs),
                               StraightInstruction.cast (regLocal dest)
                                (.local ⟨0⟩)]
                          | none, none => []) = _
                        rw [hArith, hCmp]]
                    rfl
                  unfold Proof.evalCCComparisonStep at hOut
                  cases hL : Proof.evalOperand env
                      (compileOperand k lhs) with
                  | none =>
                      rw [hL, mbind_none, obind_none] at hOut
                      simp at hOut
                  | some lv =>
                      rw [hL, mbind_some] at hOut
                      cases hR : Proof.evalOperand env
                          (compileOperand k rhs) with
                      | none =>
                          rw [hR, mbind_none, obind_none] at hOut
                          simp at hOut
                      | some rv =>
                          rw [hR, mbind_some] at hOut
                          cases hres : Proof.evalCCComparison
                              scratchLocal.type cmp lv rv with
                          | none =>
                              rw [hres, mbind_none, obind_none] at hOut
                              simp at hOut
                          | some value =>
                              rw [hres, mbind_some, obind_pure] at hOut
                              unfold Proof.evalCCCastStep at hOut
                              cases hRead : Proof.evalOperand
                                  (Proof.CCEnv.set env scratchLocal.id
                                    value) (.local ⟨0⟩) with
                              | none =>
                                  rw [hRead, mbind_none, obind_none]
                                    at hOut
                                  simp at hOut
                              | some readValue =>
                                  rw [hRead, mbind_some] at hOut
                                  cases hNorm : Proof.normalizeCC
                                      (regLocal dest).type readValue with
                                  | none =>
                                      rw [hNorm, mbind_none, obind_none]
                                        at hOut
                                      simp at hOut
                                  | some normValue =>
                                      rw [hNorm, mbind_some, obind_pure]
                                        at hOut
                                      rw [ih hRestWF _ envOut hOut,
                                        set_preserves_counter p _ _
                                          normValue
                                          (regLocal_ne_counter p dest
                                            hDest),
                                        show Proof.CCEnv.set env
                                          scratchLocal.id value
                                          ⟨counterReg p + 1⟩ =
                                            env ⟨counterReg p + 1⟩ from
                                          set_preserves_counter p env
                                            scratchLocal.id value
                                            (scratch_ne_counter p)]

/--
**M4 statement-level correspondence**: under the counter invariant, the
variable-index compilation of an instruction list evaluates to exactly
the same result as iteration `k`'s literal compilation.
-/
theorem evalCCSequence_var_eq_lit (p : Program) (k : Nat) :
    ∀ (instrs : List Instr), (∀ i ∈ instrs, i.WF p.regCount) →
    ∀ (env : Proof.CCEnv),
      env ⟨counterReg p + 1⟩ = some ((k % M : Nat) : Int) →
      Proof.evalCCSequence env (compileInstrsVar p instrs) =
        Proof.evalCCSequence env (compileInstrs k instrs) := by
  intro instrs
  induction instrs with
  | nil => intro _ _ _; rfl
  | cons instr rest ih =>
      intro hWF env hCounter
      have hInstrWF := hWF instr (by simp)
      have hRestWF : ∀ i ∈ rest, i.WF p.regCount := fun i hi =>
        hWF i (by simp [hi])
      cases instr with
      | mov dest src =>
          obtain ⟨hDest, _⟩ := hInstrWF
          have hOp := evalOperand_var_eq_lit p k env hCounter src
          show (Proof.evalCCAssignStep env (regLocal dest)
                (compileOperandVar p src)).bind
              (fun env => Proof.evalCCSequence env
                (compileInstrsVar p rest)) =
            (Proof.evalCCAssignStep env (regLocal dest)
                (compileOperand k src)).bind
              (fun env => Proof.evalCCSequence env
                (compileInstrs k rest))
          unfold Proof.evalCCAssignStep
          rw [hOp]
          cases hVal : Proof.evalOperand env (compileOperand k src) with
          | none => rfl
          | some value =>
              show Proof.evalCCSequence
                  (Proof.CCEnv.set env (regLocal dest).id value)
                  (compileInstrsVar p rest) =
                Proof.evalCCSequence
                  (Proof.CCEnv.set env (regLocal dest).id value)
                  (compileInstrs k rest)
              exact ih hRestWF _ (by
                rw [set_preserves_counter p env _ value
                  (regLocal_ne_counter p dest hDest)]
                exact hCounter)
      | binop dest op lhs rhs =>
          obtain ⟨hDest, _, _⟩ := hInstrWF
          have hOpL := evalOperand_var_eq_lit p k env hCounter lhs
          have hOpR := evalOperand_var_eq_lit p k env hCounter rhs
          cases hArith : op.arithmetic? with
          | some arith =>
              have hVarList :
                  compileInstrsVar p (.binop dest op lhs rhs :: rest) =
                    .binary (regLocal dest) arith
                        (compileOperandVar p lhs)
                        (compileOperandVar p rhs) ::
                      compileInstrsVar p rest := by
                show compileInstrVar p (.binop dest op lhs rhs) ++
                    compileInstrsVar p rest = _
                rw [show compileInstrVar p (.binop dest op lhs rhs) =
                  [.binary (regLocal dest) arith
                    (compileOperandVar p lhs)
                    (compileOperandVar p rhs)] from by
                    show (match op.arithmetic?, op.comparison? with
                      | some arith, _ =>
                          [StraightInstruction.binary (regLocal dest)
                            arith (compileOperandVar p lhs)
                            (compileOperandVar p rhs)]
                      | none, some comparison =>
                          [StraightInstruction.compare scratchLocal
                            comparison (compileOperandVar p lhs)
                            (compileOperandVar p rhs),
                           StraightInstruction.cast (regLocal dest)
                            (.local ⟨0⟩)]
                      | none, none => []) = _
                    rw [hArith]]
                rfl
              have hLitList :
                  compileInstrs k (.binop dest op lhs rhs :: rest) =
                    .binary (regLocal dest) arith
                        (compileOperand k lhs)
                        (compileOperand k rhs) ::
                      compileInstrs k rest := by
                show compileInstr k (.binop dest op lhs rhs) ++
                    compileInstrs k rest = _
                rw [show compileInstr k (.binop dest op lhs rhs) =
                  [.binary (regLocal dest) arith
                    (compileOperand k lhs)
                    (compileOperand k rhs)] from by
                    show (match op.arithmetic?, op.comparison? with
                      | some arith, _ =>
                          [StraightInstruction.binary (regLocal dest)
                            arith (compileOperand k lhs)
                            (compileOperand k rhs)]
                      | none, some comparison =>
                          [StraightInstruction.compare scratchLocal
                            comparison (compileOperand k lhs)
                            (compileOperand k rhs),
                           StraightInstruction.cast (regLocal dest)
                            (.local ⟨0⟩)]
                      | none, none => []) = _
                    rw [hArith]]
                rfl
              rw [hVarList, hLitList]
              show (Proof.evalCCBinaryStep env (regLocal dest) arith
                    (compileOperandVar p lhs)
                    (compileOperandVar p rhs)).bind
                  (fun env => Proof.evalCCSequence env
                    (compileInstrsVar p rest)) =
                (Proof.evalCCBinaryStep env (regLocal dest) arith
                    (compileOperand k lhs)
                    (compileOperand k rhs)).bind
                  (fun env => Proof.evalCCSequence env
                    (compileInstrs k rest))
              unfold Proof.evalCCBinaryStep
              rw [hOpL, hOpR]
              cases hL : Proof.evalOperand env (compileOperand k lhs) with
              | none => rfl
              | some lv =>
                  simp only [mbind_some, obind_pure]
                  cases hR : Proof.evalOperand env
                      (compileOperand k rhs) with
                  | none => rfl
                  | some rv =>
                      simp only [mbind_some, obind_pure]
                      cases hres : Proof.evalCCBinary
                          (regLocal dest).type arith lv rv with
                      | none => rfl
                      | some value =>
                          show Proof.evalCCSequence
                              (Proof.CCEnv.set env (regLocal dest).id
                                value) (compileInstrsVar p rest) =
                            Proof.evalCCSequence
                              (Proof.CCEnv.set env (regLocal dest).id
                                value) (compileInstrs k rest)
                          exact ih hRestWF _ (by
                            rw [set_preserves_counter p env _ value
                              (regLocal_ne_counter p dest hDest)]
                            exact hCounter)
          | none =>
              cases hCmp : op.comparison? with
              | none =>
                  exfalso
                  cases op <;> simp [Op.arithmetic?] at hArith <;>
                    simp [Op.comparison?] at hCmp
              | some cmp =>
                  have hVarList :
                      compileInstrsVar p (.binop dest op lhs rhs :: rest) =
                        .compare scratchLocal cmp
                            (compileOperandVar p lhs)
                            (compileOperandVar p rhs) ::
                          .cast (regLocal dest) (.local ⟨0⟩) ::
                            compileInstrsVar p rest := by
                    show compileInstrVar p (.binop dest op lhs rhs) ++
                        compileInstrsVar p rest = _
                    rw [show compileInstrVar p (.binop dest op lhs rhs) =
                      [.compare scratchLocal cmp
                        (compileOperandVar p lhs)
                        (compileOperandVar p rhs),
                       .cast (regLocal dest) (.local ⟨0⟩)] from by
                        show (match op.arithmetic?, op.comparison? with
                          | some arith, _ =>
                              [StraightInstruction.binary (regLocal dest)
                                arith (compileOperandVar p lhs)
                                (compileOperandVar p rhs)]
                          | none, some comparison =>
                              [StraightInstruction.compare scratchLocal
                                comparison (compileOperandVar p lhs)
                                (compileOperandVar p rhs),
                               StraightInstruction.cast (regLocal dest)
                                (.local ⟨0⟩)]
                          | none, none => []) = _
                        rw [hArith, hCmp]]
                    rfl
                  have hLitList :
                      compileInstrs k (.binop dest op lhs rhs :: rest) =
                        .compare scratchLocal cmp
                            (compileOperand k lhs)
                            (compileOperand k rhs) ::
                          .cast (regLocal dest) (.local ⟨0⟩) ::
                            compileInstrs k rest := by
                    show compileInstr k (.binop dest op lhs rhs) ++
                        compileInstrs k rest = _
                    rw [show compileInstr k (.binop dest op lhs rhs) =
                      [.compare scratchLocal cmp
                        (compileOperand k lhs)
                        (compileOperand k rhs),
                       .cast (regLocal dest) (.local ⟨0⟩)] from by
                        show (match op.arithmetic?, op.comparison? with
                          | some arith, _ =>
                              [StraightInstruction.binary (regLocal dest)
                                arith (compileOperand k lhs)
                                (compileOperand k rhs)]
                          | none, some comparison =>
                              [StraightInstruction.compare scratchLocal
                                comparison (compileOperand k lhs)
                                (compileOperand k rhs),
                               StraightInstruction.cast (regLocal dest)
                                (.local ⟨0⟩)]
                          | none, none => []) = _
                        rw [hArith, hCmp]]
                    rfl
                  rw [hVarList, hLitList]
                  show ((Proof.evalCCComparisonStep env scratchLocal cmp
                        (compileOperandVar p lhs)
                        (compileOperandVar p rhs)).bind
                      (fun env =>
                        (Proof.evalCCCastStep env (regLocal dest)
                          (.local ⟨0⟩)).bind
                          (fun env => Proof.evalCCSequence env
                            (compileInstrsVar p rest)))) =
                    ((Proof.evalCCComparisonStep env scratchLocal cmp
                        (compileOperand k lhs)
                        (compileOperand k rhs)).bind
                      (fun env =>
                        (Proof.evalCCCastStep env (regLocal dest)
                          (.local ⟨0⟩)).bind
                          (fun env => Proof.evalCCSequence env
                            (compileInstrs k rest))))
                  unfold Proof.evalCCComparisonStep
                  rw [hOpL, hOpR]
                  cases hL : Proof.evalOperand env
                      (compileOperand k lhs) with
                  | none => rfl
                  | some lv =>
                      simp only [mbind_some, obind_pure]
                      cases hR : Proof.evalOperand env
                          (compileOperand k rhs) with
                      | none => rfl
                      | some rv =>
                          simp only [mbind_some, obind_pure]
                          cases hres : Proof.evalCCComparison
                              scratchLocal.type cmp lv rv with
                          | none => rfl
                          | some value =>
                              show ((Proof.evalCCCastStep
                                    (Proof.CCEnv.set env scratchLocal.id
                                      value)
                                    (regLocal dest) (.local ⟨0⟩)).bind
                                  (fun env => Proof.evalCCSequence env
                                    (compileInstrsVar p rest))) =
                                ((Proof.evalCCCastStep
                                    (Proof.CCEnv.set env scratchLocal.id
                                      value)
                                    (regLocal dest) (.local ⟨0⟩)).bind
                                  (fun env => Proof.evalCCSequence env
                                    (compileInstrs k rest)))
                              cases hCast : Proof.evalCCCastStep
                                  (Proof.CCEnv.set env scratchLocal.id
                                    value)
                                  (regLocal dest) (.local ⟨0⟩) with
                              | none => rfl
                              | some envCast =>
                                  show Proof.evalCCSequence envCast
                                      (compileInstrsVar p rest) =
                                    Proof.evalCCSequence envCast
                                      (compileInstrs k rest)
                                  refine ih hRestWF envCast ?_
                                  unfold Proof.evalCCCastStep at hCast
                                  cases hRead : Proof.evalOperand
                                      (Proof.CCEnv.set env scratchLocal.id
                                        value) (.local ⟨0⟩) with
                                  | none =>
                                      simp only [hRead, mbind_none,
                                        obind_none] at hCast
                                      simp at hCast
                                  | some readValue =>
                                      rw [hRead, mbind_some] at hCast
                                      cases hNorm : Proof.normalizeCC
                                          (regLocal dest).type
                                          readValue with
                                      | none =>
                                          simp only [hNorm, mbind_none,
                                            obind_none] at hCast
                                          simp at hCast
                                      | some normValue =>
                                          simp only [hNorm, mbind_some,
                                            obind_pure] at hCast
                                          injection hCast with hEnvEq
                                          rw [← hEnvEq,
                                            set_preserves_counter p _ _
                                              normValue
                                              (regLocal_ne_counter p dest
                                                hDest),
                                            show Proof.CCEnv.set env
                                              scratchLocal.id value
                                              ⟨counterReg p + 1⟩ =
                                                env ⟨counterReg p + 1⟩ from
                                              set_preserves_counter p env
                                                scratchLocal.id value
                                                (scratch_ne_counter p)]
                                          exact hCounter

/--
The counter-augmented program: one more register (the counter), and the
body extended with the source-level increment. Its standard unrolled
semantics is exactly what the rolled loop executes — so every packaging
and bridge theorem applies to it unchanged, and no frame reasoning about
the counter is ever needed.
-/
def Program.counterAugment (p : Program) : Program := {
  regCount := p.regCount + 1
  loopCount := p.loopCount
  init := p.init
  body := p.body ++ [.binop p.regCount .add (.reg p.regCount) (.lit 1)]
  epilogue := p.epilogue
  output := p.output
}

/-- The literal-side block of one rolled iteration. -/
def litBlock (p : Program) (k : Nat) : List StraightInstruction :=
  compileInstrs k p.body ++ [incInstr p]

/-- The augmented body compiles to exactly the literal block. -/
theorem counterAugment_body_compile (p : Program) (k : Nat) :
    compileInstrs k (Program.counterAugment p).body = litBlock p k := by
  show compileInstrs k
      (p.body ++ [.binop p.regCount .add (.reg p.regCount) (.lit 1)]) = _
  unfold compileInstrs
  rw [List.flatMap_append]
  rfl

/-- The rolled loop's dynamic trace: the block repeated (recursive, so
front-splits are definitional). -/
def rolledTrace (p : Program) : Nat → List StraightInstruction
  | 0 => []
  | count + 1 =>
      (compileInstrsVar p p.body ++ [incInstr p]) ++ rolledTrace p count

/-- The literal-side segment starting at `start` (recursive). -/
def litSeg (p : Program) : Nat → Nat → List StraightInstruction
  | _, 0 => []
  | start, count + 1 => litBlock p start ++ litSeg p (start + 1) count

theorem litSeg_snoc (p : Program) :
    ∀ (count start : Nat),
      litSeg p start (count + 1) =
        litSeg p start count ++ litBlock p (start + count)
  | 0, start => by
      show litBlock p start ++ [] = [] ++ litBlock p (start + 0)
      rw [List.append_nil, List.nil_append, Nat.add_zero]
  | count + 1, start => by
      show litBlock p start ++ litSeg p (start + 1) (count + 1) = _
      rw [litSeg_snoc p count (start + 1)]
      show _ = (litBlock p start ++ litSeg p (start + 1) count) ++
        litBlock p (start + (count + 1))
      rw [List.append_assoc,
        show start + 1 + count = start + (count + 1) from by omega]

/-- The augmented program's standard unrolled trace is the literal
segment from zero. -/
theorem foldTrace_augment_eq_litSeg (p : Program) :
    ∀ (count : Nat),
      foldTrace count
          (fun k => compileInstrs k (Program.counterAugment p).body) =
        litSeg p 0 count
  | 0 => rfl
  | count + 1 => by
      rw [foldTrace_succ, foldTrace_augment_eq_litSeg p count,
        counterAugment_body_compile p count, litSeg_snoc p count 0,
        Nat.zero_add]

/-- One increment step: the counter advances by one, normalized. -/
theorem inc_step (p : Program) (env : Proof.CCEnv) (start : Nat)
    (hCounter : env ⟨counterReg p + 1⟩ = some ((start % M : Nat) : Int)) :
    Proof.evalCCSequence env [incInstr p] =
      some (Proof.CCEnv.set env ⟨counterReg p + 1⟩
        (((start + 1) % M : Nat) : Int)) := by
  show (Proof.evalCCBinaryStep env (regLocal (counterReg p)) .add
      (.local ⟨counterReg p + 1⟩) (.uintLit .u64 1)).bind
      (fun env => some env) = _
  unfold Proof.evalCCBinaryStep
  rw [show Proof.evalOperand env
      (.local ⟨counterReg p + 1⟩ : CCIR.Operand) =
      some ((start % M : Nat) : Int) from hCounter]
  rw [show Proof.evalOperand env (.uintLit .u64 1 : CCIR.Operand) =
      some ((1 % M : Nat) : Int) from normalizeCC_u64_natCast 1]
  simp only [mbind_some, regLocal]
  rw [evalCCBinary_u64_natCast .add .add rfl (start % M) (1 % M)
    (Nat.mod_lt 1 M_pos)]
  rw [show denoteOp .add (start % M) (1 % M) =
      some ((start + 1) % M) from by
    show some ((start % M + 1 % M) % M) = some ((start + 1) % M)
    rw [← Nat.add_mod]]
  rfl

/-- The counter's value after a literal segment. -/
theorem litSeg_counter (p : Program)
    (hBody : ∀ i ∈ p.body, i.WF p.regCount) :
    ∀ (count start : Nat) (env envOut : Proof.CCEnv),
      env ⟨counterReg p + 1⟩ = some ((start % M : Nat) : Int) →
      Proof.evalCCSequence env (litSeg p start count) = some envOut →
      envOut ⟨counterReg p + 1⟩ =
        some (((start + count) % M : Nat) : Int) := by
  intro count
  induction count with
  | zero =>
      intro start env envOut hCounter hRun
      injection hRun with h
      rw [← h, Nat.add_zero]
      exact hCounter
  | succ count ih =>
      intro start env envOut hCounter hRun
      replace hRun : Proof.evalCCSequence env
          (litBlock p start ++ litSeg p (start + 1) count) =
            some envOut := hRun
      rw [Proof.evalCCSequence_append] at hRun
      cases hBlock : Proof.evalCCSequence env (litBlock p start) with
      | none =>
          rw [hBlock] at hRun
          simp only [mbind_none] at hRun
          exact absurd hRun (by simp)
      | some envMid =>
          rw [hBlock] at hRun
          simp only [mbind_some] at hRun
          have hMidCounter : envMid ⟨counterReg p + 1⟩ =
              some (((start + 1) % M : Nat) : Int) := by
            unfold litBlock at hBlock
            rw [Proof.evalCCSequence_append] at hBlock
            cases hBodyRun : Proof.evalCCSequence env
                (compileInstrs start p.body) with
            | none =>
                rw [hBodyRun] at hBlock
                simp only [mbind_none] at hBlock
                exact absurd hBlock (by simp)
            | some envBody =>
                rw [hBodyRun] at hBlock
                simp only [mbind_some] at hBlock
                have hBodyCounter : envBody ⟨counterReg p + 1⟩ =
                    some ((start % M : Nat) : Int) := by
                  rw [lit_preserves_counter p start p.body hBody env
                    envBody hBodyRun]
                  exact hCounter
                rw [inc_step p envBody start hBodyCounter] at hBlock
                injection hBlock with h
                rw [← h]
                simp [Proof.CCEnv.set]
          have := ih (start + 1) envMid envOut hMidCounter hRun
          rw [show start + 1 + count = start + (count + 1) from by omega]
            at this
          exact this

/--
**M4 assembly**: the rolled loop's dynamic trace evaluates exactly as
the counter-augmented program's standard unrolled trace.
-/
theorem rolledTrace_eq_litSeg (p : Program)
    (hBody : ∀ i ∈ p.body, i.WF p.regCount) :
    ∀ (count start : Nat) (env : Proof.CCEnv),
      env ⟨counterReg p + 1⟩ = some ((start % M : Nat) : Int) →
      Proof.evalCCSequence env (rolledTrace p count) =
        Proof.evalCCSequence env (litSeg p start count) := by
  intro count
  induction count with
  | zero => intro _ _ _; rfl
  | succ count ih =>
      intro start env hCounter
      show Proof.evalCCSequence env
          ((compileInstrsVar p p.body ++ [incInstr p]) ++
            rolledTrace p count) =
        Proof.evalCCSequence env
          (litBlock p start ++ litSeg p (start + 1) count)
      unfold litBlock
      rw [Proof.evalCCSequence_append, Proof.evalCCSequence_append,
        Proof.evalCCSequence_append, Proof.evalCCSequence_append,
        evalCCSequence_var_eq_lit p start p.body hBody env hCounter]
      cases hBodyRun : Proof.evalCCSequence env
          (compileInstrs start p.body) with
      | none => rfl
      | some envBody =>
          simp only [mbind_some]
          have hBodyCounter : envBody ⟨counterReg p + 1⟩ =
              some ((start % M : Nat) : Int) := by
            rw [lit_preserves_counter p start p.body hBody env envBody
              hBodyRun]
            exact hCounter
          rw [inc_step p envBody start hBodyCounter]
          simp only [mbind_some]
          exact ih (start + 1) _ (by simp [Proof.CCEnv.set])

/-- Consumer corollary: rolled execution ≡ the augmented program's
standard `foldTrace` semantics, so packaging, bridge, and denotation
theorems apply to `p.counterAugment` while the artifact runs rolled. -/
theorem rolledTrace_eq_augmented (p : Program)
    (hBody : ∀ i ∈ p.body, i.WF p.regCount)
    (count : Nat) (env : Proof.CCEnv)
    (hCounter : env ⟨counterReg p + 1⟩ = some ((0 % M : Nat) : Int)) :
    Proof.evalCCSequence env (rolledTrace p count) =
      Proof.evalCCSequence env
        (foldTrace count
          (fun k => compileInstrs k (Program.counterAugment p).body)) := by
  rw [foldTrace_augment_eq_litSeg p count]
  exact rolledTrace_eq_litSeg p hBody count 0 env hCounter

/-- Typing context for rolled lowering: the padded program at
`loopCount := 1`.  `lowerSequence` consults the function only through
`localType?`, and the preamble plus a single body copy already declares
every local at its (uniform) type, so lowering against this context
produces exactly the statements it would against the full program —
without materializing `loopCount` unrolled body copies at emission
time. -/
def loweringContext (p : Program) (name : String) : CCIR.Function :=
  { p with regCount := p.regCount + 1, loopCount := 1 }.toFn name

/-- Rolled-body statements: the body compiled once at the counter
variable, through the production lowering. -/
def rolledBody (p : Program) (name : String) : Option (List C.CStmt) :=
  match lowerSequence (loweringContext p name)
      (compileInstrsVar p p.body) with
  | .ok statements => some statements
  | .error _ => none

/-- The rolled C function: declarations, init, one `while` loop with a
counter increment, return. Emission-only — semantics stays `foldTrace`. -/
def rolledCFunction (p : Program) (name : String) : Option C.CFunction := do
  let bodyStatements ← rolledBody p name
  let initStatements ←
    match lowerSequence (loweringContext p name)
        (preamble p.regCount ++ compileInstrs 0 p.init) with
    | .ok statements => some statements
    | .error _ => none
  let epilogueStatements ←
    match lowerSequence (loweringContext p name)
        (compileInstrs 0 p.epilogue) with
    | .ok statements => some statements
    | .error _ => none
  let counter : C.CExpr :=
    .var (ABI.localName (counterReg p + 1)) .u64
  some {
    name := ABI.mangle name
    params := #[]
    result := .u64
    body :=
      #[C.CStmt.decl .u8 (ABI.localName 0) none] ++
      ((Array.range p.regCount).map fun i =>
        C.CStmt.decl .u64 (ABI.localName (i + 1)) none) ++
      #[.decl .u64 (ABI.localName (counterReg p + 1))
          (some (.uintLit .u64 0))] ++
      initStatements.toArray ++
      #[.whileLoop (.binary .u8 .lt counter
          (.uintLit .u64 p.loopCount))
        (bodyStatements.toArray.push
          (.assign counter
            (.binary .u64 .add counter (.uintLit .u64 1))))] ++
      epilogueStatements.toArray ++
      #[.return (some (.var (ABI.localName (p.output + 1)) .u64))]
    sourceDecl := some name
  }

/-- Emit the rolled function as a checked translation unit. -/
def emitRolled (p : Program) (name : String) : Except (Array String) String := do
  match rolledCFunction p name with
  | none => throw #["rolled lowering failed"]
  | some fn =>
      match C.emitChecked .portable {
        -- No `lean_*` call is emitted, so `<lean/lean.h>` is omitted; see
        -- the note in `LeanCompCert/Lower/Pure.lean`.
        includes := #["stdint.h", "stddef.h"]
        functions := #[fn]
        externals := #[{
          name := fn.name
          params := #[]
          result := .u64
          trusted := true
        }]
      } with
      | .ok source => pure source
      | .error errors => throw (errors.map fun e => e.pretty)

end LeanCompCert.Verified.Reflect
