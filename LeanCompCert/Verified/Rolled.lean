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

/-! ## The rolled C function

Emission is unchanged, byte for byte.  What is new is that every piece of it
now has a name, so the theorems below can be about the emitted statements
themselves rather than about a paraphrase of them. -/

/-- The padded program: one more register (the loop counter), and a single
loop iteration.  Only its *typing* is used. -/
def loweringProgram (p : Program) : Program :=
  { p with regCount := p.regCount + 1, loopCount := 1 }

/-- Typing context for rolled lowering: the padded program at
`loopCount := 1`.  `lowerSequence` consults the function only through
`localType?`, and the preamble plus a single body copy already declares
every local at its (uniform) type, so lowering against this context
produces exactly the statements it would against the full program —
without materializing `loopCount` unrolled body copies at emission
time. -/
def loweringContext (p : Program) (name : String) : CCIR.Function :=
  (loweringProgram p).toFn name

/-- One rolled iteration, at CCIR level: the body compiled once against the
counter *variable*, followed by the counter increment.  This is the block the
emitted `while` body is the lowering of, and the block `rolledTrace` repeats. -/
def rolledBlock (p : Program) : List StraightInstruction :=
  compileInstrsVar p p.body ++ [incInstr p]

theorem rolledTrace_succ (p : Program) (count : Nat) :
    rolledTrace p (count + 1) = rolledBlock p ++ rolledTrace p count := rfl

/-- The straight-line prologue: zero the scratch and every register, then run
`init`. -/
def rolledPrologue (p : Program) : List StraightInstruction :=
  preamble p.regCount ++ compileInstrs 0 p.init

def rolledEpilogue (p : Program) : List StraightInstruction :=
  compileInstrs 0 p.epilogue

private def okOption {ε α : Type _} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- The counter's C variable. -/
def counterExpr (p : Program) : C.CExpr :=
  .var (ABI.localName (counterReg p + 1)) .u64

/-- The emitted loop guard, `v_counter < UINT64_C(loopCount)`, whose value has
the validator's `u8` comparison type. -/
def rolledGuard (p : Program) : C.CExpr :=
  .binary .u8 .lt (counterExpr p) (.uintLit .u64 p.loopCount)

/-- The declarations the rolled function opens with: the comparison scratch,
one per register, and the counter — the only one with an initialiser. -/
def rolledDecls (p : Program) : Array C.CStmt :=
  #[C.CStmt.decl .u8 (ABI.localName 0) none] ++
  ((Array.range p.regCount).map fun i =>
    C.CStmt.decl .u64 (ABI.localName (i + 1)) none) ++
  #[.decl .u64 (ABI.localName (counterReg p + 1)) (some (.uintLit .u64 0))]

/-- **The rolled function's body, minus the `return`.**  Declarations, the
lowered prologue, one `while` loop, the lowered epilogue.  Every statement here
is inside the proved C model (`Proof.evalCSequenceFuel`). -/
def rolledFunctionBody (p : Program) (name : String) :
    Option (Array C.CStmt) := do
  let bodyStatements ←
    okOption (lowerSequence (loweringContext p name) (rolledBlock p))
  let initStatements ←
    okOption (lowerSequence (loweringContext p name) (rolledPrologue p))
  let epilogueStatements ←
    okOption (lowerSequence (loweringContext p name) (rolledEpilogue p))
  some (
    rolledDecls p ++
    initStatements.toArray ++
    #[.whileLoop (rolledGuard p) bodyStatements.toArray] ++
    epilogueStatements.toArray)

/-- The rolled C function: declarations, init, one `while` loop with a
counter increment, return. -/
def rolledCFunction (p : Program) (name : String) : Option C.CFunction := do
  let body ← rolledFunctionBody p name
  some {
    name := ABI.mangle name
    params := #[]
    result := .u64
    body := body.push (.return (some (.var (ABI.localName (p.output + 1)) .u64)))
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

/-! ## The proved C model of the rolled function

Everything above is emission.  Everything below relates the *emitted
statements* — the declarations, the prologue, the `while` loop and the
epilogue, as `C.CStmt`s — to the counter-augmented program's denotation, inside
`Proof.PureSemantics`.  The result is that `rolledLoop` is covered by the
proved chain exactly as `provedStraightLine` is, without the unrolled
statements ever being materialised.

The shape of `while` this needs, and all this covers, is stated at
`Proof.evalCWhile`: a counted loop with a `u64` counter register, a fixed
literal trip count, and an assignment-only body. -/

/-- **The proved restricted-C model of the emitted rolled function.**

Run the emitted statements from the empty environment and read the variable the
emitted `return` reads.  The iteration budget is `loopCount + 1`: one unit per
iteration plus one for the exit test — exactly what the counted loop needs.  A
short budget makes the model `none`, never wrong. -/
def rolledResult (p : Program) (name : String) : Option Int := do
  let body ← rolledFunctionBody p name
  let env ←
    Proof.evalCSequenceFuel (p.loopCount + 1) Verified.emptyCEnv body.toList
  env (ABI.localName (p.output + 1))

/-- The counter's zero initialisation at CCIR level; the emitted C does it with
the counter declaration's initialiser. -/
def counterZero (p : Program) : StraightInstruction :=
  .assign (regLocal (counterReg p)) (.uintLit .u64 0)

/-- **The CCIR trace the rolled C function realises.**  Counter zeroing,
prologue, `loopCount` copies of the rolled block, epilogue. -/
def rolledInstrs (p : Program) : List StraightInstruction :=
  [counterZero p] ++ rolledPrologue p ++ rolledTrace p p.loopCount ++
    rolledEpilogue p

/-! ### Widening: `p`'s programs are well formed with one more register -/

theorem operandWF_widen {a b : Nat} (h : a ≤ b) :
    ∀ {o : Operand}, o.WF a → o.WF b
  | .reg _, hi => Nat.lt_of_lt_of_le hi h
  | .lit _, _ => trivial
  | .idx, _ => trivial

theorem instrWF_widen {a b : Nat} (h : a ≤ b) :
    ∀ {i : Instr}, i.WF a → i.WF b
  | .mov _ _, ⟨hd, hs⟩ => ⟨Nat.lt_of_lt_of_le hd h, operandWF_widen h hs⟩
  | .binop _ _ _ _, ⟨hd, hl, hr⟩ =>
      ⟨Nat.lt_of_lt_of_le hd h, operandWF_widen h hl, operandWF_widen h hr⟩

theorem loweringProgram_WF (p : Program) (hWF : p.WF) :
    (loweringProgram p).WF := by
  obtain ⟨hOut, hInit, hBody, hEpi⟩ := hWF
  exact ⟨Nat.lt_succ_of_lt hOut,
    fun i hi => instrWF_widen (Nat.le_succ _) (hInit i hi),
    fun i hi => instrWF_widen (Nat.le_succ _) (hBody i hi),
    fun i hi => instrWF_widen (Nat.le_succ _) (hEpi i hi)⟩

/-- The counter-augmented program is well formed whenever `p` is: the extra
register is the counter, and the extra instruction only touches it. -/
theorem counterAugment_WF (p : Program) (hWF : p.WF) :
    (p.counterAugment).WF := by
  obtain ⟨hOut, hInit, hBody, hEpi⟩ := hWF
  refine ⟨Nat.lt_succ_of_lt hOut,
    fun i hi => instrWF_widen (Nat.le_succ _) (hInit i hi), ?_,
    fun i hi => instrWF_widen (Nat.le_succ _) (hEpi i hi)⟩
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact instrWF_widen (Nat.le_succ _) (hBody i h)
  · simp only [List.mem_singleton] at h
    subst h
    exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _, trivial⟩

/-! ### The three emitted segments lower structurally -/

theorem srcOp_compileOperandVar (p : Program) (operand : Operand)
    (hWF : operand.WF p.regCount) :
    SrcOp (p.regCount + 1) (compileOperandVar p operand) := by
  cases operand with
  | reg i => exact .reg i (Nat.lt_succ_of_lt hWF)
  | lit value => exact .lit value
  | idx =>
      exact .reg (counterReg p)
        (show p.regCount < p.regCount + 1 from Nat.lt_succ_self _)

theorem shape_compileInstrVar (p : Program) (instr : Instr)
    (hWF : instr.WF p.regCount) :
    ∀ si ∈ compileInstrVar p instr, Shape (p.regCount + 1) si := by
  cases instr with
  | mov dest src =>
      intro si hMem
      obtain ⟨hDest, hSrc⟩ := hWF
      simp only [compileInstrVar, List.mem_singleton] at hMem
      subst hMem
      exact .assignReg dest _ (srcOp_compileOperandVar p src hSrc)
  | binop dest op lhs rhs =>
      intro si hMem
      obtain ⟨hDest, hLhs, hRhs⟩ := hWF
      cases hArith : op.arithmetic? with
      | some arith =>
          rw [show compileInstrVar p (.binop dest op lhs rhs) =
            [.binary (regLocal dest) arith
              (compileOperandVar p lhs) (compileOperandVar p rhs)] from by
              show (match op.arithmetic?, op.comparison? with
                | some arith, _ =>
                    [StraightInstruction.binary (regLocal dest) arith
                      (compileOperandVar p lhs) (compileOperandVar p rhs)]
                | none, some comparison =>
                    [StraightInstruction.compare scratchLocal comparison
                      (compileOperandVar p lhs) (compileOperandVar p rhs),
                     StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                | none, none => []) = _
              rw [hArith]] at hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact .binary dest arith _ _
            (srcOp_compileOperandVar p lhs hLhs)
            (srcOp_compileOperandVar p rhs hRhs)
      | none =>
          cases hCmp : op.comparison? with
          | none =>
              exfalso
              cases op <;> simp [Op.arithmetic?] at hArith <;>
                simp [Op.comparison?] at hCmp
          | some cmp =>
              rw [show compileInstrVar p (.binop dest op lhs rhs) =
                [.compare scratchLocal cmp
                  (compileOperandVar p lhs) (compileOperandVar p rhs),
                 .cast (regLocal dest) (.local ⟨0⟩)] from by
                  show (match op.arithmetic?, op.comparison? with
                    | some arith, _ =>
                        [StraightInstruction.binary (regLocal dest) arith
                          (compileOperandVar p lhs) (compileOperandVar p rhs)]
                    | none, some comparison =>
                        [StraightInstruction.compare scratchLocal comparison
                          (compileOperandVar p lhs) (compileOperandVar p rhs),
                         StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                    | none, none => []) = _
                  rw [hArith, hCmp]] at hMem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
              cases hMem with
              | inl hCompare =>
                  subst hCompare
                  exact .compare cmp _ _
                    (srcOp_compileOperandVar p lhs hLhs)
                    (srcOp_compileOperandVar p rhs hRhs)
              | inr hCast =>
                  subst hCast
                  exact .cast dest

theorem shape_compileInstrsVar (p : Program) (instrs : List Instr)
    (hWF : ∀ i ∈ instrs, i.WF p.regCount) :
    ∀ si ∈ compileInstrsVar p instrs, Shape (p.regCount + 1) si := by
  intro si hMem
  simp only [compileInstrsVar, List.mem_flatMap] at hMem
  obtain ⟨instr, hInstr, hSi⟩ := hMem
  exact shape_compileInstrVar p instr (hWF instr hInstr) si hSi

theorem shape_rolledBlock (p : Program) (hWF : p.WF) :
    ∀ si ∈ rolledBlock p, Shape (p.regCount + 1) si := by
  intro si hMem
  rcases List.mem_append.mp hMem with h | h
  · exact shape_compileInstrsVar p p.body hWF.2.2.1 si h
  · simp only [List.mem_singleton] at h
    subst h
    exact .binary (counterReg p) .add _ _
      (.reg (counterReg p) (Nat.lt_succ_self _)) (.lit 1)

theorem shape_rolledPrologue (p : Program) (hWF : p.WF) :
    ∀ si ∈ rolledPrologue p, Shape (p.regCount + 1) si := by
  intro si hMem
  rcases List.mem_append.mp hMem with h | h
  · exact Shape.widen (Nat.le_succ _) (shape_preamble p.regCount si h)
  · exact Shape.widen (Nat.le_succ _)
      (shape_compileInstrs 0 p.init hWF.2.1 si h)

theorem shape_rolledEpilogue (p : Program) (hWF : p.WF) :
    ∀ si ∈ rolledEpilogue p, Shape (p.regCount + 1) si := fun si h =>
  Shape.widen (Nat.le_succ _) (shape_compileInstrs 0 p.epilogue hWF.2.2.2 si h)

theorem lowered_rolledBlock (p : Program) (name : String) (hWF : p.WF) :
    lowerSequence (loweringContext p name) (rolledBlock p) =
      .ok ((rolledBlock p).map compiledStmt) :=
  lowerSequence_shapes (loweringProgram p) name (loweringProgram_WF p hWF)
    (rolledBlock p) (shape_rolledBlock p hWF)

theorem lowered_rolledPrologue (p : Program) (name : String) (hWF : p.WF) :
    lowerSequence (loweringContext p name) (rolledPrologue p) =
      .ok ((rolledPrologue p).map compiledStmt) :=
  lowerSequence_shapes (loweringProgram p) name (loweringProgram_WF p hWF)
    (rolledPrologue p) (shape_rolledPrologue p hWF)

theorem lowered_rolledEpilogue (p : Program) (name : String) (hWF : p.WF) :
    lowerSequence (loweringContext p name) (rolledEpilogue p) =
      .ok ((rolledEpilogue p).map compiledStmt) :=
  lowerSequence_shapes (loweringProgram p) name (loweringProgram_WF p hWF)
    (rolledEpilogue p) (shape_rolledEpilogue p hWF)

/-- The emitted body, spelled out.  Note that the `while` body is the lowering
of `rolledBlock`, increment included: the increment statement the emitter
writes is exactly what the production lowering makes of `incInstr`. -/
theorem rolledFunctionBody_eq (p : Program) (name : String) (hWF : p.WF) :
    rolledFunctionBody p name = some (
      rolledDecls p ++
      ((rolledPrologue p).map compiledStmt).toArray ++
      #[.whileLoop (rolledGuard p) ((rolledBlock p).map compiledStmt).toArray] ++
      ((rolledEpilogue p).map compiledStmt).toArray) := by
  unfold rolledFunctionBody
  rw [lowered_rolledBlock p name hWF, lowered_rolledPrologue p name hWF,
    lowered_rolledEpilogue p name hWF]
  rfl

/-! ### Numeric facts about the emitted guard -/

theorem normalize_u64_natCast (n : Nat) :
    Proof.normalize C.CType.u64 ((n : Nat) : Int) = some ((n % M : Nat) : Int) :=
  (Proof.normalize_lowerType CCIR.CCType.u64 ((n : Nat) : Int)).trans
    (normalizeCC_u64_natCast n)

private theorem normalize_u8 (n : Nat) (h : n < 2 ^ 8) :
    Proof.normalize C.CType.u8 ((n : Nat) : Int) = some ((n : Nat) : Int) := by
  rw [show Proof.normalize C.CType.u8 ((n : Nat) : Int) =
      Proof.normalizeCC CCIR.CCType.u8 ((n : Nat) : Int) from
    Proof.normalize_lowerType CCIR.CCType.u8 _, normalizeCC_u8_def]
  exact congrArg some
    ((Int.natCast_emod n (2 ^ 8)).symm.trans
      (congrArg _ (Nat.mod_eq_of_lt h)))

private theorem evalCExpr_binary (env : Proof.CEnv) (t : C.CType)
    (op : C.CBinaryOp) (a b : C.CExpr) (x y : Int)
    (ha : Proof.evalCExpr env a = some x)
    (hb : Proof.evalCExpr env b = some y) :
    Proof.evalCExpr env (.binary t op a b) = Proof.evalBinary t op x y := by
  show (Proof.evalCExpr env a).bind (fun x =>
    (Proof.evalCExpr env b).bind (fun y => Proof.evalBinary t op x y)) = _
  rw [ha, hb]
  rfl

/-- The guard's value, at any counter value below the modulus. -/
theorem evalCExpr_rolledGuard (p : Program) (cEnv : Proof.CEnv) (k : Nat)
    (hCount : p.loopCount < M)
    (hCounter : cEnv (ABI.localName (counterReg p + 1)) = some ((k : Nat) : Int)) :
    Proof.evalCExpr cEnv (rolledGuard p) =
      some (if k < p.loopCount then 1 else 0) := by
  show Proof.evalCExpr cEnv
    (.binary .u8 .lt (counterExpr p) (.uintLit .u64 p.loopCount)) = _
  rw [evalCExpr_binary cEnv .u8 .lt (counterExpr p) (.uintLit .u64 p.loopCount)
    ((k : Nat) : Int) ((p.loopCount : Nat) : Int) hCounter
    (by
      show Proof.normalize C.CType.u64 ((p.loopCount : Nat) : Int) = _
      rw [normalize_u64_natCast, Nat.mod_eq_of_lt hCount])]
  show Proof.normalize C.CType.u8
      (if ((k : Nat) : Int) < ((p.loopCount : Nat) : Int) then 1 else 0) = _
  by_cases hlt : k < p.loopCount
  · rw [if_pos (by exact_mod_cast hlt), if_pos hlt]
    exact normalize_u8 1 (by decide)
  · rw [if_neg (by exact_mod_cast hlt), if_neg hlt]
    exact normalize_u8 0 (by decide)

/-! ### The rolled block advances the counter by one -/

theorem rolledBlock_counter (p : Program)
    (hBody : ∀ i ∈ p.body, i.WF p.regCount) (start : Nat)
    (env envOut : Proof.CCEnv)
    (hCounter : env ⟨counterReg p + 1⟩ = some ((start % M : Nat) : Int))
    (hRun : Proof.evalCCSequence env (rolledBlock p) = some envOut) :
    envOut ⟨counterReg p + 1⟩ = some (((start + 1) % M : Nat) : Int) := by
  unfold rolledBlock at hRun
  rw [Proof.evalCCSequence_append,
    evalCCSequence_var_eq_lit p start p.body hBody env hCounter] at hRun
  cases hBodyRun : Proof.evalCCSequence env (compileInstrs start p.body) with
  | none => rw [hBodyRun] at hRun; exact absurd hRun (by simp)
  | some envBody =>
      rw [hBodyRun] at hRun
      replace hRun : Proof.evalCCSequence envBody [incInstr p] =
        some envOut := hRun
      have hBodyCounter : envBody ⟨counterReg p + 1⟩ =
          some ((start % M : Nat) : Int) := by
        rw [lit_preserves_counter p start p.body hBody env envBody hBodyRun]
        exact hCounter
      rw [inc_step p envBody start hBodyCounter] at hRun
      injection hRun with h
      rw [← h]
      simp [Proof.CCEnv.set]

/-! ### The loop -/

private def LoopInv (p : Program) (remaining : Nat) (cEnv : Proof.CEnv) :
    Prop :=
  remaining ≤ p.loopCount ∧
    ∃ ccEnv : Proof.CCEnv, Proof.EnvRel ccEnv cEnv ∧
      ccEnv ⟨counterReg p + 1⟩ = some (((p.loopCount - remaining : Nat)) : Int)

/-- **The guard discharge.**  Under the counter invariant, the emitted `while`
runs exactly `loopCount` copies of its body — no more, no fewer. -/
theorem evalCWhile_rolled (p : Program) (name : String) (hWF : p.WF)
    (hCount : p.loopCount < M)
    (ccEnv : Proof.CCEnv) (cEnv : Proof.CEnv)
    (hRel : Proof.EnvRel ccEnv cEnv)
    (hCounter : ccEnv ⟨counterReg p + 1⟩ = some ((0 : Nat) : Int)) :
    Proof.evalCWhile (rolledGuard p) ((rolledBlock p).map compiledStmt)
        (p.loopCount + 1) cEnv =
      Proof.evalCSequence cEnv
        (Proof.repeatStmts ((rolledBlock p).map compiledStmt) p.loopCount) := by
  have hWFs := wellFormed_shapes (loweringProgram p) name
    (loweringProgram_WF p hWF) (rolledBlock p) (shape_rolledBlock p hWF)
  refine Proof.evalCWhile_unroll _ _ (LoopInv p) ?_ ?_ ?_ p.loopCount cEnv
    ⟨Nat.le_refl _, ccEnv, hRel, by rw [Nat.sub_self]; exact hCounter⟩
  · rintro env ⟨_, cc, hcc, hctr⟩
    rw [evalCExpr_rolledGuard p env (p.loopCount - 0) hCount
      (by rw [hcc ⟨counterReg p + 1⟩]; exact hctr), if_neg (by omega)]
  · rintro remaining env ⟨hLe, cc, hcc, hctr⟩
    refine ⟨1, ?_, by decide⟩
    rw [evalCExpr_rolledGuard p env (p.loopCount - (remaining + 1)) hCount
      (by rw [hcc ⟨counterReg p + 1⟩]; exact hctr), if_pos (by omega)]
  · rintro remaining env next ⟨hLe, cc, hcc, hctr⟩ hRun
    have hRes := Proof.lowerSequence_correct (loweringContext p name)
      (rolledBlock p) ((rolledBlock p).map compiledStmt) cc env hcc hWFs
      (lowered_rolledBlock p name hWF)
    cases hccRun : Proof.evalCCSequence cc (rolledBlock p) with
    | none =>
        rw [hccRun, hRun] at hRes
        exact absurd hRes (by simp [Proof.ResultsRel])
    | some ccNext =>
        rw [hccRun, hRun] at hRes
        refine ⟨Nat.le_of_succ_le hLe, ccNext, hRes, ?_⟩
        have hStart : (p.loopCount - (remaining + 1)) % M =
            p.loopCount - (remaining + 1) := Nat.mod_eq_of_lt (by omega)
        have := rolledBlock_counter p hWF.2.2.1 (p.loopCount - (remaining + 1))
          cc ccNext (by rw [hStart]; exact hctr) hccRun
        rw [show (p.loopCount - (remaining + 1) + 1) % M =
            p.loopCount - remaining from by
          rw [show p.loopCount - (remaining + 1) + 1 = p.loopCount - remaining
            from by omega]
          exact Nat.mod_eq_of_lt (by omega)] at this
        exact this

theorem lowerSequence_rolledTrace (p : Program) (name : String) (hWF : p.WF) :
    ∀ count : Nat,
      lowerSequence (loweringContext p name) (rolledTrace p count) =
        .ok (Proof.repeatStmts ((rolledBlock p).map compiledStmt) count) := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [rolledTrace_succ, Proof.repeatStmts_succ]
      exact Proof.lowerSequence_append (loweringContext p name)
        (rolledBlock p) (rolledTrace p count) _ _
        (lowered_rolledBlock p name hWF) ih

theorem rolledTrace_mem (p : Program) :
    ∀ (count : Nat), ∀ si ∈ rolledTrace p count, si ∈ rolledBlock p := by
  intro count
  induction count with
  | zero => intro si hMem; exact absurd hMem (by simp [rolledTrace])
  | succ count ih =>
      intro si hMem
      rw [rolledTrace_succ] at hMem
      rcases List.mem_append.mp hMem with h | h
      · exact h
      · exact ih si h

/-- **The loop, related to the CCIR trace.**  The emitted `while` and
`loopCount` copies of the rolled block reach related states. -/
theorem rolledLoop_resultsRel (p : Program) (name : String) (hWF : p.WF)
    (hCount : p.loopCount < M)
    (ccEnv : Proof.CCEnv) (cEnv : Proof.CEnv)
    (hRel : Proof.EnvRel ccEnv cEnv)
    (hCounter : ccEnv ⟨counterReg p + 1⟩ = some ((0 : Nat) : Int)) :
    Proof.ResultsRel
      (Proof.evalCCSequence ccEnv (rolledTrace p p.loopCount))
      (Proof.evalCWhile (rolledGuard p) ((rolledBlock p).map compiledStmt)
        (p.loopCount + 1) cEnv) := by
  rw [evalCWhile_rolled p name hWF hCount ccEnv cEnv hRel hCounter]
  exact Proof.lowerSequence_correct (loweringContext p name)
    (rolledTrace p p.loopCount) _ ccEnv cEnv hRel
    (fun si hSi => wellFormed_shapes (loweringProgram p) name
      (loweringProgram_WF p hWF) (rolledBlock p) (shape_rolledBlock p hWF)
      si (rolledTrace_mem p p.loopCount si hSi))
    (lowerSequence_rolledTrace p name hWF p.loopCount)

/-! ### The declarations -/

private theorem evalCSequence_declNone :
    ∀ (l : List Nat) (env : Proof.CEnv),
      Proof.evalCSequence env
          (l.map fun i => C.CStmt.decl .u64 (ABI.localName (i + 1)) none) =
        some env := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons i rest ih =>
      intro env
      show (Proof.evalCStmt env
          (C.CStmt.decl .u64 (ABI.localName (i + 1)) none)).bind
        (fun e => Proof.evalCSequence e
          (rest.map fun i => C.CStmt.decl .u64 (ABI.localName (i + 1)) none)) =
          some env
      exact ih env

theorem evalCSequence_rolledDecls (p : Program) (env : Proof.CEnv) :
    Proof.evalCSequence env (rolledDecls p).toList =
      some (Proof.CEnv.set env (ABI.localName (counterReg p + 1))
        ((0 : Nat) : Int)) := by
  have hList : (rolledDecls p).toList =
      C.CStmt.decl .u8 (ABI.localName 0) none ::
        (((List.range p.regCount).map fun i =>
            C.CStmt.decl .u64 (ABI.localName (i + 1)) none) ++
          [C.CStmt.decl .u64 (ABI.localName (counterReg p + 1))
            (some (.uintLit .u64 0))]) := by
    simp [rolledDecls]
  rw [hList]
  show (Proof.evalCStmt env (C.CStmt.decl .u8 (ABI.localName 0) none)).bind
    (fun e => Proof.evalCSequence e _) = _
  show Proof.evalCSequence env _ = _
  rw [Proof.evalCSequence_append, evalCSequence_declNone _ env]
  show (Proof.evalCStmt env (C.CStmt.decl .u64
      (ABI.localName (counterReg p + 1)) (some (.uintLit .u64 0)))).bind
    (fun e => Proof.evalCSequence e []) = _
  show ((Proof.evalCExpr env (.uintLit .u64 0)).bind (fun value =>
    (Proof.normalize C.CType.u64 value).bind (fun stored =>
      some (Proof.CEnv.set env (ABI.localName (counterReg p + 1))
        stored)))).bind (fun e => Proof.evalCSequence e []) = _
  rw [show Proof.evalCExpr env (.uintLit .u64 (0 : Nat)) =
      some (((0 : Nat) : Nat) : Int) from by
    show Proof.normalize C.CType.u64 (((0 : Nat) : Nat) : Int) = _
    rw [normalize_u64_natCast, Nat.zero_mod]]
  show ((Proof.normalize C.CType.u64 (((0 : Nat) : Nat) : Int)).bind
    (fun stored => some (Proof.CEnv.set env
      (ABI.localName (counterReg p + 1)) stored))).bind
      (fun e => Proof.evalCSequence e []) = _
  rw [normalize_u64_natCast, Nat.zero_mod]
  rfl

/-! ### The prologue preserves the counter -/

theorem rolledPrologue_counter (p : Program) (hWF : p.WF)
    (env envOut : Proof.CCEnv)
    (hRun : Proof.evalCCSequence env (rolledPrologue p) = some envOut) :
    envOut ⟨counterReg p + 1⟩ = env ⟨counterReg p + 1⟩ := by
  unfold rolledPrologue at hRun
  rw [Proof.evalCCSequence_append] at hRun
  cases hMid : Proof.evalCCSequence env (preamble p.regCount) with
  | none => rw [hMid] at hRun; exact absurd hRun (by simp)
  | some envMid =>
      rw [hMid] at hRun
      replace hRun : Proof.evalCCSequence envMid (compileInstrs 0 p.init) =
        some envOut := hRun
      rw [lit_preserves_counter p 0 p.init hWF.2.1 envMid envOut hRun]
      exact preamble_preserves ⟨counterReg p + 1⟩
        (by intro h; exact Nat.noConfusion (congrArg CCIR.LocalId.value h))
        p.regCount
        (by
          intro i hi h
          have : counterReg p + 1 = i + 1 := congrArg CCIR.LocalId.value h
          unfold counterReg at this
          omega)
        env envMid hMid

/-! ### Assembly -/

private theorem read_of_resultsRel {ccR : Option Proof.CCEnv}
    {cR : Option Proof.CEnv} (h : Proof.ResultsRel ccR cR)
    (id : CCIR.LocalId) :
    (cR.bind (fun env => env (ABI.localName id.value))) =
      ccR.bind (fun env => env id) := by
  cases ccR with
  | none =>
      cases cR with
      | none => rfl
      | some c => exact absurd h (by simp [Proof.ResultsRel])
  | some cc =>
      cases cR with
      | none => exact absurd h (by simp [Proof.ResultsRel])
      | some c => exact h id

/-- **The rolled artifact's C model tracks its CCIR trace.** -/
theorem rolled_resultsRel (p : Program) (name : String) (hWF : p.WF)
    (hCount : p.loopCount < M) :
    Proof.ResultsRel
      (Proof.evalCCSequence Verified.emptyCCEnv (rolledInstrs p))
      (Proof.evalCSequenceFuel (p.loopCount + 1) Verified.emptyCEnv
        ((rolledDecls p ++
          ((rolledPrologue p).map compiledStmt).toArray ++
          #[.whileLoop (rolledGuard p)
              ((rolledBlock p).map compiledStmt).toArray] ++
          ((rolledEpilogue p).map compiledStmt).toArray) : Array C.CStmt).toList) := by
  have hDeclsFree : ∀ stmt ∈ (rolledDecls p).toList, Proof.LoopFree stmt := by
    intro stmt hMem
    have hList : (rolledDecls p).toList =
        C.CStmt.decl .u8 (ABI.localName 0) none ::
          (((List.range p.regCount).map fun i =>
              C.CStmt.decl .u64 (ABI.localName (i + 1)) none) ++
            [C.CStmt.decl .u64 (ABI.localName (counterReg p + 1))
              (some (.uintLit .u64 0))]) := by
      simp [rolledDecls]
    rw [hList] at hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · trivial
    · rcases List.mem_append.mp hMem with h | h
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        trivial
      · simp only [List.mem_singleton] at h
        subst h
        trivial
  have hProFree : ∀ stmt ∈ ((rolledPrologue p).map compiledStmt),
      Proof.LoopFree stmt :=
    Proof.lowerSequence_loopFree (loweringContext p name) (rolledPrologue p) _
      (lowered_rolledPrologue p name hWF)
  have hEpiFree : ∀ stmt ∈ ((rolledEpilogue p).map compiledStmt),
      Proof.LoopFree stmt :=
    Proof.lowerSequence_loopFree (loweringContext p name) (rolledEpilogue p) _
      (lowered_rolledEpilogue p name hWF)
  -- Split both sides into their four segments.
  rw [show ((rolledDecls p ++
        ((rolledPrologue p).map compiledStmt).toArray ++
        #[C.CStmt.whileLoop (rolledGuard p)
            ((rolledBlock p).map compiledStmt).toArray] ++
        ((rolledEpilogue p).map compiledStmt).toArray) : Array C.CStmt).toList =
      (((rolledDecls p).toList ++ ((rolledPrologue p).map compiledStmt)) ++
        [C.CStmt.whileLoop (rolledGuard p)
          ((rolledBlock p).map compiledStmt).toArray]) ++
        ((rolledEpilogue p).map compiledStmt) from by simp]
  show Proof.ResultsRel
    (Proof.evalCCSequence Verified.emptyCCEnv
      ((([counterZero p] ++ rolledPrologue p) ++ rolledTrace p p.loopCount) ++
        rolledEpilogue p)) _
  rw [Proof.evalCCSequence_append, Proof.evalCCSequence_append,
    Proof.evalCCSequence_append, Proof.evalCSequenceFuel_append,
    Proof.evalCSequenceFuel_append, Proof.evalCSequenceFuel_append,
    Proof.evalCSequenceFuel_of_loopFree _ _ hDeclsFree,
    evalCSequence_rolledDecls]
  -- The counter is now zero on both sides, and the environments are related.
  have hCounterZero : Proof.evalCCSequence Verified.emptyCCEnv
      [counterZero p] =
        some (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩
          ((0 : Nat) : Int)) := by
    show ((Proof.evalCCAssignStep Verified.emptyCCEnv
      (regLocal (counterReg p)) (.uintLit .u64 0)).bind
        (fun env => Proof.evalCCSequence env [])) = _
    unfold Proof.evalCCAssignStep
    rw [show Proof.evalOperand Verified.emptyCCEnv
        (.uintLit .u64 0 : CCIR.Operand) = some ((0 : Nat) : Int) from
      normalizeCC_u64_natCast 0]
    rfl
  rw [hCounterZero]
  simp only [mbind_some]
  have hRel1 : Proof.EnvRel
      (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩ ((0 : Nat) : Int))
      (Proof.CEnv.set Verified.emptyCEnv (ABI.localName (counterReg p + 1))
        ((0 : Nat) : Int)) :=
    Proof.EnvRel.set Verified.emptyEnvRel ⟨counterReg p + 1⟩ ((0 : Nat) : Int)
  have hCtr1 : (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩
      ((0 : Nat) : Int)) ⟨counterReg p + 1⟩ = some ((0 : Nat) : Int) := by
    simp [Proof.CCEnv.set]
  -- Prologue.
  rw [Proof.evalCSequenceFuel_of_loopFree _ _ hProFree]
  have hPro := Proof.lowerSequence_correct (loweringContext p name)
    (rolledPrologue p) _ _ _ hRel1
    (wellFormed_shapes (loweringProgram p) name (loweringProgram_WF p hWF)
      (rolledPrologue p) (shape_rolledPrologue p hWF))
    (lowered_rolledPrologue p name hWF)
  cases hProCC : Proof.evalCCSequence
      (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩
        ((0 : Nat) : Int)) (rolledPrologue p) with
  | none =>
      rw [hProCC] at hPro
      cases hProC : Proof.evalCSequence
          (Proof.CEnv.set Verified.emptyCEnv
            (ABI.localName (counterReg p + 1)) ((0 : Nat) : Int))
          ((rolledPrologue p).map compiledStmt) with
      | none => trivial
      | some c => rw [hProC] at hPro; exact absurd hPro (by simp [Proof.ResultsRel])
  | some cc2 =>
      rw [hProCC] at hPro
      cases hProC : Proof.evalCSequence
          (Proof.CEnv.set Verified.emptyCEnv
            (ABI.localName (counterReg p + 1)) ((0 : Nat) : Int))
          ((rolledPrologue p).map compiledStmt) with
      | none => rw [hProC] at hPro; exact absurd hPro (by simp [Proof.ResultsRel])
      | some c2 =>
          rw [hProC] at hPro
          simp only [mbind_some]
          have hCtr2 : cc2 ⟨counterReg p + 1⟩ = some ((0 : Nat) : Int) := by
            rw [rolledPrologue_counter p hWF _ _ hProCC]
            exact hCtr1
          -- Loop.
          have hLoop := rolledLoop_resultsRel p name hWF hCount cc2 c2 hPro hCtr2
          show Proof.ResultsRel
            ((Proof.evalCCSequence cc2 (rolledTrace p p.loopCount)).bind
              (fun env => Proof.evalCCSequence env (rolledEpilogue p)))
            ((Proof.evalCSequenceFuel (p.loopCount + 1) c2
              [C.CStmt.whileLoop (rolledGuard p)
                ((rolledBlock p).map compiledStmt).toArray]).bind
              (fun env => Proof.evalCSequenceFuel (p.loopCount + 1) env
                ((rolledEpilogue p).map compiledStmt)))
          rw [show Proof.evalCSequenceFuel (p.loopCount + 1) c2
              [C.CStmt.whileLoop (rolledGuard p)
                ((rolledBlock p).map compiledStmt).toArray] =
            Proof.evalCWhile (rolledGuard p)
              ((rolledBlock p).map compiledStmt) (p.loopCount + 1) c2 from by
            show (Proof.evalCWhile (rolledGuard p)
                (((rolledBlock p).map compiledStmt).toArray.toList)
                (p.loopCount + 1) c2).bind (fun env => some env) = _
            simp]
          cases hLoopCC : Proof.evalCCSequence cc2 (rolledTrace p p.loopCount) with
          | none =>
              rw [hLoopCC] at hLoop
              cases hLoopC : Proof.evalCWhile (rolledGuard p)
                  ((rolledBlock p).map compiledStmt) (p.loopCount + 1) c2 with
              | none => trivial
              | some c => rw [hLoopC] at hLoop; exact absurd hLoop (by simp [Proof.ResultsRel])
          | some cc3 =>
              rw [hLoopCC] at hLoop
              cases hLoopC : Proof.evalCWhile (rolledGuard p)
                  ((rolledBlock p).map compiledStmt) (p.loopCount + 1) c2 with
              | none => rw [hLoopC] at hLoop; exact absurd hLoop (by simp [Proof.ResultsRel])
              | some c3 =>
                  rw [hLoopC] at hLoop
                  simp only [Option.bind_some]
                  rw [Proof.evalCSequenceFuel_of_loopFree _ _ hEpiFree]
                  exact Proof.lowerSequence_correct (loweringContext p name)
                    (rolledEpilogue p) _ _ _ hLoop
                    (wellFormed_shapes (loweringProgram p) name
                      (loweringProgram_WF p hWF) (rolledEpilogue p)
                      (shape_rolledEpilogue p hWF))
                    (lowered_rolledEpilogue p name hWF)

/-- The rolled artifact's C model equals its CCIR trace's result. -/
theorem rolledResult_eq_ccir (p : Program) (name : String) (hWF : p.WF)
    (hCount : p.loopCount < M) :
    rolledResult p name =
      (Proof.evalCCSequence Verified.emptyCCEnv (rolledInstrs p)).bind
        (fun env => env ⟨p.output + 1⟩) := by
  unfold rolledResult
  rw [rolledFunctionBody_eq p name hWF]
  show (Proof.evalCSequenceFuel (p.loopCount + 1) Verified.emptyCEnv _).bind
    (fun env => env (ABI.localName (p.output + 1))) = _
  exact read_of_resultsRel (rolled_resultsRel p name hWF hCount)
    ⟨p.output + 1⟩

/-! ### From the CCIR trace to the augmented program's denotation -/

theorem evalCCSequence_rolledTail (p : Program) (hWF : p.WF)
    (env : Proof.CCEnv)
    (hCounter : env ⟨counterReg p + 1⟩ = some ((0 % M : Nat) : Int)) :
    Proof.evalCCSequence env
        (compileInstrs 0 p.init ++
          (rolledTrace p p.loopCount ++ rolledEpilogue p)) =
      Proof.evalCCSequence env
        (compileInstrs 0 (p.counterAugment).init ++
          (foldTrace (p.counterAugment).loopCount
              (fun k => compileInstrs k (p.counterAugment).body) ++
            compileInstrs 0 (p.counterAugment).epilogue)) := by
  rw [Proof.evalCCSequence_append, Proof.evalCCSequence_append]
  show (Proof.evalCCSequence env (compileInstrs 0 p.init)).bind _ =
    (Proof.evalCCSequence env (compileInstrs 0 p.init)).bind _
  cases hInit : Proof.evalCCSequence env (compileInstrs 0 p.init) with
  | none => rfl
  | some env2 =>
      simp only [Option.bind_some]
      have hCtr2 : env2 ⟨counterReg p + 1⟩ = some ((0 % M : Nat) : Int) := by
        rw [lit_preserves_counter p 0 p.init hWF.2.1 env env2 hInit]
        exact hCounter
      rw [Proof.evalCCSequence_append, Proof.evalCCSequence_append,
        rolledTrace_eq_augmented p hWF.2.2.1 p.loopCount env2 hCtr2]
      rfl

theorem evalCC_rolledInstrs (p : Program) (hWF : p.WF) :
    (Proof.evalCCSequence Verified.emptyCCEnv (rolledInstrs p)).bind
        (fun env => env ⟨p.output + 1⟩) =
      (p.counterAugment).denote.map (fun n => (n : Int)) := by
  have hCounterZero : Proof.evalCCSequence Verified.emptyCCEnv
      [counterZero p] =
        some (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩
          ((0 : Nat) : Int)) := by
    show ((Proof.evalCCAssignStep Verified.emptyCCEnv
      (regLocal (counterReg p)) (.uintLit .u64 0)).bind
        (fun env => Proof.evalCCSequence env [])) = _
    unfold Proof.evalCCAssignStep
    rw [show Proof.evalOperand Verified.emptyCCEnv
        (.uintLit .u64 0 : CCIR.Operand) = some ((0 : Nat) : Int) from
      normalizeCC_u64_natCast 0]
    rfl
  obtain ⟨env0, hPreamble, hRegs⟩ := preamble_correct p.regCount
    (Proof.CCEnv.set Verified.emptyCCEnv ⟨counterReg p + 1⟩ ((0 : Nat) : Int))
  have hCounter0 : env0 ⟨counterReg p + 1⟩ = some ((0 : Nat) : Int) := by
    rw [preamble_preserves ⟨counterReg p + 1⟩
      (by intro h; exact Nat.noConfusion (congrArg CCIR.LocalId.value h))
      p.regCount
      (by
        intro i hi h
        have : counterReg p + 1 = i + 1 := congrArg CCIR.LocalId.value h
        unfold counterReg at this
        omega)
      _ env0 hPreamble]
    simp [Proof.CCEnv.set]
  have hInv0 : StateInv (p.counterAugment).regCount initialState env0 := by
    refine ⟨?_, fun i _ => M_pos⟩
    intro i hi
    by_cases hEq : i = p.regCount
    · subst hEq
      exact hCounter0
    · exact hRegs i (by
        have : i < p.regCount + 1 := hi
        omega)
  show (Proof.evalCCSequence Verified.emptyCCEnv
    ((([counterZero p] ++ rolledPrologue p) ++ rolledTrace p p.loopCount) ++
      rolledEpilogue p)).bind _ = _
  rw [show (([counterZero p] ++ rolledPrologue p) ++
        rolledTrace p p.loopCount) ++ rolledEpilogue p =
      ([counterZero p] ++ preamble p.regCount) ++
        (compileInstrs 0 p.init ++
          (rolledTrace p p.loopCount ++ rolledEpilogue p)) from by
    unfold rolledPrologue
    simp [List.append_assoc]]
  rw [Proof.evalCCSequence_append, Proof.evalCCSequence_append,
    hCounterZero]
  simp only [mbind_some]
  rw [hPreamble]
  simp only [mbind_some]
  rw [evalCCSequence_rolledTail p hWF env0 (by rw [hCounter0]; rfl)]
  exact Program.evalCC_compileCore (p.counterAugment) (counterAugment_WF p hWF)
    env0 hInv0

/-- **The rolled route, covered.**  The proved restricted-C model of the
emitted `while`-loop function returns exactly the counter-augmented program's
denotation — the same statement `Computation.result_preserved` makes for the
straight-line route, for a translation unit whose size is independent of the
trip count. -/
theorem rolledResult_eq_denote (p : Program) (name : String) (hWF : p.WF)
    (hCount : p.loopCount < M) :
    rolledResult p name = (p.counterAugment).denote.map (fun n => (n : Int)) :=
  (rolledResult_eq_ccir p name hWF hCount).trans (evalCC_rolledInstrs p hWF)

/-- The counter-augmented program's denotation *is* the source result of the
unrolled `Computation` the rolled artifact stands for — for any such
computation, so none has to be built. -/
theorem counterAugment_sourceResult (p : Program) (hWF : p.WF)
    (computation : Verified.Computation)
    (hInstructions : computation.instructions = (p.counterAugment).compile)
    (hOutput : computation.output = ⟨p.output + 1⟩) :
    computation.sourceResult =
      (p.counterAugment).denote.map (fun n => (n : Int)) :=
  sourceResult_eq_denote (p.counterAugment) (counterAugment_WF p hWF)
    computation hInstructions hOutput

end LeanCompCert.Verified.Reflect
