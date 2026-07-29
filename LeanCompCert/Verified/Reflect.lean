import LeanCompCert.Verified.Decide

/-!
# A verified reflection bridge from Lean folds to the proved fragment

This module closes the Lean-to-C bridge for the bounded-fold subset used by
finite `native_decide` certificates: a deep-embedded register program whose

- **denotation** is ordinary Lean `Nat` arithmetic (`Program.denote`), fast
  for the kernel to evaluate; and whose
- **compilation** (`Program.compile`) targets the machine-checked
  `StraightInstruction` fragment,

together with a once-and-for-all structural theorem
(`Program.evalCCSequence_compile`) that the compiled CCIR trace computes
exactly the denotation. Combined with the existing semantic-preservation
theorem, a certificate's `Decision` specification no longer requires
evaluating the CCIR model: the kernel evaluates only the Lean-level fold.

The machine model: registers hold `u64` values (`< 2⁶⁴`); comparison results
are materialized through the validator's `u8` comparison discipline and a
proved widening cast, but denote directly as `0`/`1`. The loop index is a
first-class operand, so a program's body is compiled once per iteration with
the index specialized to a literal — exactly `Proof.foldTrace`.
-/

namespace LeanCompCert.Verified.Reflect

open LeanCompCert
open LeanCompCert.Proof

/-- The `u64` modulus. -/
def M : Nat := 2 ^ 64

/-- Operands: a register, a `u64` literal, or the current loop index. -/
inductive Operand where
  | reg (index : Nat)
  | lit (value : Nat)
  | idx
  deriving Repr, DecidableEq

/-- Register-machine operations, mirroring the proved fragment. -/
inductive Op where
  | add | sub | mul | udiv | urem
  | band | bor | bxor | shl | lshr
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq

/-- Comparison operations produce `0`/`1` and compile through `u8`. -/
def Op.comparison? : Op → Option UnsignedComparison
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .ult
  | .le => some .ule
  | .gt => some .ugt
  | .ge => some .uge
  | _ => none

def Op.arithmetic? : Op → Option UnsignedBinary
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .udiv => some .udiv
  | .urem => some .urem
  | .band => some .bitAnd
  | .bor => some .bitOr
  | .bxor => some .bitXor
  | .shl => some .shl
  | .lshr => some .lshr
  | _ => none

/-- Register-machine instructions. -/
inductive Instr where
  | mov (dest : Nat) (src : Operand)
  | binop (dest : Nat) (op : Op) (lhs rhs : Operand)
  deriving Repr, DecidableEq

/--
A bounded-fold program: an initialization block, a loop body executed with
the index running over `0, …, loopCount − 1`, an epilogue, and an output
register. `regCount` bounds every register index used.
-/
structure Program where
  regCount : Nat
  loopCount : Nat
  init : List Instr
  body : List Instr
  epilogue : List Instr
  output : Nat
  deriving Repr

/-! ## Denotation: plain Lean arithmetic -/

/-- Register states hold `Nat` values; the invariant `s i < M` is maintained
by every write. -/
abbrev RegState := Nat → Nat

def RegState.set (s : RegState) (index value : Nat) : RegState :=
  fun candidate => if candidate = index then value else s candidate

def denoteOperand (index : Nat) (s : RegState) : Operand → Nat
  | .reg i => s i
  | .lit value => value % M
  | .idx => index % M

/-- Operation denotation over `Nat`, mirroring the CCIR scalar model at
`u64` exactly (division and remainder by zero are undefined). -/
def denoteOp : Op → Nat → Nat → Option Nat
  | .add, a, b => some ((a + b) % M)
  | .sub, a, b => some ((a + (M - b)) % M)
  | .mul, a, b => some ((a * b) % M)
  | .udiv, a, b => if b = 0 then none else some ((a / b) % M)
  | .urem, a, b => if b = 0 then none else some ((a % b) % M)
  | .band, a, b => some ((a &&& b) % M)
  | .bor, a, b => some ((a ||| b) % M)
  | .bxor, a, b => some ((a ^^^ b) % M)
  | .shl, a, b => some ((a <<< b) % M)
  | .lshr, a, b => some ((a >>> b) % M)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .ne, a, b => some (if a ≠ b then 1 else 0)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .le, a, b => some (if a ≤ b then 1 else 0)
  | .gt, a, b => some (if a > b then 1 else 0)
  | .ge, a, b => some (if a ≥ b then 1 else 0)

def denoteInstr (index : Nat) (s : RegState) : Instr → Option RegState
  | .mov dest src => some (s.set dest (denoteOperand index s src))
  | .binop dest op lhs rhs => do
      let result ←
        denoteOp op (denoteOperand index s lhs) (denoteOperand index s rhs)
      pure (s.set dest result)

def denoteInstrs (index : Nat) (s : RegState) : List Instr → Option RegState
  | [] => some s
  | instr :: rest => do
      denoteInstrs index (← denoteInstr index s instr) rest

/-- The all-zero initial state. -/
def initialState : RegState := fun _ => 0

def Program.denote (p : Program) : Option Nat := do
  let s ← denoteInstrs 0 initialState p.init
  let s ← (List.range p.loopCount).foldlM
    (fun s index => denoteInstrs index s p.body) s
  let s ← denoteInstrs 0 s p.epilogue
  pure (s p.output)

/-! ## Compilation into the proved fragment -/

/-- Register `i` lives in CCIR local `i + 1`; local `0` is the `u8`
comparison scratch. -/
def regLocal (index : Nat) : CCIR.LocalDecl := {
  id := ⟨index + 1⟩
  type := .u64
}

def scratchLocal : CCIR.LocalDecl := {
  id := ⟨0⟩
  type := .u8
}

def compileOperand (index : Nat) : Operand → CCIR.Operand
  | .reg i => .local ⟨i + 1⟩
  | .lit value => .uintLit .u64 value
  | .idx => .uintLit .u64 index

def compileInstr (index : Nat) : Instr → List StraightInstruction
  | .mov dest src => [.assign (regLocal dest) (compileOperand index src)]
  | .binop dest op lhs rhs =>
      match op.arithmetic?, op.comparison? with
      | some arith, _ =>
          [.binary (regLocal dest) arith
            (compileOperand index lhs) (compileOperand index rhs)]
      | none, some comparison =>
          [.compare scratchLocal comparison
            (compileOperand index lhs) (compileOperand index rhs),
           .cast (regLocal dest) (.local ⟨0⟩)]
      | none, none => []

def compileInstrs (index : Nat) (instrs : List Instr) :
    List StraightInstruction :=
  instrs.flatMap (compileInstr index)

/-- Zero-initialize the comparison scratch and every register, so the
machine state matches `initialState` and every local — including the
scratch — has a typed declaration resolvable by `Lower.localType?`. -/
def preamble (regCount : Nat) : List StraightInstruction :=
  .assign scratchLocal (.uintLit .u8 0) ::
    ((List.range regCount).map fun i =>
      .assign (regLocal i) (.uintLit .u64 0))

def Program.compile (p : Program) : List StraightInstruction :=
  preamble p.regCount ++
    compileInstrs 0 p.init ++
    foldTrace p.loopCount (fun index => compileInstrs index p.body) ++
    compileInstrs 0 p.epilogue

/-! ## Well-formedness -/

def Operand.WF (regCount : Nat) : Operand → Prop
  | .reg i => i < regCount
  | _ => True

instance (regCount : Nat) (operand : Operand) :
    Decidable (operand.WF regCount) := by
  cases operand <;> simp only [Operand.WF] <;> infer_instance

def Instr.WF (regCount : Nat) : Instr → Prop
  | .mov dest src => dest < regCount ∧ src.WF regCount
  | .binop dest _ lhs rhs =>
      dest < regCount ∧ lhs.WF regCount ∧ rhs.WF regCount

instance (regCount : Nat) (instr : Instr) :
    Decidable (instr.WF regCount) := by
  cases instr <;> simp only [Instr.WF] <;> infer_instance

def Program.WF (p : Program) : Prop :=
  p.output < p.regCount ∧
    (∀ instr ∈ p.init, instr.WF p.regCount) ∧
    (∀ instr ∈ p.body, instr.WF p.regCount) ∧
    (∀ instr ∈ p.epilogue, instr.WF p.regCount)

instance (p : Program) : Decidable p.WF := by
  unfold Program.WF
  infer_instance

/-! ## Arithmetic agreement between the denotation and the CCIR model -/

theorem M_pos : 0 < M := by decide

private theorem modulus64_ne : (Int.ofNat (2 ^ 64)) ≠ 0 := by decide
private theorem modulus8_ne : (Int.ofNat (2 ^ 8)) ≠ 0 := by decide

theorem normalizeCC_u64_def (x : Int) :
    normalizeCC .u64 x = some (x.emod (Int.ofNat (2 ^ 64))) := by
  show (if (Int.ofNat (2 ^ 64)) = 0 then none
    else some (x.emod (Int.ofNat (2 ^ 64)))) = _
  rw [if_neg modulus64_ne]

theorem normalizeCC_u8_def (x : Int) :
    normalizeCC .u8 x = some (x.emod (Int.ofNat (2 ^ 8))) := by
  show (if (Int.ofNat (2 ^ 8)) = 0 then none
    else some (x.emod (Int.ofNat (2 ^ 8)))) = _
  rw [if_neg modulus8_ne]

theorem normalizeCC_u64_natCast (n : Nat) :
    normalizeCC .u64 (n : Int) = some (((n % M : Nat) : Int)) := by
  rw [normalizeCC_u64_def]
  exact congrArg some (Int.natCast_emod n (2 ^ 64)).symm

private theorem sub_M_emod (x : Int) :
    (x - Int.ofNat (2 ^ 64)).emod (Int.ofNat (2 ^ 64)) =
      x.emod (Int.ofNat (2 ^ 64)) := by
  have h := Int.sub_emod x (Int.ofNat (2 ^ 64)) (Int.ofNat (2 ^ 64))
  rw [Int.emod_self, Int.sub_zero] at h
  exact h.trans (Int.emod_emod_of_dvd x (Int.dvd_refl _))

theorem denoteOperand_lt
    (index : Nat) {regCount : Nat} {s : RegState}
    (hBounded : ∀ i, i < regCount → s i < M)
    (operand : Operand) (hWF : operand.WF regCount) :
    denoteOperand index s operand < M := by
  cases operand with
  | reg i => exact hBounded i hWF
  | lit value => exact Nat.mod_lt _ M_pos
  | idx => exact Nat.mod_lt _ M_pos

theorem denoteOp_lt
    (op : Op) (a b result : Nat) (hResult : denoteOp op a b = some result) :
    result < M := by
  have hOne : (1 : Nat) < M := by
    show 1 < 2 ^ 64
    exact Nat.one_lt_two_pow (by decide)
  cases op <;> simp only [denoteOp] at hResult
  case udiv =>
    split at hResult
    · exact absurd hResult (by simp)
    · cases hResult; exact Nat.mod_lt _ M_pos
  case urem =>
    split at hResult
    · exact absurd hResult (by simp)
    · cases hResult; exact Nat.mod_lt _ M_pos
  case eq => cases hResult; split <;> first | exact hOne | exact M_pos
  case ne => cases hResult; split <;> first | exact hOne | exact M_pos
  case lt => cases hResult; split <;> first | exact hOne | exact M_pos
  case le => cases hResult; split <;> first | exact hOne | exact M_pos
  case gt => cases hResult; split <;> first | exact hOne | exact M_pos
  case ge => cases hResult; split <;> first | exact hOne | exact M_pos
  all_goals (cases hResult; exact Nat.mod_lt _ M_pos)

theorem evalCCBinary_u64_natCast
    (op : Op) (arith : UnsignedBinary) (hOp : op.arithmetic? = some arith)
    (a b : Nat) (hb : b < M) :
    evalCCBinary .u64 arith (a : Int) (b : Int) =
      (denoteOp op a b).map (fun n => (n : Int)) := by
  cases op <;> simp only [Op.arithmetic?, Option.some.injEq,
    reduceCtorEq] at hOp <;> subst hOp
  case add =>
    show normalizeCC .u64 ((a : Int) + (b : Int)) = _
    rw [show ((a : Int) + (b : Int)) = ((a + b : Nat) : Int) by omega,
      normalizeCC_u64_natCast]
    rfl
  case sub =>
    show normalizeCC .u64 ((a : Int) - (b : Int)) = _
    have hM : b < 2 ^ 64 := hb
    rw [normalizeCC_u64_def,
      show ((a : Int) - (b : Int)) =
        ((a + (M - b) : Nat) : Int) - Int.ofNat (2 ^ 64) by
          show _ = _ - ((2 ^ 64 : Nat) : Int)
          simp only [M]; omega,
      sub_M_emod,
      show ((a + (M - b) : Nat) : Int).emod (Int.ofNat (2 ^ 64)) =
        (((a + (M - b)) % M : Nat) : Int) from
          (Int.natCast_emod _ _).symm]
    rfl
  case mul =>
    show normalizeCC .u64 ((a : Int) * (b : Int)) = _
    rw [show ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) from
        (Int.natCast_mul a b).symm,
      normalizeCC_u64_natCast]
    rfl
  case udiv =>
    show (if (b : Int) = 0 then none
      else normalizeCC .u64 (((a : Int)).ediv (b : Int))) = _
    by_cases hZero : b = 0
    · subst hZero
      rfl
    · rw [if_neg (by exact_mod_cast hZero),
        show (((a : Int)).ediv (b : Int)) = ((a / b : Nat) : Int) from
          (Int.natCast_ediv a b).symm,
        normalizeCC_u64_natCast,
        show denoteOp .udiv a b = some ((a / b) % M) from by
          simp [denoteOp, hZero]]
      rfl
  case urem =>
    show (if (b : Int) = 0 then none
      else normalizeCC .u64 (((a : Int)).emod (b : Int))) = _
    by_cases hZero : b = 0
    · subst hZero
      rfl
    · rw [if_neg (by exact_mod_cast hZero),
        show (((a : Int)).emod (b : Int)) = ((a % b : Nat) : Int) from
          (Int.natCast_emod a b).symm,
        normalizeCC_u64_natCast,
        show denoteOp .urem a b = some ((a % b) % M) from by
          simp [denoteOp, hZero]]
      rfl
  case band =>
    show normalizeCC .u64
      (Int.ofNat (Nat.land ((a : Int)).toNat ((b : Int)).toNat)) = _
    rw [Int.toNat_natCast, Int.toNat_natCast]
    exact (normalizeCC_u64_natCast (Nat.land a b)).trans rfl
  case bor =>
    show normalizeCC .u64
      (Int.ofNat (Nat.lor ((a : Int)).toNat ((b : Int)).toNat)) = _
    rw [Int.toNat_natCast, Int.toNat_natCast]
    exact (normalizeCC_u64_natCast (Nat.lor a b)).trans rfl
  case bxor =>
    show normalizeCC .u64
      (Int.ofNat (Nat.xor ((a : Int)).toNat ((b : Int)).toNat)) = _
    rw [Int.toNat_natCast, Int.toNat_natCast]
    exact (normalizeCC_u64_natCast (Nat.xor a b)).trans rfl
  case shl =>
    show normalizeCC .u64
      (Int.shiftLeft (a : Int) ((b : Int)).toNat) = _
    rw [Int.toNat_natCast,
      show Int.shiftLeft (a : Int) b = ((a <<< b : Nat) : Int) from rfl,
      normalizeCC_u64_natCast]
    rfl
  case lshr =>
    show normalizeCC .u64
      (Int.ofNat (Nat.shiftRight ((a : Int)).toNat ((b : Int)).toNat)) = _
    rw [Int.toNat_natCast, Int.toNat_natCast]
    exact (normalizeCC_u64_natCast (Nat.shiftRight a b)).trans rfl

private theorem normalizeCC_u8_zero : normalizeCC .u8 (0 : Int) = some 0 := by
  rw [normalizeCC_u8_def]; rfl

private theorem normalizeCC_u8_one : normalizeCC .u8 (1 : Int) = some 1 := by
  rw [normalizeCC_u8_def]; rfl

theorem evalCCComparison_u8_natCast
    (op : Op) (cmp : UnsignedComparison) (hOp : op.comparison? = some cmp)
    (a b : Nat) :
    evalCCComparison .u8 cmp (a : Int) (b : Int) =
      (denoteOp op a b).map (fun n => (n : Int)) := by
  cases op <;> simp only [Op.comparison?, Option.some.injEq,
    reduceCtorEq] at hOp <;> subst hOp
  case eq =>
    show normalizeCC .u8 (if (a : Int) = (b : Int) then 1 else 0) = _
    by_cases h : a = b
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .eq a b = some 1 from by simp [denoteOp, h]]
      rfl
    · rw [if_neg (by exact_mod_cast h), normalizeCC_u8_zero,
        show denoteOp .eq a b = some 0 from by simp [denoteOp, h]]
      rfl
  case ne =>
    show normalizeCC .u8 (if (a : Int) ≠ (b : Int) then 1 else 0) = _
    by_cases h : a = b
    · rw [if_neg (by simp [h]), normalizeCC_u8_zero,
        show denoteOp .ne a b = some 0 from by simp [denoteOp, h]]
      rfl
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .ne a b = some 1 from by simp [denoteOp, h]]
      rfl
  case lt =>
    show normalizeCC .u8 (if (a : Int) < (b : Int) then 1 else 0) = _
    by_cases h : a < b
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .lt a b = some 1 from by simp [denoteOp, h]]
      rfl
    · rw [if_neg (by exact_mod_cast h), normalizeCC_u8_zero,
        show denoteOp .lt a b = some 0 from by simp [denoteOp, h]]
      rfl
  case le =>
    show normalizeCC .u8 (if (a : Int) ≤ (b : Int) then 1 else 0) = _
    by_cases h : a ≤ b
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .le a b = some 1 from by simp [denoteOp, h]]
      rfl
    · rw [if_neg (by exact_mod_cast h), normalizeCC_u8_zero,
        show denoteOp .le a b = some 0 from by simp [denoteOp, h]]
      rfl
  case gt =>
    show normalizeCC .u8 (if (a : Int) > (b : Int) then 1 else 0) = _
    by_cases h : a > b
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .gt a b = some 1 from by simp [denoteOp, h]]
      rfl
    · rw [if_neg (by exact_mod_cast h), normalizeCC_u8_zero,
        show denoteOp .gt a b = some 0 from by simp [denoteOp, h]]
      rfl
  case ge =>
    show normalizeCC .u8 (if (a : Int) ≥ (b : Int) then 1 else 0) = _
    by_cases h : a ≥ b
    · rw [if_pos (by exact_mod_cast h), normalizeCC_u8_one,
        show denoteOp .ge a b = some 1 from by simp [denoteOp, h]]
      rfl
    · rw [if_neg (by exact_mod_cast h), normalizeCC_u8_zero,
        show denoteOp .ge a b = some 0 from by simp [denoteOp, h]]
      rfl

theorem denoteOp_cmp_le_one
    (op : Op) (cmp : UnsignedComparison) (hOp : op.comparison? = some cmp)
    (a b result : Nat) (hResult : denoteOp op a b = some result) :
    result ≤ 1 := by
  cases op <;> simp only [Op.comparison?, Option.some.injEq,
    reduceCtorEq] at hOp <;> simp only [denoteOp, Option.some.injEq]
    at hResult <;> subst hResult <;> split <;> simp

/-! ## The simulation invariant and step lemmas -/

/-- Register `i`'s value is held (as a normalized integer) by CCIR local
`i + 1`, and every register value is a `u64`. -/
def StateInv (regCount : Nat) (s : RegState) (env : CCEnv) : Prop :=
  (∀ i, i < regCount → env ⟨i + 1⟩ = some ((s i : Int))) ∧
    (∀ i, i < regCount → s i < M)

/-- The lock-step relation between denotation results and CCIR results. -/
def StepRel (regCount : Nat) : Option RegState → Option CCEnv → Prop
  | some s, some env => StateInv regCount s env
  | none, none => True
  | _, _ => False

private theorem regLocal_ne_scratch (i : Nat) :
    (⟨i + 1⟩ : CCIR.LocalId) ≠ ⟨0⟩ := by
  intro h
  cases h

private theorem regLocal_eq_iff (i j : Nat) :
    ((⟨i + 1⟩ : CCIR.LocalId) = ⟨j + 1⟩) ↔ i = j := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

theorem evalOperand_compileOperand
    (index regCount : Nat) (s : RegState) (env : CCEnv)
    (hInv : StateInv regCount s env)
    (operand : Operand) (hWF : operand.WF regCount) :
    evalOperand env (compileOperand index operand) =
      some ((denoteOperand index s operand : Nat) : Int) := by
  cases operand with
  | reg i => exact hInv.1 i hWF
  | lit value =>
      show normalizeCC .u64 (value : Int) = _
      exact normalizeCC_u64_natCast value
  | idx =>
      show normalizeCC .u64 (index : Int) = _
      exact normalizeCC_u64_natCast index

private theorem stateInv_set
    {regCount : Nat} {s : RegState} {env : CCEnv}
    (hInv : StateInv regCount s env)
    (dest value : Nat) (hValue : value < M) :
    StateInv regCount (s.set dest value)
      (env.set ⟨dest + 1⟩ ((value : Nat) : Int)) := by
  constructor
  · intro i hi
    by_cases hEq : i = dest
    · subst hEq
      simp [CCEnv.set, RegState.set]
    · have hId : (⟨i + 1⟩ : CCIR.LocalId) ≠ ⟨dest + 1⟩ := by
        intro h
        exact hEq ((regLocal_eq_iff i dest).mp h)
      simp only [CCEnv.set, RegState.set, if_neg hId, if_neg hEq]
      exact hInv.1 i hi
  · intro i hi
    by_cases hEq : i = dest
    · subst hEq
      simpa [RegState.set] using hValue
    · simp only [RegState.set, if_neg hEq]
      exact hInv.2 i hi

private theorem stateInv_set_scratch
    {regCount : Nat} {s : RegState} {env : CCEnv}
    (hInv : StateInv regCount s env) (value : Int) :
    StateInv regCount s (env.set ⟨0⟩ value) := by
  constructor
  · intro i hi
    simp only [CCEnv.set, if_neg (regLocal_ne_scratch i)]
    exact hInv.1 i hi
  · exact hInv.2

theorem denoteInstr_correct
    (index regCount : Nat) (s : RegState) (env : CCEnv)
    (hInv : StateInv regCount s env)
    (instr : Instr) (hWF : instr.WF regCount) :
    StepRel regCount (denoteInstr index s instr)
      (evalCCSequence env (compileInstr index instr)) := by
  cases instr with
  | mov dest src =>
      obtain ⟨hDest, hSrc⟩ := hWF
      show StepRel regCount (some (s.set dest (denoteOperand index s src)))
        (evalCCSequence env [.assign (regLocal dest) (compileOperand index src)])
      have hOperand := evalOperand_compileOperand
        index regCount s env hInv src hSrc
      show StepRel regCount _
        ((evalCCAssignStep env (regLocal dest)
          (compileOperand index src)).bind
            (fun env => evalCCSequence env []))
      unfold evalCCAssignStep
      rw [hOperand]
      show StepRel regCount _
        (some (env.set ⟨dest + 1⟩ ((denoteOperand index s src : Nat) : Int)))
      exact stateInv_set hInv dest _
        (denoteOperand_lt index hInv.2 src hSrc)
  | binop dest op lhs rhs =>
      obtain ⟨hDest, hLhs, hRhs⟩ := hWF
      have hLhsOperand := evalOperand_compileOperand
        index regCount s env hInv lhs hLhs
      have hRhsOperand := evalOperand_compileOperand
        index regCount s env hInv rhs hRhs
      cases hArith : op.arithmetic? with
      | some arith =>
          show StepRel regCount
            ((denoteOp op (denoteOperand index s lhs)
              (denoteOperand index s rhs)).bind
                (fun result => some (s.set dest result)))
            (evalCCSequence env
              (compileInstr index (.binop dest op lhs rhs)))
          have hCompile :
              compileInstr index (.binop dest op lhs rhs) =
                [.binary (regLocal dest) arith
                  (compileOperand index lhs) (compileOperand index rhs)] := by
            show (match op.arithmetic?, op.comparison? with
              | some arith, _ =>
                  [StraightInstruction.binary (regLocal dest) arith
                    (compileOperand index lhs) (compileOperand index rhs)]
              | none, some comparison =>
                  [StraightInstruction.compare scratchLocal comparison
                    (compileOperand index lhs) (compileOperand index rhs),
                   StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
              | none, none => []) = _
            rw [hArith]
          rw [hCompile]
          show StepRel regCount _
            ((evalCCBinaryStep env (regLocal dest) arith
              (compileOperand index lhs)
              (compileOperand index rhs)).bind
                (fun env => evalCCSequence env []))
          unfold evalCCBinaryStep
          rw [hLhsOperand, hRhsOperand]
          show StepRel regCount _
            (((evalCCBinary .u64 arith
                ((denoteOperand index s lhs : Nat) : Int)
                ((denoteOperand index s rhs : Nat) : Int)).bind
              (fun result => some (env.set ⟨dest + 1⟩ result))).bind
                (fun env => evalCCSequence env []))
          rw [evalCCBinary_u64_natCast op arith hArith _ _
            (denoteOperand_lt index hInv.2 rhs hRhs)]
          cases hResult : denoteOp op
            (denoteOperand index s lhs) (denoteOperand index s rhs) with
          | none =>
              trivial
          | some result =>
              show StepRel regCount (some (s.set dest result))
                (some (env.set ⟨dest + 1⟩ ((result : Nat) : Int)))
              exact stateInv_set hInv dest result
                (denoteOp_lt op _ _ result hResult)
      | none =>
          cases hCmp : op.comparison? with
          | none =>
              exfalso
              cases op <;> simp [Op.arithmetic?] at hArith <;>
                simp [Op.comparison?] at hCmp
          | some cmp =>
              have hCompile :
                  compileInstr index (.binop dest op lhs rhs) =
                    [.compare scratchLocal cmp
                      (compileOperand index lhs) (compileOperand index rhs),
                     .cast (regLocal dest) (.local ⟨0⟩)] := by
                show (match op.arithmetic?, op.comparison? with
                  | some arith, _ =>
                      [StraightInstruction.binary (regLocal dest) arith
                        (compileOperand index lhs) (compileOperand index rhs)]
                  | none, some comparison =>
                      [StraightInstruction.compare scratchLocal comparison
                        (compileOperand index lhs) (compileOperand index rhs),
                       StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                  | none, none => []) = _
                rw [hArith, hCmp]
              rw [hCompile]
              have hDenote :
                  ∃ result, denoteOp op (denoteOperand index s lhs)
                      (denoteOperand index s rhs) = some result ∧
                    result ≤ 1 := by
                cases op <;> simp [Op.comparison?] at hCmp <;>
                  exact ⟨_, rfl, by split <;> decide⟩
              obtain ⟨result, hResult, hResultLe⟩ := hDenote
              show StepRel regCount
                ((denoteOp op (denoteOperand index s lhs)
                  (denoteOperand index s rhs)).bind
                    (fun result => some (s.set dest result)))
                ((evalCCComparisonStep env scratchLocal cmp
                  (compileOperand index lhs)
                  (compileOperand index rhs)).bind
                    (fun env =>
                      (evalCCCastStep env (regLocal dest)
                        (.local ⟨0⟩)).bind
                          (fun env => evalCCSequence env [])))
              unfold evalCCComparisonStep
              rw [hLhsOperand, hRhsOperand]
              show StepRel regCount _
                (((evalCCComparison .u8 cmp
                    ((denoteOperand index s lhs : Nat) : Int)
                    ((denoteOperand index s rhs : Nat) : Int)).bind
                  (fun value => some (env.set ⟨0⟩ value))).bind _)
              rw [evalCCComparison_u8_natCast op cmp hCmp, hResult]
              show StepRel regCount (some (s.set dest result))
                ((evalCCCastStep (env.set ⟨0⟩ ((result : Nat) : Int))
                  (regLocal dest) (.local ⟨0⟩)).bind
                    (fun env => evalCCSequence env []))
              unfold evalCCCastStep
              show StepRel regCount _
                ((((env.set ⟨0⟩ ((result : Nat) : Int)) ⟨0⟩).bind
                  (fun value => (normalizeCC .u64 value).bind
                    (fun value =>
                      some ((env.set ⟨0⟩ ((result : Nat) : Int)).set
                        ⟨dest + 1⟩ value)))).bind
                          (fun env => evalCCSequence env []))
              rw [show (env.set ⟨0⟩ ((result : Nat) : Int)) ⟨0⟩ =
                some ((result : Nat) : Int) by simp [CCEnv.set]]
              have hResultLt : result < M :=
                Nat.lt_of_le_of_lt hResultLe (by decide)
              show StepRel regCount (some (s.set dest result))
                (((normalizeCC .u64 ((result : Nat) : Int)).bind
                  (fun value =>
                    some ((env.set ⟨0⟩ ((result : Nat) : Int)).set
                      ⟨dest + 1⟩ value))).bind
                        (fun env => evalCCSequence env []))
              rw [show normalizeCC .u64 ((result : Nat) : Int) =
                  some ((result : Nat) : Int) by
                rw [normalizeCC_u64_natCast, Nat.mod_eq_of_lt hResultLt]]
              show StepRel regCount (some (s.set dest result))
                (some ((env.set ⟨0⟩ ((result : Nat) : Int)).set
                  ⟨dest + 1⟩ ((result : Nat) : Int)))
              exact stateInv_set (stateInv_set_scratch hInv _)
                dest result hResultLt

theorem denoteInstrs_correct
    (index regCount : Nat) (instrs : List Instr)
    (hWF : ∀ instr ∈ instrs, instr.WF regCount) :
    ∀ (s : RegState) (env : CCEnv), StateInv regCount s env →
    StepRel regCount (denoteInstrs index s instrs)
      (evalCCSequence env (compileInstrs index instrs)) := by
  induction instrs with
  | nil =>
      intro s env hInv
      exact hInv
  | cons instr rest ih =>
      intro s env hInv
      have hStep := denoteInstr_correct index regCount s env hInv instr
        (hWF instr (by simp))
      have hRest : ∀ instr ∈ rest, instr.WF regCount := by
        intro i hi
        exact hWF i (by simp [hi])
      show StepRel regCount
        ((denoteInstr index s instr).bind
          (fun s => denoteInstrs index s rest))
        (evalCCSequence env
          (compileInstr index instr ++ compileInstrs index rest))
      rw [evalCCSequence_append]
      cases hDenote : denoteInstr index s instr with
      | none =>
          rw [hDenote] at hStep
          cases hEval : evalCCSequence env (compileInstr index instr) with
          | none => trivial
          | some envNext =>
              rw [hEval] at hStep
              exact absurd hStep (by simp [StepRel])
      | some sNext =>
          rw [hDenote] at hStep
          cases hEval : evalCCSequence env (compileInstr index instr) with
          | none =>
              exact absurd (hEval ▸ hStep) (by simp [StepRel])
          | some envNext =>
              rw [hEval] at hStep
              exact ih hRest sNext envNext hStep

theorem preamble_correct (regCount : Nat) :
    ∀ env : CCEnv,
    ∃ envOut, evalCCSequence env (preamble regCount) = some envOut ∧
      (∀ i, i < regCount → envOut ⟨i + 1⟩ = some ((0 : Nat) : Int)) := by
  induction regCount with
  | zero =>
      intro env
      refine ⟨env.set ⟨0⟩ ((0 : Nat) : Int), ?_, ?_⟩
      · show ((evalCCAssignStep env scratchLocal
          (.uintLit .u8 0)).bind (fun env => evalCCSequence env [])) = _
        unfold evalCCAssignStep
        rw [show evalOperand env (.uintLit .u8 0) =
          some ((0 : Nat) : Int) from by
            show normalizeCC .u8 ((0 : Nat) : Int) = _
            rw [normalizeCC_u8_def]
            rfl]
        rfl
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
  | succ regCount ih =>
      intro env
      obtain ⟨envMid, hMid, hRegs⟩ := ih env
      have hPreamble : preamble (regCount + 1) =
          preamble regCount ++
            [.assign (regLocal regCount) (.uintLit .u64 0)] := by
        unfold preamble
        rw [List.range_succ, List.map_append]
        rfl
      rw [hPreamble]
      rw [evalCCSequence_append, hMid]
      show ∃ envOut,
        ((evalCCAssignStep envMid (regLocal regCount)
          (.uintLit .u64 0)).bind (fun env => evalCCSequence env [])) =
            some envOut ∧ _
      unfold evalCCAssignStep
      rw [show evalOperand envMid (.uintLit .u64 0) =
          some ((0 : Nat) : Int) from normalizeCC_u64_natCast 0]
      refine ⟨envMid.set ⟨regCount + 1⟩ ((0 : Nat) : Int), rfl, ?_⟩
      intro i hi
      by_cases hEq : i = regCount
      · subst hEq
        simp [CCEnv.set]
      · have hId : (⟨i + 1⟩ : CCIR.LocalId) ≠ ⟨regCount + 1⟩ := by
          intro h
          exact hEq ((regLocal_eq_iff i regCount).mp h)
        simp only [CCEnv.set, if_neg hId]
        exact hRegs i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hEq)

theorem foldBody_correct
    (regCount : Nat) (body : List Instr)
    (hWF : ∀ instr ∈ body, instr.WF regCount)
    (indices : List Nat) :
    ∀ (s : RegState) (env : CCEnv), StateInv regCount s env →
    StepRel regCount
      (indices.foldlM (fun s index => denoteInstrs index s body) s)
      (indices.foldlM
        (fun env index => evalCCSequence env (compileInstrs index body)) env) := by
  induction indices with
  | nil =>
      intro s env hInv
      exact hInv
  | cons index rest ih =>
      intro s env hInv
      have hStep := denoteInstrs_correct index regCount body hWF s env hInv
      show StepRel regCount
        ((denoteInstrs index s body).bind
          (fun s => rest.foldlM (fun s index => denoteInstrs index s body) s))
        ((evalCCSequence env (compileInstrs index body)).bind
          (fun env => rest.foldlM
            (fun env index =>
              evalCCSequence env (compileInstrs index body)) env))
      cases hDenote : denoteInstrs index s body with
      | none =>
          rw [hDenote] at hStep
          cases hEval : evalCCSequence env (compileInstrs index body) with
          | none => trivial
          | some envNext =>
              rw [hEval] at hStep
              exact absurd hStep (by simp [StepRel])
      | some sNext =>
          rw [hDenote] at hStep
          cases hEval : evalCCSequence env (compileInstrs index body) with
          | none =>
              exact absurd (hEval ▸ hStep) (by simp [StepRel])
          | some envNext =>
              rw [hEval] at hStep
              exact ih sNext envNext hStep

private theorem bind_some_option {α β : Type _} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

/-! ## The bridge theorem -/

/--
**The reflection bridge**: the compiled CCIR trace of a well-formed program
computes exactly the program's Lean-level denotation. This is a structural
theorem — no per-certificate evaluation of the CCIR model is ever needed
again.
-/
theorem Program.evalCC_compile (p : Program) (hWF : p.WF) :
    ((evalCCSequence Verified.emptyCCEnv p.compile).bind
        (fun env => env ⟨p.output + 1⟩)) =
      p.denote.map (fun n => (n : Int)) := by
  obtain ⟨hOutput, hInit, hBody, hEpilogue⟩ := hWF
  obtain ⟨env0, hPreamble, hRegs⟩ :=
    preamble_correct p.regCount Verified.emptyCCEnv
  have hInv0 : StateInv p.regCount initialState env0 :=
    ⟨fun i hi => hRegs i hi, fun i _ => M_pos⟩
  unfold Program.compile
  rw [List.append_assoc, List.append_assoc]
  rw [evalCCSequence_append, hPreamble]
  show ((evalCCSequence env0 (compileInstrs 0 p.init ++
      (foldTrace p.loopCount (fun index => compileInstrs index p.body) ++
        compileInstrs 0 p.epilogue))).bind
    (fun env => env ⟨p.output + 1⟩)) = _
  rw [evalCCSequence_append]
  have hInitStep := denoteInstrs_correct 0 p.regCount p.init hInit
    initialState env0 hInv0
  unfold Program.denote
  cases hInitDenote : denoteInstrs 0 initialState p.init with
  | none =>
      rw [hInitDenote] at hInitStep
      cases hInitEval : evalCCSequence env0 (compileInstrs 0 p.init) with
      | none =>
          rfl
      | some env1 =>
          rw [hInitEval] at hInitStep
          exact absurd hInitStep (by simp [StepRel])
  | some s1 =>
      rw [hInitDenote] at hInitStep
      cases hInitEval : evalCCSequence env0 (compileInstrs 0 p.init) with
      | none =>
          exact absurd (hInitEval ▸ hInitStep) (by simp [StepRel])
      | some env1 =>
          rw [hInitEval] at hInitStep
          simp only [bind_some_option]
          rw [evalCCSequence_append]
          rw [evalCCSequence_foldTrace]
          have hFoldStep := foldBody_correct p.regCount p.body hBody
            (List.range p.loopCount) s1 env1 hInitStep
          cases hFoldDenote : (List.range p.loopCount).foldlM
              (fun s index => denoteInstrs index s p.body) s1 with
          | none =>
              rw [hFoldDenote] at hFoldStep
              cases hFoldEval : (List.range p.loopCount).foldlM
                  (fun env index =>
                    evalCCSequence env (compileInstrs index p.body)) env1 with
              | none =>
                  rfl
              | some env2 =>
                  rw [hFoldEval] at hFoldStep
                  exact absurd hFoldStep (by simp [StepRel])
          | some s2 =>
              rw [hFoldDenote] at hFoldStep
              cases hFoldEval : (List.range p.loopCount).foldlM
                  (fun env index =>
                    evalCCSequence env (compileInstrs index p.body)) env1 with
              | none =>
                  exact absurd (hFoldEval ▸ hFoldStep) (by simp [StepRel])
              | some env2 =>
                  rw [hFoldEval] at hFoldStep
                  simp only [bind_some_option]
                  have hEpilogueStep := denoteInstrs_correct 0 p.regCount
                    p.epilogue hEpilogue s2 env2 hFoldStep
                  cases hEpilogueDenote :
                      denoteInstrs 0 s2 p.epilogue with
                  | none =>
                      rw [hEpilogueDenote] at hEpilogueStep
                      cases hEpilogueEval : evalCCSequence env2
                          (compileInstrs 0 p.epilogue) with
                      | none =>
                          rfl
                      | some env3 =>
                          rw [hEpilogueEval] at hEpilogueStep
                          exact absurd hEpilogueStep (by simp [StepRel])
                  | some s3 =>
                      rw [hEpilogueDenote] at hEpilogueStep
                      cases hEpilogueEval : evalCCSequence env2
                          (compileInstrs 0 p.epilogue) with
                      | none =>
                          exact absurd (hEpilogueEval ▸ hEpilogueStep)
                            (by simp [StepRel])
                      | some env3 =>
                          rw [hEpilogueEval] at hEpilogueStep
                          simp only [bind_some_option]
                          show env3 ⟨p.output + 1⟩ = some ((s3 p.output : Nat) : Int)
                          exact hEpilogueStep.1 p.output hOutput

/-! ## Packaging: certificates without CCIR-model evaluation -/

/--
For any `Computation` whose trace is a compiled program, the CCIR source
result **is** the program's denotation, structurally.
-/
theorem sourceResult_eq_denote
    (p : Program) (hWF : p.WF)
    (computation : Verified.Computation)
    (hInstructions : computation.instructions = p.compile)
    (hOutput : computation.output = ⟨p.output + 1⟩) :
    computation.sourceResult = p.denote.map (fun n => (n : Int)) := by
  unfold Verified.Computation.sourceResult
  rw [hInstructions, hOutput]
  exact Program.evalCC_compile p hWF

/--
The kernel-fast acceptance route: `Returns` reduces to the Lean-level
denotation, so `decide` evaluates the fold at native `Nat` speed instead of
walking the CCIR model.
-/
theorem returns_iff_denote
    (p : Program) (hWF : p.WF)
    (computation : Verified.Computation)
    (hInstructions : computation.instructions = p.compile)
    (hOutput : computation.output = ⟨p.output + 1⟩)
    (n : Nat) :
    computation.Returns ((n : Nat) : Int) ↔ p.denote = some n := by
  have hSource := sourceResult_eq_denote p hWF computation hInstructions hOutput
  constructor
  · intro h
    have hMap : p.denote.map (fun n => (n : Int)) = some ((n : Nat) : Int) := by
      rw [← hSource]
      exact h
    cases hDenote : p.denote with
    | none =>
        rw [hDenote] at hMap
        have hMap' : (none : Option Int) = some ((n : Nat) : Int) := hMap
        simp at hMap' 
    | some value =>
        rw [hDenote] at hMap
        have hValue : ((value : Nat) : Int) = ((n : Nat) : Int) :=
          Option.some.inj hMap
        exact congrArg some (by exact_mod_cast hValue)
  · intro h
    show computation.sourceResult = some ((n : Nat) : Int)
    rw [hSource, h]
    rfl

end LeanCompCert.Verified.Reflect

