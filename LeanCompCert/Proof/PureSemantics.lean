import LeanCompCert.Lower.Pure
import Std.Data.String.ToNat

namespace LeanCompCert.Proof

open LeanCompCert

/-- Scalar environments for CCIR locals and emitted C local names. -/
abbrev CCEnv := CCIR.LocalId → Option Int
abbrev CEnv := String → Option Int

def bitWidth : C.CType → Option Nat
  | .bool | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 | .f32 => some 32
  | .u64 | .i64 | .f64 => some 64
  | .usize | .isize => some System.Platform.numBits
  | _ => none

def ccBitWidth : CCIR.CCType → Option Nat
  | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 | .f32 => some 32
  | .u64 | .i64 | .f64 => some 64
  | .usize | .isize => some System.Platform.numBits
  | _ => none

def normalize (type : C.CType) (value : Int) : Option Int := do
  let bits ← bitWidth type
  let modulus : Int := Int.ofNat (2 ^ bits)
  if modulus = 0 then none else some (value.emod modulus)

def normalizeCC (type : CCIR.CCType) (value : Int) : Option Int := do
  let bits ← ccBitWidth type
  let modulus : Int := Int.ofNat (2 ^ bits)
  if modulus = 0 then none else some (value.emod modulus)

theorem bitWidth_lowerType (type : CCIR.CCType) :
    bitWidth (Lower.lowerType type) = ccBitWidth type := by
  cases type <;> rfl

theorem normalize_lowerType (type : CCIR.CCType) (value : Int) :
    normalize (Lower.lowerType type) value = normalizeCC type value := by
  simp only [normalize, normalizeCC, bitWidth_lowerType]

def evalUnary (type : C.CType) (op : C.CUnaryOp) (value : Int) : Option Int :=
  match op with
  | .boolNot => normalize type (if value = 0 then 1 else 0)
  | .neg => normalize type (-value)
  | .bitNot => do
      let bits ← bitWidth type
      let modulus : Int := Int.ofNat (2 ^ bits)
      normalize type (modulus - 1 - value)

def evalBinary
    (type : C.CType)
    (op : C.CBinaryOp)
    (lhs rhs : Int) : Option Int :=
  match op with
  | .add => normalize type (lhs + rhs)
  | .sub => normalize type (lhs - rhs)
  | .mul => normalize type (lhs * rhs)
  | .div => if rhs = 0 then none else normalize type (lhs.ediv rhs)
  | .rem => if rhs = 0 then none else normalize type (lhs.emod rhs)
  | .bitAnd =>
      normalize type (Int.ofNat (Nat.land lhs.toNat rhs.toNat))
  | .bitOr =>
      normalize type (Int.ofNat (Nat.lor lhs.toNat rhs.toNat))
  | .bitXor =>
      normalize type (Int.ofNat (Nat.xor lhs.toNat rhs.toNat))
  | .shl =>
      normalize type (Int.shiftLeft lhs rhs.toNat)
  | .shr =>
      normalize type (Int.ofNat (Nat.shiftRight lhs.toNat rhs.toNat))
  | .eq => normalize type (if lhs = rhs then 1 else 0)
  | .ne => normalize type (if lhs ≠ rhs then 1 else 0)
  | .lt => normalize type (if lhs < rhs then 1 else 0)
  | .le => normalize type (if lhs ≤ rhs then 1 else 0)
  | .gt => normalize type (if lhs > rhs then 1 else 0)
  | .ge => normalize type (if lhs ≥ rhs then 1 else 0)
  | .logicalAnd =>
      normalize type (if lhs ≠ 0 ∧ rhs ≠ 0 then 1 else 0)
  | .logicalOr =>
      normalize type (if lhs ≠ 0 ∨ rhs ≠ 0 then 1 else 0)

/--
Executable scalar semantics for the restricted C expression AST. Pointer and
memory expressions are intentionally outside the proved pure fragment.
-/
def evalCExpr (env : CEnv) : C.CExpr → Option Int
  | .var name _ => env name
  | .uintLit type value => normalize type value
  | .intLit type value => normalize type value
  | .boolLit value => normalize .bool (if value then 1 else 0)
  | .null _ => none
  | .unary type op value => do
      evalUnary type op (← evalCExpr env value)
  | .binary type op lhs rhs => do
      evalBinary type op (← evalCExpr env lhs) (← evalCExpr env rhs)
  | .cast type value => do
      normalize type (← evalCExpr env value)
  | .addressOf _ _ | .deref _ _ | .field _ _ _ | .index _ _ _ => none

/-- Scalar semantics of CCIR operands, defined independently of C types. -/
def evalOperand (env : CCEnv) : CCIR.Operand → Option Int
  | .local id => env id
  | .global _ => none
  | .uintLit type value => normalizeCC type value
  | .intLit type value => normalizeCC type value
  | .null _ => none

/-- The emitted C name environment represents the same CCIR local values. -/
def EnvRel (ccEnv : CCEnv) (cEnv : CEnv) : Prop :=
  ∀ id, cEnv (ABI.localName id.value) = ccEnv id

theorem lowerOperand_correct
    (fn : CCIR.Function)
    (operand : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hLower : Lower.lowerOperand fn operand = .ok expr) :
    evalCExpr cEnv expr = evalOperand ccEnv operand := by
  cases operand with
  | «local» id =>
      simp only [Lower.lowerOperand] at hLower
      split at hLower
      next type hType =>
        cases hLower
        exact hEnv id
      next hMissing => contradiction
  | global id =>
      simp [Lower.lowerOperand] at hLower
  | uintLit type value =>
      simp only [Lower.lowerOperand] at hLower
      cases hLower
      exact normalize_lowerType type value
  | intLit type value =>
      simp only [Lower.lowerOperand] at hLower
      cases hLower
      exact normalize_lowerType type value
  | null type =>
      simp only [Lower.lowerOperand] at hLower
      cases hLower
      rfl

inductive UnsignedBinary where
  | add | sub | mul | udiv | urem
  | bitAnd | bitOr | bitXor | shl | lshr
  deriving Repr, BEq, DecidableEq

def UnsignedBinary.ccir : UnsignedBinary → CCIR.BinaryOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .udiv => .udiv
  | .urem => .urem
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shl => .shl
  | .lshr => .lshr

def UnsignedBinary.c : UnsignedBinary → C.CBinaryOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .udiv => .div
  | .urem => .rem
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shl => .shl
  | .lshr => .shr

/-- CCIR arithmetic semantics, separate from the generated-C AST semantics. -/
def evalCCBinary
    (type : CCIR.CCType)
    (op : UnsignedBinary)
    (lhs rhs : Int) : Option Int :=
  match op with
  | .add => normalizeCC type (lhs + rhs)
  | .sub => normalizeCC type (lhs - rhs)
  | .mul => normalizeCC type (lhs * rhs)
  | .udiv => if rhs = 0 then none else normalizeCC type (lhs.ediv rhs)
  | .urem => if rhs = 0 then none else normalizeCC type (lhs.emod rhs)
  | .bitAnd =>
      normalizeCC type (Int.ofNat (Nat.land lhs.toNat rhs.toNat))
  | .bitOr =>
      normalizeCC type (Int.ofNat (Nat.lor lhs.toNat rhs.toNat))
  | .bitXor =>
      normalizeCC type (Int.ofNat (Nat.xor lhs.toNat rhs.toNat))
  | .shl =>
      normalizeCC type (Int.shiftLeft lhs rhs.toNat)
  | .lshr =>
      normalizeCC type (Int.ofNat (Nat.shiftRight lhs.toNat rhs.toNat))

theorem evalBinary_lowerType
    (type : CCIR.CCType)
    (op : UnsignedBinary)
    (lhs rhs : Int) :
    evalBinary (Lower.lowerType type) op.c lhs rhs =
      evalCCBinary type op lhs rhs := by
  cases op <;>
    simp [UnsignedBinary.c, evalBinary, evalCCBinary, normalize_lowerType]

theorem lowerBinary_unsigned
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedBinary)
    (lhs rhs : CCIR.Operand)
    (hUnsigned : dest.type.isUnsigned = true) :
    Lower.lowerBinary fn dest op.ccir lhs rhs =
      (do
        let lhs ← Lower.lowerOperand fn lhs
        let rhs ← Lower.lowerOperand fn rhs
        pure (.binary (Lower.lowerType dest.type) op.c lhs rhs)) := by
  have hSigned : (Lower.lowerType dest.type).isSigned = false := by
    generalize hType : dest.type = type at hUnsigned ⊢
    cases type <;>
      simp [CCIR.CCType.isUnsigned, Lower.lowerType, C.CType.isSigned]
        at hUnsigned ⊢
  cases op <;>
    simp [UnsignedBinary.ccir, UnsignedBinary.c, Lower.lowerBinary,
      Lower.comparisonOp, Lower.arithmeticOp, hSigned]

theorem lowerBinary_unsigned_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedBinary)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hUnsigned : dest.type.isUnsigned = true)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    evalCExpr cEnv expr =
      (do
        let lhsValue ← evalOperand ccEnv lhs
        let rhsValue ← evalOperand ccEnv rhs
        evalCCBinary dest.type op lhsValue rhsValue) := by
  rw [lowerBinary_unsigned fn dest op lhs rhs hUnsigned] at hLower
  generalize hLhs : Lower.lowerOperand fn lhs = lhsResult at hLower
  cases lhsResult with
  | error error =>
      change Except.error error = Except.ok expr at hLower
      contradiction
  | ok lhsExpr =>
      generalize hRhs : Lower.lowerOperand fn rhs = rhsResult at hLower
      cases rhsResult with
      | error error =>
          change Except.error error = Except.ok expr at hLower
          contradiction
      | ok rhsExpr =>
          change
            Except.ok (.binary (Lower.lowerType dest.type) op.c lhsExpr rhsExpr) =
              Except.ok expr at hLower
          injection hLower with hExpr
          subst expr
          simp only [evalCExpr]
          rw [lowerOperand_correct fn lhs lhsExpr ccEnv cEnv hEnv hLhs]
          rw [lowerOperand_correct fn rhs rhsExpr ccEnv cEnv hEnv hRhs]
          simp only [evalBinary_lowerType]

def CCEnv.set (env : CCEnv) (id : CCIR.LocalId) (value : Int) : CCEnv :=
  fun candidate => if candidate = id then some value else env candidate

def CEnv.set (env : CEnv) (name : String) (value : Int) : CEnv :=
  fun candidate => if candidate = name then some value else env candidate

theorem localName_injective :
    Function.Injective (fun id : CCIR.LocalId => ABI.localName id.value) := by
  intro left right h
  cases left with
  | mk left =>
      cases right with
      | mk right =>
          simp [ABI.localName] at h
          cases h
          rfl

theorem EnvRel.set
    {ccEnv : CCEnv}
    {cEnv : CEnv}
    (hEnv : EnvRel ccEnv cEnv)
    (id : CCIR.LocalId)
    (value : Int) :
    EnvRel (ccEnv.set id value) (cEnv.set (ABI.localName id.value) value) := by
  intro candidate
  by_cases hId : candidate = id
  · subst candidate
    simp [CCEnv.set, CEnv.set]
  · have hName :
        ABI.localName candidate.value ≠ ABI.localName id.value := by
      intro h
      exact hId (localName_injective h)
    simp [CCEnv.set, CEnv.set, hId, hName, hEnv candidate]

def evalCCBinaryStep
    (env : CCEnv)
    (dest : CCIR.LocalDecl)
    (op : UnsignedBinary)
    (lhs rhs : CCIR.Operand) : Option CCEnv := do
  let lhsValue ← evalOperand env lhs
  let rhsValue ← evalOperand env rhs
  let result ← evalCCBinary dest.type op lhsValue rhsValue
  pure (env.set dest.id result)

def evalCAssign (env : CEnv) (target value : C.CExpr) : Option CEnv :=
  match target with
  | .var name _ => do
      let result ← evalCExpr env value
      pure (env.set name result)
  | _ => none

def ResultsRel : Option CCEnv → Option CEnv → Prop
  | none, none => True
  | some ccEnv, some cEnv => EnvRel ccEnv cEnv
  | _, _ => False

theorem lowerBinary_assignment_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedBinary)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hUnsigned : dest.type.isUnsigned = true)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    ResultsRel
      (evalCCBinaryStep ccEnv dest op lhs rhs)
      (evalCAssign cEnv (Lower.localExpr dest) expr) := by
  have hExpr := lowerBinary_unsigned_correct
    fn dest op lhs rhs expr ccEnv cEnv hEnv hUnsigned hLower
  simp only [evalCCBinaryStep, evalCAssign, Lower.localExpr]
  rw [hExpr]
  generalize hLhs : evalOperand ccEnv lhs = lhsResult
  cases lhsResult with
  | none => simp [ResultsRel]
  | some lhsValue =>
      generalize hRhs : evalOperand ccEnv rhs = rhsResult
      cases rhsResult with
      | none => simp [ResultsRel]
      | some rhsValue =>
          generalize hValue :
            evalCCBinary dest.type op lhsValue rhsValue = result
          cases result with
          | none =>
              change ResultsRel
                ((evalCCBinary dest.type op lhsValue rhsValue).bind
                  (fun result => some (ccEnv.set dest.id result)))
                ((evalCCBinary dest.type op lhsValue rhsValue).bind
                  (fun result =>
                    some (cEnv.set (ABI.localName dest.id.value) result)))
              rw [hValue]
              trivial
          | some value =>
              change ResultsRel
                ((evalCCBinary dest.type op lhsValue rhsValue).bind
                  (fun result => some (ccEnv.set dest.id result)))
                ((evalCCBinary dest.type op lhsValue rhsValue).bind
                  (fun result =>
                    some (cEnv.set (ABI.localName dest.id.value) result)))
              rw [hValue]
              simp only [Option.bind_some, ResultsRel]
              exact hEnv.set dest.id value

theorem lowerInstruction_unsigned_binary
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (dest : CCIR.LocalDecl)
    (op : UnsignedBinary)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    Lower.lowerInstruction fn block index
        (.binary dest op.ccir lhs rhs) =
      .ok {
        statements := #[.assign (Lower.localExpr dest) expr]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hLower]
  rfl

def evalCCAssignStep
    (env : CCEnv)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand) : Option CCEnv := do
  let result ← evalOperand env value
  pure (env.set dest.id result)

theorem lowerAssignment_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hLower : Lower.lowerOperand fn value = .ok expr) :
    ResultsRel
      (evalCCAssignStep ccEnv dest value)
      (evalCAssign cEnv (Lower.localExpr dest) expr) := by
  have hExpr := lowerOperand_correct fn value expr ccEnv cEnv hEnv hLower
  simp only [evalCCAssignStep, evalCAssign, Lower.localExpr]
  rw [hExpr]
  generalize hValue : evalOperand ccEnv value = result
  cases result with
  | none => trivial
  | some result =>
      change EnvRel
        (ccEnv.set dest.id result)
        (cEnv.set (ABI.localName dest.id.value) result)
      exact hEnv.set dest.id result

theorem lowerInstruction_assign
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerOperand fn value = .ok expr) :
    Lower.lowerInstruction fn block index (.assign dest value) =
      .ok {
        statements := #[.assign (Lower.localExpr dest) expr]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hLower]
  rfl

/--
The straight-line fragment for which this file currently proves whole-trace
preservation. Each constructor is translated by the same production helper
used by `Lower.lowerInstruction`.
-/
inductive StraightInstruction where
  | assign (dest : CCIR.LocalDecl) (value : CCIR.Operand)
  | binary
      (dest : CCIR.LocalDecl)
      (op : UnsignedBinary)
      (lhs rhs : CCIR.Operand)
  deriving Repr

def StraightInstruction.toCCIR : StraightInstruction → CCIR.Instruction
  | .assign dest value => .assign dest value
  | .binary dest op lhs rhs => .binary dest op.ccir lhs rhs

def StraightInstruction.WellFormed : StraightInstruction → Prop
  | .assign _ _ => True
  | .binary dest _ _ _ => dest.type.isUnsigned = true

def evalCCStraight
    (env : CCEnv) : StraightInstruction → Option CCEnv
  | .assign dest value => evalCCAssignStep env dest value
  | .binary dest op lhs rhs => evalCCBinaryStep env dest op lhs rhs

def evalCStmt (env : CEnv) : C.CStmt → Option CEnv
  | .assign target value => evalCAssign env target value
  | _ => none

/--
Lower one proved instruction with the production operand/binary lowering
functions. The companion theorem below connects every successful result to
`Lower.lowerInstruction`, including its contextual error wrapper.
-/
def lowerStraight
    (fn : CCIR.Function) : StraightInstruction → Except Lower.LowerError C.CStmt
  | .assign dest value => do
      pure (.assign (Lower.localExpr dest) (← Lower.lowerOperand fn value))
  | .binary dest op lhs rhs => do
      pure (.assign (Lower.localExpr dest)
        (← Lower.lowerBinary fn dest op.ccir lhs rhs))

theorem lowerStraight_correct
    (fn : CCIR.Function)
    (instruction : StraightInstruction)
    (stmt : C.CStmt)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hWellFormed : instruction.WellFormed)
    (hLower : lowerStraight fn instruction = .ok stmt) :
    ResultsRel
      (evalCCStraight ccEnv instruction)
      (evalCStmt cEnv stmt) := by
  cases instruction with
  | assign dest value =>
      simp only [lowerStraight] at hLower
      generalize hExpr : Lower.lowerOperand fn value = result at hLower
      cases result with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          exact lowerAssignment_correct
            fn dest value expr ccEnv cEnv hEnv hExpr
  | binary dest op lhs rhs =>
      simp only [StraightInstruction.WellFormed] at hWellFormed
      simp only [lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerBinary fn dest op.ccir lhs rhs = result at hLower
      cases result with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          exact lowerBinary_assignment_correct
            fn dest op lhs rhs expr ccEnv cEnv hEnv hWellFormed hExpr

theorem lowerStraight_is_lowerInstruction
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (instruction : StraightInstruction)
    (stmt : C.CStmt)
    (hLower : lowerStraight fn instruction = .ok stmt) :
    Lower.lowerInstruction fn block index instruction.toCCIR =
      .ok { statements := #[stmt] } := by
  cases instruction with
  | assign dest value =>
      simp only [lowerStraight] at hLower
      generalize hExpr : Lower.lowerOperand fn value = result at hLower
      cases result with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          exact lowerInstruction_assign fn block index dest value expr hExpr
  | binary dest op lhs rhs =>
      simp only [lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerBinary fn dest op.ccir lhs rhs = result at hLower
      cases result with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          exact lowerInstruction_unsigned_binary
            fn block index dest op lhs rhs expr hExpr

def evalCCSequence (env : CCEnv) :
    List StraightInstruction → Option CCEnv
  | [] => some env
  | instruction :: rest => do
      let env ← evalCCStraight env instruction
      evalCCSequence env rest

def evalCSequence (env : CEnv) : List C.CStmt → Option CEnv
  | [] => some env
  | stmt :: rest => do
      let env ← evalCStmt env stmt
      evalCSequence env rest

def lowerSequence
    (fn : CCIR.Function) :
    List StraightInstruction → Except Lower.LowerError (List C.CStmt)
  | [] => .ok []
  | instruction :: rest => do
      let stmt ← lowerStraight fn instruction
      let statements ← lowerSequence fn rest
      pure (stmt :: statements)

/--
Every element of a successfully lowered trace is exactly the singleton
statement array returned by the production instruction lowerer at that index.
-/
def InstructionLoweringRel
    (fn : CCIR.Function)
    (block : CCIR.Block) :
    Nat → List StraightInstruction → List C.CStmt → Prop
  | _, [], [] => True
  | index, instruction :: rest, stmt :: statements =>
      Lower.lowerInstruction fn block index instruction.toCCIR =
          .ok { statements := #[stmt] } ∧
        InstructionLoweringRel fn block (index + 1) rest statements
  | _, _, _ => False

theorem lowerSequence_is_lowerInstructions
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (instructions : List StraightInstruction)
    (statements : List C.CStmt)
    (hLower : lowerSequence fn instructions = .ok statements) :
    InstructionLoweringRel fn block index instructions statements := by
  induction instructions generalizing index statements with
  | nil =>
      simp only [lowerSequence] at hLower
      injection hLower with hStatements
      subst statements
      trivial
  | cons instruction rest ih =>
      simp only [lowerSequence] at hLower
      generalize hHead : lowerStraight fn instruction = headResult at hLower
      cases headResult with
      | error error =>
          change Except.error error = Except.ok statements at hLower
          contradiction
      | ok stmt =>
          generalize hTail : lowerSequence fn rest = tailResult at hLower
          cases tailResult with
          | error error =>
              change Except.error error = Except.ok statements at hLower
              contradiction
          | ok tail =>
              change Except.ok (stmt :: tail) = Except.ok statements at hLower
              injection hLower with hStatements
              subst statements
              exact ⟨
                lowerStraight_is_lowerInstruction
                  fn block index instruction stmt hHead,
                ih (index + 1) tail hTail
              ⟩

/--
Semantic preservation for any successfully lowered straight-line trace in the
proved fragment. This is an induction over program length, not a bounded test.
-/
theorem lowerSequence_correct
    (fn : CCIR.Function)
    (instructions : List StraightInstruction)
    (statements : List C.CStmt)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hWellFormed : ∀ instruction ∈ instructions, instruction.WellFormed)
    (hLower : lowerSequence fn instructions = .ok statements) :
    ResultsRel
      (evalCCSequence ccEnv instructions)
      (evalCSequence cEnv statements) := by
  induction instructions generalizing statements ccEnv cEnv with
  | nil =>
      simp only [lowerSequence] at hLower
      injection hLower with hStatements
      subst statements
      simpa [evalCCSequence, evalCSequence, ResultsRel] using hEnv
  | cons instruction rest ih =>
      simp only [lowerSequence] at hLower
      generalize hHead : lowerStraight fn instruction = headResult at hLower
      cases headResult with
      | error error =>
          change Except.error error = Except.ok statements at hLower
          contradiction
      | ok stmt =>
          generalize hTail : lowerSequence fn rest = tailResult at hLower
          cases tailResult with
          | error error =>
              change Except.error error = Except.ok statements at hLower
              contradiction
          | ok tail =>
              change Except.ok (stmt :: tail) = Except.ok statements at hLower
              injection hLower with hStatements
              subst statements
              have hHeadWellFormed :
                  instruction.WellFormed :=
                hWellFormed instruction (by simp)
              have hRestWellFormed :
                  ∀ next ∈ rest, next.WellFormed := by
                intro next hNext
                exact hWellFormed next (by simp [hNext])
              have hStep := lowerStraight_correct fn instruction stmt
                ccEnv cEnv hEnv hHeadWellFormed hHead
              generalize hCC :
                evalCCStraight ccEnv instruction = ccResult at hStep ⊢
              generalize hC :
                evalCStmt cEnv stmt = cResult at hStep ⊢
              cases ccResult with
              | none =>
                  cases cResult with
                  | none =>
                      simp [evalCCSequence, evalCSequence, hCC, hC, ResultsRel]
                  | some nextC => contradiction
              | some nextCC =>
                  cases cResult with
                  | none => contradiction
                  | some nextC =>
                      simpa [evalCCSequence, evalCSequence, hCC, hC] using
                        ih tail nextCC nextC hStep hRestWellFormed hTail

end LeanCompCert.Proof
