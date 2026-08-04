import LeanCompCert.Lower.Pure
import Std.Data.String.ToNat

namespace LeanCompCert.Proof

open LeanCompCert

/-- Scalar environments for CCIR locals and emitted C local names. -/
abbrev CCEnv := CCIR.LocalId → Option Int
abbrev CEnv := String → Option Int

/--
Machine width of a generated-C scalar type.

Pointer and function-pointer types are modeled as **64-bit machine words**,
matching `CCIR.CCType.bitWidth`'s `pointerBits := 64` default and the LP64
targets the emitted artifacts are compiled for (aarch64 and x86_64).  This is
what makes an address materialization (`(uint64_t *)a`) a value-preserving
operation in the proved fragment rather than an undefined one; the abstract
memory of `Verified.MemFragment` is indexed by exactly such integer addresses.
On a 32-bit target the model would be unfaithful, which is why the artifact
pipeline targets LP64 only.
-/
def bitWidth : C.CType → Option Nat
  | .bool | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 | .f32 => some 32
  | .u64 | .i64 | .f64 => some 64
  | .usize | .isize => some System.Platform.numBits
  | .ptr _ | .fnPtr _ _ => some 64
  | _ => none

/-- The CCIR-side counterpart of `bitWidth`; `.obj` is a pointer too. -/
def ccBitWidth : CCIR.CCType → Option Nat
  | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 | .f32 => some 32
  | .u64 | .i64 | .f64 => some 64
  | .usize | .isize => some System.Platform.numBits
  | .obj | .ptr _ | .fnPtr _ _ => some 64
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

/--
The unsigned comparison fragment. Comparisons produce the normalized values
`1` and `0` at the destination type on both sides of the lowering.
-/
inductive UnsignedComparison where
  | eq | ne | ult | ule | ugt | uge
  deriving Repr, BEq, DecidableEq

def UnsignedComparison.ccir : UnsignedComparison → CCIR.BinaryOp
  | .eq => .eq
  | .ne => .ne
  | .ult => .ult
  | .ule => .ule
  | .ugt => .ugt
  | .uge => .uge

def UnsignedComparison.c : UnsignedComparison → C.CBinaryOp
  | .eq => .eq
  | .ne => .ne
  | .ult => .lt
  | .ule => .le
  | .ugt => .gt
  | .uge => .ge

/-- CCIR comparison semantics, separate from the generated-C AST semantics. -/
def evalCCComparison
    (type : CCIR.CCType)
    (op : UnsignedComparison)
    (lhs rhs : Int) : Option Int :=
  match op with
  | .eq => normalizeCC type (if lhs = rhs then 1 else 0)
  | .ne => normalizeCC type (if lhs ≠ rhs then 1 else 0)
  | .ult => normalizeCC type (if lhs < rhs then 1 else 0)
  | .ule => normalizeCC type (if lhs ≤ rhs then 1 else 0)
  | .ugt => normalizeCC type (if lhs > rhs then 1 else 0)
  | .uge => normalizeCC type (if lhs ≥ rhs then 1 else 0)

theorem evalBinary_lowerType_comparison
    (type : CCIR.CCType)
    (op : UnsignedComparison)
    (lhs rhs : Int) :
    evalBinary (Lower.lowerType type) op.c lhs rhs =
      evalCCComparison type op lhs rhs := by
  cases op <;>
    simp [UnsignedComparison.c, evalBinary, evalCCComparison,
      normalize_lowerType]

/--
The production comparison lowering emits a cast-free `.binary` exactly when the
lowered operand expressions carry non-signed C types. This is the decidable
side condition carried by the proved fragment's comparison instructions.
-/
def operandLowersUnsigned (fn : CCIR.Function) (operand : CCIR.Operand) : Bool :=
  match Lower.lowerOperand fn operand with
  | .ok expr => !expr.type.isSigned
  | .error _ => true

theorem lowerBinary_comparison
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedComparison)
    (lhs rhs : CCIR.Operand)
    (lhsExpr rhsExpr : C.CExpr)
    (hLhsLower : Lower.lowerOperand fn lhs = .ok lhsExpr)
    (hRhsLower : Lower.lowerOperand fn rhs = .ok rhsExpr)
    (hLhs : lhsExpr.type.isSigned = false)
    (hRhs : rhsExpr.type.isSigned = false) :
    Lower.lowerBinary fn dest op.ccir lhs rhs =
      .ok (.binary (Lower.lowerType dest.type) op.c lhsExpr rhsExpr) := by
  unfold Lower.lowerBinary
  rw [hLhsLower, hRhsLower]
  cases op <;>
    simp [UnsignedComparison.ccir, UnsignedComparison.c, Lower.comparisonOp,
      bind, Except.bind, pure, Except.pure, hLhs, hRhs]

theorem lowerBinary_comparison_error
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedComparison)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    (∃ lhsExpr, Lower.lowerOperand fn lhs = .ok lhsExpr) ∧
      (∃ rhsExpr, Lower.lowerOperand fn rhs = .ok rhsExpr) := by
  unfold Lower.lowerBinary at hLower
  cases hLhsLower : Lower.lowerOperand fn lhs with
  | error error =>
      rw [hLhsLower] at hLower
      simp [bind, Except.bind] at hLower
  | ok lhsExpr =>
      rw [hLhsLower] at hLower
      cases hRhsLower : Lower.lowerOperand fn rhs with
      | error error =>
          rw [hRhsLower] at hLower
          simp [bind, Except.bind] at hLower
      | ok rhsExpr =>
          exact ⟨⟨lhsExpr, rfl⟩, ⟨rhsExpr, rfl⟩⟩

theorem lowerBinary_comparison_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedComparison)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hLhs : operandLowersUnsigned fn lhs = true)
    (hRhs : operandLowersUnsigned fn rhs = true)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    evalCExpr cEnv expr =
      (do
        let lhsValue ← evalOperand ccEnv lhs
        let rhsValue ← evalOperand ccEnv rhs
        evalCCComparison dest.type op lhsValue rhsValue) := by
  obtain ⟨⟨lhsExpr, hLhsLower⟩, ⟨rhsExpr, hRhsLower⟩⟩ :=
    lowerBinary_comparison_error fn dest op lhs rhs expr hLower
  unfold operandLowersUnsigned at hLhs hRhs
  rw [hLhsLower] at hLhs
  rw [hRhsLower] at hRhs
  simp only [Bool.not_eq_true'] at hLhs hRhs
  rw [lowerBinary_comparison fn dest op lhs rhs lhsExpr rhsExpr
    hLhsLower hRhsLower hLhs hRhs] at hLower
  injection hLower with hExpr
  subst expr
  simp only [evalCExpr]
  rw [lowerOperand_correct fn lhs lhsExpr ccEnv cEnv hEnv hLhsLower]
  rw [lowerOperand_correct fn rhs rhsExpr ccEnv cEnv hEnv hRhsLower]
  simp only [evalBinary_lowerType_comparison]

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

def evalCCComparisonStep
    (env : CCEnv)
    (dest : CCIR.LocalDecl)
    (op : UnsignedComparison)
    (lhs rhs : CCIR.Operand) : Option CCEnv := do
  let lhsValue ← evalOperand env lhs
  let rhsValue ← evalOperand env rhs
  let result ← evalCCComparison dest.type op lhsValue rhsValue
  pure (env.set dest.id result)

theorem lowerComparison_assignment_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : UnsignedComparison)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hLhs : operandLowersUnsigned fn lhs = true)
    (hRhs : operandLowersUnsigned fn rhs = true)
    (hLower : Lower.lowerBinary fn dest op.ccir lhs rhs = .ok expr) :
    ResultsRel
      (evalCCComparisonStep ccEnv dest op lhs rhs)
      (evalCAssign cEnv (Lower.localExpr dest) expr) := by
  have hExpr := lowerBinary_comparison_correct
    fn dest op lhs rhs expr ccEnv cEnv hEnv hLhs hRhs hLower
  simp only [evalCCComparisonStep, evalCAssign, Lower.localExpr]
  rw [hExpr]
  generalize hLhsValue : evalOperand ccEnv lhs = lhsResult
  cases lhsResult with
  | none => simp [ResultsRel]
  | some lhsValue =>
      generalize hRhsValue : evalOperand ccEnv rhs = rhsResult
      cases rhsResult with
      | none => simp [ResultsRel]
      | some rhsValue =>
          generalize hValue :
            evalCCComparison dest.type op lhsValue rhsValue = result
          cases result with
          | none =>
              change ResultsRel
                ((evalCCComparison dest.type op lhsValue rhsValue).bind
                  (fun result => some (ccEnv.set dest.id result)))
                ((evalCCComparison dest.type op lhsValue rhsValue).bind
                  (fun result =>
                    some (cEnv.set (ABI.localName dest.id.value) result)))
              rw [hValue]
              trivial
          | some value =>
              change ResultsRel
                ((evalCCComparison dest.type op lhsValue rhsValue).bind
                  (fun result => some (ccEnv.set dest.id result)))
                ((evalCCComparison dest.type op lhsValue rhsValue).bind
                  (fun result =>
                    some (cEnv.set (ABI.localName dest.id.value) result)))
              rw [hValue]
              simp only [Option.bind_some, ResultsRel]
              exact hEnv.set dest.id value

theorem lowerInstruction_binary_general
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (dest : CCIR.LocalDecl)
    (op : CCIR.BinaryOp)
    (lhs rhs : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerBinary fn dest op lhs rhs = .ok expr) :
    Lower.lowerInstruction fn block index (.binary dest op lhs rhs) =
      .ok {
        statements := #[.assign (Lower.localExpr dest) expr]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hLower]
  rfl

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

/--
Width-conversion semantics: the operand value is renormalized at the
destination type. This models the production `.cast` unary lowering when the
cast target is the destination type itself.
-/
def evalCCCastStep
    (env : CCEnv)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand) : Option CCEnv := do
  let operandValue ← evalOperand env value
  let result ← normalizeCC dest.type operandValue
  pure (env.set dest.id result)

theorem lowerUnary_cast
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (operandExpr : C.CExpr)
    (hOperand : Lower.lowerOperand fn value = .ok operandExpr) :
    Lower.lowerUnary fn dest (.cast dest.type) value =
      .ok (.cast (Lower.lowerType dest.type) operandExpr) := by
  unfold Lower.lowerUnary
  rw [hOperand]
  rfl

theorem lowerUnary_cast_inv
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerUnary fn dest (.cast dest.type) value = .ok expr) :
    ∃ operandExpr,
      Lower.lowerOperand fn value = .ok operandExpr ∧
        expr = .cast (Lower.lowerType dest.type) operandExpr := by
  unfold Lower.lowerUnary at hLower
  cases hOperand : Lower.lowerOperand fn value with
  | error error =>
      rw [hOperand] at hLower
      simp [bind, Except.bind] at hLower
  | ok operandExpr =>
      rw [hOperand] at hLower
      change
        Except.ok (C.CExpr.cast (Lower.lowerType dest.type) operandExpr) =
          Except.ok expr at hLower
      injection hLower with hExpr
      exact ⟨operandExpr, rfl, hExpr.symm⟩

theorem lowerCast_assignment_correct
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (operandExpr : C.CExpr)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hOperand : Lower.lowerOperand fn value = .ok operandExpr) :
    ResultsRel
      (evalCCCastStep ccEnv dest value)
      (evalCAssign cEnv (Lower.localExpr dest)
        (.cast (Lower.lowerType dest.type) operandExpr)) := by
  have hExpr := lowerOperand_correct fn value operandExpr ccEnv cEnv hEnv hOperand
  simp only [evalCCCastStep, evalCAssign, Lower.localExpr, evalCExpr]
  rw [hExpr]
  simp only [normalize_lowerType]
  generalize hValue : evalOperand ccEnv value = operandResult
  cases operandResult with
  | none => simp [ResultsRel]
  | some operandValue =>
      generalize hNorm : normalizeCC dest.type operandValue = result
      cases result with
      | none =>
          change ResultsRel
            ((normalizeCC dest.type operandValue).bind
              (fun result => some (ccEnv.set dest.id result)))
            ((normalizeCC dest.type operandValue).bind
              (fun result =>
                some (cEnv.set (ABI.localName dest.id.value) result)))
          rw [hNorm]
          trivial
      | some resultValue =>
          change ResultsRel
            ((normalizeCC dest.type operandValue).bind
              (fun result => some (ccEnv.set dest.id result)))
            ((normalizeCC dest.type operandValue).bind
              (fun result =>
                some (cEnv.set (ABI.localName dest.id.value) result)))
          rw [hNorm]
          simp only [Option.bind_some, ResultsRel]
          exact hEnv.set dest.id resultValue

theorem lowerInstruction_unary_cast
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (dest : CCIR.LocalDecl)
    (value : CCIR.Operand)
    (expr : C.CExpr)
    (hLower : Lower.lowerUnary fn dest (.cast dest.type) value = .ok expr) :
    Lower.lowerInstruction fn block index (.unary dest (.cast dest.type) value) =
      .ok {
        statements := #[.assign (Lower.localExpr dest) expr]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hLower]
  rfl

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
  | compare
      (dest : CCIR.LocalDecl)
      (op : UnsignedComparison)
      (lhs rhs : CCIR.Operand)
  | cast (dest : CCIR.LocalDecl) (value : CCIR.Operand)
  deriving Repr

def StraightInstruction.toCCIR : StraightInstruction → CCIR.Instruction
  | .assign dest value => .assign dest value
  | .binary dest op lhs rhs => .binary dest op.ccir lhs rhs
  | .compare dest op lhs rhs => .binary dest op.ccir lhs rhs
  | .cast dest value => .unary dest (.cast dest.type) value

/--
Comparison instructions additionally record that their operands lower to
non-signed C expressions, which is exactly the cast-free case of the
production comparison lowering. The predicate is decidable, so concrete
computations discharge it with `decide`.
-/
def StraightInstruction.WellFormed
    (fn : CCIR.Function) : StraightInstruction → Prop
  | .assign _ _ => True
  | .binary dest _ _ _ => dest.type.isUnsigned = true
  | .compare _ _ lhs rhs =>
      operandLowersUnsigned fn lhs = true ∧
        operandLowersUnsigned fn rhs = true
  | .cast _ _ => True

instance (fn : CCIR.Function) (instruction : StraightInstruction) :
    Decidable (instruction.WellFormed fn) := by
  cases instruction <;>
    simp only [StraightInstruction.WellFormed] <;>
    infer_instance

def evalCCStraight
    (env : CCEnv) : StraightInstruction → Option CCEnv
  | .assign dest value => evalCCAssignStep env dest value
  | .binary dest op lhs rhs => evalCCBinaryStep env dest op lhs rhs
  | .compare dest op lhs rhs => evalCCComparisonStep env dest op lhs rhs
  | .cast dest value => evalCCCastStep env dest value

/--
Declaration semantics.

`uint64_t l_3;` leaves the object indeterminate; the model leaves the name
undefined, so any later read is `none` and the whole evaluation is stuck.  That
is the conservative direction: a result is only ever produced when it does not
depend on reading an uninitialised local.  `uint64_t l_3 = e;` stores the
initialiser **converted to the declared type**, which is what C does and what
makes the rule faithful for a narrow declared type.

`CEnv` is a flat name environment, so this models declarations that do not
shadow.  Every emitted translation unit satisfies that: locals are
`ABI.localName i` for distinct `i`, all in one block.
-/
def evalCDecl (env : CEnv) (type : C.CType) (name : String) :
    Option C.CExpr → Option CEnv
  | none => some env
  | some init => do
      let value ← evalCExpr env init
      let stored ← normalize type value
      pure (env.set name stored)

/--
Statement semantics for the loop-free part of the proved fragment.

Everything outside it — calls, branches, `switch`, `goto`, `return`, and
**`while`** — is `none`, i.e. the model refuses to say anything.  `while` is
interpreted by `evalCStmtFuel` below, which carries the iteration budget a
`while` needs and this function does not have.
-/
def evalCStmt (env : CEnv) : C.CStmt → Option CEnv
  | .assign target value => evalCAssign env target value
  | .decl type name init => evalCDecl env type name init
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
  | .compare dest op lhs rhs => do
      pure (.assign (Lower.localExpr dest)
        (← Lower.lowerBinary fn dest op.ccir lhs rhs))
  | .cast dest value => do
      pure (.assign (Lower.localExpr dest)
        (← Lower.lowerUnary fn dest (.cast dest.type) value))

theorem lowerStraight_correct
    (fn : CCIR.Function)
    (instruction : StraightInstruction)
    (stmt : C.CStmt)
    (ccEnv : CCEnv)
    (cEnv : CEnv)
    (hEnv : EnvRel ccEnv cEnv)
    (hWellFormed : instruction.WellFormed fn)
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
  | compare dest op lhs rhs =>
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
          exact lowerComparison_assignment_correct
            fn dest op lhs rhs expr ccEnv cEnv hEnv
              hWellFormed.1 hWellFormed.2 hExpr
  | cast dest value =>
      simp only [lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerUnary fn dest (.cast dest.type) value = result at hLower
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
          obtain ⟨operandExpr, hOperand, hCast⟩ :=
            lowerUnary_cast_inv fn dest value expr hExpr
          subst expr
          exact lowerCast_assignment_correct
            fn dest value operandExpr ccEnv cEnv hEnv hOperand

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
  | compare dest op lhs rhs =>
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
          exact lowerInstruction_binary_general
            fn block index dest op.ccir lhs rhs expr hExpr
  | cast dest value =>
      simp only [lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerUnary fn dest (.cast dest.type) value = result at hLower
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
          exact lowerInstruction_unary_cast
            fn block index dest value expr hExpr

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

/-! ### Lowering a whole trace

The natural non-tail-recursive shape keeps one interpreter frame alive per
instruction, and the Lean interpreter's recursion guard fires at roughly ten
thousand frames — a hard ceiling on the size of an emitted translation unit.
`lowerSequenceAux` accumulates the statements in reverse so the recursive
call is a tail call; `lowerSequence_nil` and `lowerSequence_cons` recover the
two equations every proof below uses, so nothing downstream changes. -/

/-- Tail-recursive worker: `acc` holds the statements emitted so far, in
reverse order. -/
def lowerSequenceAux (fn : CCIR.Function) :
    List StraightInstruction → List C.CStmt →
      Except Lower.LowerError (List C.CStmt)
  | [], acc => .ok acc.reverse
  | instruction :: rest, acc => do
      let stmt ← lowerStraight fn instruction
      lowerSequenceAux fn rest (stmt :: acc)

def lowerSequence
    (fn : CCIR.Function) (instructions : List StraightInstruction) :
    Except Lower.LowerError (List C.CStmt) :=
  lowerSequenceAux fn instructions []

/-- The accumulator only prefixes the result. -/
theorem lowerSequenceAux_eq (fn : CCIR.Function) :
    ∀ (instructions : List StraightInstruction) (acc : List C.CStmt),
      lowerSequenceAux fn instructions acc =
        Except.map (fun ss => acc.reverse ++ ss)
          (lowerSequenceAux fn instructions []) := by
  intro instructions
  induction instructions with
  | nil =>
      intro acc
      show Except.ok acc.reverse = Except.map _ (Except.ok ([] : List C.CStmt))
      simp [Except.map]
  | cons instruction rest ih =>
      intro acc
      show (lowerStraight fn instruction).bind
            (fun stmt => lowerSequenceAux fn rest (stmt :: acc)) =
        Except.map _ ((lowerStraight fn instruction).bind
            (fun stmt => lowerSequenceAux fn rest (stmt :: [])))
      cases hHead : lowerStraight fn instruction with
      | error e => rfl
      | ok stmt =>
          show lowerSequenceAux fn rest (stmt :: acc) =
            Except.map _ (lowerSequenceAux fn rest (stmt :: []))
          rw [ih (stmt :: acc), ih (stmt :: [])]
          cases lowerSequenceAux fn rest [] <;> simp [Except.map]

theorem lowerSequence_nil (fn : CCIR.Function) :
    lowerSequence fn [] = .ok [] := rfl

theorem lowerSequence_cons (fn : CCIR.Function)
    (instruction : StraightInstruction) (rest : List StraightInstruction) :
    lowerSequence fn (instruction :: rest) =
      (do
        let stmt ← lowerStraight fn instruction
        let statements ← lowerSequence fn rest
        pure (stmt :: statements)) := by
  show (lowerStraight fn instruction).bind
      (fun stmt => lowerSequenceAux fn rest (stmt :: [])) =
    (lowerStraight fn instruction).bind (fun stmt =>
      (lowerSequenceAux fn rest []).bind
        (fun statements => pure (stmt :: statements)))
  cases hHead : lowerStraight fn instruction with
  | error e => rfl
  | ok stmt =>
      show lowerSequenceAux fn rest (stmt :: []) =
        (lowerSequenceAux fn rest []).bind
          (fun statements => pure (stmt :: statements))
      rw [lowerSequenceAux_eq fn rest (stmt :: [])]
      cases lowerSequenceAux fn rest [] <;> rfl

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
      rw [lowerSequence_nil] at hLower
      injection hLower with hStatements
      subst statements
      trivial
  | cons instruction rest ih =>
      rw [lowerSequence_cons] at hLower
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
    (hWellFormed : ∀ instruction ∈ instructions, instruction.WellFormed fn)
    (hLower : lowerSequence fn instructions = .ok statements) :
    ResultsRel
      (evalCCSequence ccEnv instructions)
      (evalCSequence cEnv statements) := by
  induction instructions generalizing statements ccEnv cEnv with
  | nil =>
      rw [lowerSequence_nil] at hLower
      injection hLower with hStatements
      subst statements
      simpa [evalCCSequence, evalCSequence, ResultsRel] using hEnv
  | cons instruction rest ih =>
      rw [lowerSequence_cons] at hLower
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
                  instruction.WellFormed fn :=
                hWellFormed instruction (by simp)
              have hRestWellFormed :
                  ∀ next ∈ rest, next.WellFormed fn := by
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

/--
Loop bodies compose. These lemmas let bounded-iteration (fold) certificates
reuse `lowerSequence_correct` without re-proving anything per iteration: an
unrolled trace is still one straight-line trace, and its lowering and
semantics decompose along the unrolling.
-/
theorem lowerSequence_append
    (fn : CCIR.Function)
    (first rest : List StraightInstruction)
    (firstStatements restStatements : List C.CStmt)
    (hFirst : lowerSequence fn first = .ok firstStatements)
    (hRest : lowerSequence fn rest = .ok restStatements) :
    lowerSequence fn (first ++ rest) =
      .ok (firstStatements ++ restStatements) := by
  induction first generalizing firstStatements with
  | nil =>
      rw [lowerSequence_nil] at hFirst
      injection hFirst with hStatements
      subst firstStatements
      simpa using hRest
  | cons instruction tail ih =>
      rw [lowerSequence_cons] at hFirst
      generalize hHead : lowerStraight fn instruction = headResult at hFirst
      cases headResult with
      | error error =>
          change Except.error error = Except.ok firstStatements at hFirst
          contradiction
      | ok stmt =>
          generalize hTail : lowerSequence fn tail = tailResult at hFirst
          cases tailResult with
          | error error =>
              change Except.error error = Except.ok firstStatements at hFirst
              contradiction
          | ok tailStatements =>
              change
                Except.ok (stmt :: tailStatements) =
                  Except.ok firstStatements at hFirst
              injection hFirst with hStatements
              subst firstStatements
              show lowerSequence fn (instruction :: (tail ++ rest)) = _
              rw [lowerSequence_cons]
              rw [hHead, ih tailStatements hTail]
              rfl

theorem evalCCSequence_append
    (env : CCEnv)
    (first rest : List StraightInstruction) :
    evalCCSequence env (first ++ rest) =
      (do
        let env ← evalCCSequence env first
        evalCCSequence env rest) := by
  induction first generalizing env with
  | nil => simp [evalCCSequence]
  | cons instruction tail ih =>
      cases hHead : evalCCStraight env instruction with
      | none => simp [evalCCSequence, hHead]
      | some next => simp [evalCCSequence, hHead, ih next]

theorem evalCSequence_append
    (env : CEnv)
    (first rest : List C.CStmt) :
    evalCSequence env (first ++ rest) =
      (do
        let env ← evalCSequence env first
        evalCSequence env rest) := by
  induction first generalizing env with
  | nil => simp [evalCSequence]
  | cons stmt tail ih =>
      cases hHead : evalCStmt env stmt with
      | none => simp [evalCSequence, hHead]
      | some next => simp [evalCSequence, hHead, ih next]

/-! ### `while`, at the trip counts the emitter actually produces

`Lower` never emits a loop, but `Verified.Reflect.emitRolled` does: a
10⁷-iteration fold is emitted as one `while` whose body is the fold body
compiled **once** against a counter register.  Without a rule for `while` the
whole rolled route sits outside the proved C model, which is precisely the
route large campaigns must use.

The rule below is **fuelled**, and deliberately so.  A general `while` rule
would have to be a partial function or an inductive relation; the shape this
package emits is a counted loop — a `u64` counter register, an increment at the
end of the body, and a fixed literal trip count — for which a bounded semantics
is exact.  Fuel exhaustion is `none`, so an under-supplied budget can only make
the model refuse to answer, never answer wrongly.

**Covered.**  `while (cond) { s₁; …; sₙ }` where

* `cond` is a scalar expression of the `evalCExpr` fragment (variables,
  literals, unary and binary operators, casts — no memory);
* every `sᵢ` is loop-free, i.e. interpreted by `evalCStmt`: an assignment to a
  variable, or a declaration; and
* the loop leaves the guard false within the supplied fuel.

**Not covered**, and `none` rather than approximated: nested loops, `break`,
`continue`, `goto` into or out of the body, `return` inside the body, a guard
that reads memory, and any loop that has not exited when the fuel runs out.
-/

/-- The body block, concatenated `count` times.  The unrolled form of a
`count`-iteration loop. -/
def repeatStmts (body : List C.CStmt) : Nat → List C.CStmt
  | 0 => []
  | count + 1 => body ++ repeatStmts body count

theorem repeatStmts_succ (body : List C.CStmt) (count : Nat) :
    repeatStmts body (count + 1) = body ++ repeatStmts body count := rfl

/--
Fuelled `while` semantics: evaluate the guard, stop on `0`, otherwise run the
body once and recurse with one unit less fuel.  Out of fuel is `none` — the
model declines rather than guesses.
-/
def evalCWhile (cond : C.CExpr) (body : List C.CStmt) :
    Nat → CEnv → Option CEnv
  | 0, _ => none
  | fuel + 1, env =>
      match evalCExpr env cond with
      | none => none
      | some guard =>
          if guard = 0 then some env
          else (evalCSequence env body).bind (evalCWhile cond body fuel)

/-- Statement semantics with an iteration budget for loops.  Identical to
`evalCStmt` on every statement that is not a `while`. -/
def evalCStmtFuel (fuel : Nat) (env : CEnv) : C.CStmt → Option CEnv
  | .whileLoop cond body => evalCWhile cond body.toList fuel env
  | stmt => evalCStmt env stmt

def evalCSequenceFuel (fuel : Nat) (env : CEnv) : List C.CStmt → Option CEnv
  | [] => some env
  | stmt :: rest => do
      let env ← evalCStmtFuel fuel env stmt
      evalCSequenceFuel fuel env rest

/-- Statements the loop-free semantics interprets. -/
def LoopFree : C.CStmt → Prop
  | .whileLoop _ _ => False
  | _ => True

instance (stmt : C.CStmt) : Decidable (LoopFree stmt) := by
  cases stmt <;> simp only [LoopFree] <;> infer_instance

/-! #### Conservativity

Adding the loop rule moves nothing that was already proved.  `evalCStmtFuel`
*is* `evalCStmt` on every loop-free statement, whatever the budget, so every
existing theorem about `evalCSequence` transfers verbatim — and every statement
`lowerSequence` produces is an assignment, hence loop-free, so no lowered trace
in this package is affected at all. -/

theorem evalCStmtFuel_of_loopFree (fuel : Nat) (env : CEnv) (stmt : C.CStmt)
    (h : LoopFree stmt) : evalCStmtFuel fuel env stmt = evalCStmt env stmt := by
  cases stmt <;> first | rfl | exact absurd h (by simp [LoopFree])

theorem evalCSequenceFuel_of_loopFree (fuel : Nat) :
    ∀ (statements : List C.CStmt), (∀ stmt ∈ statements, LoopFree stmt) →
      ∀ env : CEnv,
        evalCSequenceFuel fuel env statements = evalCSequence env statements := by
  intro statements
  induction statements with
  | nil => intro _ _; rfl
  | cons stmt rest ih =>
      intro hFree env
      show (evalCStmtFuel fuel env stmt).bind
          (fun env => evalCSequenceFuel fuel env rest) =
        (evalCStmt env stmt).bind (fun env => evalCSequence env rest)
      rw [evalCStmtFuel_of_loopFree fuel env stmt (hFree stmt (by simp))]
      cases evalCStmt env stmt with
      | none => rfl
      | some next => exact ih (fun s hs => hFree s (by simp [hs])) next

/-- Every statement the verified lowering emits is an assignment, so no trace
this package lowers can contain a loop. -/
private theorem assign_of_bind_ok
    (result : Except Lower.LowerError C.CExpr)
    (target : C.CExpr) (stmt : C.CStmt)
    (h : (result.bind (fun e => pure (C.CStmt.assign target e))) = .ok stmt) :
    ∃ value, stmt = .assign target value := by
  cases result with
  | error e => exact absurd h (by simp [Except.bind])
  | ok expr =>
      change Except.ok (C.CStmt.assign target expr) = Except.ok stmt at h
      injection h with hStmt
      exact ⟨expr, hStmt.symm⟩

theorem lowerStraight_loopFree (fn : CCIR.Function)
    (instruction : StraightInstruction) (stmt : C.CStmt)
    (hLower : lowerStraight fn instruction = .ok stmt) : LoopFree stmt := by
  have hShape : ∃ target value, stmt = .assign target value := by
    cases instruction with
    | assign dest value =>
        simp only [lowerStraight] at hLower
        obtain ⟨e, he⟩ := assign_of_bind_ok (Lower.lowerOperand fn value)
          (Lower.localExpr dest) stmt hLower
        exact ⟨_, _, he⟩
    | binary dest op lhs rhs =>
        simp only [lowerStraight] at hLower
        obtain ⟨e, he⟩ := assign_of_bind_ok
          (Lower.lowerBinary fn dest op.ccir lhs rhs)
          (Lower.localExpr dest) stmt hLower
        exact ⟨_, _, he⟩
    | compare dest op lhs rhs =>
        simp only [lowerStraight] at hLower
        obtain ⟨e, he⟩ := assign_of_bind_ok
          (Lower.lowerBinary fn dest op.ccir lhs rhs)
          (Lower.localExpr dest) stmt hLower
        exact ⟨_, _, he⟩
    | cast dest value =>
        simp only [lowerStraight] at hLower
        obtain ⟨e, he⟩ := assign_of_bind_ok
          (Lower.lowerUnary fn dest (.cast dest.type) value)
          (Lower.localExpr dest) stmt hLower
        exact ⟨_, _, he⟩
  obtain ⟨target, value, rfl⟩ := hShape
  trivial

theorem lowerSequence_loopFree (fn : CCIR.Function) :
    ∀ (instructions : List StraightInstruction) (statements : List C.CStmt),
      lowerSequence fn instructions = .ok statements →
      ∀ stmt ∈ statements, LoopFree stmt := by
  intro instructions
  induction instructions with
  | nil =>
      intro statements hLower stmt hMem
      rw [lowerSequence_nil] at hLower
      injection hLower with hStatements
      subst statements
      exact absurd hMem (by simp)
  | cons instruction rest ih =>
      intro statements hLower stmt hMem
      rw [lowerSequence_cons] at hLower
      cases hHead : lowerStraight fn instruction with
      | error e =>
          rw [hHead] at hLower
          exact absurd hLower (by simp [bind, Except.bind])
      | ok head =>
          rw [hHead] at hLower
          cases hTail : lowerSequence fn rest with
          | error e =>
              rw [hTail] at hLower
              exact absurd hLower (by simp [bind, Except.bind])
          | ok tail =>
              rw [hTail] at hLower
              change Except.ok (head :: tail) = Except.ok statements at hLower
              injection hLower with hStatements
              subst statements
              rcases List.mem_cons.mp hMem with rfl | hTailMem
              · exact lowerStraight_loopFree fn instruction stmt hHead
              · exact ih tail hTail stmt hTailMem

/-! #### Unrolling

The generic rule.  Given a measure that counts down the remaining iterations,
falsifies the guard at zero and keeps it true above zero, a `while` with one
unit of fuel per remaining iteration (plus one for the exit test) evaluates
exactly as the body concatenated that many times.  Nothing here knows what the
guard is; the counter argument is supplied by the caller as `Inv`. -/
theorem evalCWhile_unroll
    (cond : C.CExpr) (body : List C.CStmt) (Inv : Nat → CEnv → Prop)
    (hFalse : ∀ env, Inv 0 env → evalCExpr env cond = some 0)
    (hTrue : ∀ (remaining : Nat) (env : CEnv), Inv (remaining + 1) env →
      ∃ guard, evalCExpr env cond = some guard ∧ guard ≠ 0)
    (hStep : ∀ (remaining : Nat) (env next : CEnv), Inv (remaining + 1) env →
      evalCSequence env body = some next → Inv remaining next) :
    ∀ (remaining : Nat) (env : CEnv), Inv remaining env →
      evalCWhile cond body (remaining + 1) env =
        evalCSequence env (repeatStmts body remaining) := by
  intro remaining
  induction remaining with
  | zero =>
      intro env hInv
      have hUnfold : evalCWhile cond body 1 env = some env := by
        show (match evalCExpr env cond with
          | none => none
          | some guard =>
              if guard = 0 then some env
              else (evalCSequence env body).bind (evalCWhile cond body 0)) =
          some env
        rw [hFalse env hInv]
        show (if (0 : Int) = 0 then some env
          else (evalCSequence env body).bind (evalCWhile cond body 0)) = _
        exact if_pos rfl
      rw [hUnfold]
      rfl
  | succ remaining ih =>
      intro env hInv
      obtain ⟨guard, hGuard, hNe⟩ := hTrue remaining env hInv
      have hUnfold : evalCWhile cond body (remaining + 1 + 1) env =
          (evalCSequence env body).bind
            (evalCWhile cond body (remaining + 1)) := by
        show (match evalCExpr env cond with
          | none => none
          | some guard =>
              if guard = 0 then some env
              else (evalCSequence env body).bind
                (evalCWhile cond body (remaining + 1))) = _
        rw [hGuard]
        show (if guard = 0 then some env
          else (evalCSequence env body).bind
            (evalCWhile cond body (remaining + 1))) = _
        exact if_neg hNe
      rw [hUnfold, repeatStmts_succ, evalCSequence_append]
      cases hBody : evalCSequence env body with
      | none => rfl
      | some next =>
          show evalCWhile cond body (remaining + 1) next = _
          exact ih next (hStep remaining env next hInv hBody)

theorem evalCSequenceFuel_append (fuel : Nat) (env : CEnv)
    (first rest : List C.CStmt) :
    evalCSequenceFuel fuel env (first ++ rest) =
      (do
        let env ← evalCSequenceFuel fuel env first
        evalCSequenceFuel fuel env rest) := by
  induction first generalizing env with
  | nil => rfl
  | cons stmt tail ih =>
      cases hHead : evalCStmtFuel fuel env stmt with
      | none => simp [evalCSequenceFuel, hHead]
      | some next => simp [evalCSequenceFuel, hHead, ih next]

/--
A bounded loop, expressed as the concatenation of its unrolled iterations.
This is the proved-fragment encoding of fold-style `native_decide`
certificates: `body k` is the straight-line trace of iteration `k`.
-/
def foldTrace
    (count : Nat)
    (body : Nat → List StraightInstruction) : List StraightInstruction :=
  (List.range count).flatMap body

theorem foldTrace_zero (body : Nat → List StraightInstruction) :
    foldTrace 0 body = [] := rfl

theorem foldTrace_succ
    (count : Nat)
    (body : Nat → List StraightInstruction) :
    foldTrace (count + 1) body = foldTrace count body ++ body count := by
  simp [foldTrace, List.range_succ]

/--
Evaluating an unrolled bounded loop is a monadic fold of its iteration
semantics. This connects fold certificates to ordinary Lean folds, so a
`Decision` specification can be proved by induction on the iteration count
instead of by whole-trace evaluation.
-/
theorem evalCCSequence_foldTrace
    (body : Nat → List StraightInstruction)
    (count : Nat)
    (env : CCEnv) :
    evalCCSequence env (foldTrace count body) =
      (List.range count).foldlM
        (fun env index => evalCCSequence env (body index)) env := by
  induction count generalizing env with
  | zero => simp [foldTrace, evalCCSequence]
  | succ count ih =>
      rw [foldTrace_succ, evalCCSequence_append, List.range_succ]
      cases hPrefix :
          evalCCSequence env (foldTrace count body) with
      | none => simp [ih] at hPrefix; simp [hPrefix]
      | some next =>
          rw [ih] at hPrefix
          simp [hPrefix]

end LeanCompCert.Proof
