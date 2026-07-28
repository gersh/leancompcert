import LeanCompCert.CCIR.Validate
import LeanCompCert.C.Emit
import LeanCompCert.ABI.Symbols

namespace LeanCompCert.Lower

open LeanCompCert

structure LowerError where
  message : String
  function : Option CCIR.GlobalId := none
  block : Option CCIR.BlockId := none
  instruction : Option Nat := none
  deriving Repr, BEq, Inhabited

def LowerError.pretty (error : LowerError) : String :=
  let fn := error.function.map (fun id => s!" in @{id.name}") |>.getD ""
  let block := error.block.map (fun id => s!" at {id}") |>.getD ""
  let instruction := error.instruction.map (fun index => s!" instruction {index}") |>.getD ""
  s!"lowering error{fn}{block}{instruction}: {error.message}"

private partial def lowerCompoundType : CCIR.CCType → C.CType
  | .void => .void
  | .u8 => .u8
  | .u16 => .u16
  | .u32 => .u32
  | .u64 => .u64
  | .usize => .usize
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32
  | .i64 => .i64
  | .isize => .isize
  | .f32 => .f32
  | .f64 => .f64
  | .obj => .ptr (.named "lean_object")
  | .ptr element => .ptr (lowerCompoundType element)
  | .fnPtr args result =>
      .fnPtr (args.map lowerCompoundType) (lowerCompoundType result)

/--
Lower a CCIR type to the restricted C AST. The public definition exposes
kernel-reducible equations for every scalar constructor; the opaque recursive
helper is needed only below pointer and function-pointer constructors.
-/
def lowerType : CCIR.CCType → C.CType
  | .void => .void
  | .u8 => .u8
  | .u16 => .u16
  | .u32 => .u32
  | .u64 => .u64
  | .usize => .usize
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32
  | .i64 => .i64
  | .isize => .isize
  | .f32 => .f32
  | .f64 => .f64
  | .obj => .ptr (.named "lean_object")
  | .ptr element => .ptr (lowerCompoundType element)
  | .fnPtr args result =>
      .fnPtr (args.map lowerCompoundType) (lowerCompoundType result)

private def unsignedRepresentation : C.CType → C.CType
  | .i8 => .u8
  | .i16 => .u16
  | .i32 => .u32
  | .i64 => .u64
  | .isize => .usize
  | type => type

def localExpr (decl : CCIR.LocalDecl) : C.CExpr :=
  .var (ABI.localName decl.id.value) (lowerType decl.type)

def localType? (fn : CCIR.Function) (id : CCIR.LocalId) : Option CCIR.CCType :=
  let params := fn.params.toList.find? (fun param => param.id == id)
  match params with
  | some param => some param.type
  | none =>
      fn.blocks.toList.findSome? fun block =>
        block.instructions.toList.findSome? fun instruction =>
          match instruction.destination? with
          | some decl => if decl.id == id then some decl.type else none
          | none => none

def lowerOperand (fn : CCIR.Function) : CCIR.Operand → Except LowerError C.CExpr
  | .local id =>
      match localType? fn id with
      | some type => .ok (.var (ABI.localName id.value) (lowerType type))
      | none => .error {
          message := s!"unknown local {id}"
          function := some fn.name
        }
  | .global id =>
      .error {
        message := s!"global @{id.name} needs an exact function-pointer type"
        function := some fn.name
      }
  | .uintLit type value => .ok (.uintLit (lowerType type) value)
  | .intLit type value => .ok (.intLit (lowerType type) value)
  | .null type => .ok (.null (lowerType type))

def lowerUnary
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : CCIR.UnaryOp)
    (operand : CCIR.Operand) : Except LowerError C.CExpr := do
  let value ← lowerOperand fn operand
  let destType := lowerType dest.type
  match op with
  | .cast target => pure (.cast (lowerType target) value)
  | .boolNot => pure (.unary destType .boolNot value)
  | .bitNot =>
      if destType.isSigned then
        let unsigned := unsignedRepresentation destType
        pure (.cast destType (.unary unsigned .bitNot (.cast unsigned value)))
      else
        pure (.unary destType .bitNot value)
  | .neg =>
      if destType.isSigned then
        let unsigned := unsignedRepresentation destType
        pure (.cast destType (.unary unsigned .neg (.cast unsigned value)))
      else
        pure (.unary destType .neg value)

def comparisonOp : CCIR.BinaryOp → Option C.CBinaryOp
  | .eq => some .eq | .ne => some .ne
  | .ult | .slt => some .lt
  | .ule | .sle => some .le
  | .ugt | .sgt => some .gt
  | .uge | .sge => some .ge
  | _ => none

def arithmeticOp : CCIR.BinaryOp → Option C.CBinaryOp
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .udiv | .sdiv => some .div
  | .urem | .srem => some .rem
  | .bitAnd => some .bitAnd | .bitOr => some .bitOr | .bitXor => some .bitXor
  | .shl => some .shl | .lshr | .ashr => some .shr
  | _ => none

def lowerBinary
    (fn : CCIR.Function)
    (dest : CCIR.LocalDecl)
    (op : CCIR.BinaryOp)
    (lhsOperand rhsOperand : CCIR.Operand) : Except LowerError C.CExpr := do
  let lhs ← lowerOperand fn lhsOperand
  let rhs ← lowerOperand fn rhsOperand
  let destType := lowerType dest.type
  if let some comparison := comparisonOp op then
    let signedComparison := match op with
      | .slt | .sle | .sgt | .sge => true
      | _ => false
    let lhs :=
      if signedComparison then lhs
      else if lhs.type.isSigned then .cast (unsignedRepresentation lhs.type) lhs else lhs
    let rhs :=
      if signedComparison then rhs
      else if rhs.type.isSigned then .cast (unsignedRepresentation rhs.type) rhs else rhs
    pure (.binary destType comparison lhs rhs)
  else
    let some operation := arithmeticOp op
      | throw { message := s!"unhandled binary operation {repr op}", function := some fn.name }
    match op with
    | .sdiv | .srem =>
        throw {
          message := "signed division/remainder requires a checked runtime helper"
          function := some fn.name
        }
    | .ashr =>
        throw {
          message := "arithmetic right shift requires a target-independent runtime helper"
          function := some fn.name
        }
    | _ =>
        if destType.isSigned && (op == .add || op == .sub || op == .mul
            || op == .bitAnd || op == .bitOr || op == .bitXor || op == .shl) then
          let unsigned := unsignedRepresentation destType
          pure (.cast destType (.binary unsigned operation
            (.cast unsigned lhs) (.cast unsigned rhs)))
        else
          pure (.binary destType operation lhs rhs)

private def runtimeExternal
    (symbol : String)
    (params : Array C.CType)
    (result : C.CType) : C.CExternal := {
  name := symbol
  params
  result
  trusted := true
}

structure InstructionResult where
  statements : Array C.CStmt
  externals : Array C.CExternal := #[]

def lowerInstruction
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (instruction : CCIR.Instruction) : Except LowerError InstructionResult := do
  let withContext (error : LowerError) := {
    error with
    function := error.function.orElse (fun _ => some fn.name)
    block := error.block.orElse (fun _ => some block.id)
    instruction := error.instruction.orElse (fun _ => some index)
  }
  try
    match instruction with
    | .assign dest value =>
        pure { statements := #[.assign (localExpr dest) (← lowerOperand fn value)] }
    | .unary dest op value =>
        pure { statements := #[.assign (localExpr dest) (← lowerUnary fn dest op value)] }
    | .binary dest op lhs rhs =>
        pure { statements := #[.assign (localExpr dest) (← lowerBinary fn dest op lhs rhs)] }
    | .load dest address =>
        let address ← lowerOperand fn address
        pure { statements := #[.assign (localExpr dest) (.deref (lowerType dest.type) address)] }
    | .store address value =>
        let address ← lowerOperand fn address
        let value ← lowerOperand fn value
        pure { statements := #[.assign (.deref value.type address) value] }
    | .call dest callee args result =>
        let mut loweredArgs := #[]
        for arg in args do
          loweredArgs := loweredArgs.push (← lowerOperand fn arg)
        pure {
          statements := #[.call (dest.map localExpr) (ABI.mangle callee.name)
            loweredArgs (lowerType result)]
        }
    | .runtimeCall dest symbol args result =>
        let mut loweredArgs := #[]
        for arg in args do
          loweredArgs := loweredArgs.push (← lowerOperand fn arg)
        pure {
          statements := #[.call (dest.map localExpr) symbol loweredArgs (lowerType result)]
          externals := #[runtimeExternal symbol (loweredArgs.map C.CExpr.type) (lowerType result)]
        }
    | .retain value =>
        let value ← lowerOperand fn value
        pure {
          statements := #[.call none "lean_inc" #[value] .void]
          externals := #[runtimeExternal "lean_inc" #[value.type] .void]
        }
    | .release value =>
        let value ← lowerOperand fn value
        pure {
          statements := #[.call none "lean_dec" #[value] .void]
          externals := #[runtimeExternal "lean_dec" #[value.type] .void]
        }
    | .allocCtor dest tag fieldCount =>
        let args := #[
          C.CExpr.uintLit .u32 tag,
          C.CExpr.uintLit .u32 fieldCount,
          C.CExpr.uintLit .u32 0
        ]
        pure {
          statements := #[.call (some (localExpr dest)) "lean_alloc_ctor" args
            (lowerType dest.type)]
          externals := #[runtimeExternal "lean_alloc_ctor" #[.u32, .u32, .u32]
            (lowerType dest.type)]
        }
    | .setField object index value =>
        let object ← lowerOperand fn object
        let value ← lowerOperand fn value
        pure {
          statements := #[.call none "lean_ctor_set"
            #[object, .uintLit .usize index, value] .void]
          externals := #[runtimeExternal "lean_ctor_set"
            #[object.type, .usize, value.type] .void]
        }
    | .getTag dest object =>
        let object ← lowerOperand fn object
        pure {
          statements := #[.call (some (localExpr dest)) "lean_obj_tag"
            #[object] (lowerType dest.type)]
          externals := #[runtimeExternal "lean_obj_tag" #[object.type] (lowerType dest.type)]
        }
    | .project dest object index =>
        let object ← lowerOperand fn object
        pure {
          statements := #[.call (some (localExpr dest)) "lean_ctor_get"
            #[object, .uintLit .usize index] (lowerType dest.type)]
          externals := #[runtimeExternal "lean_ctor_get" #[object.type, .usize]
            (lowerType dest.type)]
        }
  catch error =>
    throw (withContext error)

private def lowerTerminator
    (fn : CCIR.Function)
    (block : CCIR.Block) : Except LowerError (Array C.CStmt) := do
  match block.terminator with
  | .goto target => pure #[.goto (ABI.blockLabel target.value)]
  | .branch condition thenBlock elseBlock =>
      let condition ← lowerOperand fn condition
      pure #[.ifThenElse condition
        #[.goto (ABI.blockLabel thenBlock.value)]
        #[.goto (ABI.blockLabel elseBlock.value)]]
  | .switch discriminant cases default =>
      let discriminant ← lowerOperand fn discriminant
      let cases := cases.map fun (value, target) => {
        value
        body := #[.goto (ABI.blockLabel target.value)]
      }
      let default := default.map fun target => #[.goto (ABI.blockLabel target.value)]
      pure #[.switch discriminant cases default]
  | .return none => pure #[.return none]
  | .return (some value) => pure #[.return (some (← lowerOperand fn value))]
  | .unreachable reason => pure #[.unreachable reason]

private def collectDestinations (fn : CCIR.Function) : Array CCIR.LocalDecl :=
  fn.blocks.foldl (init := #[]) fun declarations block =>
    block.instructions.foldl (init := declarations) fun current instruction =>
      match instruction.destination? with
      | none => current
      | some decl =>
          if fn.params.any (fun param => param.id == decl.id) then current
          else if current.any (fun existing => existing.id == decl.id) then current
          else current.push decl

private def addExternal
    (externals : Array C.CExternal)
    (external : C.CExternal) : Array C.CExternal :=
  if externals.any (fun existing => existing.name == external.name) then externals
  else externals.push external

private def lowerFunction (fn : CCIR.Function) :
    Except LowerError (C.CFunction × Array C.CExternal) := do
  let mut body : Array C.CStmt := #[]
  for sourceDecl in fn.sourceDecl do
    body := body.push (.comment s!"Lean declaration: {sourceDecl}")
  for decl in collectDestinations fn do
    body := body.push (.decl (lowerType decl.type) (ABI.localName decl.id.value))
  body := body.push (.goto (ABI.blockLabel fn.entry.value))
  let mut externals := #[]
  for block in fn.blocks do
    body := body.push (.label (ABI.blockLabel block.id.value))
    for index in [:block.instructions.size] do
      let result ← lowerInstruction fn block index block.instructions[index]!
      body := body ++ result.statements
      for external in result.externals do
        externals := addExternal externals external
    body := body ++ (← lowerTerminator fn block)
  pure ({
    name := ABI.mangle fn.name.name
    params := fn.params.map fun param => {
      name := ABI.localName param.id.value
      type := lowerType param.type
    }
    result := lowerType fn.result
    body
    sourceDecl := fn.sourceDecl
  }, externals)

def lowerProgram (program : CCIR.Program) : Except (Array LowerError) C.CTranslationUnit := do
  let validation := CCIR.validateProgram program
  if !validation.isEmpty then
    throw (validation.map fun error => { message := error.pretty })
  let mut functions := #[]
  let mut externals := #[]
  for fn in program.functions do
    match lowerFunction fn with
    | .error error => throw #[error]
    | .ok (lowered, usedExternals) =>
        functions := functions.push lowered
        externals := externals.push {
          name := lowered.name
          params := lowered.params.map C.CParam.type
          result := lowered.result
          trusted := true
        }
        for external in usedExternals do
          externals := addExternal externals external
  pure {
    includes := #["stdint.h", "stddef.h", "lean/lean.h"]
    externals
    functions
  }

def compileProgram
    (profile : C.Profile)
    (program : CCIR.Program) : Except (Array String) (C.CTranslationUnit × String) := do
  let unit ← match lowerProgram program with
    | .ok unit => pure unit
    | .error errors => throw (errors.map LowerError.pretty)
  match C.emitChecked profile unit with
  | .ok source => pure (unit, source)
  | .error errors => throw (errors.map C.ValidationError.pretty)

end LeanCompCert.Lower
