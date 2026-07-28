import LeanCompCert.LCNF.Validate
import LeanCompCert.Lower.Pure

namespace LeanCompCert.Lower.LCNF

open LeanCompCert

structure Error where
  declaration : String
  feature : String
  message : String
  deriving Repr, BEq, Inhabited

def Error.pretty (error : Error) : String :=
  s!"LCNF lowering error in `{error.declaration}` [{error.feature}]: {error.message}"

private def lowerType : LCNF.ViewType → Except String CCIR.CCType
  | .void => .ok .void
  | .u8 => .ok .u8
  | .u16 => .ok .u16
  | .u32 => .ok .u32
  | .u64 => .ok .u64
  | .usize => .ok .usize
  | .f32 => .ok .f32
  | .f64 => .ok .f64
  | .object | .tagged | .taggedObject | .erased => .ok .obj
  | .unknown description => .error s!"unknown impure type: {description}"

private structure Binding where
  sourceId : String
  localDecl : CCIR.LocalDecl
  deriving Repr, Inhabited

private structure BuildState where
  bindings : Array Binding := #[]
  nextLocal : Nat := 0
  nextBlock : Nat := 1
  blocks : Array CCIR.Block := #[]
  deriving Repr, Inhabited

private def binding? (state : BuildState) (sourceId : String) : Option Binding :=
  state.bindings.toList.find? (fun binding => binding.sourceId == sourceId)

private def allocate
    (state : BuildState)
    (sourceId sourceName : String)
    (type : CCIR.CCType) : CCIR.LocalDecl × BuildState :=
  match binding? state sourceId with
  | some binding => (binding.localDecl, state)
  | none =>
      let localDecl : CCIR.LocalDecl := {
        id := ⟨state.nextLocal⟩
        type
        sourceName := if sourceName.isEmpty then none else some sourceName
      }
      (localDecl, {
        state with
        bindings := state.bindings.push { sourceId, localDecl }
        nextLocal := state.nextLocal + 1
      })

private def operand (declName : String) (state : BuildState) : LCNF.Arg → Except Error CCIR.Operand
  | .local sourceId =>
      match binding? state sourceId with
      | some binding => .ok (.local binding.localDecl.id)
      | none => .error {
          declaration := declName
          feature := "unknown-local"
          message := s!"LCNF value `{sourceId}` has no machine binding"
        }
  | .erased => .error {
      declaration := declName
      feature := "erased-argument"
      message := "erased arguments require the Lean tagged-object representation"
    }

private def localOperand
    (declName : String)
    (state : BuildState)
    (sourceId : String) : Except Error CCIR.Operand :=
  operand declName state (.local sourceId)

private def literal
    (declName : String)
    (_type : CCIR.CCType) : LCNF.Literal → Except Error CCIR.Operand
  | .u8 value => .ok (.uintLit .u8 value)
  | .u16 value => .ok (.uintLit .u16 value)
  | .u32 value => .ok (.uintLit .u32 value)
  | .u64 value => .ok (.uintLit .u64 value)
  | .usize value => .ok (.uintLit .usize value)
  | .nat _ => .error {
      declaration := declName
      feature := "natural-literal"
      message := "Nat literals require immediate-or-big-number object lowering"
    }
  | .string _ => .error {
      declaration := declName
      feature := "string-literal"
      message := "string constants require static Lean object emission"
    }

private def binaryPrimitive? (name : String) : Option CCIR.BinaryOp :=
  if name.endsWith ".add" then some .add
  else if name.endsWith ".sub" then some .sub
  else if name.endsWith ".mul" then some .mul
  else if name.endsWith ".div" then some .udiv
  else if name.endsWith ".mod" then some .urem
  else if name.endsWith ".and" then some .bitAnd
  else if name.endsWith ".or" then some .bitOr
  else if name.endsWith ".xor" then some .bitXor
  else if name.endsWith ".shiftLeft" then some .shl
  else if name.endsWith ".shiftRight" then some .lshr
  else if name.endsWith ".decEq" then some .eq
  else if name.endsWith ".decLt" then some .ult
  else if name.endsWith ".decLe" then some .ule
  else none

private def repeatInstruction
    (count : Nat)
    (instruction : CCIR.Instruction) : Array CCIR.Instruction :=
  Array.replicate count instruction

private def lowerValue
    (declName : String)
    (state : BuildState)
    (destination : CCIR.LocalDecl)
    (value : LCNF.Value) : Except Error (Array CCIR.Instruction) := do
  match value with
  | .literal value =>
      pure #[.assign destination (← literal declName destination.type value)]
  | .directCall callee args =>
      let mut operands := #[]
      for arg in args do
        operands := operands.push (← operand declName state arg)
      if let some operation := binaryPrimitive? callee then
        if operands.size != 2 then
          throw {
            declaration := declName
            feature := "primitive-arity"
            message := s!"primitive `{callee}` expects two arguments, got {operands.size}"
          }
        pure #[.binary destination operation operands[0]! operands[1]!]
      else
        pure #[.call (some destination) ⟨callee⟩ operands destination.type]
  | .ctor info args =>
      if info.objectFields == 0 && info.usizeFields == 0 && info.scalarBytes == 0 then
        pure #[.assign destination (.uintLit destination.type info.tag)]
      else
        let mut instructions := #[.allocCtor destination info.tag info.objectFields]
        let object := CCIR.Operand.local destination.id
        let mut objectIndex := 0
        for arg in args do
          match arg with
          | .erased => pure ()
          | .local _ =>
              if objectIndex < info.objectFields then
                instructions := instructions.push
                  (.setField object objectIndex (← operand declName state arg))
                objectIndex := objectIndex + 1
        pure instructions
  | .project (.object index) object =>
      pure #[.project destination (← localOperand declName state object) index]
  | .project (.usize _) _ | .project (.scalar _ _) _ =>
      throw {
        declaration := declName
        feature := "scalar-projection"
        message := "scalar constructor field layout lowering is not implemented"
      }
  | .erased =>
      throw {
        declaration := declName
        feature := "erased-value"
        message := "erased values require tagged-object lowering"
      }
  | .localCall _ _ =>
      throw {
        declaration := declName
        feature := "indirect-call"
        message := "closure calls require an exact arity-specific signature"
      }
  | .partialApply _ _ =>
      throw {
        declaration := declName
        feature := "partial-application"
        message := "closure allocation is not implemented"
      }
  | .reset _ _ | .reuse _ _ _ _ =>
      throw {
        declaration := declName
        feature := "reset-reuse"
        message := "destructive constructor reuse is not implemented"
      }
  | .box _ _ | .unbox _ | .isShared _ =>
      throw {
        declaration := declName
        feature := "boxed-value-operation"
        message := "boxed scalar operations are not in the pure first-order subset"
      }
  | .unsupported description =>
      throw {
        declaration := declName
        feature := "unsupported"
        message := description
      }

mutual

partial def lowerCode
    (declName : String)
    (resultType : CCIR.CCType)
    (code : LCNF.Code)
    (blockId : CCIR.BlockId)
    (instructions : Array CCIR.Instruction)
    (state : BuildState) : Except Error BuildState := do
  match code with
  | .letValue decl next =>
      let type ← lowerType decl.type |>.mapError fun message => {
        declaration := declName
        feature := "type"
        message
      }
      let (destination, state) := allocate state decl.id decl.name type
      let instructions := instructions ++ (← lowerValue declName state destination decl.value)
      lowerCode declName resultType next blockId instructions state
  | .return sourceId =>
      let value ← localOperand declName state sourceId
      pure { state with blocks := state.blocks.push {
        id := blockId
        instructions
        terminator := .return (some value)
      }}
  | .unreachable =>
      pure { state with blocks := state.blocks.push {
        id := blockId
        instructions
        terminator := .unreachable "Lean LCNF unreachable"
      }}
  | .cases discriminant alternatives =>
      let discriminant ← localOperand declName state discriminant
      let mut state := state
      let mut cases := #[]
      let mut default : Option CCIR.BlockId := none
      let mut scheduled : Array (CCIR.BlockId × LCNF.Code) := #[]
      for alternative in alternatives do
        let target : CCIR.BlockId := ⟨state.nextBlock⟩
        state := { state with nextBlock := state.nextBlock + 1 }
        match alternative with
        | .constructor info body =>
            cases := cases.push (info.tag, target)
            scheduled := scheduled.push (target, body)
        | .default body =>
            default := some target
            scheduled := scheduled.push (target, body)
      state := { state with blocks := state.blocks.push {
        id := blockId
        instructions
        terminator := .switch discriminant cases default
      }}
      for (target, body) in scheduled do
        state ← lowerCode declName resultType body target #[] state
      pure state
  | .setObjectField object index value next =>
      let instruction := .setField
        (← localOperand declName state object) index (← operand declName state value)
      lowerCode declName resultType next blockId (instructions.push instruction) state
  | .retain object count _ _ next =>
      let instruction := .retain (← localOperand declName state object)
      lowerCode declName resultType next blockId
        (instructions ++ repeatInstruction count instruction) state
  | .release object count _ _ _ next =>
      let instruction := .release (← localOperand declName state object)
      lowerCode declName resultType next blockId
        (instructions ++ repeatInstruction count instruction) state
  | .setTag _ _ _ =>
      throw {
        declaration := declName
        feature := "set-tag"
        message := "in-place constructor tag mutation is not implemented"
      }
  | .setUSizeField _ _ _ _ | .setScalarField _ _ _ _ _ _ =>
      throw {
        declaration := declName
        feature := "scalar-field-store"
        message := "scalar constructor field layout lowering is not implemented"
      }
  | .delete _ _ =>
      throw {
        declaration := declName
        feature := "explicit-delete"
        message := "explicit object deletion requires runtime ownership lowering"
      }
  | .joinPoint _ _ | .jump _ _ =>
      throw {
        declaration := declName
        feature := "join-point"
        message := "LCNF join-point CFG lowering is not implemented"
      }
  | .unsupported description =>
      throw {
        declaration := declName
        feature := "unsupported"
        message := description
      }

end

def lowerDecl (decl : LCNF.Decl) : Except Error CCIR.Function := do
  let resultType ← lowerType decl.result |>.mapError fun message => {
    declaration := decl.name
    feature := "result-type"
    message
  }
  let mut state : BuildState := {}
  let mut params := #[]
  for param in decl.params do
    let type ← lowerType param.type |>.mapError fun message => {
      declaration := decl.name
      feature := "parameter-type"
      message
    }
    let (localDecl, nextState) := allocate state param.id param.name type
    state := nextState
    params := params.push localDecl
  let body ← match decl.value with
    | .code body => pure body
    | .external => throw {
        declaration := decl.name
        feature := "external"
        message := "external declarations have no body to lower"
      }
  state ← lowerCode decl.name resultType body ⟨0⟩ #[] state
  pure {
    name := ⟨decl.name⟩
    params
    result := resultType
    entry := ⟨0⟩
    blocks := state.blocks
    sourceDecl := some decl.name
  }

structure ModuleResult where
  functions : Array CCIR.Function
  rejected : Array Error
  deriving Repr, Inhabited

def lowerModuleCompatible (module : LCNF.Module) : ModuleResult := Id.run do
  let mut functions := #[]
  let mut rejected := #[]
  for decl in module.declarations do
    match decl.value with
    | .external => pure ()
    | .code _ =>
        match lowerDecl decl with
        | .ok fn => functions := functions.push fn
        | .error error => rejected := rejected.push error
  return { functions, rejected }

end LeanCompCert.Lower.LCNF
