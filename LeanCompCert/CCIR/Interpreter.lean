import LeanCompCert.CCIR.Validate

namespace LeanCompCert.CCIR

inductive Value where
  | void
  | scalar (type : CCType) (value : Int)
  | null (type : CCType)
  | object (id : Nat)
  deriving Repr, BEq, Inhabited

def Value.type : Value → CCType
  | .void => .void
  | .scalar type _ => type
  | .null type => type
  | .object _ => .obj

def Value.pretty : Value → String
  | .void => "void"
  | .scalar type value => s!"{type}({value})"
  | .null type => s!"null<{type}>"
  | .object id => s!"object#{id}"

structure HeapObject where
  tag : Nat
  fields : Array Value
  refCount : Nat := 1
  deriving Repr, BEq, Inhabited

structure MachineState where
  heap : Array HeapObject := #[]
  remainingSteps : Nat
  executedSteps : Nat := 0
  deriving Repr, Inhabited

structure EvalError where
  message : String
  function : Option GlobalId := none
  block : Option BlockId := none
  deriving Repr, BEq

def EvalError.pretty (error : EvalError) : String :=
  let fn := error.function.map (fun id => s!" in @{id.name}") |>.getD ""
  let block := error.block.map (fun id => s!" at {id}") |>.getD ""
  s!"evaluation error{fn}{block}: {error.message}"

structure EvalResult where
  value : Value
  steps : Nat
  heap : Array HeapObject
  deriving Repr, BEq

private abbrev Locals := Array (LocalId × Value)

private def lookupLocal? (locals : Locals) (id : LocalId) : Option Value :=
  (locals.toList.find? (fun entry => entry.1 == id)).map Prod.snd

private def setLocal (locals : Locals) (id : LocalId) (value : Value) : Locals :=
  if (lookupLocal? locals id).isSome then
    locals.map fun entry => if entry.1 == id then (id, value) else entry
  else
    locals.push (id, value)

private def consume
    (state : MachineState)
    (fn : Function)
    (block : Option BlockId := none) : Except EvalError MachineState :=
  match state.remainingSteps with
  | 0 => .error {
      message := "step limit exhausted"
      function := some fn.name
      block
    }
  | remaining + 1 => .ok {
      state with
      remainingSteps := remaining
      executedSteps := state.executedSteps + 1
    }

private def evalOperand (locals : Locals) : Operand → Except EvalError Value
  | .local id =>
      match lookupLocal? locals id with
      | some value => .ok value
      | none => .error { message := s!"unknown local {id}" }
  | .global id => .error { message := s!"global @{id.name} is not a first-class value" }
  | .uintLit type value => .ok (.scalar type (Int.ofNat value))
  | .intLit type value => .ok (.scalar type value)
  | .null type => .ok (.null type)

private def modulus (type : CCType) : Option Int :=
  type.bitWidth.map fun bits => Int.ofNat (2 ^ bits)

private def unsignedValue (type : CCType) (value : Int) : Except EvalError Int :=
  match modulus type with
  | none => .error { message := s!"type {type} has no integer modulus" }
  | some modulus =>
      if modulus == 0 then .error { message := "zero integer modulus" }
      else .ok (value.emod modulus)

private def normalize (type : CCType) (value : Int) : Except EvalError Int := do
  let unsigned ← unsignedValue type value
  if type.isSigned then
    let bits := type.bitWidth.getD 0
    let half := Int.ofNat (2 ^ (bits - 1))
    let modulus := Int.ofNat (2 ^ bits)
    pure (if unsigned >= half then unsigned - modulus else unsigned)
  else
    pure unsigned

private def scalarValue (value : Value) : Except EvalError (CCType × Int) :=
  match value with
  | .scalar type value => .ok (type, value)
  | other => .error { message := s!"expected scalar, got {other.pretty}" }

private def boolValue (condition : Bool) : Value :=
  .scalar .u8 (if condition then 1 else 0)

private def evalUnary (op : UnaryOp) (destType : CCType) (input : Value) :
    Except EvalError Value := do
  let (inputType, value) ← scalarValue input
  let result ← match op with
    | .bitNot =>
        let unsigned ← unsignedValue inputType value
        let modulus ← match modulus inputType with
          | some value => pure value
          | none => throw { message := s!"cannot invert {inputType}" }
        normalize destType (modulus - 1 - unsigned)
    | .boolNot => normalize destType (if value == 0 then 1 else 0)
    | .neg => normalize destType (-value)
    | .cast target => normalize target value
  pure (.scalar destType result)

private def evalBinary
    (op : BinaryOp)
    (destType : CCType)
    (lhs rhs : Value) : Except EvalError Value := do
  let (lhsType, lhsValue) ← scalarValue lhs
  let (_, rhsValue) ← scalarValue rhs
  let lhsUnsigned ← unsignedValue lhsType lhsValue
  let rhsUnsigned ← unsignedValue lhsType rhsValue
  let shift := rhsUnsigned.toNat
  match op with
  | .eq => pure (boolValue (lhsValue == rhsValue))
  | .ne => pure (boolValue (lhsValue != rhsValue))
  | .ult => pure (boolValue (lhsUnsigned < rhsUnsigned))
  | .ule => pure (boolValue (lhsUnsigned <= rhsUnsigned))
  | .ugt => pure (boolValue (lhsUnsigned > rhsUnsigned))
  | .uge => pure (boolValue (lhsUnsigned >= rhsUnsigned))
  | .slt => pure (boolValue (lhsValue < rhsValue))
  | .sle => pure (boolValue (lhsValue <= rhsValue))
  | .sgt => pure (boolValue (lhsValue > rhsValue))
  | .sge => pure (boolValue (lhsValue >= rhsValue))
  | .udiv =>
      if rhsUnsigned == 0 then throw { message := "unsigned division by zero" }
      else pure (.scalar destType (← normalize destType (lhsUnsigned.ediv rhsUnsigned)))
  | .urem =>
      if rhsUnsigned == 0 then throw { message := "unsigned remainder by zero" }
      else pure (.scalar destType (← normalize destType (lhsUnsigned.emod rhsUnsigned)))
  | .sdiv =>
      if rhsValue == 0 then throw { message := "signed division by zero" }
      else pure (.scalar destType (← normalize destType (lhsValue.ediv rhsValue)))
  | .srem =>
      if rhsValue == 0 then throw { message := "signed remainder by zero" }
      else pure (.scalar destType (← normalize destType (lhsValue.emod rhsValue)))
  | .add => pure (.scalar destType (← normalize destType (lhsValue + rhsValue)))
  | .sub => pure (.scalar destType (← normalize destType (lhsValue - rhsValue)))
  | .mul => pure (.scalar destType (← normalize destType (lhsValue * rhsValue)))
  | .bitAnd =>
      let value := Int.ofNat (Nat.land lhsUnsigned.toNat rhsUnsigned.toNat)
      pure (.scalar destType (← normalize destType value))
  | .bitOr =>
      let value := Int.ofNat (Nat.lor lhsUnsigned.toNat rhsUnsigned.toNat)
      pure (.scalar destType (← normalize destType value))
  | .bitXor =>
      let value := Int.ofNat (Nat.xor lhsUnsigned.toNat rhsUnsigned.toNat)
      pure (.scalar destType (← normalize destType value))
  | .shl =>
      pure (.scalar destType (← normalize destType (Int.shiftLeft lhsUnsigned shift)))
  | .lshr =>
      pure (.scalar destType (← normalize destType (Int.ofNat (Nat.shiftRight lhsUnsigned.toNat shift))))
  | .ashr =>
      pure (.scalar destType (← normalize destType (Int.shiftRight lhsValue shift)))

private def evalOperands (locals : Locals) (operands : Array Operand) :
    Except EvalError (Array Value) := do
  let mut values := #[]
  for operand in operands do
    values := values.push (← evalOperand locals operand)
  pure values

private def heapObject
    (state : MachineState)
    (id : Nat) : Except EvalError HeapObject :=
  match state.heap[id]? with
  | some object => .ok object
  | none => .error { message := s!"invalid heap object #{id}" }

mutual

partial def evalInstruction
    (program : Program)
    (fn : Function)
    (block : Block)
    (locals : Locals)
    (state : MachineState)
    (instruction : Instruction) : Except EvalError (Locals × MachineState) := do
  let state ← consume state fn (some block.id)
  match instruction with
  | .assign dest operand =>
      let value ← evalOperand locals operand
      pure (setLocal locals dest.id value, state)
  | .unary dest op operand =>
      let value ← evalOperand locals operand
      let result ← evalUnary op dest.type value
      pure (setLocal locals dest.id result, state)
  | .binary dest op lhs rhs =>
      let lhs ← evalOperand locals lhs
      let rhs ← evalOperand locals rhs
      let result ← evalBinary op dest.type lhs rhs
      pure (setLocal locals dest.id result, state)
  | .call dest callee operands _ =>
      let args ← evalOperands locals operands
      let (result, state) ← evalFunction program callee args state
      match dest with
      | some dest => pure (setLocal locals dest.id result, state)
      | none => pure (locals, state)
  | .runtimeCall _ symbol _ _ =>
      throw {
        message := s!"runtime call `{symbol}` has no interpreter implementation"
        function := some fn.name
        block := some block.id
      }
  | .load _ _ | .store _ _ =>
      throw {
        message := "raw memory operations are unavailable in the safe CCIR interpreter"
        function := some fn.name
        block := some block.id
      }
  | .retain operand =>
      match ← evalOperand locals operand with
      | .object id =>
          let object ← heapObject state id
          let heap := state.heap.set! id { object with refCount := object.refCount + 1 }
          pure (locals, { state with heap })
      | value => throw { message := s!"retain expects object, got {value.pretty}" }
  | .release operand =>
      match ← evalOperand locals operand with
      | .object id =>
          let object ← heapObject state id
          if object.refCount == 0 then
            throw { message := s!"reference-count underflow on object #{id}" }
          let heap := state.heap.set! id { object with refCount := object.refCount - 1 }
          pure (locals, { state with heap })
      | value => throw { message := s!"release expects object, got {value.pretty}" }
  | .allocCtor dest tag fieldCount =>
      let id := state.heap.size
      let fields := Array.replicate fieldCount (.null .obj)
      let heap := state.heap.push { tag, fields }
      pure (setLocal locals dest.id (.object id), { state with heap })
  | .setField objectOperand index valueOperand =>
      match ← evalOperand locals objectOperand with
      | .object id =>
          let object ← heapObject state id
          if index >= object.fields.size then
            throw { message := s!"field {index} is out of bounds for object #{id}" }
          let value ← evalOperand locals valueOperand
          let object := { object with fields := object.fields.set! index value }
          pure (locals, { state with heap := state.heap.set! id object })
      | value => throw { message := s!"set_field expects object, got {value.pretty}" }
  | .getTag dest objectOperand =>
      match ← evalOperand locals objectOperand with
      | .object id =>
          let object ← heapObject state id
          pure (setLocal locals dest.id (.scalar dest.type object.tag), state)
      | value => throw { message := s!"get_tag expects object, got {value.pretty}" }
  | .project dest objectOperand index =>
      match ← evalOperand locals objectOperand with
      | .object id =>
          let object ← heapObject state id
          match object.fields[index]? with
          | some value => pure (setLocal locals dest.id value, state)
          | none => throw { message := s!"field {index} is out of bounds for object #{id}" }
      | value => throw { message := s!"project expects object, got {value.pretty}" }

partial def evalBlock
    (program : Program)
    (fn : Function)
    (block : Block)
    (locals : Locals)
    (state : MachineState) : Except EvalError (Value × MachineState) := do
  let mut locals := locals
  let mut state := state
  for instruction in block.instructions do
    let result ← evalInstruction program fn block locals state instruction
    locals := result.1
    state := result.2
  let finalState ← consume state fn (some block.id)
  match block.terminator with
  | .goto target =>
      match fn.findBlock? target with
      | some target => evalBlock program fn target locals finalState
      | none => throw { message := s!"missing block {target}", function := some fn.name }
  | .branch condition thenBlock elseBlock =>
      let (_, value) ← scalarValue (← evalOperand locals condition)
      let target := if value != 0 then thenBlock else elseBlock
      match fn.findBlock? target with
      | some target => evalBlock program fn target locals finalState
      | none => throw { message := s!"missing block {target}", function := some fn.name }
  | .switch discriminant cases default =>
      let (_, value) ← scalarValue (← evalOperand locals discriminant)
      let selected := (cases.toList.find? (fun entry => Int.ofNat entry.1 == value)).map Prod.snd
      match selected.orElse (fun _ => default) with
      | some target =>
          match fn.findBlock? target with
          | some target => evalBlock program fn target locals finalState
          | none => throw { message := s!"missing block {target}", function := some fn.name }
      | none => throw {
          message := s!"switch value {value} has no case or default"
          function := some fn.name
          block := some block.id
        }
  | .return none => pure (.void, finalState)
  | .return (some operand) => pure (← evalOperand locals operand, finalState)
  | .unreachable reason => throw {
      message := s!"reached unreachable instruction: {reason}"
      function := some fn.name
      block := some block.id
    }

partial def evalFunction
    (program : Program)
    (id : GlobalId)
    (args : Array Value)
    (state : MachineState) : Except EvalError (Value × MachineState) := do
  let fn ← match program.findFunction? id with
    | some fn => pure fn
    | none => throw { message := s!"unknown function @{id.name}" }
  if args.size != fn.params.size then
    throw {
      message := s!"@{id.name} expects {fn.params.size} arguments, got {args.size}"
      function := some id
    }
  let mut locals := #[]
  for pair in fn.params.zip args do
    locals := locals.push (pair.1.id, pair.2)
  let entry ← match fn.findBlock? fn.entry with
    | some block => pure block
    | none => throw {
        message := s!"missing entry block {fn.entry}"
        function := some id
      }
  evalBlock program fn entry locals state

end

def evalPure
    (program : Program)
    (entry : GlobalId)
    (args : Array Value)
    (maxSteps : Nat := 100000) : Except EvalError EvalResult := do
  let validation := validateProgram program
  if !validation.isEmpty then
    throw {
      message := s!"program failed validation: {validation[0]!.pretty}"
      function := some entry
    }
  let initial : MachineState := { remainingSteps := maxSteps }
  let (value, state) ← evalFunction program entry args initial
  pure { value, steps := state.executedSteps, heap := state.heap }

def eval
    (program : Program)
    (entry : GlobalId)
    (args : Array Value)
    (maxSteps : Nat := 100000) : IO (Except EvalError EvalResult) :=
  pure (evalPure program entry args maxSteps)

end LeanCompCert.CCIR
