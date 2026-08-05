import LeanCompCert.CCIR.Basic

namespace LeanCompCert.CCIR

inductive ValidationRule where
  | duplicateFunction
  | duplicateBlock
  | missingEntry
  | missingBlock
  | duplicateLocal
  | unknownLocal
  | operandType
  | instructionType
  | returnType
  | callSignature
  | unsupported
  deriving Repr, BEq, DecidableEq, Inhabited

def ValidationRule.toString : ValidationRule → String
  | .duplicateFunction => "duplicate-function"
  | .duplicateBlock => "duplicate-block"
  | .missingEntry => "missing-entry"
  | .missingBlock => "missing-block"
  | .duplicateLocal => "duplicate-local"
  | .unknownLocal => "unknown-local"
  | .operandType => "operand-type"
  | .instructionType => "instruction-type"
  | .returnType => "return-type"
  | .callSignature => "call-signature"
  | .unsupported => "unsupported"

structure ValidationError where
  rule : ValidationRule
  message : String
  function : Option GlobalId := none
  block : Option BlockId := none
  instruction : Option Nat := none
  deriving Repr, BEq, Inhabited

def ValidationError.pretty (error : ValidationError) : String :=
  let fn := error.function.map (fun name => s!" in `{name.name}`") |>.getD ""
  let block := error.block.map (fun id => s!" at {id}") |>.getD ""
  let instruction := error.instruction.map (fun index => s!" instruction {index}") |>.getD ""
  s!"[{error.rule.toString}]{fn}{block}{instruction}: {error.message}"

private def findLocalType? (locals : Array LocalDecl) (id : LocalId) : Option CCType :=
  (locals.toList.find? (fun decl => decl.id == id)).map LocalDecl.type

private def operandType? (locals : Array LocalDecl) : Operand → Option CCType
  | .local id => findLocalType? locals id
  | .global _ => none
  | .uintLit type _ | .intLit type _ | .null type => some type

private def addError
    (errors : Array ValidationError)
    (rule : ValidationRule)
    (message : String)
    (fn : Function)
    (block : Option BlockId := none)
    (instruction : Option Nat := none) : Array ValidationError :=
  errors.push {
    rule
    message
    function := some fn.name
    block
    instruction
  }

private def collectLocals (fn : Function) : Array LocalDecl :=
  fn.blocks.foldl (init := fn.params) fun locals block =>
    block.instructions.foldl (init := locals) fun current instruction =>
      match instruction.destination? with
      | some decl =>
          match findLocalType? current decl.id with
          | none => current.push decl
          | some _ => current
      | none => current

private def validateLocalDeclarations (fn : Function) : Array ValidationError := Id.run do
  let mut errors := #[]
  let mut locals : Array LocalDecl := #[]
  let declarations :=
    fn.blocks.foldl (init := fn.params) fun result block =>
      block.instructions.foldl (init := result) fun current instruction =>
        match instruction.destination? with
        | some decl => current.push decl
        | none => current
  for decl in declarations do
    match findLocalType? locals decl.id with
    | none => locals := locals.push decl
    | some previous =>
        if previous != decl.type then
          errors := addError errors .duplicateLocal
            s!"local {decl.id} has conflicting types {previous} and {decl.type}" fn
  return errors

private def validateOperand
    (fn : Function)
    (block : Block)
    (index : Nat)
    (locals : Array LocalDecl)
    (operand : Operand) : Array ValidationError :=
  match operand with
  | .local id =>
      if (findLocalType? locals id).isSome then #[]
      else #[{
        rule := .unknownLocal
        message := s!"operand references undeclared local {id}"
        function := some fn.name
        block := some block.id
        instruction := some index
      }]
  | .global id => #[{
      rule := .operandType
      message := s!"global @{id.name} cannot be used as an untyped value operand"
      function := some fn.name
      block := some block.id
      instruction := some index
    }]
  | .uintLit type _ =>
      if type.isUnsigned then #[] else #[{
        rule := .operandType
        message := s!"unsigned literal has non-unsigned type {type}"
        function := some fn.name
        block := some block.id
        instruction := some index
      }]
  | .intLit type _ =>
      if type.isInteger then #[] else #[{
        rule := .operandType
        message := s!"integer literal has non-integer type {type}"
        function := some fn.name
        block := some block.id
        instruction := some index
      }]
  | .null type =>
      match type with
      | .ptr _ | .fnPtr _ _ | .obj => #[]
      | _ => #[{
          rule := .operandType
          message := s!"null has non-pointer type {type}"
          function := some fn.name
          block := some block.id
          instruction := some index
        }]

private def sameType
    (errors : Array ValidationError)
    (fn : Function)
    (block : Block)
    (index : Nat)
    (actual : Option CCType)
    (expected : CCType)
    (context : String) : Array ValidationError :=
  match actual with
  | some type =>
      if type == expected then errors
      else addError errors .instructionType
        s!"{context}: expected {expected}, got {type}" fn (some block.id) (some index)
  | none => errors

private def validateInstruction
    (fn : Function)
    (block : Block)
    (index : Nat)
    (locals : Array LocalDecl)
    (instruction : Instruction) : Array ValidationError := Id.run do
  let mut errors := #[]
  for operand in instruction.operands do
    errors := errors ++ validateOperand fn block index locals operand
  match instruction with
  | .assign dest value =>
      errors := sameType errors fn block index (operandType? locals value) dest.type "assignment"
  | .unary dest op value =>
      match op with
      | .cast target =>
          if target != dest.type then
            errors := addError errors .instructionType
              s!"cast target {target} differs from destination {dest.type}"
              fn (some block.id) (some index)
      | .bitNot | .boolNot | .neg =>
          if !dest.type.isInteger then
            errors := addError errors .instructionType
              s!"integer unary operation has destination type {dest.type}"
              fn (some block.id) (some index)
          errors := sameType errors fn block index (operandType? locals value)
            dest.type "unary operand"
  | .binary dest op lhs rhs =>
      let lhsType := operandType? locals lhs
      let rhsType := operandType? locals rhs
      let comparison := match op with
        | .eq | .ne | .ult | .ule | .ugt | .uge
        | .slt | .sle | .sgt | .sge => true
        | _ => false
      if comparison then
        if dest.type != .u8 then
          errors := addError errors .instructionType
            s!"comparison destination must be u8, got {dest.type}"
            fn (some block.id) (some index)
        match lhsType, rhsType with
        | some lhsType, some rhsType =>
            if lhsType != rhsType then
              errors := addError errors .instructionType
                s!"comparison operands differ: {lhsType} and {rhsType}"
                fn (some block.id) (some index)
        | _, _ => pure ()
      else
        if !dest.type.isInteger then
          errors := addError errors .instructionType
            s!"binary integer operation has destination type {dest.type}"
            fn (some block.id) (some index)
        errors := sameType errors fn block index lhsType dest.type "left operand"
        match op with
        | .shl | .lshr | .ashr =>
            match rhsType with
            | some type =>
                if !type.isInteger then
                  errors := addError errors .instructionType
                    s!"shift count has non-integer type {type}"
                    fn (some block.id) (some index)
            | none => pure ()
        | _ =>
            errors := sameType errors fn block index rhsType dest.type "right operand"
  | .load dest address =>
      match operandType? locals address with
      | some (.ptr element) =>
          if element != dest.type then
            errors := addError errors .instructionType
              s!"load destination {dest.type} differs from pointer element {element}"
              fn (some block.id) (some index)
      | some type =>
          errors := addError errors .instructionType
            s!"load address has non-pointer type {type}" fn (some block.id) (some index)
      | none => pure ()
  | .store address value =>
      match operandType? locals address with
      | some (.ptr element) =>
          errors := sameType errors fn block index (operandType? locals value)
            element "stored value"
      | some type =>
          errors := addError errors .instructionType
            s!"store address has non-pointer type {type}" fn (some block.id) (some index)
      | none => pure ()
  | .loadIndex dest base offset =>
      match operandType? locals base with
      | some (.ptr element) =>
          if element != dest.type then
            errors := addError errors .instructionType
              s!"indexed load destination {dest.type} differs from pointer element {element}"
              fn (some block.id) (some index)
      | some type =>
          errors := addError errors .instructionType
            s!"indexed load base has non-pointer type {type}" fn (some block.id) (some index)
      | none => pure ()
      match operandType? locals offset with
      | some type =>
          if !type.isInteger then
            errors := addError errors .instructionType
              s!"indexed load offset has non-integer type {type}"
              fn (some block.id) (some index)
      | none => pure ()
  | .storeIndex base offset value =>
      match operandType? locals base with
      | some (.ptr element) =>
          errors := sameType errors fn block index (operandType? locals value)
            element "indexed stored value"
      | some type =>
          errors := addError errors .instructionType
            s!"indexed store base has non-pointer type {type}" fn (some block.id) (some index)
      | none => pure ()
      match operandType? locals offset with
      | some type =>
          if !type.isInteger then
            errors := addError errors .instructionType
              s!"indexed store offset has non-integer type {type}"
              fn (some block.id) (some index)
      | none => pure ()
  | .call dest _ _ result | .runtimeCall dest _ _ result =>
      match dest with
      | some decl =>
          if decl.type != result then
            errors := addError errors .instructionType
              s!"call result {result} differs from destination {decl.type}"
              fn (some block.id) (some index)
      | none =>
          if result != .void then
            errors := addError errors .instructionType
              s!"non-void call result {result} is discarded without an explicit sink"
              fn (some block.id) (some index)
  | .retain value | .release value =>
      errors := sameType errors fn block index (operandType? locals value) .obj
        "reference-count operand"
  | .allocCtor dest _ _ =>
      if dest.type != .obj then
        errors := addError errors .instructionType
          s!"constructor allocation destination must be obj, got {dest.type}"
          fn (some block.id) (some index)
  | .setField object _ _ =>
      errors := sameType errors fn block index (operandType? locals object) .obj
        "field-store object"
  | .getTag dest object =>
      if !dest.type.isUnsigned then
        errors := addError errors .instructionType
          s!"constructor tag destination must be unsigned, got {dest.type}"
          fn (some block.id) (some index)
      errors := sameType errors fn block index (operandType? locals object) .obj
        "tag object"
  | .project _ object _ =>
      errors := sameType errors fn block index (operandType? locals object) .obj
        "projected object"
  return errors

private def validateTerminator
    (fn : Function)
    (block : Block)
    (locals : Array LocalDecl) : Array ValidationError := Id.run do
  let mut errors := #[]
  let addMissing (target : BlockId) :=
    if (fn.findBlock? target).isSome then #[]
    else #[{
      rule := .missingBlock
      message := s!"terminator targets missing block {target}"
      function := some fn.name
      block := some block.id
    }]
  match block.terminator with
  | .goto target => errors := errors ++ addMissing target
  | .branch condition thenBlock elseBlock =>
      errors := errors ++ validateOperand fn block block.instructions.size locals condition
      match operandType? locals condition with
      | some type =>
          if !type.isInteger then
            errors := addError errors .instructionType
              s!"branch condition has non-integer type {type}" fn (some block.id)
      | none => pure ()
      errors := errors ++ addMissing thenBlock ++ addMissing elseBlock
  | .switch discriminant cases default =>
      errors := errors ++ validateOperand fn block block.instructions.size locals discriminant
      match operandType? locals discriminant with
      | some type =>
          if !type.isInteger then
            errors := addError errors .instructionType
              s!"switch discriminant has non-integer type {type}" fn (some block.id)
      | none => pure ()
      for (_, target) in cases do
        errors := errors ++ addMissing target
      for target in default do
        errors := errors ++ addMissing target
  | .return value =>
      match value with
      | none =>
          if fn.result != .void then
            errors := addError errors .returnType
              s!"void return in function returning {fn.result}" fn (some block.id)
      | some operand =>
          errors := errors ++ validateOperand fn block block.instructions.size locals operand
          errors := sameType errors fn block block.instructions.size
            (operandType? locals operand) fn.result "return"
  | .unreachable _ => pure ()
  return errors

def validateFunction (fn : Function) : Array ValidationError := Id.run do
  let mut errors := validateLocalDeclarations fn
  if !(fn.findBlock? fn.entry).isSome then
    errors := addError errors .missingEntry s!"entry block {fn.entry} does not exist" fn
  -- `seen` accumulates the block ids already visited.  It replaces a
  -- `fn.blocks[:index]` slice: `Subarray`'s `ForIn` instance does not reduce
  -- in the kernel, and this validator has to, for `Attest.Artifact.source?`
  -- to be checkable by `decide +kernel`.
  let mut seen : Array BlockId := #[]
  for index in [:fn.blocks.size] do
    let block := fn.blocks[index]!
    for previous in seen do
      if previous == block.id then
        errors := addError errors .duplicateBlock s!"duplicate block {block.id}" fn (some block.id)
    seen := seen.push block.id
    let locals := collectLocals fn
    for instructionIndex in [:block.instructions.size] do
      errors := errors ++ validateInstruction fn block instructionIndex locals
        block.instructions[instructionIndex]!
    errors := errors ++ validateTerminator fn block locals
  return errors

private def signature?
    (program : Program)
    (id : GlobalId) : Option (Array CCType × CCType) :=
  match program.findFunction? id with
  | some fn => some (fn.params.map LocalDecl.type, fn.result)
  | none =>
      (program.externals.toList.find? (fun external => external.name == id)).map
        (fun external => (external.args, external.result))

private def validateCalls (program : Program) (fn : Function) : Array ValidationError := Id.run do
  let locals := collectLocals fn
  let mut errors := #[]
  for block in fn.blocks do
    for index in [:block.instructions.size] do
      match block.instructions[index]! with
      | .call _ callee args result =>
          match signature? program callee with
          | none =>
              errors := addError errors .callSignature
                s!"unknown direct callee @{callee.name}" fn (some block.id) (some index)
          | some (expectedArgs, expectedResult) =>
              if expectedArgs.size != args.size then
                errors := addError errors .callSignature
                  s!"@{callee.name} expects {expectedArgs.size} arguments, got {args.size}"
                  fn (some block.id) (some index)
              for pair in (args.zip expectedArgs) do
                let (operand, expected) := pair
                errors := sameType errors fn block index (operandType? locals operand)
                  expected s!"argument to @{callee.name}"
              if expectedResult != result then
                errors := addError errors .callSignature
                  s!"@{callee.name} returns {expectedResult}, call records {result}"
                  fn (some block.id) (some index)
      | _ => pure ()
  return errors

def validateProgram (program : Program) : Array ValidationError := Id.run do
  let mut errors := #[]
  -- `seen` replaces a `program.functions[:index]` slice; see `validateFunction`.
  let mut seen : Array GlobalId := #[]
  for index in [:program.functions.size] do
    let fn := program.functions[index]!
    for previous in seen do
      if previous == fn.name then
        errors := errors.push {
          rule := .duplicateFunction
          message := s!"duplicate function @{fn.name.name}"
          function := some fn.name
        }
    seen := seen.push fn.name
    errors := errors ++ validateFunction fn ++ validateCalls program fn
  return errors

end LeanCompCert.CCIR
