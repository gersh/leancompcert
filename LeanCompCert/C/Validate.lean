import LeanCompCert.ABI.Symbols
import LeanCompCert.C.Profile

namespace LeanCompCert.C

inductive ValidationRule where
  | invalidIdentifier
  | duplicateSymbol
  | unsupportedType
  | signedOverflow
  | pointerArithmetic
  | incompatibleAssignment
  | incompatibleCall
  | invalidCondition
  | duplicateCase
  | missingLabel
  | untrustedExternal
  deriving Repr, BEq, DecidableEq, Inhabited

def ValidationRule.toString : ValidationRule → String
  | .invalidIdentifier => "invalid-identifier"
  | .duplicateSymbol => "duplicate-symbol"
  | .unsupportedType => "unsupported-type"
  | .signedOverflow => "signed-overflow"
  | .pointerArithmetic => "pointer-arithmetic"
  | .incompatibleAssignment => "incompatible-assignment"
  | .incompatibleCall => "incompatible-call"
  | .invalidCondition => "invalid-condition"
  | .duplicateCase => "duplicate-case"
  | .missingLabel => "missing-label"
  | .untrustedExternal => "untrusted-external"

structure ValidationError where
  rule : ValidationRule
  message : String
  function : Option String := none
  statementPath : Array Nat := #[]
  deriving Repr, BEq, Inhabited

def ValidationError.pretty (error : ValidationError) : String :=
  let fn := error.function.map (fun name => s!" in `{name}`") |>.getD ""
  let path :=
    if error.statementPath.isEmpty then ""
    else s!" at statement {String.intercalate "." (error.statementPath.toList.map toString)}"
  s!"[{error.rule.toString}]{fn}{path}: {error.message}"

private def isIdentStart (character : Char) : Bool :=
  character == '_' || character.isAlpha

private def isIdentRest (character : Char) : Bool :=
  isIdentStart character || character.isDigit

private def keywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do",
   "double", "else", "enum", "extern", "float", "for", "goto", "if",
   "inline", "int", "long", "register", "restrict", "return", "short",
   "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
   "unsigned", "void", "volatile", "while", "_Alignas", "_Alignof",
   "_Atomic", "_Bool", "_Complex", "_Generic", "_Imaginary", "_Noreturn",
   "_Static_assert", "_Thread_local"]

def isValidIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      isIdentStart first
        && rest.all isIdentRest
        && !(keywords.contains name)

/-- Compiler-generated scalar local names are C identifiers at every index. -/
theorem isValidIdentifier_localName (id : Nat) :
    isValidIdentifier (ABI.localName id) = true := by
  change isValidIdentifier ("v_" ++ id.repr) = true
  simp [isValidIdentifier, isIdentStart, isIdentRest, Nat.toList_repr]
  constructor
  · intro character hCharacter
    right
    exact Nat.isDigit_of_mem_toDigits
      (b := 10) (n := id) (c := character)
      (by decide) (by decide) hCharacter
  · intro hKeyword
    have hKeywords : ∀ keyword ∈ keywords,
        keyword.startsWith "v_" = false := by
      decide +kernel
    have hFalse := hKeywords ("v_" ++ id.repr) hKeyword
    have hTrue : ("v_" ++ id.repr).startsWith "v_" = true := by
      simp
    rw [hTrue] at hFalse
    contradiction

private def error
    (rule : ValidationRule)
    (message : String)
    (fn : Option String := none)
    (path : Array Nat := #[]) : ValidationError :=
  { rule, message, function := fn, statementPath := path }

/-
`validateType` is structural, not `partial`.  The recursion under `fnPtr` goes
through `validateTypes` on `args.toList`, a projection of the constructor
argument, so the kernel unfolds it; `validateTypes` visits the arguments left
to right and concatenates, exactly as the `for` loop it replaces did.
-/
mutual
/-- Errors in a type, under a profile. -/
def validateType
    (profile : Profile)
    (type : CType)
    (fn : Option String := none) : Array ValidationError :=
  let unsupported : Array ValidationError :=
    if !type.supportedBy profile then
      #[error .unsupportedType
        s!"type is not supported by the {profile.toString} profile: {repr type}" fn]
    else #[]
  unsupported ++
    match type with
    | .named name =>
        if !isValidIdentifier name then
          #[error .invalidIdentifier s!"invalid named type `{name}`" fn]
        else #[]
    | .ptr element => validateType profile element fn
    | .fnPtr args result =>
        validateTypes profile args.toList fn ++ validateType profile result fn
    | _ => #[]

/-- Errors in each type of the list, left to right. -/
def validateTypes
    (profile : Profile)
    (types : List CType)
    (fn : Option String := none) : Array ValidationError :=
  match types with
  | [] => #[]
  | type :: rest => validateType profile type fn ++ validateTypes profile rest fn
end

@[simp] theorem validateType_portable_u8 (fn : Option String := none) :
    validateType .portable .u8 fn = #[] := by
  rfl

@[simp] theorem validateType_portable_u64 (fn : Option String := none) :
    validateType .portable .u64 fn = #[] := by
  rfl

/-- Errors in an expression.  Structural: every recursive call is on a direct
subexpression, so the kernel unfolds it. -/
def validateExpr
    (profile : Profile)
    (expr : CExpr)
    (fn : Option String := none)
    (path : Array Nat := #[]) : Array ValidationError := Id.run do
  let mut errors := validateType profile expr.type fn
  match expr with
  | .var name _ =>
      if !isValidIdentifier name then
        errors := errors.push (error .invalidIdentifier s!"invalid variable `{name}`" fn path)
  | .uintLit type _ =>
      if !type.isUnsigned then
        errors := errors.push (error .incompatibleAssignment
          s!"unsigned literal has type {repr type}" fn path)
  | .intLit type _ =>
      if !type.isInteger then
        errors := errors.push (error .incompatibleAssignment
          s!"integer literal has type {repr type}" fn path)
  | .boolLit _ | .null _ => pure ()
  | .unary _ op value =>
      errors := errors ++ validateExpr profile value fn path
      if op == .neg && value.type.isSigned then
        errors := errors.push (error .signedOverflow
          "signed negation can overflow; lower through unsigned arithmetic" fn path)
  | .binary _ op lhs rhs =>
      errors := errors ++ validateExpr profile lhs fn path
      errors := errors ++ validateExpr profile rhs fn path
      if (op == .add || op == .sub || op == .mul) && lhs.type.isSigned then
        errors := errors.push (error .signedOverflow
          "signed arithmetic can overflow; lower through an unsigned representation" fn path)
      if (op == .add || op == .sub) && (lhs.type.isPointer || rhs.type.isPointer) then
        errors := errors.push (error .pointerArithmetic
          "generated pointer arithmetic is outside Profile 1" fn path)
  | .cast _ value | .addressOf _ value | .deref _ value =>
      errors := errors ++ validateExpr profile value fn path
  | .field _ object name =>
      errors := errors ++ validateExpr profile object fn path
      if !isValidIdentifier name then
        errors := errors.push (error .invalidIdentifier s!"invalid field `{name}`" fn path)
  | .index _ array index =>
      errors := errors ++ validateExpr profile array fn path
      errors := errors ++ validateExpr profile index fn path
  return errors

theorem validateExpr_var_eq_empty
    (profile : Profile) (type : CType) (name : String)
    (fn : Option String) (path : Array Nat)
    (hType : validateType profile type fn = #[])
    (hName : isValidIdentifier name = true) :
    validateExpr profile (.var name type) fn path = #[] := by
  simp [validateExpr, CExpr.type, hType, hName]

theorem validateExpr_uintLit_eq_empty
    (profile : Profile) (type : CType) (value : Nat)
    (fn : Option String) (path : Array Nat)
    (hType : validateType profile type fn = #[])
    (hUnsigned : type.isUnsigned = true) :
    validateExpr profile (.uintLit type value) fn path = #[] := by
  simp [validateExpr, CExpr.type, hType, hUnsigned]

theorem validateExpr_binary_eq_empty
    (profile : Profile) (type : CType) (op : CBinaryOp)
    (lhs rhs : CExpr) (fn : Option String) (path : Array Nat)
    (hType : validateType profile type fn = #[])
    (hLhs : validateExpr profile lhs fn path = #[])
    (hRhs : validateExpr profile rhs fn path = #[])
    (hSigned :
      ((op == .add || op == .sub || op == .mul) && lhs.type.isSigned) = false)
    (hPointer :
      ((op == .add || op == .sub) &&
        (lhs.type.isPointer || rhs.type.isPointer)) = false) :
    validateExpr profile (.binary type op lhs rhs) fn path = #[] := by
  unfold CExpr.type at hSigned hPointer
  unfold validateExpr
  simp only [CExpr.type, hType, hLhs, hRhs, Array.empty_append]
  rw [hSigned, hPointer]
  rfl

theorem validateExpr_cast_eq_empty
    (profile : Profile) (type : CType) (value : CExpr)
    (fn : Option String) (path : Array Nat)
    (hType : validateType profile type fn = #[])
    (hValue : validateExpr profile value fn path = #[]) :
    validateExpr profile (.cast type value) fn path = #[] := by
  simp [validateExpr, CExpr.type, hType, hValue]

/-
Label collection, structural and stack-safe.

`CStmt` nests through `Array CStmt` and `Array CSwitchCase`; the companions
below recurse on `.toList` of those arrays.  The list companion carries an
accumulator so a long generated straight-line block does not consume one
interpreter stack frame per statement.  Statements are visited left to right
and their labels concatenated in that order.
-/
mutual
private def collectLabelsStmt : CStmt → Array String
  | .label name => #[name]
  | .ifThenElse _ thenBody elseBody =>
      collectLabelsListAux #[] thenBody.toList ++
        collectLabelsListAux #[] elseBody.toList
  | .switch _ cases default =>
      collectLabelsCases cases.toList ++
        (match default with
          | none => #[]
          | some body => collectLabelsListAux #[] body.toList)
  | .whileLoop _ body => collectLabelsListAux #[] body.toList
  | _ => #[]

private def collectLabelsListAux (acc : Array String) :
    List CStmt → Array String
  | [] => acc
  | statement :: rest =>
      collectLabelsListAux (acc ++ collectLabelsStmt statement) rest

private def collectLabelsCase : CSwitchCase → Array String
  | ⟨_, body⟩ => collectLabelsListAux #[] body.toList

private def collectLabelsCases : List CSwitchCase → Array String
  | [] => #[]
  | case :: rest => collectLabelsCase case ++ collectLabelsCases rest
end

private def collectLabels (statements : Array CStmt) : Array String :=
  collectLabelsListAux #[] statements.toList

/-
Statement validation, structural rather than `partial`.

The `for index in [:statements.size]` loop this replaces is not a structural
recursion, so the kernel could not unfold it.  `validateStmtList` walks the
list instead, carrying the index it would have taken from the loop, and the
switch arms are walked by `validateCaseList`, which carries the values of the
earlier arms in place of the `cases[:caseIndex]` slice.  Each statement
contributes exactly the errors, in exactly the order, that the loop produced.
-/
mutual
/-- Errors contributed by one statement, at the given statement path. -/
def validateStatement
    (profile : Profile)
    (fn : CFunction)
    (statement : CStmt)
    (labels : Array String)
    (statementPath : Array Nat) : Array ValidationError := Id.run do
  let mut errors : Array ValidationError := #[]
  match statement with
  | .decl type name init =>
      errors := errors ++ validateType profile type (some fn.name)
      if !isValidIdentifier name then
        errors := errors.push (error .invalidIdentifier
          s!"invalid local declaration `{name}`" (some fn.name) statementPath)
      for value in init do
        errors := errors ++ validateExpr profile value (some fn.name) statementPath
        if value.type != type then
          errors := errors.push (error .incompatibleAssignment
            s!"initializer type {repr value.type} differs from {repr type}"
            (some fn.name) statementPath)
  | .assign target value =>
      errors := errors ++ validateExpr profile target (some fn.name) statementPath
      errors := errors ++ validateExpr profile value (some fn.name) statementPath
      if target.type != value.type then
        errors := errors.push (error .incompatibleAssignment
          s!"assignment types differ: {repr target.type} and {repr value.type}"
          (some fn.name) statementPath)
  | .call destination callee args result =>
      if !isValidIdentifier callee then
        errors := errors.push (error .invalidIdentifier
          s!"invalid callee `{callee}`" (some fn.name) statementPath)
      for arg in args do
        errors := errors ++ validateExpr profile arg (some fn.name) statementPath
      match destination with
      | some destination =>
          errors := errors ++ validateExpr profile destination (some fn.name) statementPath
          if destination.type != result then
            errors := errors.push (error .incompatibleCall
              "call result differs from destination type" (some fn.name) statementPath)
      | none =>
          if result != .void then
            errors := errors.push (error .incompatibleCall
              "non-void call result is discarded" (some fn.name) statementPath)
  | .callIndirect destination callee signature args =>
      errors := errors ++ validateExpr profile callee (some fn.name) statementPath
      match signature with
      | .fnPtr expectedArgs result =>
          if expectedArgs.size != args.size then
            errors := errors.push (error .incompatibleCall
              s!"indirect call expects {expectedArgs.size} arguments, got {args.size}"
              (some fn.name) statementPath)
          for pair in args.zip expectedArgs do
            errors := errors ++ validateExpr profile pair.1 (some fn.name) statementPath
            if pair.1.type != pair.2 then
              errors := errors.push (error .incompatibleCall
                "indirect call argument type mismatch" (some fn.name) statementPath)
          match destination with
          | some destination =>
              if destination.type != result then
                errors := errors.push (error .incompatibleCall
                  "indirect call result type mismatch" (some fn.name) statementPath)
          | none =>
              if result != .void then
                errors := errors.push (error .incompatibleCall
                  "indirect non-void result is discarded" (some fn.name) statementPath)
      | _ =>
          errors := errors.push (error .incompatibleCall
            "indirect call does not carry an exact function-pointer signature"
            (some fn.name) statementPath)
  | .ifThenElse condition thenBody elseBody =>
      errors := errors ++ validateExpr profile condition (some fn.name) statementPath
      if !condition.type.isInteger then
        errors := errors.push (error .invalidCondition
          "if condition is not an integer scalar" (some fn.name) statementPath)
      errors := errors ++
        validateStmtList profile fn thenBody.toList labels (statementPath.push 0) 0
      errors := errors ++
        validateStmtList profile fn elseBody.toList labels (statementPath.push 1) 0
  | .switch discriminant cases default =>
      errors := errors ++ validateExpr profile discriminant (some fn.name) statementPath
      if !discriminant.type.isInteger then
        errors := errors.push (error .invalidCondition
          "switch discriminant is not an integer" (some fn.name) statementPath)
      errors := errors ++
        validateCaseList profile fn cases.toList labels statementPath 0 #[]
      match default with
      | none => pure ()
      | some body =>
          errors := errors ++
            validateStmtList profile fn body.toList labels
              (statementPath.push cases.size) 0
  | .whileLoop condition body =>
      errors := errors ++ validateExpr profile condition (some fn.name) statementPath
      if !condition.type.isInteger then
        errors := errors.push (error .invalidCondition
          "while condition is not an integer scalar" (some fn.name) statementPath)
      errors := errors ++
        validateStmtList profile fn body.toList labels statementPath 0
  | .goto label =>
      if !(labels.contains label) then
        errors := errors.push (error .missingLabel
          s!"goto targets missing label `{label}`" (some fn.name) statementPath)
  | .label label =>
      if !isValidIdentifier label then
        errors := errors.push (error .invalidIdentifier
          s!"invalid label `{label}`" (some fn.name) statementPath)
  | .return value =>
      match value with
      | none =>
          if fn.result != .void then
            errors := errors.push (error .incompatibleAssignment
              "void return in non-void function" (some fn.name) statementPath)
      | some value =>
          errors := errors ++ validateExpr profile value (some fn.name) statementPath
          if value.type != fn.result then
            errors := errors.push (error .incompatibleAssignment
              "return value type differs from function result" (some fn.name) statementPath)
  | .unreachable _ | .comment _ => pure ()
  return errors

/-- Errors of a statement list, whose first element sits at `path.push index`.
The accumulator makes the long straight-line case tail-recursive. -/
def validateStmtList
    (profile : Profile)
    (fn : CFunction)
    (statements : List CStmt)
    (labels : Array String)
    (path : Array Nat)
    (index : Nat)
    (errors : Array ValidationError := #[]) : Array ValidationError :=
  match statements with
  | [] => errors
  | statement :: rest =>
      validateStmtList profile fn rest labels path (index + 1)
        (errors ++ validateStatement profile fn statement labels (path.push index))

/-- Errors of one switch arm's body, at the arm's own statement path. -/
def validateCase
    (profile : Profile)
    (fn : CFunction)
    (case : CSwitchCase)
    (labels : Array String)
    (casePath : Array Nat) : Array ValidationError :=
  match case with
  | ⟨_, body⟩ => validateStmtList profile fn body.toList labels casePath 0

/-- Errors of the switch arms.  `earlier` holds the case values already seen,
which is what `cases[:caseIndex]` provided in the loop this replaces. -/
def validateCaseList
    (profile : Profile)
    (fn : CFunction)
    (cases : List CSwitchCase)
    (labels : Array String)
    (statementPath : Array Nat)
    (caseIndex : Nat)
    (earlier : Array Nat)
    (errors : Array ValidationError := #[]) : Array ValidationError :=
  match cases with
  | [] => errors
  | case :: rest =>
      let duplicates : Array ValidationError :=
        earlier.foldl (init := #[]) fun current value =>
          if value == case.value then
            current.push (error .duplicateCase
              s!"duplicate switch case {case.value}" (some fn.name) statementPath)
          else current
      validateCaseList profile fn rest labels statementPath (caseIndex + 1)
        (earlier.push case.value)
        (errors ++ duplicates ++
          validateCase profile fn case labels (statementPath.push caseIndex))
end

/-- Errors of a statement block, rooted at `path`. -/
def validateStatements
    (profile : Profile)
    (fn : CFunction)
    (statements : Array CStmt)
    (labels : Array String)
    (path : Array Nat := #[]) : Array ValidationError :=
  validateStmtList profile fn statements.toList labels path 0

def validateFunction (profile : Profile) (fn : CFunction) : Array ValidationError := Id.run do
  let mut errors := validateType profile fn.result (some fn.name)
  if !isValidIdentifier fn.name then
    errors := errors.push (error .invalidIdentifier s!"invalid function `{fn.name}`" (some fn.name))
  for param in fn.params do
    errors := errors ++ validateType profile param.type (some fn.name)
    if !isValidIdentifier param.name then
      errors := errors.push (error .invalidIdentifier
        s!"invalid parameter `{param.name}`" (some fn.name))
  let labels := collectLabels fn.body
  errors := errors ++ validateStatements profile fn fn.body labels
  return errors

def validateTranslationUnit
    (profile : Profile)
    (unit : CTranslationUnit) : Array ValidationError := Id.run do
  let mut errors := #[]
  let mut symbols : Array String := #[]
  for external in unit.externals do
    if symbols.contains external.name then
      errors := errors.push (error .duplicateSymbol s!"duplicate symbol `{external.name}`")
    symbols := symbols.push external.name
    if !isValidIdentifier external.name then
      errors := errors.push (error .invalidIdentifier s!"invalid external `{external.name}`")
    if !external.trusted && !profile.rules.allowUntrustedExternals then
      errors := errors.push (error .untrustedExternal
        s!"external `{external.name}` is not trusted in profile {profile.toString}")
    for type in external.params do
      errors := errors ++ validateType profile type
    errors := errors ++ validateType profile external.result
  for global in unit.globals do
    if symbols.contains global.name then
      errors := errors.push (error .duplicateSymbol s!"duplicate symbol `{global.name}`")
    symbols := symbols.push global.name
    if !isValidIdentifier global.name then
      errors := errors.push (error .invalidIdentifier s!"invalid global `{global.name}`")
    errors := errors ++ validateType profile global.type
  for fn in unit.functions do
    if symbols.contains fn.name then
      match unit.externals.toList.find? (fun external => external.name == fn.name) with
      | some external =>
          let paramTypes := fn.params.map CParam.type
          if external.params != paramTypes || external.result != fn.result then
            errors := errors.push (error .duplicateSymbol
              s!"prototype for `{fn.name}` does not match its definition")
      | none =>
          errors := errors.push (error .duplicateSymbol s!"duplicate symbol `{fn.name}`")
    symbols := symbols.push fn.name
    errors := errors ++ validateFunction profile fn
  return errors

/-! ## Compositional validation certificates

Large generated functions should not have to reduce the complete diagnostic
validator in one kernel term.  The predicates below expose the compositional
fact used by `validateStmtList`: if every statement contributes no errors for
any diagnostic path, the complete list contributes no errors.  Consumers can
prove the per-statement facts in small shards and assemble them without
re-running the underlying computation.
-/

/-- A statement is validation-clean independently of its diagnostic path and
the ambient label table.  The latter quantification is convenient for the
label-free statement subset emitted by the verified rolled compiler. -/
def StatementValid
    (profile : Profile)
    (fn : CFunction)
    (statement : CStmt) : Prop :=
  ∀ labels path, validateStatement profile fn statement labels path = #[]

/-- Every statement in a list carries a compositional validation proof. -/
def StatementListValid
    (profile : Profile)
    (fn : CFunction)
    (statements : List CStmt) : Prop :=
  ∀ statement ∈ statements, StatementValid profile fn statement

/-- Indexed form of `StatementListValid`, convenient for generated proof
shards whose statement positions are known statically. -/
def StatementListIndexedValid
    (profile : Profile)
    (fn : CFunction)
    (statements : List CStmt) : Prop :=
  ∀ index : Fin statements.length,
    StatementValid profile fn (statements.get index)

theorem StatementListValid.nil
    (profile : Profile)
    (fn : CFunction) :
    StatementListValid profile fn [] := by
  simp [StatementListValid]

theorem StatementListValid.cons
    (profile : Profile)
    (fn : CFunction)
    (statement : CStmt)
    (statements : List CStmt)
    (hHead : StatementValid profile fn statement)
    (hTail : StatementListValid profile fn statements) :
    StatementListValid profile fn (statement :: statements) := by
  intro member hMember
  rcases List.mem_cons.mp hMember with rfl | hRest
  · exact hHead
  · exact hTail member hRest

theorem StatementListValid.append
    (profile : Profile)
    (fn : CFunction)
    (left right : List CStmt)
    (hLeft : StatementListValid profile fn left)
    (hRight : StatementListValid profile fn right) :
    StatementListValid profile fn (left ++ right) := by
  intro statement hStatement
  rcases List.mem_append.mp hStatement with hStatement | hStatement
  · exact hLeft statement hStatement
  · exact hRight statement hStatement

/-- Indexed per-statement certificates cover the ordinary membership-based
list predicate. -/
theorem statementListValid_of_indexed
    (profile : Profile)
    (fn : CFunction)
    (statements : List CStmt)
    (hValid : StatementListIndexedValid profile fn statements) :
    StatementListValid profile fn statements := by
  induction statements with
  | nil => simp [StatementListValid]
  | cons head tail ih =>
      intro statement hStatement
      rcases List.mem_cons.mp hStatement with rfl | hTail
      · exact hValid ⟨0, by simp⟩
      · apply ih
        · intro index
          exact hValid index.succ
        · exact hTail

/-- A validation-clean statement list leaves the diagnostic accumulator
unchanged.  In particular, it can be used as one independently checked shard
of a much larger generated function. -/
theorem validateStmtList_eq_acc_of_statementListValid
    (profile : Profile)
    (fn : CFunction)
    (statements : List CStmt)
    (labels : Array String)
    (path : Array Nat)
    (index : Nat)
    (errors : Array ValidationError)
    (hValid : StatementListValid profile fn statements) :
    validateStmtList profile fn statements labels path index errors = errors := by
  induction statements generalizing index errors with
  | nil => rfl
  | cons statement rest ih =>
      rw [validateStmtList]
      rw [hValid statement (by simp) labels (path.push index)]
      simp only [Array.append_empty]
      apply ih
      intro member hMember
      exact hValid member (by simp [hMember])

/-- The public block validator is empty when all of its statements have
compositional validation certificates. -/
theorem validateStatements_eq_empty_of_statementListValid
    (profile : Profile)
    (fn : CFunction)
    (statements : Array CStmt)
    (labels : Array String)
    (path : Array Nat := #[])
    (hValid : StatementListValid profile fn statements.toList) :
    validateStatements profile fn statements labels path = #[] := by
  exact validateStmtList_eq_acc_of_statementListValid
    profile fn statements.toList labels path 0 #[] hValid

/-- A while statement validates compositionally from its condition and body.
This is the nested-block step needed by rolled generated functions. -/
theorem StatementValid.whileLoop
    (profile : Profile)
    (fn : CFunction)
    (condition : CExpr)
    (body : Array CStmt)
    (hCondition :
      ∀ path, validateExpr profile condition (some fn.name) path = #[])
    (hInteger : condition.type.isInteger = true)
    (hBody : StatementListValid profile fn body.toList) :
  StatementValid profile fn (.whileLoop condition body) := by
  intro labels path
  simp only [validateStatement]
  rw [hCondition path]
  simp only [Array.empty_append, hInteger, Bool.not_true]
  exact validateStmtList_eq_acc_of_statementListValid
    profile fn body.toList labels path 0 #[] hBody

theorem StatementValid.declNone
    (profile : Profile)
    (fn : CFunction)
    (type : CType)
    (name : String)
    (hType : validateType profile type (some fn.name) = #[])
    (hName : isValidIdentifier name = true) :
  StatementValid profile fn (.decl type name none) := by
  intro labels path
  simp [validateStatement, hType, hName]

theorem StatementValid.declSome
    (profile : Profile)
    (fn : CFunction)
    (type : CType)
    (name : String)
    (value : CExpr)
    (hType : validateType profile type (some fn.name) = #[])
    (hName : isValidIdentifier name = true)
    (hValue : ∀ path,
      validateExpr profile value (some fn.name) path = #[])
    (hValueType : (value.type != type) = false) :
  StatementValid profile fn (.decl type name (some value)) := by
  intro labels path
  simp [validateStatement, hType, hName, hValue path, hValueType]

theorem StatementValid.assign
    (profile : Profile)
    (fn : CFunction)
    (target value : CExpr)
    (hTarget : ∀ path,
      validateExpr profile target (some fn.name) path = #[])
    (hValue : ∀ path,
      validateExpr profile value (some fn.name) path = #[])
    (hTypes : (target.type != value.type) = false) :
  StatementValid profile fn (.assign target value) := by
  intro labels path
  simp [validateStatement, hTarget path, hValue path, hTypes]

theorem StatementValid.returnSome
    (profile : Profile)
    (fn : CFunction)
    (value : CExpr)
    (hValue : ∀ path,
      validateExpr profile value (some fn.name) path = #[])
    (hType : (value.type != fn.result) = false) :
  StatementValid profile fn (.return (some value)) := by
  intro labels path
  simp [validateStatement, hValue path, hType]

/-- A parameter-free generated function validates from its result/name checks
and compositional body certificate. -/
theorem validateFunction_eq_empty_of_noParams
    (profile : Profile)
    (fn : CFunction)
    (hParams : fn.params = #[])
    (hResult : validateType profile fn.result (some fn.name) = #[])
    (hName : isValidIdentifier fn.name = true)
    (hBody : StatementListValid profile fn fn.body.toList) :
    validateFunction profile fn = #[] := by
  unfold validateFunction
  rw [hResult]
  simp only [hName, Bool.not_true, hParams]
  rw [validateStatements_eq_empty_of_statementListValid
    profile fn fn.body (collectLabels fn.body) #[] hBody]
  rfl

end LeanCompCert.C
