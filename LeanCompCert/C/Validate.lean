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

private def error
    (rule : ValidationRule)
    (message : String)
    (fn : Option String := none)
    (path : Array Nat := #[]) : ValidationError :=
  { rule, message, function := fn, statementPath := path }

partial def validateType
    (profile : Profile)
    (type : CType)
    (fn : Option String := none) : Array ValidationError := Id.run do
  let mut errors := #[]
  if !type.supportedBy profile then
    errors := errors.push (error .unsupportedType
      s!"type is not supported by the {profile.toString} profile: {repr type}" fn)
  match type with
  | .named name =>
      if !isValidIdentifier name then
        errors := errors.push (error .invalidIdentifier s!"invalid named type `{name}`" fn)
  | .ptr element => errors := errors ++ validateType profile element fn
  | .fnPtr args result =>
      for arg in args do
        errors := errors ++ validateType profile arg fn
      errors := errors ++ validateType profile result fn
  | _ => pure ()
  return errors

partial def validateExpr
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

private partial def collectLabels (statements : Array CStmt) : Array String :=
  statements.foldl (init := #[]) fun labels statement =>
    match statement with
    | .label name => labels.push name
    | .ifThenElse _ thenBody elseBody =>
        labels ++ collectLabels thenBody ++ collectLabels elseBody
    | .switch _ cases default =>
        let labels := cases.foldl (init := labels)
          fun current case => current ++ collectLabels case.body
        default.map (fun body => labels ++ collectLabels body) |>.getD labels
    | .whileLoop _ body => labels ++ collectLabels body
    | _ => labels

partial def validateStatements
    (profile : Profile)
    (fn : CFunction)
    (statements : Array CStmt)
    (labels : Array String)
    (path : Array Nat := #[]) : Array ValidationError := Id.run do
  let mut errors := #[]
  for index in [:statements.size] do
    let statement := statements[index]!
    let statementPath := path.push index
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
        errors := errors ++ validateStatements profile fn thenBody labels (statementPath.push 0)
        errors := errors ++ validateStatements profile fn elseBody labels (statementPath.push 1)
    | .switch discriminant cases default =>
        errors := errors ++ validateExpr profile discriminant (some fn.name) statementPath
        if !discriminant.type.isInteger then
          errors := errors.push (error .invalidCondition
            "switch discriminant is not an integer" (some fn.name) statementPath)
        for caseIndex in [:cases.size] do
          let case := cases[caseIndex]!
          for previous in cases[:caseIndex] do
            if previous.value == case.value then
              errors := errors.push (error .duplicateCase
                s!"duplicate switch case {case.value}" (some fn.name) statementPath)
          errors := errors ++ validateStatements profile fn case.body labels
            (statementPath.push caseIndex)
        for default in default do
          errors := errors ++ validateStatements profile fn default labels
            (statementPath.push cases.size)
    | .whileLoop condition body =>
        errors := errors ++ validateExpr profile condition (some fn.name) statementPath
        if !condition.type.isInteger then
          errors := errors.push (error .invalidCondition
            "while condition is not an integer scalar" (some fn.name) statementPath)
        errors := errors ++ validateStatements profile fn body labels statementPath
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

end LeanCompCert.C
