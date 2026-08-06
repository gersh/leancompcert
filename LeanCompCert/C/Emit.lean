import LeanCompCert.C.Validate

namespace LeanCompCert.C

/-
Type emission, structural rather than `partial`.

The recursion under `fnPtr` goes through `CType.emitList` on `args.toList`, a
projection of the constructor argument, so the kernel unfolds it.
`CType.emitList` is `List.map CType.emit` (`CType.emitList_eq_map`), so the
emitted text is unchanged.
-/
mutual
/-- The C spelling of a type. -/
def CType.emit : CType → String
  | .void => "void"
  | .bool => "uint8_t"
  | .u8 => "uint8_t"
  | .u16 => "uint16_t"
  | .u32 => "uint32_t"
  | .u64 => "uint64_t"
  | .usize => "size_t"
  | .i8 => "int8_t"
  | .i16 => "int16_t"
  | .i32 => "int32_t"
  | .i64 => "int64_t"
  | .isize => "ptrdiff_t"
  | .f32 => "float"
  | .f64 => "double"
  | .named name => name
  | .ptr element => s!"{element.emit} *"
  | .fnPtr args result =>
      let params := String.intercalate ", " (CType.emitList args.toList)
      s!"{result.emit} (*)({params})"

/-- `List.map CType.emit`, spelled out so the recursion is structural. -/
def CType.emitList : List CType → List String
  | [] => []
  | type :: rest => type.emit :: CType.emitList rest
end

theorem CType.emitList_eq_map (types : List CType) :
    CType.emitList types = types.map CType.emit := by
  induction types with
  | nil => rfl
  | cons _ _ ih => simp [CType.emitList, ih]

private def emitDecl (type : CType) (name : String) : String :=
  match type with
  | .fnPtr args result =>
      let params := String.intercalate ", " (CType.emitList args.toList)
      s!"{result.emit} (*{name})({params})"
  | _ => s!"{type.emit} {name}"

private def unarySymbol : CUnaryOp → String
  | .bitNot => "~"
  | .boolNot => "!"
  | .neg => "-"

private def binarySymbol : CBinaryOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .rem => "%"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .shl => "<<" | .shr => ">>"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
  | .gt => ">" | .ge => ">=" | .logicalAnd => "&&" | .logicalOr => "||"

private def escapeString (value : String) : String :=
  value.toList.foldl (init := "") fun result character =>
    result ++ match character with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | character => character.toString

/-- The C spelling of an expression.  Structural: every recursive call is on a
direct subexpression. -/
def CExpr.emit : CExpr → String
  | .var name _ => name
  | .uintLit .u64 value => s!"UINT64_C({value})"
  | .uintLit .u32 value => s!"UINT32_C({value})"
  | .uintLit _ value => toString value
  | .intLit .i64 value => s!"INT64_C({value})"
  | .intLit .i32 value => s!"INT32_C({value})"
  | .intLit _ value => toString value
  | .boolLit true => "UINT8_C(1)"
  | .boolLit false => "UINT8_C(0)"
  | .null type => s!"(({type.emit})0)"
  | .unary _ op value => s!"({unarySymbol op}{value.emit})"
  | .binary _ op lhs rhs => s!"({lhs.emit} {binarySymbol op} {rhs.emit})"
  | .cast type value => s!"(({type.emit})({value.emit}))"
  | .addressOf _ value => s!"(&{value.emit})"
  | .deref _ value => s!"(*{value.emit})"
  | .field _ object name => s!"({object.emit}.{name})"
  | .index _ arr idx => s!"({arr.emit}[{idx.emit}])"

/-- Close the one sequence a `/* … */` comment cannot contain, by splitting it.

Structural, character by character, rather than `String.replace`: the latter is
compiled by well-founded recursion (`WellFounded.opaqueFix`) and the kernel
will not unfold it, which alone is enough to make the emitted text of any
function carrying a `sourceDecl` comment unevaluable by `decide +kernel`.
Left-to-right, non-overlapping, one `"* /"` per `"*/"` — the same replacement
`String.replace "*/" "* /"` performs. -/
private def splitCommentEnd : List Char → List Char
  | [] => []
  | '*' :: '/' :: rest => '*' :: ' ' :: '/' :: splitCommentEnd rest
  | character :: rest => character :: splitCommentEnd rest

private def escapeComment (text : String) : String :=
  String.ofList (splitCommentEnd text.toList)

private def indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 4) ' ')

/-
Statement emission, structural rather than `partial`.

`CStmt` nests through `Array CStmt` and `Array CSwitchCase`.  The companions
below recurse on `.toList` of those arrays — projections of the constructor
arguments — and each switch arm is emitted by its own function in the mutual
group, which is what lets the kernel unfold the whole walk.

`emitStmtList` is `List.flatMap (emitStatement · level)`
(`emitStmtList_eq_flatMap`), and the switch arms are concatenated in index
order with the default arm last, so the emitted lines are unchanged.
-/
mutual
/-- Emit a statement, indented `level` blocks in. -/
def emitStatement (statement : CStmt) (level : Nat) : List String :=
  let pad := indent level
  match statement with
  | .decl type name none => [s!"{pad}{emitDecl type name};"]
  | .decl type name (some init) => [s!"{pad}{emitDecl type name} = {init.emit};"]
  | .assign target value => [s!"{pad}{target.emit} = {value.emit};"]
  | .call destination callee args _ =>
      let args := String.intercalate ", " (args.toList.map CExpr.emit)
      let call := s!"{callee}({args})"
      [match destination with
        | some destination => s!"{pad}{destination.emit} = {call};"
        | none => s!"{pad}{call};"]
  | .callIndirect destination callee _ args =>
      let args := String.intercalate ", " (args.toList.map CExpr.emit)
      let call := s!"{callee.emit}({args})"
      [match destination with
        | some destination => s!"{pad}{destination.emit} = {call};"
        | none => s!"{pad}{call};"]
  | .ifThenElse condition thenBody elseBody =>
      let thenLines :=
        [s!"{pad}if ({condition.emit})", s!"{pad}\{"]
          ++ emitStmtList thenBody.toList (level + 1) ++ [s!"{pad}}"]
      if elseBody.isEmpty then thenLines
      else thenLines ++ [s!"{pad}else", s!"{pad}\{"]
        ++ emitStmtList elseBody.toList (level + 1) ++ [s!"{pad}}"]
  | .switch discriminant cases default =>
      let header := [s!"{pad}switch ({discriminant.emit}) \{"]
      let arms := emitCaseList cases.toList level
      let fallback :=
        match default with
        | none => []
        | some body =>
            [s!"{indent (level + 1)}default:"]
              ++ emitStmtList body.toList (level + 2)
              ++ [s!"{indent (level + 2)}break;"]
      header ++ arms ++ fallback ++ [s!"{pad}}"]
  | .whileLoop condition body =>
      [s!"{pad}while ({condition.emit})", s!"{pad}\{"]
        ++ emitStmtList body.toList (level + 1) ++ [s!"{pad}}"]
  | .goto label => [s!"{pad}goto {label};"]
  | .label label => [s!"{indent (level - 1)}{label}:"]
  | .return none => [s!"{pad}return;"]
  | .return (some value) => [s!"{pad}return {value.emit};"]
  | .unreachable reason =>
      [s!"{pad}lean_compcert_unreachable(\"{escapeString reason}\");"]
  | .comment text =>
      let safe := escapeComment text
      [s!"{pad}/* {safe} */"]

/-- Emit each statement of the list in turn, all at `level`. -/
def emitStmtList (statements : List CStmt) (level : Nat)
    (reversed : List String := []) : List String :=
  match statements with
  | [] => reversed.reverse
  | statement :: rest =>
      emitStmtList rest level ((emitStatement statement level).reverse ++ reversed)

/-- Emit one `case` arm, label and `break` included. -/
def emitCase (arm : CSwitchCase) (level : Nat) : List String :=
  match arm with
  | ⟨value, body⟩ =>
      [s!"{indent (level + 1)}case {value}:"]
        ++ emitStmtList body.toList (level + 2)
        ++ [s!"{indent (level + 2)}break;"]

/-- Emit the `case` arms in order. -/
def emitCaseList (arms : List CSwitchCase) (level : Nat) : List String :=
  match arms with
  | [] => []
  | arm :: rest => emitCase arm level ++ emitCaseList rest level
end

/-- Emit a statement array, all at `level`. -/
def emitStatements (statements : Array CStmt) (level : Nat) : List String :=
  emitStmtList statements.toList level

/-- Emit a brace-delimited block whose statements sit one level deeper. -/
def emitBlock (statements : Array CStmt) (level : Nat) : List String :=
  [s!"{indent level}\{"] ++ emitStatements statements (level + 1) ++ [s!"{indent level}}"]

private theorem emitStmtList_acc (statements : List CStmt) (level : Nat)
    (reversed : List String) :
    emitStmtList statements level reversed =
      reversed.reverse ++
        statements.flatMap (fun statement => emitStatement statement level) := by
  induction statements generalizing reversed with
  | nil => simp [emitStmtList]
  | cons statement rest ih =>
      rw [emitStmtList, ih]
      simp [List.reverse_append, List.append_assoc]

theorem emitStmtList_eq_flatMap (statements : List CStmt) (level : Nat) :
    emitStmtList statements level
      = statements.flatMap (fun statement => emitStatement statement level) := by
  simpa using emitStmtList_acc statements level []

theorem emitStatements_eq (statements : Array CStmt) (level : Nat) :
    emitStatements statements level
      = statements.toList.flatMap (fun statement => emitStatement statement level) :=
  emitStmtList_eq_flatMap _ _

def CExternal.emit (external : CExternal) : String :=
  let params :=
    if external.params.isEmpty then "void"
    else String.intercalate ", " (CType.emitList external.params.toList)
  s!"extern {external.result.emit} {external.name}({params});"

def CGlobal.emit (global : CGlobal) : String :=
  let storage := if global.internal then "static " else ""
  let qualifier := if global.constant then "const " else ""
  let init := match global.init with
    | .zero => "{0}"
    | .uintLit type value => (CExpr.uintLit type value).emit
    | .intLit type value => (CExpr.intLit type value).emit
    | .string value => s!"\"{escapeString value}\""
    | .address symbol => s!"&{symbol}"
  s!"{storage}{qualifier}{emitDecl global.type global.name} = {init};"

def CFunction.emit (fn : CFunction) : String :=
  let storage := if fn.internal then "static " else ""
  let params :=
    if fn.params.isEmpty then "void"
    else String.intercalate ", " (fn.params.toList.map fun param => emitDecl param.type param.name)
  let header := s!"{storage}{fn.result.emit} {fn.name}({params})"
  String.intercalate "\n" ([header] ++ emitBlock fn.body 0)

def CTranslationUnit.emit (unit : CTranslationUnit) : String :=
  let includes := unit.includes.toList.map fun header => s!"#include <{header}>"
  let externals := unit.externals.toList.map CExternal.emit
  let globals := unit.globals.toList.map CGlobal.emit
  let functions := unit.functions.toList.map CFunction.emit
  let sections := [
    String.intercalate "\n" includes,
    String.intercalate "\n" externals,
    String.intercalate "\n" globals,
    String.intercalate "\n\n" functions
  ] |>.filter (fun content => !content.isEmpty)
  String.intercalate "\n\n" sections ++ "\n"

def emitChecked (profile : Profile) (unit : CTranslationUnit) :
    Except (Array ValidationError) String :=
  let errors := validateTranslationUnit profile unit
  if errors.isEmpty then .ok unit.emit else .error errors

end LeanCompCert.C
