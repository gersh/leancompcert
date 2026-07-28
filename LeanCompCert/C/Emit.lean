import LeanCompCert.C.Validate

namespace LeanCompCert.C

partial def CType.emit : CType → String
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
      let params := String.intercalate ", " (args.toList.map CType.emit)
      s!"{result.emit} (*)({params})"

private def emitDecl (type : CType) (name : String) : String :=
  match type with
  | .fnPtr args result =>
      let params := String.intercalate ", " (args.toList.map CType.emit)
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

partial def CExpr.emit : CExpr → String
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

private def indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 4) ' ')

mutual
partial def emitStatements (statements : Array CStmt) (level : Nat) : List String :=
  statements.toList.flatMap fun statement => emitStatement statement level

partial def emitBlock (statements : Array CStmt) (level : Nat) : List String :=
  [s!"{indent level}\{"] ++ emitStatements statements (level + 1) ++ [s!"{indent level}}"]

partial def emitStatement (statement : CStmt) (level : Nat) : List String :=
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
      let thenLines := [s!"{pad}if ({condition.emit})"] ++ emitBlock thenBody level
      if elseBody.isEmpty then thenLines
      else thenLines ++ [s!"{pad}else"] ++ emitBlock elseBody level
  | .switch discriminant cases default => Id.run do
      let mut lines := [s!"{pad}switch ({discriminant.emit}) \{"]
      for arm in cases do
        lines := lines ++ [s!"{indent (level + 1)}case {arm.value}:"]
          ++ emitStatements arm.body (level + 2)
          ++ [s!"{indent (level + 2)}break;"]
      for body in default do
        lines := lines ++ [s!"{indent (level + 1)}default:"]
          ++ emitStatements body (level + 2)
          ++ [s!"{indent (level + 2)}break;"]
      return lines ++ [s!"{pad}}"]
  | .whileLoop condition body =>
      [s!"{pad}while ({condition.emit})"] ++ emitBlock body level
  | .goto label => [s!"{pad}goto {label};"]
  | .label label => [s!"{indent (level - 1)}{label}:"]
  | .return none => [s!"{pad}return;"]
  | .return (some value) => [s!"{pad}return {value.emit};"]
  | .unreachable reason =>
      [s!"{pad}lean_compcert_unreachable(\"{escapeString reason}\");"]
  | .comment text =>
      let safe := text.replace "*/" "* /"
      [s!"{pad}/* {safe} */"]
end

def CExternal.emit (external : CExternal) : String :=
  let params :=
    if external.params.isEmpty then "void"
    else String.intercalate ", " (external.params.toList.map CType.emit)
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
