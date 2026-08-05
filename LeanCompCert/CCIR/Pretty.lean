import LeanCompCert.CCIR.Basic

namespace LeanCompCert.CCIR

def Operand.pretty : Operand → String
  | .local id => toString id
  | .global id => s!"@{id.name}"
  | .uintLit type value => s!"{type.toString}({value})"
  | .intLit type value => s!"{type.toString}({value})"
  | .null type => s!"null<{type.toString}>"

def UnaryOp.pretty : UnaryOp → String
  | .bitNot => "bitnot"
  | .boolNot => "not"
  | .neg => "neg"
  | .cast target => s!"cast<{target.toString}>"

def BinaryOp.pretty : BinaryOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .udiv => "udiv" | .urem => "urem"
  | .sdiv => "sdiv" | .srem => "srem"
  | .bitAnd => "and" | .bitOr => "or" | .bitXor => "xor"
  | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr"
  | .eq => "eq" | .ne => "ne"
  | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

private def renderArgs (args : Array Operand) : String :=
  String.intercalate ", " (args.toList.map Operand.pretty)

def Instruction.pretty : Instruction → String
  | .assign dest value =>
      s!"{dest.id} : {dest.type} = copy {value.pretty}"
  | .unary dest op value =>
      s!"{dest.id} : {dest.type} = {op.pretty} {value.pretty}"
  | .binary dest op lhs rhs =>
      s!"{dest.id} : {dest.type} = {op.pretty} {lhs.pretty}, {rhs.pretty}"
  | .load dest address =>
      s!"{dest.id} : {dest.type} = load {address.pretty}"
  | .store address value =>
      s!"store {address.pretty}, {value.pretty}"
  | .loadIndex dest base index =>
      s!"{dest.id} : {dest.type} = load_index {base.pretty}, {index.pretty}"
  | .storeIndex base index value =>
      s!"store_index {base.pretty}, {index.pretty}, {value.pretty}"
  | .call dest callee args result =>
      let lhs := dest.map (fun result => s!"{result.id} : {result.type} = ") |>.getD ""
      s!"{lhs}call @{callee.name}({renderArgs args}) : {result}"
  | .runtimeCall dest symbol args result =>
      let lhs := dest.map (fun result => s!"{result.id} : {result.type} = ") |>.getD ""
      s!"{lhs}runtime @{symbol}({renderArgs args}) : {result}"
  | .retain value => s!"retain {value.pretty}"
  | .release value => s!"release {value.pretty}"
  | .allocCtor dest tag fields =>
      s!"{dest.id} : {dest.type} = alloc_ctor tag={tag}, fields={fields}"
  | .setField object index value =>
      s!"set_field {object.pretty}, {index}, {value.pretty}"
  | .getTag dest object =>
      s!"{dest.id} : {dest.type} = get_tag {object.pretty}"
  | .project dest object index =>
      s!"{dest.id} : {dest.type} = project {object.pretty}, {index}"

def Terminator.pretty : Terminator → String
  | .goto target => s!"goto {target}"
  | .branch condition thenBlock elseBlock =>
      s!"branch {condition.pretty}, {thenBlock}, {elseBlock}"
  | .switch discriminant cases default =>
      let renderedCases := cases.toList.map fun (tag, target) => s!"{tag}: {target}"
      let renderedDefault := default.map (fun target => s!", default: {target}") |>.getD ""
      s!"switch {discriminant.pretty} [{String.intercalate ", " renderedCases}{renderedDefault}]"
  | .return none => "return"
  | .return (some value) => s!"return {value.pretty}"
  | .unreachable reason => s!"unreachable \"{reason}\""

def Block.pretty (block : Block) : String :=
  let body := block.instructions.toList.map (fun instr => s!"  {instr.pretty}")
  String.intercalate "\n" ([s!"{block.id}:"] ++ body ++ [s!"  {block.terminator.pretty}"])

def Function.pretty (fn : Function) : String :=
  let params := fn.params.toList.map fun param => s!"{param.id} : {param.type}"
  let header := s!"fn @{fn.name.name}({String.intercalate ", " params}) -> {fn.result} entry {fn.entry}"
  let blocks := String.intercalate "\n" (fn.blocks.toList.map Block.pretty)
  s!"{header} \{\n{blocks}\n}"

def Program.pretty (program : Program) : String :=
  String.intercalate "\n\n" (program.functions.toList.map Function.pretty)

end LeanCompCert.CCIR
