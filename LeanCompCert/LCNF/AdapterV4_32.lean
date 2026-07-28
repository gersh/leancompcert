import Lean.Compiler.LCNF
import LeanCompCert.LCNF.View

namespace LeanCompCert.LCNF.AdapterV4_32

namespace Internal

open Lean
open Lean.Compiler.LCNF

def id (fvarId : FVarId) : String :=
  fvarId.name.toString

def type (expression : Expr) : LCNF.ViewType :=
  match expression with
  | ImpureType.float => .f64
  | ImpureType.float32 => .f32
  | ImpureType.uint8 => .u8
  | ImpureType.uint16 => .u16
  | ImpureType.uint32 => .u32
  | ImpureType.uint64 => .u64
  | ImpureType.usize => .usize
  | ImpureType.object => .object
  | ImpureType.tagged => .tagged
  | ImpureType.tobject => .taggedObject
  | ImpureType.erased => .erased
  | ImpureType.void => .void
  | other => .unknown (toString other)

def param (value : Lean.Compiler.LCNF.Param .impure) : LCNF.Param := {
  id := id value.fvarId
  name := value.binderName.toString
  type := type value.type
  borrowed := value.borrow
}

def literal : Lean.Compiler.LCNF.LitValue → LCNF.Literal
  | .nat value => .nat value
  | .str value => .string value
  | .uint8 value => .u8 value.toNat
  | .uint16 value => .u16 value.toNat
  | .uint32 value => .u32 value.toNat
  | .uint64 value => .u64 value.toNat
  | .usize value => .usize value.toNat

def arg : Lean.Compiler.LCNF.Arg .impure → LCNF.Arg
  | .erased => .erased
  | .fvar fvarId => .local (id fvarId)

def ctorInfo (info : Lean.Compiler.LCNF.CtorInfo) : LCNF.CtorInfo := {
  name := info.name.toString
  tag := info.cidx
  objectFields := info.size
  usizeFields := info.usize
  scalarBytes := info.ssize
}

def value : Lean.Compiler.LCNF.LetValue .impure → LCNF.Value
  | .lit value => .literal (literal value)
  | .erased => .erased
  | .fvar fvarId args => .localCall (id fvarId) (args.map arg)
  | .ctor info args => .ctor (ctorInfo info) (args.map arg)
  | .oproj index object => .project (.object index) (id object)
  | .uproj index object => .project (.usize index) (id object)
  | .sproj bytes offset object => .project (.scalar bytes offset) (id object)
  | .fap fn args => .directCall fn.toString (args.map arg)
  | .pap fn args => .partialApply fn.toString (args.map arg)
  | .reset count object => .reset count (id object)
  | .reuse object info updateHeader args =>
      .reuse (id object) (ctorInfo info) updateHeader (args.map arg)
  | .box type' value => .box (type type') (id value)
  | .unbox value => .unbox (id value)
  | .isShared value => .isShared (id value)

def letDecl (decl : Lean.Compiler.LCNF.LetDecl .impure) : LCNF.LetDecl := {
  id := id decl.fvarId
  name := decl.binderName.toString
  type := type decl.type
  value := value decl.value
}

mutual
partial def code : Lean.Compiler.LCNF.Code .impure → LCNF.Code
  | .let decl next => .letValue (letDecl decl) (code next)
  | .jp decl next => .joinPoint (funDecl decl) (code next)
  | .jmp target args => .jump (id target) (args.map arg)
  | .cases cases =>
      .cases (id cases.discr) (cases.alts.map alternative)
  | .return value => .return (id value)
  | .unreach _ => .unreachable
  | .oset object index value next =>
      .setObjectField (id object) index (arg value) (code next)
  | .uset object index value next =>
      .setUSizeField (id object) index (id value) (code next)
  | .sset object bytes offset value type' next =>
      .setScalarField (id object) bytes offset (id value) (type type') (code next)
  | .setTag object tag next => .setTag (id object) tag (code next)
  | .inc object count check persistent next =>
      .retain (id object) count check persistent (code next)
  | .dec object count check persistent fields next =>
      .release (id object) count check persistent fields (code next)
  | .del object next => .delete (id object) (code next)

partial def funDecl : Lean.Compiler.LCNF.FunDecl .impure → LCNF.FunDecl
  | .mk fvarId binderName params result body => {
      id := id fvarId
      name := binderName.toString
      params := params.map param
      result := type result
      body := code body
    }

partial def alternative : Lean.Compiler.LCNF.Alt .impure → LCNF.Alternative
  | .ctorAlt info body => .constructor (ctorInfo info) (code body)
  | .default body => .default (code body)
end

def declaration (decl : Lean.Compiler.LCNF.Decl .impure) : LCNF.Decl := {
  name := decl.name.toString
  params := decl.params.map param
  result := type decl.type
  value := match decl.value with
    | .code body => .code (code body)
    | .extern _ => .external
  recursive := decl.recursive
  safe := decl.safe
}

end Internal

def declaration := Internal.declaration

end LeanCompCert.LCNF.AdapterV4_32
