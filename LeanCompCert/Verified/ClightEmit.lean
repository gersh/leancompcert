import LeanCompCert.Verified.Package

/-!
# M6 — Direct Clight emission

Emits CompCert Clight AST terms (as Coq source) **directly** from the
proven statement lists (`compiledStmt` output), bypassing both the C
pretty-printer and clightgen's parser for the formal object. The emitted
function is goto-free — a right-nested `Ssequence` of `Sset` statements
ending in `Sreturn` — so CompCert's bigstep semantics applies, enabling
the Coq-side semantics theorem (see `scripts/coq/` and the acceptance
suite): CompCert's own semantics, checked by Coq's kernel, computes the
certified value.

The shapes mirror clightgen's normalized output exactly (verified against
`fixedpoint-cert.v`): `u64` literals as `Econst_long`, the `u8` scratch
via `Ecast (... tint) tuchar`, comparisons as
`Ecast (Ebinop Ocmp … tint) tuchar`, widening casts as
`Ecast (Etempvar … tuchar) tulong`.
-/

namespace LeanCompCert.Verified.ClightEmit

open LeanCompCert

def binopName : C.CBinaryOp → String
  | .add => "Oadd" | .sub => "Osub" | .mul => "Omul"
  | .div => "Odiv" | .rem => "Omod"
  | .bitAnd => "Oand" | .bitOr => "Oor" | .bitXor => "Oxor"
  | .shl => "Oshl" | .shr => "Oshr"
  | .eq => "Oeq" | .ne => "One" | .lt => "Olt" | .le => "Ole"
  | .gt => "Ogt" | .ge => "Oge"
  | .logicalAnd => "Oand" | .logicalOr => "Oor"

def isComparison : C.CBinaryOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def clightType : C.CType → String
  | .u8 => "tuchar"
  | _ => "tulong"

/-- Operand expressions (the compiledStmt subset). -/
def operandTerm : C.CExpr → Option String
  | .var name t => some s!"(Etempvar _{name} {clightType t})"
  | .uintLit .u64 v => some s!"(Econst_long (Int64.repr {v}) tulong)"
  | .uintLit .u8 v => some s!"(Ecast (Econst_int (Int.repr {v}) tint) tuchar)"
  | _ => none

/-- Right-hand sides of `Sset` for each proven statement shape. -/
def rhsTerm : C.CExpr → Option String
  | .var name t => some s!"(Etempvar _{name} {clightType t})"
  | .uintLit .u64 v => some s!"(Econst_long (Int64.repr {v}) tulong)"
  | .uintLit .u8 v => some s!"(Ecast (Econst_int (Int.repr {v}) tint) tuchar)"
  | .binary destType op lhs rhs => do
      let l ← operandTerm lhs
      let r ← operandTerm rhs
      if isComparison op then
        pure s!"(Ecast (Ebinop {binopName op} {l} {r} tint) {clightType destType})"
      else
        pure s!"(Ebinop {binopName op} {l} {r} {clightType destType})"
  | .cast t (.var name st) =>
      some s!"(Ecast (Etempvar _{name} {clightType st}) {clightType t})"
  | _ => none

def stmtTerm : C.CStmt → Option String
  | .assign (.var name _) value => do
      pure s!"(Sset _{name} {← rhsTerm value})"
  | _ => none

/-- Collect the variable names appearing as assignment targets, with their
declared C types, preserving first-seen order. -/
def collectTemps (stmts : List C.CStmt) : List (String × String) :=
  stmts.foldl (init := []) fun acc stmt =>
    match stmt with
    | .assign (.var name t) _ =>
        if acc.any (·.1 == name) then acc
        else acc ++ [(name, clightType t)]
    | _ => acc

/-- The full Coq source: prelude, ident definitions, and the function. -/
def emitClight (fnName : String) (stmts : List C.CStmt)
    (returnVar : String) : Option String := do
  let mut body := s!"(Sreturn (Some (Etempvar _{returnVar} tulong)))"
  for stmt in stmts.reverse do
    let term ← stmtTerm stmt
    body := s!"(Ssequence {term} {body})"
  let temps := collectTemps stmts
  let idents := String.intercalate "\n" <|
    temps.map fun (name, _) =>
      s!"Definition _{name} : ident := $\"{name}\"."
  let tempList := String.intercalate " :: " <|
    temps.map fun (name, t) => s!"(_{name}, {t})"
  pure <| String.intercalate "\n" [
    "From Coq Require Import String List ZArith.",
    "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.",
    "Import Clightdefs.ClightNotations.",
    "Local Open Scope Z_scope.",
    "Local Open Scope string_scope.",
    "Local Open Scope clight_scope.",
    "",
    idents,
    "",
    s!"Definition f_{fnName} : function := \{|",
    "  fn_return := tulong;",
    "  fn_callconv := cc_default;",
    "  fn_params := nil;",
    "  fn_vars := nil;",
    s!"  fn_temps := ({tempList} :: nil);",
    s!"  fn_body := {body}",
    "|}."
  ]

end LeanCompCert.Verified.ClightEmit
