import LeanCompCert.Verified.ClightContract

/-!
# Emission through the proved Clight compiler

This emitter serializes a `Reflect.Program` as data in Coq.  The emitted
Clight function is *defined* by `ClightDSLCompiler.compile_program`; it is not
an independently generated AST.  Consequently the generic Coq theorem
`compile_program_correct` applies to the exact function in the artifact.
-/

namespace LeanCompCert.Verified.ProgramClightEmit

open LeanCompCert.Verified.Reflect

private def operandTerm : Operand → String
  | .reg index => s!"(Dreg {index})"
  | .lit value => s!"(Dlit {value})"
  | .idx => "Didx"

private def opTerm : Op → String
  | .add => "Dadd"
  | .sub => "Dsub"
  | .mul => "Dmul"
  | .udiv => "Ddiv"
  | .urem => "Dmod"
  | .band => "Dand"
  | .bor => "Dor"
  | .bxor => "Dxor"
  | .shl => "Dshl"
  | .lshr => "Dshr"
  | .eq => "Deq"
  | .ne => "Dne"
  | .lt => "Dlt"
  | .le => "Dle"
  | .gt => "Dgt"
  | .ge => "Dge"

private def instrTerm : Instr → String
  | .mov dest src => s!"(Dmov {dest} {operandTerm src})"
  | .binop dest op lhs rhs =>
      s!"(Dbinop {dest} {opTerm op} {operandTerm lhs} {operandTerm rhs})"

private def listTerm (xs : List Instr) : String :=
  String.intercalate " :: " (xs.map instrTerm ++ ["nil"])

/--
Emit a Coq certificate for `p`.  The closed `source_denote` lemma is checked
by Coq computation.  `function_correct` then follows from the once-and-for-all
compiler theorem and refers to the exact `f_<name>` definition in this file.
-/
def emitProgram (fnName : String) (p : Program) (expected : Nat)
    (_hWF : p.CompCertWF) (_hDenote : p.denote = some expected) : String :=
  String.intercalate "\n" [
    "(* Generated from LeanCompCert.Verified.Reflect.Program. *)",
    "From Coq Require Import List ZArith.",
    "From compcert Require Import Integers Values Events Memory AST Ctypes Cop Clight ClightBigstep Clightdefs.",
    "Require Import Direct.ClightDSLCompiler.",
    "Local Open Scope Z_scope.",
    "",
    s!"Definition source_{fnName} : dsl_program := \{|",
    s!"  dp_reg_count := {p.regCount};",
    s!"  dp_loop_count := {p.loopCount};",
    s!"  dp_init := {listTerm p.init};",
    s!"  dp_body := {listTerm p.body};",
    s!"  dp_epilogue := {listTerm p.epilogue};",
    s!"  dp_output := {p.output}",
    "|}.",
    "",
    s!"Definition f_{fnName} : function := compile_program source_{fnName}.",
    s!"Definition expected_{fnName} : int64 := Int64.repr {expected}.",
    "",
    s!"Lemma source_{fnName}_denote :",
    s!"  dsl_denote source_{fnName} = Some expected_{fnName}.",
    "Proof. vm_compute. reflexivity. Qed.",
    "",
    s!"Theorem f_{fnName}_correct :",
    "  ClightBigstep.eval_funcall function_entry2 empty_ge Mem.empty",
    s!"    (Internal f_{fnName}) nil E0 Mem.empty (Vlong expected_{fnName}).",
    "Proof.",
    s!"  apply (compile_program_correct source_{fnName} expected_{fnName} empty_ge Mem.empty).",
    s!"  exact source_{fnName}_denote.",
    "Qed.",
    ""
  ]

end LeanCompCert.Verified.ProgramClightEmit
