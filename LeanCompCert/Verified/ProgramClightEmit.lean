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

/--
Emit a symbolic Coq contract for `p` without evaluating its denotation.

This is the artifact form for an external/attested run: Coq constructs the
exact Clight function with the proved compiler and proves, once and for all,
that every successful source denotation is preserved.  In particular, the
generated file contains no `vm_compute` of `p.denote`; the long computation is
left to the compiled artifact.
-/
def emitProgramContract (fnName : String) (p : Program)
    (_hWF : p.CompCertWF) : String :=
  String.intercalate "\n" [
    "(* Generated symbolic contract from LeanCompCert.Verified.Reflect.Program. *)",
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
    "",
    s!"Theorem f_{fnName}_preserves_denotation :",
    "  forall (w : int64) (ge : genv) (m : mem),",
    s!"    dsl_denote source_{fnName} = Some w ->",
    "    ClightBigstep.eval_funcall function_entry2 ge m",
    s!"      (Internal f_{fnName}) nil E0 m (Vlong w).",
    "Proof.",
    "  intros w ge m Hdenote.",
    s!"  unfold f_{fnName}.",
    s!"  exact (compile_program_correct source_{fnName} w ge m Hdenote).",
    "Qed.",
    ""
  ]

/--
Emit the compact, rolled form of the symbolic Coq contract.

Unlike `emitProgramContract`, the Clight syntax produced by this artifact has
one `Sloop` and one copy of `p.body`; its size is independent of
`p.loopCount`.  Coq checks only the small structural `rolled_wf` obligation
(register bounds and that the loop counter fits in `uint64_t`).  The theorem
keeps `dsl_denote source = Some w` as a premise, so generating or checking the
artifact never runs the certificate computation.

This defines the *canonical* rolled Clight function proved by
`ClightRolledCompiler`.  Relating a separately printed C file to this exact
AST additionally requires the per-emission `clightgen` equality bridge.
-/
def emitRolledProgramContract (fnName : String) (p : Program)
    (_hWF : p.CompCertWF) (_hCount : p.loopCount < M) : String :=
  String.intercalate "\n" [
    "(* Generated compact symbolic contract from LeanCompCert.Verified.Reflect.Program. *)",
    "From Coq Require Import List ZArith Lia.",
    "From compcert Require Import Integers Values Events Memory AST Ctypes Cop Clight ClightBigstep Clightdefs.",
    "Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler.",
    "Require Import Direct.ClightEmitterCompiler.",
    "Local Open Scope Z_scope.",
    "",
    s!"Definition loop_limit_{fnName} : Z := {p.loopCount}.",
    "",
    s!"Definition source_{fnName} : dsl_program := \{|",
    s!"  dp_reg_count := {p.regCount};",
    s!"  dp_loop_count := Z.to_nat loop_limit_{fnName};",
    s!"  dp_init := {listTerm p.init};",
    s!"  dp_body := {listTerm p.body};",
    s!"  dp_epilogue := {listTerm p.epilogue};",
    s!"  dp_output := {p.output}",
    "|}.",
    "",
    s!"Definition emitter_source_{fnName} : emitter_source := \{|",
    s!"  es_reg_count := {p.regCount};",
    s!"  es_init := {listTerm p.init};",
    s!"  es_body := {listTerm p.body};",
    s!"  es_epilogue := {listTerm p.epilogue};",
    s!"  es_output := {p.output}",
    "|}.",
    "",
    s!"Lemma emitter_source_{fnName}_matches :",
    s!"  emitter_source_matches emitter_source_{fnName} source_{fnName}.",
    "Proof. constructor; reflexivity. Qed.",
    "",
    s!"Lemma source_{fnName}_rolled_wf : rolled_wf source_{fnName}.",
    "Proof.",
    "  constructor.",
    s!"  - unfold source_{fnName}; cbn; lia.",
    s!"  - unfold source_{fnName}; cbn [dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [dp_loop_count].",
    "    rewrite Z2Nat.id.",
    s!"    + unfold loop_limit_{fnName}.",
    s!"      change ({p.loopCount} < 18446744073709551616)%Z.",
    "      vm_compute; reflexivity.",
    s!"    + unfold loop_limit_{fnName}.",
    s!"      change (0 <= {p.loopCount})%Z; lia.",
    "Qed.",
    "",
    s!"Lemma source_{fnName}_loop_relation :",
    s!"  loop_limit_{fnName} = Z.of_nat (dp_loop_count source_{fnName}).",
    "Proof.",
    s!"  unfold source_{fnName}; cbn [dp_loop_count].",
    "  symmetry; apply Z2Nat.id.",
    s!"  unfold loop_limit_{fnName}.",
    s!"  change (0 <= {p.loopCount})%Z; lia.",
    "Qed.",
    "",
    s!"Definition f_{fnName} : function := compile_rolled_program source_{fnName}.",
    "",
    s!"Theorem f_{fnName}_preserves_denotation :",
    "  forall (w : int64) (ge : genv) (m : mem),",
    s!"    dsl_denote source_{fnName} = Some w ->",
    "    ClightBigstep.eval_funcall function_entry2 ge m",
    s!"      (Internal f_{fnName}) nil E0 m (Vlong w).",
    "Proof.",
    "  intros w ge m Hdenote.",
    s!"  unfold f_{fnName}.",
    s!"  exact (compile_rolled_program_correct source_{fnName} w ge m",
    s!"    source_{fnName}_rolled_wf Hdenote).",
    "Qed.",
    ""
  ]

end LeanCompCert.Verified.ProgramClightEmit
