import LeanCompCert.Verified.ArrayInterpreterBridge

/-!
# Symbolic Coq contracts for rolled array programs

This is the `AProgram` counterpart of `ProgramClightEmit`.  It serializes the
first-order array DSL twice: once with its semantic loop count and array
length, and once as the count-free payload inspected by the exact Clight
compiler.  The generated theorem obligations are structural only; no program
denotation is evaluated while emitting or checking the contract.
-/

namespace LeanCompCert.Verified.ArrayProgramClightEmit

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

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

private def scalarTerm : Instr → String
  | .mov dest src => s!"(Dmov {dest} {operandTerm src})"
  | .binop dest op lhs rhs =>
      s!"(Dbinop {dest} {opTerm op} {operandTerm lhs} {operandTerm rhs})"

private def instrTerm : AInstr → String
  | .scalar instruction => s!"(ADscalar {scalarTerm instruction})"
  | .load dest index => s!"(ADload {dest} {index})"
  | .store index source => s!"(ADstore {index} {source})"

private def listTerm (xs : List AInstr) : String :=
  String.intercalate " :: " (xs.map instrTerm ++ ["nil"])

/-- Emit the symbolic source contract consumed by the exact array checker.

`hWF`, `hCount`, and `hArrayFits` are Lean proofs that the literal structural
obligations emitted below are true.  The generated Coq proof rechecks those
obligations independently.  No `AProgram.denote` result is an argument. -/
def emitRolledAProgramContract (fnName : String) (p : AProgram)
    (_hWF : p.WF) (_hCount : p.loopCount < M)
    (_hArrayFits : 8 * p.arrayLen ≤ M) : String :=
  String.intercalate "\n" [
    "(* Generated symbolic contract from LeanCompCert AProgram. *)",
    "From Coq Require Import List ZArith Lia.",
    "From compcert Require Import Integers Values AST Ctypes Clight.",
    "Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler",
    "  Direct.ClightArrayEmitterCompiler.",
    "Import ListNotations.",
    "Local Open Scope Z_scope.",
    "",
    s!"Definition array_len_{fnName} : Z := {p.arrayLen}.",
    s!"Definition loop_limit_{fnName} : Z := {p.loopCount}.",
    "",
    s!"Definition source_{fnName} : adsl_program := \{|",
    s!"  ap_reg_count := {p.regCount};",
    s!"  ap_array_len := array_len_{fnName};",
    s!"  ap_loop_count := Z.to_nat loop_limit_{fnName};",
    s!"  ap_init := {listTerm p.init};",
    s!"  ap_body := {listTerm p.body};",
    s!"  ap_epilogue := {listTerm p.epilogue};",
    s!"  ap_output := {p.output}",
    "|}.",
    "",
    s!"Definition emitter_source_{fnName} : array_emitter_source := \{|",
    s!"  aes_reg_count := {p.regCount};",
    s!"  aes_init := {listTerm p.init};",
    s!"  aes_body := {listTerm p.body};",
    s!"  aes_epilogue := {listTerm p.epilogue};",
    s!"  aes_output := {p.output}",
    "|}.",
    "",
    s!"Lemma emitter_source_{fnName}_matches :",
    s!"  array_emitter_source_matches emitter_source_{fnName}",
    s!"    source_{fnName}.",
    "Proof. constructor; reflexivity. Qed.",
    "",
    s!"Lemma source_{fnName}_wf : adsl_wf source_{fnName}.",
    "Proof.",
    "  constructor.",
    s!"  - unfold source_{fnName}; cbn; lia.",
    s!"  - unfold source_{fnName}; cbn [adinstr_wf dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [adinstr_wf dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [adinstr_wf dinstr_wf doperand_wf];",
    "      repeat constructor; lia.",
    s!"  - unfold source_{fnName}; cbn [ap_loop_count].",
    "    rewrite Z2Nat.id.",
    s!"    + unfold loop_limit_{fnName}.",
    s!"      change ({p.loopCount} < 18446744073709551616)%Z.",
    "      lia.",
    s!"    + unfold loop_limit_{fnName}; lia.",
    s!"  - unfold source_{fnName}, array_len_{fnName}; cbn; lia.",
    s!"  - unfold source_{fnName}, array_len_{fnName}; cbn.",
    "    rewrite (Ptrofs.modulus_eq64 eq_refl).",
    s!"    change (8 * {p.arrayLen} <= 18446744073709551616)%Z.",
    "    lia.",
    "Qed.",
    "",
    s!"Lemma source_{fnName}_loop_relation :",
    s!"  loop_limit_{fnName} = Z.of_nat (ap_loop_count source_{fnName}).",
    "Proof.",
    s!"  unfold source_{fnName}; cbn [ap_loop_count].",
    "  symmetry; apply Z2Nat.id.",
    s!"  unfold loop_limit_{fnName}; lia.",
    "Qed.",
    ""
  ]

end LeanCompCert.Verified.ArrayProgramClightEmit
