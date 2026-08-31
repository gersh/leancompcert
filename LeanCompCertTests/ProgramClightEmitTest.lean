import LeanCompCert.Verified.ProgramClightEmit

namespace LeanCompCertTests.ProgramClightEmitTest

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ProgramClightEmit

def tiny : Program := {
  regCount := 2
  loopCount := 1
  init := [.mov 0 (.lit 7)]
  body := [.binop 1 .shl (.reg 0) (.lit 3)]
  epilogue := []
  output := 1
}

theorem tiny_wf : tiny.CompCertWF := by native_decide
theorem tiny_denote : tiny.denote = some 56 := by native_decide

def emitted : String := emitProgram "tiny" tiny 56 tiny_wf tiny_denote

def contract : String := emitProgramContract "tiny" tiny tiny_wf

def rolledContract : String :=
  emitRolledProgramContract "tiny" tiny tiny_wf (by decide)

/-- A trillion iterations exercise the artifact-size boundary.  Its dynamic
safety proof is derived from instruction syntax, so neither this definition
nor contract emission executes the loop. -/
def trillion : Program := { tiny with loopCount := 1000000000000 }

theorem trillion_wf : trillion.CompCertWF := by
  refine ⟨by decide,
    LeanCompCert.Verified.ClightContract.programSafe_of_static trillion ?_ ?_ ?_⟩
  all_goals decide

def trillionRolledContract : String :=
  emitRolledProgramContract "trillion" trillion trillion_wf (by decide)

example : emitted.contains "Definition source_tiny : dsl_program" := by native_decide
example : emitted.contains "Definition f_tiny : function := compile_program source_tiny" := by native_decide
example : emitted.contains
    "apply (compile_program_correct source_tiny expected_tiny empty_ge Mem.empty)" := by
  native_decide
example : emitted.contains "(Dbinop 1 Dshl (Dreg 0) (Dlit 3))" := by native_decide

example : contract.contains "Theorem f_tiny_preserves_denotation" := by native_decide
example : contract.contains "compile_program_correct source_tiny w ge m Hdenote" := by
  native_decide
example : !contract.contains "vm_compute" := by native_decide

example : rolledContract.contains
    "Definition f_tiny : function := compile_rolled_program source_tiny" := by
  native_decide
example : rolledContract.contains
    "Definition emitter_source_tiny : emitter_source" := by
  native_decide
example : rolledContract.contains "Lemma emitter_source_tiny_matches" := by
  native_decide
example : rolledContract.contains "Theorem f_tiny_preserves_denotation" := by
  native_decide
example : rolledContract.contains "Lemma source_tiny_loop_relation" := by
  native_decide
example : rolledContract.contains
    "compile_rolled_program_correct source_tiny w ge m" := by
  native_decide
example : rolledContract.contains
    "dp_loop_count := Z.to_nat loop_limit_tiny" := by
  native_decide
example : !rolledContract.contains "dsl_denote source_tiny = Some expected" := by
  native_decide
example : trillionRolledContract.contains
    "Definition loop_limit_trillion : Z := 1000000000000" := by
  native_decide
example : trillionRolledContract.contains
    "Definition f_trillion : function := compile_rolled_program source_trillion" := by
  native_decide
example : trillionRolledContract.length < 2500 := by native_decide

end LeanCompCertTests.ProgramClightEmitTest
