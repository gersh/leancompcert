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

example : emitted.contains "Definition source_tiny : dsl_program" := by native_decide
example : emitted.contains "Definition f_tiny : function := compile_program source_tiny" := by native_decide
example : emitted.contains
    "apply (compile_program_correct source_tiny expected_tiny empty_ge Mem.empty)" := by
  native_decide
example : emitted.contains "(Dbinop 1 Dshl (Dreg 0) (Dlit 3))" := by native_decide

end LeanCompCertTests.ProgramClightEmitTest
