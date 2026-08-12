import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckFold

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

set_option maxRecDepth 20000000

theorem bodyC1_wf : ∀ i ∈ bodyC1, i.WF MertensCDEM.regCount := by
  intro i hi
  simp only [bodyC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, MertensCDEM.regCount]

theorem bodyC2_wf : ∀ i ∈ bodyC2, i.WF MertensCDEM.regCount := by
  intro i hi
  simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, MertensCDEM.regCount]

theorem bodyC3_wf : ∀ i ∈ bodyC3, i.WF MertensCDEM.regCount := by
  intro i hi
  simp only [bodyC3, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, MertensCDEM.regCount]

theorem bodyC_wf : ∀ i ∈ bodyC, i.WF MertensCDEM.regCount := by
  intro i hi
  rw [bodyC] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyC1_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC2_wf i h
  · exact bodyC3_wf i h

theorem body_wf : ∀ i ∈ body, i.WF MertensCDEM.regCount := by
  intro i hi
  rw [body] at hi
  rcases List.mem_append.mp hi with h | h
  · exact MertensCDEM.bodyA_wf trialCfg i h
  rcases List.mem_append.mp h with h | h
  · exact MertensCDEM.bodyB_wf i h
  · exact bodyC_wf i h

theorem initBlock_wf : ∀ i ∈ initBlock, i.WF MertensCDEM.regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp +decide [Instr.WF, Operand.WF, MertensCDEM.regCount]

theorem program_wf : program.WF :=
  ⟨by decide, initBlock_wf, body_wf, by intro i hi; cases hi⟩

theorem program_compiled :
    ((Proof.evalCCSequence Verified.emptyCCEnv program.compile).bind
        (fun env => env ⟨program.output + 1⟩)) =
      program.denote.map (fun n => (n : Int)) :=
  Program.evalCC_compile program program_wf

end LeanCompCert.Ports.CDEMAbelMarkBudgetCheck
