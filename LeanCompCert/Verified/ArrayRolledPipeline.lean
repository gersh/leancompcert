import LeanCompCert.Verified.ArrayCounterAugmentSource

/-!
# Rolled array programs in caller-owned memory

This module joins the arbitrary-input-array compiler simulation with the
constant-size rolled-loop equivalence.  It is the bridge used by compiled
producer/consumer pipelines: the generated executable retains the producer's
array in memory, while Lean reasons symbolically about the corresponding
source array and never evaluates the production loop.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment

/-- A rolled program started with a represented caller-owned array simulates
the counter-augmented source execution from that array.  The theorem is
uniform in `p.loopCount`; applying it to a production count does not unfold
or evaluate the loop in Lean. -/
theorem AProgram.evalCC_rolledCompile_fromArray
    (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState)
    (hRun : p.counterAugment.runFromArray arr = some out) :
    ∃ m,
      evalMCCSequence
          (p.counterAugment.initialMCCWithMem base mem)
          p.rolledCompile = some m ∧
        ARel p.counterAugment.regCount p.arrayLen base out m := by
  have hAugWF := counterAugment_WF p hWF
  have hAugBase : BaseOk p.counterAugment.arrayLen base := by
    simpa [AProgram.counterAugment] using hBase
  obtain ⟨m, hEval, hRel⟩ :=
    p.counterAugment.evalCC_compile_fromArray hAugWF base hAugBase arr mem
      (by simpa [AProgram.counterAugment] using hCells)
      (by simpa [AProgram.counterAugment] using hCellsLt) out hRun
  refine ⟨m, ?_, ?_⟩
  · change evalMCCSequence
        ({ env := (p.counterAugment.initialMCC base).env, mem := mem } : MCCState)
          p.rolledCompile = some m
    rw [evalMCCSequence_rolledCompile_eq_counterAugment_withMem
      p hWF base mem]
    simpa [AProgram.initialMCCWithMem] using hEval
  · simpa [AProgram.counterAugment] using hRel

/-- Identify a retained rolled machine state with a successful source run.
The machine execution is supplied as a receipt; determinism equates it with
the state produced by compiler simulation.  This is uniform in the loop count
and does not replay the source fold. -/
theorem AProgram.sourceRel_of_rolledCompile_fromArray
    (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState) (hRun : p.runFromArray arr = some out)
    (m : MCCState)
    (hEval : evalMCCSequence
      (p.counterAugment.initialMCCWithMem base mem) p.rolledCompile = some m) :
    ∃ out',
      p.counterAugment.runFromArray arr = some out' ∧
      AState.AgreeBelow p.regCount out out' ∧
      ARel p.counterAugment.regCount p.arrayLen base out' m := by
  obtain ⟨out', hRun', hAgree⟩ :=
    p.counterAugment_runFromArray_of_runFromArray hWF arr out hRun
  obtain ⟨m', hEval', hRel⟩ := p.evalCC_rolledCompile_fromArray hWF base
    hBase arr mem hCells hCellsLt out' hRun'
  have hm : m' = m := by
    rw [hEval] at hEval'
    exact (Option.some.inj hEval').symm
  subst m'
  exact ⟨out', hRun', hAgree, hRel⟩

/-- Read one retained result cell back to the original source state. -/
theorem AProgram.cell_eq_of_rolledCompile_fromArray
    (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState) (hRun : p.runFromArray arr = some out)
    (m : MCCState)
    (hEval : evalMCCSequence
      (p.counterAugment.initialMCCWithMem base mem) p.rolledCompile = some m)
    (k value : Nat) (hk : k < p.arrayLen)
    (hCell : m.mem (cellAddr base k) = some (value : Int)) :
    out.arr k = value := by
  obtain ⟨out', _hRun', hAgree, hRel⟩ :=
    p.sourceRel_of_rolledCompile_fromArray hWF base hBase arr mem hCells
      hCellsLt out hRun m hEval
  have hSourceCell := hRel.hcells k hk
  rw [hCell] at hSourceCell
  have hOut' : out'.arr k = value := by
    exact_mod_cast (Option.some.inj hSourceCell).symm
  rw [hAgree.2]
  exact hOut'

/-- Read a successful rolled execution back into the already-proved symbolic
source state.  The expensive loop is executed by the compiled artifact; Lean
uses determinism of the CCIR trace and the compiler simulation to identify
the compact returned word. -/
theorem AProgram.output_eq_of_rolledCompile_fromArray
    (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState)
    (hRun : p.runFromArray arr = some out)
    (value : Nat)
    (hReceipt : Option.bind
      (evalMCCSequence
        (p.counterAugment.initialMCCWithMem base mem)
        p.rolledCompile)
      (fun m : MCCState => m.env ⟨p.output + 1⟩) =
        some ((value : Nat) : Int)) :
    out.regs p.output = value := by
  obtain ⟨out', hRun', hAgree⟩ :=
    p.counterAugment_runFromArray_of_runFromArray hWF arr out hRun
  obtain ⟨m, hEval, hRel⟩ := p.evalCC_rolledCompile_fromArray hWF base
    hBase arr mem hCells hCellsLt out' hRun'
  rw [hEval] at hReceipt
  simp only [Option.bind_some] at hReceipt
  have hOut : p.output < p.counterAugment.regCount := by
    change p.output < p.regCount + 1
    exact Nat.lt_succ_of_lt hWF.1
  have hState := hRel.hregs.1 p.output hOut
  rw [hReceipt] at hState
  have hOut' : out'.regs p.output = value := by
    exact_mod_cast Option.some.inj hState.symm
  exact (hAgree.1 p.output hWF.1).trans hOut'

#print axioms AProgram.evalCC_rolledCompile_fromArray
#print axioms AProgram.sourceRel_of_rolledCompile_fromArray
#print axioms AProgram.cell_eq_of_rolledCompile_fromArray
#print axioms AProgram.output_eq_of_rolledCompile_fromArray

end LeanCompCert.Verified.ArrayState
