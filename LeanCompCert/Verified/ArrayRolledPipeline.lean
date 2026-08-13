import LeanCompCert.Verified.ArrayPipeline
import LeanCompCert.Verified.ArrayRolled

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

#print axioms AProgram.evalCC_rolledCompile_fromArray

end LeanCompCert.Verified.ArrayState
