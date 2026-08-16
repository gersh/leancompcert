import LeanCompCert.Ports.Prop1224RowObservation
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Retained CompCert receipts for Proposition 12.2.4 row shards

A production shard is accepted only when two executions agree: the ordinary
compiled program supplies its result words, while the mechanically audited
compiled program returns zero.  The latter proves source definedness; compiler
simulation then transports every retained result word to that source run.
-/

namespace LeanCompCert.Ports.Prop1224Row

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment

/-- Positive compiled receipt for one closed row shard. -/
def RowReceipt (c : RowCfg) (expected : List Nat) : Prop :=
  expected.length = resultRegs.length ∧
  ∃ m : MCCState,
    evalMCCSequence
        ((rowProgram c).counterAugment.initialMCCWithMem
          0 (initialMem (rowProgram c).arrayLen 0))
        (rowProgram c).rolledCompile = some m ∧
    m.env ⟨(rowProgram c).output + 1⟩ = some 0 ∧
    ∀ i (hi : i < expected.length),
      m.mem (cellAddr 0 (c.resultBase + i)) =
        some (expected.get ⟨i, hi⟩ : Int)

/-- Fail-safe compiled receipt for the same closed row shard. -/
def RowAuditReceipt (c : RowCfg) : Prop :=
  ∃ m : MCCState,
    evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (rowProgram c)).counterAugment.initialMCCWithMem
            0 (initialMem (rowProgram c).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (rowProgram c)).rolledCompile = some m ∧
    m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
      (rowProgram c)).output + 1⟩ = some 0

/-- The audit receipt establishes a genuine source execution of the shard. -/
theorem rowAudit_source_run (c : RowCfg)
    (hBase : BaseOk (rowProgram c).arrayLen 0)
    (hlen : 0 < (rowProgram c).arrayLen)
    (hlenM : (rowProgram c).arrayLen < M)
    (h : RowAuditReceipt c) :
    ∃ out, (rowProgram c).runFromArray (fun _ => 0) = some out := by
  rcases h with ⟨m, hEval, hZero⟩
  have hReceipt : Option.bind
      (evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (rowProgram c)).counterAugment.initialMCCWithMem
            0 (initialMem (rowProgram c).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (rowProgram c)).rolledCompile)
      (fun m : MCCState => m.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (rowProgram c)).output + 1⟩) = some (0 : Int) := by
    rw [hEval]
    exact hZero
  exact LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
    (rowProgram c) (rowProgram_wf c) 0 hBase (fun _ => 0)
    (initialMem (rowProgram c).arrayLen 0)
    (fun k hk => initialMem_cell (rowProgram c).arrayLen 0 hk)
    (fun _ => by decide) hlen hlenM hReceipt

/-- Positive and audit receipts identify the exact source-visible result
vector.  The source loop remains opaque regardless of shard size. -/
theorem rowReceipt_source_observation (c : RowCfg) (expected : List Nat)
    (hBase : BaseOk (rowProgram c).arrayLen 0)
    (hlen : 0 < (rowProgram c).arrayLen)
    (hlenM : (rowProgram c).arrayLen < M)
    (hAudit : RowAuditReceipt c) (hPositive : RowReceipt c expected) :
    ∃ out,
      (rowProgram c).runFromArray (fun _ => 0) = some out ∧
      out.regs outputReg = 0 ∧
      ∀ i (hi : i < expected.length),
        out.arr (c.resultBase + i) = expected.get ⟨i, hi⟩ := by
  rcases rowAudit_source_run c hBase hlen hlenM hAudit with
    ⟨out, hRun⟩
  rcases hPositive with ⟨hlenExpected, m, hEval, hOutput, hCells⟩
  obtain ⟨outAug, hOutAug, hAgree⟩ :=
    (rowProgram c).counterAugment_runFromArray_of_runFromArray
      (rowProgram_wf c) (fun _ => 0) out hRun
  obtain ⟨m', hEval', hRel⟩ :=
    (rowProgram c).evalCC_rolledCompile_fromArray
      (rowProgram_wf c) 0 hBase (fun _ => 0)
      (initialMem (rowProgram c).arrayLen 0)
      (fun k hk => initialMem_cell (rowProgram c).arrayLen 0 hk)
      (fun _ _ => by decide) outAug hOutAug
  have hm : m' = m := by
    rw [hEval] at hEval'
    exact (Option.some.inj hEval').symm
  subst m'
  have hOut : out.regs outputReg = 0 := by
    have haug : outputReg < (rowProgram c).counterAugment.regCount := by
      simp [AProgram.counterAugment, AProgram.augCount, rowProgram,
        outputReg, regCount]
    have hr := hRel.hregs.1 outputReg haug
    change m.env ⟨outputReg + 1⟩ =
      some (outAug.regs outputReg : Int) at hr
    have hOutput' : m.env ⟨outputReg + 1⟩ = some 0 := by
      simpa [rowProgram, outputReg] using hOutput
    have hzero : outAug.regs outputReg = 0 := by
      rw [hOutput'] at hr
      exact_mod_cast (Option.some.inj hr).symm
    have hout : outputReg < (rowProgram c).regCount := by
      simp [rowProgram, outputReg, regCount]
    exact (hAgree.1 outputReg hout).trans hzero
  refine ⟨out, hRun, hOut, ?_⟩
  intro i hi
  have hiResult : i < resultRegs.length := by omega
  have hk : c.resultBase + i < (rowProgram c).arrayLen := by
    have hi20 : i < 20 := by
      simpa [resultRegs, violRegs] using hiResult
    simp only [rowProgram, RowCfg.arrayLen]
    omega
  have hr := hRel.hcells (c.resultBase + i) hk
  rw [hCells i hi] at hr
  have hAug : outAug.arr (c.resultBase + i) = expected.get ⟨i, hi⟩ := by
    exact_mod_cast (Option.some.inj hr).symm
  rw [hAgree.2]
  exact hAug

#print axioms rowAudit_source_run
#print axioms rowReceipt_source_observation

end LeanCompCert.Ports.Prop1224Row
