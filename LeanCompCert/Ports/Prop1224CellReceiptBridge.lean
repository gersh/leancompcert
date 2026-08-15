import LeanCompCert.Ports.Prop1224CellObservation
import LeanCompCert.Ports.Prop1224CellMarginTelescope
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Retained CompCert receipts for Proposition 12.2.4 cell shards

As for the row stage, a positive execution supplies the result vector and a
mechanically audited execution proves that the partial source program is
defined.  The bridge is generic in the row constants and shard dimensions.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment

def CellReceipt (c : CellCfg) (seed : CellSeed) (expected : List Nat) : Prop :=
  expected.length = resultRegs.length ∧
  ∃ m : MCCState,
    evalMCCSequence
        ((cellProgram c seed).counterAugment.initialMCCWithMem
          0 (initialMem (cellProgram c seed).arrayLen 0))
        (cellProgram c seed).rolledCompile = some m ∧
    m.env ⟨(cellProgram c seed).output + 1⟩ = some 0 ∧
    ∀ i (hi : i < expected.length),
      m.mem (cellAddr 0 (c.resultBase + i)) =
        some (expected.get ⟨i, hi⟩ : Int)

def CellAuditReceipt (c : CellCfg) (seed : CellSeed) : Prop :=
  ∃ m : MCCState,
    evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (cellProgram c seed)).counterAugment.initialMCCWithMem
            0 (initialMem (cellProgram c seed).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (cellProgram c seed)).rolledCompile = some m ∧
    m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
      (cellProgram c seed)).output + 1⟩ = some 0

theorem cellAudit_source_run (c : CellCfg) (seed : CellSeed)
    (hBase : BaseOk (cellProgram c seed).arrayLen 0)
    (hlen : 0 < (cellProgram c seed).arrayLen)
    (hlenM : (cellProgram c seed).arrayLen < M)
    (h : CellAuditReceipt c seed) :
    ∃ out, (cellProgram c seed).runFromArray (fun _ => 0) = some out := by
  rcases h with ⟨m, hEval, hZero⟩
  have hReceipt : Option.bind
      (evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (cellProgram c seed)).counterAugment.initialMCCWithMem
            0 (initialMem (cellProgram c seed).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (cellProgram c seed)).rolledCompile)
      (fun m : MCCState => m.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (cellProgram c seed)).output + 1⟩) = some (0 : Int) := by
    rw [hEval]
    exact hZero
  exact LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
    (cellProgram c seed) (cellProgram_wf c seed) 0 hBase (fun _ => 0)
    (initialMem (cellProgram c seed).arrayLen 0)
    (fun k hk => initialMem_cell (cellProgram c seed).arrayLen 0 hk)
    (fun _ => by decide) hlen hlenM hReceipt

theorem cellReceipt_source_observation (c : CellCfg) (seed : CellSeed)
    (expected : List Nat)
    (hBase : BaseOk (cellProgram c seed).arrayLen 0)
    (hlen : 0 < (cellProgram c seed).arrayLen)
    (hlenM : (cellProgram c seed).arrayLen < M)
    (hAudit : CellAuditReceipt c seed)
    (hPositive : CellReceipt c seed expected) :
    ∃ out,
      (cellProgram c seed).runFromArray (fun _ => 0) = some out ∧
      out.regs outputReg = 0 ∧
      ∀ i (hi : i < expected.length),
        out.arr (c.resultBase + i) = expected.get ⟨i, hi⟩ := by
  rcases cellAudit_source_run c seed hBase hlen hlenM hAudit with
    ⟨out, hRun⟩
  rcases hPositive with ⟨hlenExpected, m, hEval, hOutput, hCells⟩
  obtain ⟨outAug, hOutAug, hAgree⟩ :=
    (cellProgram c seed).counterAugment_runFromArray_of_runFromArray
      (cellProgram_wf c seed) (fun _ => 0) out hRun
  obtain ⟨m', hEval', hRel⟩ :=
    (cellProgram c seed).evalCC_rolledCompile_fromArray
      (cellProgram_wf c seed) 0 hBase (fun _ => 0)
      (initialMem (cellProgram c seed).arrayLen 0)
      (fun k hk => initialMem_cell (cellProgram c seed).arrayLen 0 hk)
      (fun _ _ => by decide) outAug hOutAug
  have hm : m' = m := by
    rw [hEval] at hEval'
    exact (Option.some.inj hEval').symm
  subst m'
  have hOut : out.regs outputReg = 0 := by
    have haug : outputReg < (cellProgram c seed).counterAugment.regCount := by
      simp [AProgram.counterAugment, AProgram.augCount, cellProgram,
        outputReg, regCount]
    have hr := hRel.hregs.1 outputReg haug
    change m.env ⟨outputReg + 1⟩ =
      some (outAug.regs outputReg : Int) at hr
    have hOutput' : m.env ⟨outputReg + 1⟩ = some 0 := by
      simpa [cellProgram, outputReg] using hOutput
    have hzero : outAug.regs outputReg = 0 := by
      rw [hOutput'] at hr
      exact_mod_cast (Option.some.inj hr).symm
    have hout : outputReg < (cellProgram c seed).regCount := by
      simp [cellProgram, outputReg, regCount]
    exact (hAgree.1 outputReg hout).trans hzero
  refine ⟨out, hRun, hOut, ?_⟩
  intro i hi
  have hiResult : i < resultRegs.length := by omega
  have hk : c.resultBase + i < (cellProgram c seed).arrayLen := by
    have hi11 : i < 11 := by
      simpa [resultRegs, violRegs] using hiResult
    simp only [cellProgram, CellCfg.arrayLen]
    omega
  have hr := hRel.hcells (c.resultBase + i) hk
  rw [hCells i hi] at hr
  have hAug : outAug.arr (c.resultBase + i) = expected.get ⟨i, hi⟩ := by
    exact_mod_cast (Option.some.inj hr).symm
  rw [hAgree.2]
  exact hAug

/-- The retained result slot for `rVMargin` is the terminal counter of the
actual source-denotational body fold.  This exposes a positive CompCert receipt
without replaying the production loop in Lean. -/
theorem cellReceipt_loop_vmargin_zero (c : CellCfg) (seed : CellSeed)
    (expected : List Nat)
    (hBase : BaseOk (cellProgram c seed).arrayLen 0)
    (hlen : 0 < (cellProgram c seed).arrayLen)
    (hlenM : (cellProgram c seed).arrayLen < M)
    (hAudit : CellAuditReceipt c seed)
    (hPositive : CellReceipt c seed expected)
    (h6 : 6 < expected.length)
    (hExpectedMargin : expected.get ⟨6, h6⟩ = 0) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (cellProgram c seed).init
    (runMarginBodies c (List.range (c.period * c.segCount)) entry).regs
      rVMargin = 0 := by
  rcases cellReceipt_source_observation c seed expected hBase hlen hlenM
      hAudit hPositive with ⟨out, hRun, _, hObserved⟩
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (cellProgram c seed).init
  let loopOut := runMarginBodies c
    (List.range (c.period * c.segCount)) entry
  have houtEq := (cellProgram c seed).eq_arun_of_runFromArray_eq_some
    (fun _ => 0) out hRun
  change out = arun 0
    ((List.range (c.period * c.segCount)).foldl
      (fun st idx => arun idx st c.body) entry) c.epilogue at houtEq
  rw [← runMarginBodies_eq_foldl] at houtEq
  change out = arun 0 loopOut c.epilogue at houtEq
  have hiResult : 6 < resultRegs.length := by decide
  have hbound : c.resultBase + resultRegs.length ≤ M := by
    simp only [cellProgram, CellCfg.arrayLen] at hlenM
    simp [resultRegs, violRegs]
    omega
  have hEpi := epilogue_result_cell c loopOut 6 hiResult hbound
  have hget : resultRegs.get ⟨6, hiResult⟩ = rVMargin := by
    have hp : hiResult = (by decide : 6 < resultRegs.length) :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  have hEpiMargin :
      (arun 0 loopOut c.epilogue).arr (c.resultBase + 6) =
        loopOut.regs rVMargin := by
    rw [hget] at hEpi
    exact hEpi
  have houtMargin : out.arr (c.resultBase + 6) =
      loopOut.regs rVMargin := by
    rw [houtEq]
    exact hEpiMargin
  rw [hObserved 6 h6, hExpectedMargin] at houtMargin
  exact houtMargin.symm

/-- A zero retained CompCert margin slot proves every local comparison in the
symbolic body trace.  The only remaining hypotheses are the size-independent
word/readiness invariants used by the exact instruction semantics. -/
theorem cellReceipt_allMarginsPass (c : CellCfg) (seed : CellSeed)
    (expected : List Nat)
    (hBase : BaseOk (cellProgram c seed).arrayLen 0)
    (hlen : 0 < (cellProgram c seed).arrayLen)
    (hlenM : (cellProgram c seed).arrayLen < M)
    (hAudit : CellAuditReceipt c seed)
    (hPositive : CellReceipt c seed expected)
    (h6 : 6 < expected.length)
    (hExpectedMargin : expected.get ⟨6, h6⟩ = 0)
    (htrace : MarginTraceReady c (List.range (c.period * c.segCount))
      (arun 0 (initialAStateWithArray (fun _ => 0))
        (cellProgram c seed).init)) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (cellProgram c seed).init
    AllMarginsPass c (List.range (c.period * c.segCount)) entry := by
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (cellProgram c seed).init
  apply allMarginsPass_of_terminal_zero c
    (List.range (c.period * c.segCount)) entry htrace
  · exact cellEntry_vmargin_zero c seed (fun _ => 0)
  · exact cellReceipt_loop_vmargin_zero c seed expected hBase hlen hlenM
      hAudit hPositive h6 hExpectedMargin

#print axioms cellAudit_source_run
#print axioms cellReceipt_source_observation
#print axioms cellReceipt_loop_vmargin_zero
#print axioms cellReceipt_allMarginsPass

end LeanCompCert.Ports.Prop1224Cell
