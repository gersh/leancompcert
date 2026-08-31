import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Retired physical CompCert receipts for the pre-strengthening dense R2 head

This module is historical provenance only.  Its observations use the former
twenty-result-cell offset `arrayLen - 20`.  The strengthened program has
twenty-one result cells, so these declarations do not instantiate the live
`DenseHeadAcceptance` contract (`arrayLen - 21`) and this module is
intentionally absent from `LeanCompCert.lean`.  A future causal campaign must
re-run the current literal program; do not import these axioms into a live
semantic route.

The positive programs record the eleven carry words.  Independently emitted
fail-safe audit programs certify that every partial source operation in both
dense folds was defined.  Compiler simulation and determinism then recover
the source executions without asking Lean to evaluate either numerical fold.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.Reflect

def DenseHeadObservation (p : AProgram) (carry : R2Seed) (m : MCCState) : Prop :=
  m.env ⟨p.output + 1⟩ = some 0 ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 0)) = some (carry.d : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 1)) = some (carry.err : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 2)) = some (carry.prev : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 3)) = some (carry.terms : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 4)) = some (carry.sq : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 5)) = some (carry.sq2 : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 6)) = some (carry.ex : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 7)) = some (carry.th : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 8)) = some (carry.ln : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 9)) = some (carry.thr : Int) ∧
  m.mem (cellAddr 0 (p.arrayLen - 20 + 10)) = some (carry.viol : Int)

def DenseHeadRunReceipt (p : AProgram) (carry : R2Seed) : Prop :=
  ∃ m : MCCState,
    evalMCCSequence
        (p.counterAugment.initialMCCWithMem 0 (initialMem p.arrayLen 0))
        p.rolledCompile = some m ∧
    DenseHeadObservation p carry m

def DenseHeadAuditReceipt (p : AProgram) : Prop :=
  ∃ m : MCCState,
    evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram p).counterAugment.initialMCCWithMem
          0 (initialMem p.arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram p).rolledCompile = some m ∧
    m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram p).output + 1⟩ = some 0

abbrev denseHeadFirstProgram : AProgram :=
  r2DenseHeadProgram denseHeadFirstCfg denseHeadFirstSeed

abbrev denseHeadSecondProgram : AProgram :=
  r2DenseHeadProgram denseHeadSecondCfg denseHeadSecondSeed

/-- Retained CompCert 3.17 execution of the positive first dense shard. -/
axiom denseHeadFirst_compcert_run :
  DenseHeadRunReceipt denseHeadFirstProgram denseHeadFirstCarry

/-- Retained CompCert 3.17 execution of the fail-safe first dense shard. -/
axiom denseHeadFirstAudit_compcert_run :
  DenseHeadAuditReceipt denseHeadFirstProgram

/-- Retained CompCert 3.17 execution of the positive second dense shard. -/
axiom denseHeadSecond_compcert_run :
  DenseHeadRunReceipt denseHeadSecondProgram denseHeadFinalCarry

/-- Retained CompCert 3.17 execution of the fail-safe second dense shard. -/
axiom denseHeadSecondAudit_compcert_run :
  DenseHeadAuditReceipt denseHeadSecondProgram

private theorem denseHeadBaseOk (p : AProgram)
    (h : 8 * p.arrayLen ≤ M) :
    BaseOk p.arrayLen 0 := by
  constructor
  · omega
  · simpa only [Int.zero_add] using (Int.ofNat_le.mpr h)

/-- A zero audit receipt recovers a source execution of a dense shard. -/
theorem denseHead_source_run_of_audit (p : AProgram) (hp : p.WF)
    (hBase : 8 * p.arrayLen ≤ M)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M)
    (h : DenseHeadAuditReceipt p) :
    ∃ out, p.runFromArray (fun _ => 0) = some out := by
  rcases h with ⟨m, hEval, hZero⟩
  apply LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
    p hp 0 (denseHeadBaseOk p hBase) (fun _ => 0)
      (initialMem p.arrayLen 0)
  · intro k hk
    exact initialMem_cell p.arrayLen 0 hk
  · intro k
    exact M_pos
  · exact hlen
  · exact hlenM
  · rw [hEval]
    exact hZero

/-- A positive receipt identifies all eleven source carry cells. -/
theorem denseHead_source_observation (p : AProgram) (hp : p.WF)
    (hBase : 8 * p.arrayLen ≤ M) (hlen20 : 20 ≤ p.arrayLen)
    (carry : R2Seed)
    (hRun : ∃ out, p.runFromArray (fun _ => 0) = some out)
    (hReceipt : DenseHeadRunReceipt p carry) :
    ∃ out, p.runFromArray (fun _ => 0) = some out ∧
      out.arr (p.arrayLen - 20 + 0) = carry.d ∧
      out.arr (p.arrayLen - 20 + 1) = carry.err ∧
      out.arr (p.arrayLen - 20 + 2) = carry.prev ∧
      out.arr (p.arrayLen - 20 + 3) = carry.terms ∧
      out.arr (p.arrayLen - 20 + 4) = carry.sq ∧
      out.arr (p.arrayLen - 20 + 5) = carry.sq2 ∧
      out.arr (p.arrayLen - 20 + 6) = carry.ex ∧
      out.arr (p.arrayLen - 20 + 7) = carry.th ∧
      out.arr (p.arrayLen - 20 + 8) = carry.ln ∧
      out.arr (p.arrayLen - 20 + 9) = carry.thr ∧
      out.arr (p.arrayLen - 20 + 10) = carry.viol := by
  rcases hRun with ⟨out, hSource⟩
  rcases hReceipt with ⟨m, hEval, hObs⟩
  have hBaseOk := denseHeadBaseOk p hBase
  have hCells : ∀ k, k < p.arrayLen →
      initialMem p.arrayLen 0 (cellAddr 0 k) = some ((((fun _ => 0) k : Nat) : Int)) := by
    intro k hk
    exact initialMem_cell p.arrayLen 0 hk
  have hWords : ∀ k : Nat, k < p.arrayLen → (fun _ => 0) k < M := by
    intro k hk
    exact M_pos
  have cell (slot value : Nat) (hslot : slot < 20)
      (hm : m.mem (cellAddr 0 (p.arrayLen - 20 + slot)) = some (value : Int)) :
      out.arr (p.arrayLen - 20 + slot) = value := by
    apply p.cell_eq_of_rolledCompile_fromArray hp 0 hBaseOk (fun _ => 0)
      (initialMem p.arrayLen 0) hCells hWords out hSource m hEval
    · omega
    · exact hm
  exact ⟨out, hSource,
    cell 0 carry.d (by decide) hObs.2.1,
    cell 1 carry.err (by decide) hObs.2.2.1,
    cell 2 carry.prev (by decide) hObs.2.2.2.1,
    cell 3 carry.terms (by decide) hObs.2.2.2.2.1,
    cell 4 carry.sq (by decide) hObs.2.2.2.2.2.1,
    cell 5 carry.sq2 (by decide) hObs.2.2.2.2.2.2.1,
    cell 6 carry.ex (by decide) hObs.2.2.2.2.2.2.2.1,
    cell 7 carry.th (by decide) hObs.2.2.2.2.2.2.2.2.1,
    cell 8 carry.ln (by decide) hObs.2.2.2.2.2.2.2.2.2.1,
    cell 9 carry.thr (by decide) hObs.2.2.2.2.2.2.2.2.2.2.1,
    cell 10 carry.viol (by decide) hObs.2.2.2.2.2.2.2.2.2.2.2⟩

set_option maxRecDepth 40000 in
theorem denseHeadFirst_verified_source_observation :
    ∃ out, denseHeadFirstProgram.runFromArray (fun _ => 0) = some out ∧
      out.arr (denseHeadFirstProgram.arrayLen - 20 + 0) = denseHeadFirstCarry.d ∧
      out.arr (denseHeadFirstProgram.arrayLen - 20 + 10) = denseHeadFirstCarry.viol := by
  have hRun := denseHead_source_run_of_audit denseHeadFirstProgram
    (r2DenseHeadProgram_wf _ _)
    (by rw [show denseHeadFirstProgram.arrayLen = 7434 by
      exact denseHeadFirst_arrayLen]; decide)
    (by rw [show denseHeadFirstProgram.arrayLen = 7434 by
      exact denseHeadFirst_arrayLen]; decide)
    (by rw [show denseHeadFirstProgram.arrayLen = 7434 by
      exact denseHeadFirst_arrayLen]; decide)
    denseHeadFirstAudit_compcert_run
  rcases denseHead_source_observation denseHeadFirstProgram
      (r2DenseHeadProgram_wf _ _)
      (by rw [show denseHeadFirstProgram.arrayLen = 7434 by
        exact denseHeadFirst_arrayLen]; decide)
      (by rw [show denseHeadFirstProgram.arrayLen = 7434 by
        exact denseHeadFirst_arrayLen]; decide)
      denseHeadFirstCarry hRun
      denseHeadFirst_compcert_run with
    ⟨out, hsource, hd, _, _, _, _, _, _, _, _, _, hv⟩
  exact ⟨out, hsource, hd, hv⟩

set_option maxRecDepth 40000 in
theorem denseHeadSecond_verified_source_observation :
    ∃ out, denseHeadSecondProgram.runFromArray (fun _ => 0) = some out ∧
      out.arr (denseHeadSecondProgram.arrayLen - 20 + 0) = denseHeadFinalCarry.d ∧
      out.arr (denseHeadSecondProgram.arrayLen - 20 + 10) = denseHeadFinalCarry.viol := by
  have hRun := denseHead_source_run_of_audit denseHeadSecondProgram
    (r2DenseHeadProgram_wf _ _)
    (by rw [show denseHeadSecondProgram.arrayLen = 1008348 by
      exact denseHeadSecond_arrayLen]; decide)
    (by rw [show denseHeadSecondProgram.arrayLen = 1008348 by
      exact denseHeadSecond_arrayLen]; decide)
    (by rw [show denseHeadSecondProgram.arrayLen = 1008348 by
      exact denseHeadSecond_arrayLen]; decide)
    denseHeadSecondAudit_compcert_run
  rcases denseHead_source_observation denseHeadSecondProgram
      (r2DenseHeadProgram_wf _ _)
      (by rw [show denseHeadSecondProgram.arrayLen = 1008348 by
        exact denseHeadSecond_arrayLen]; decide)
      (by rw [show denseHeadSecondProgram.arrayLen = 1008348 by
        exact denseHeadSecond_arrayLen]; decide)
      denseHeadFinalCarry hRun
      denseHeadSecond_compcert_run with
    ⟨out, hsource, hd, _, _, _, _, _, _, _, _, _, hv⟩
  exact ⟨out, hsource, hd, hv⟩

#print axioms denseHeadFirst_verified_source_observation
#print axioms denseHeadSecond_verified_source_observation

end LeanCompCert.Ports.R2SegSieve
