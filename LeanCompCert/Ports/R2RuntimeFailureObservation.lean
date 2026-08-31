import LeanCompCert.Ports.R2SegEpilogueObservation
import LeanCompCert.Ports.R2RuntimeProductionAuditReceipt

/-!
# Decoded legacy failure classes from the compiled production receipt

The retained positive and fail-safe executions already recover one exact
source run.  Here the generic epilogue theorem decodes the aggregate and nine
per-class zero result cells present in that receipt back to the source
registers immediately after the final-tail test.  The newer tenth (`rVSub`)
cell is deliberately not claimed: establishing it requires a fresh run of the
strengthened artifact.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 10000

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- The exact caller-owned array admitted by the retained setup receipt. -/
def runtimeProductionPacked : AState :=
  rootPackedState runtimeProductionCfg
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr

/-- Exact source entry of the retained production sweep. -/
def runtimeProductionEntry : AState :=
  arun 0 (initialAStateWithArray runtimeProductionPacked.arr)
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init

/-- Exact source loop state observed by the retained production epilogue. -/
def runtimeProductionLoopOut : AState :=
  (List.range
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).loopCount).foldl
    (fun s index => arun index s
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).body)
    runtimeProductionEntry

/-- State immediately after the failure-test prefix of the epilogue. -/
def runtimeProductionTested : AState :=
  arun 0 runtimeProductionLoopOut
    (epilogueTestPrefix runtimeProductionCfg)

/-- Index one of the nine failure counters present in the retained production
receipt. The current `violRegs` has a tenth entry, which this accessor cannot
name. -/
def legacyViolReg (i : Nat) (hi : i < 9) : Nat :=
  violRegs.get ⟨i, by
    have hi' : i < 10 := by omega
    simpa [violRegs] using hi'⟩

/-- The nine legacy failure classes, and their aggregate, are zero in the
source state observed by the production epilogue. Lean only projects the
retained cells; it does not replay the production loop. The current tenth
entry of `violRegs` is outside the retained receipt's slot range. -/
theorem runtimeProduction_verified_failure_classes_zero :
    runtimeProductionTested.regs rViol = 0 ∧
      ∀ i (hi : i < 9),
        runtimeProductionTested.regs (legacyViolReg i hi) = 0 := by
  rcases runtimeProduction_verified_source_observation with
    ⟨packed, out, hRun, _hpacked, _hreceipt, hobs⟩
  have hpackedExact : packed = rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr := _hpacked
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)
    packed.arr out hRun
  subst packed
  change out = arun 0 runtimeProductionLoopOut
    runtimeProductionCfg.epilogue at hout
  have hcells := epilogue_failure_cells runtimeProductionCfg
    runtimeProductionLoopOut (by decide)
  change
    (arun 0 runtimeProductionLoopOut runtimeProductionCfg.epilogue).arr
          (runtimeProductionCfg.resultBase + 10) =
        runtimeProductionTested.regs rViol ∧
      ∀ i (hi : i < violRegs.length),
        (arun 0 runtimeProductionLoopOut runtimeProductionCfg.epilogue).arr
            (runtimeProductionCfg.resultBase + 11 + i) =
          runtimeProductionTested.regs (violRegs.get ⟨i, hi⟩) at hcells
  rw [← hout] at hcells
  have hzAgg :
      runtimeProductionTested.regs rViol = 0 := by
    have hz := hobs.2.2.2.2.2.2.2.2.2.2.2 10 (by decide) (by decide)
    exact hcells.1.symm.trans hz
  refine ⟨hzAgg, ?_⟩
  intro i hi
  have hi10 : i < violRegs.length := by
    have hi' : i < 10 := by omega
    simpa [violRegs] using hi'
  have hz := hobs.2.2.2.2.2.2.2.2.2.2.2 (11 + i) (by omega) (by omega)
  have hzero :
      runtimeProductionTested.regs (violRegs.get ⟨i, hi10⟩) = 0 :=
    (hcells.2 i hi10).symm.trans (by
      simpa only [Nat.add_assoc] using hz)
  have hget : violRegs.get ⟨i, hi10⟩ = legacyViolReg i hi := by
    apply congrArg violRegs.get
    apply Fin.ext
    rfl
  rwa [hget] at hzero

/-- Named projections used by the marking and stream telescopes. -/
theorem runtimeProduction_verified_no_mark_or_drain_failure :
    runtimeProductionLoopOut.regs rVMark = 0 ∧
      runtimeProductionLoopOut.regs rVCap = 0 ∧
      runtimeProductionLoopOut.regs rVDrain = 0 := by
  rcases runtimeProduction_verified_failure_classes_zero with ⟨_hv, hs⟩
  have hmark := hs 3 (by decide)
  have hcap := hs 4 (by decide)
  have hdrain := hs 5 (by decide)
  have hgetMark : legacyViolReg 3 (by decide) = rVMark := by rfl
  have hgetCap : legacyViolReg 4 (by decide) = rVCap := by rfl
  have hgetDrain : legacyViolReg 5 (by decide) = rVDrain := by rfl
  rw [hgetMark] at hmark
  rw [hgetCap] at hcap
  rw [hgetDrain] at hdrain
  have frame (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
          (epilogueTestPrefix runtimeProductionCfg) = false) :
      runtimeProductionTested.regs r = runtimeProductionLoopOut.regs r := by
    rw [runtimeProductionTested]
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r
      (epilogueTestPrefix runtimeProductionCfg) h runtimeProductionLoopOut
  refine ⟨?_, ?_, ?_⟩
  · exact (frame rVMark (by rfl)).symm.trans hmark
  · exact (frame rVCap (by rfl)).symm.trans hcap
  · exact (frame rVDrain (by rfl)).symm.trans hdrain

#print axioms runtimeProduction_verified_failure_classes_zero
#print axioms runtimeProduction_verified_no_mark_or_drain_failure

end LeanCompCert.Ports.R2SegSieve
