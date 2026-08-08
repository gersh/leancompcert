import LeanCompCert.Ports.ArraySegMobiusPlattAuditTrace
import LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
import LeanCompCert.Ports.ArraySegMobiusSquaredSeed

/-!
# Transparent fold receipts for the aligned Platt campaign

This layer composes the opaque compiled trace receipts with the verified
finite production schedules.  Its conclusions mention only the transparent
paper-faithful squared fold; the enormous machine trace remains behind the
separately compiled theorem boundary.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattAuditFold

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.ArraySegMobiusSquaredSeed
open LeanCompCert.Ports.ArraySegMobiusProductionBounds
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.ArraySegMobiusPlattConfig
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate
open LeanCompCert.Ports.ArraySegMobiusPlattAuditTrace

set_option maxRecDepth 10000 in
/-- Generic schedule/receipt composition.  The explicit window-count equality
keeps closed configuration arithmetic out of the trace-algebra theorem. -/
theorem production_fold_viol_zero
    (c : Cfg) (k len : Nat) (seed : MobLiveSeed)
    (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hk : k ≤ 15)
    (hrootEnd : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hmainEnd : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62)
    (hcount : bootFuel + 1 + (laterFuel + 1) = c.rootCount)
    (hmainCount : mainFuel = c.segCount)
    (hz :
      let machineFuel := c.period * (c.rootCount + c.segCount)
      (readRes (squaredCombinedIndexedRun 0 c k machineFuel
        (combinedEntry c seed))).viol = 0) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let fuel := (rootFuel + mainFuel) * c.period
    (squaredResFold k
      (combinedSignals 0 c k fuel (combinedEntry c seed))
      (readRes (combinedEntry c seed))).viol = 0 := by
  have hfuel :
      (bootFuel + 1 + (laterFuel + 1) + mainFuel) * c.period =
        c.period * (c.rootCount + c.segCount) := by
    rw [hcount, hmainCount, Nat.mul_comm]
  have heq := readRes_squaredCombinedProductionSeed_eq_combinedSignals_fold
    c k len seed bootBound bootFuel laterFuel mainFuel delta h hk
    hrootEnd hmainPos hmainEnd
  dsimp only at heq hz ⊢
  rw [hfuel] at heq
  rw [heq] at hz
  rw [hfuel]
  exact hz

/-- Opening link as a transparent paper-faithful fold receipt. -/
theorem plattFirst_fold_viol_zero :
    let rootFuel := plattFirstBootFuel + 1 + (plattFirstLaterFuel + 1)
    let fuel := (rootFuel + plattFirstMainFuel) * plattAlignedFirst.period
    (squaredResFold mobWideBits
      (combinedSignals 0 plattAlignedFirst mobWideBits fuel
        (combinedEntry plattAlignedFirst plattFirstSeed))
      (readRes (combinedEntry plattAlignedFirst plattFirstSeed))).viol = 0 := by
  exact production_fold_viol_zero plattAlignedFirst mobWideBits 0
    plattFirstSeed plattBootBound plattFirstBootFuel plattFirstLaterFuel
    plattFirstMainFuel plattFirstDelta plattAlignedFirst_productionSchedule
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    plattFirst_readRes_viol_zero

/-- Tail link in the same transparent form. -/
theorem plattTail_fold_viol_zero :
    let rootFuel := plattTailBootFuel + 1 + (plattTailLaterFuel + 1)
    let fuel := (rootFuel + plattTailMainFuel) * plattAlignedTail.period
    (squaredResFold mobWideBits
      (combinedSignals 0 plattAlignedTail mobWideBits fuel
        (combinedEntry plattAlignedTail plattTailSeed))
      (readRes (combinedEntry plattAlignedTail plattTailSeed))).viol = 0 := by
  exact production_fold_viol_zero plattAlignedTail mobWideBits 0
    plattTailSeed plattBootBound plattTailBootFuel plattTailLaterFuel
    plattTailMainFuel plattTailDelta plattAlignedTail_productionSchedule
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    plattTail_readRes_viol_zero

end LeanCompCert.Ports.ArraySegMobiusPlattAuditFold
