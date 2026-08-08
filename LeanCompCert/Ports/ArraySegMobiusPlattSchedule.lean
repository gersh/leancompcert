import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Ports.ArraySegMobiusPlattConfig

/-!
# Finite certificate boundary for the aligned Platt schedules

`ProductionCoreSchedule` deliberately exposes every range guard used by the
symbolic segmented-sieve proof.  For the two literal paper configurations,
almost all of those fields are elementary numeral arithmetic.  This module
isolates the genuinely computational fields (prime-table construction and
finite list capacities) so a small LeanCompCert checker can supply exactly
those fields without asking the kernel to normalize the large root scan.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattSchedule

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattConfig

set_option maxRecDepth 10000

/-- The finite, data-dependent remainder of a production schedule. -/
structure ScheduleFiniteEvidence (c : Cfg)
    (bootBound bootFuel laterFuel : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  markBudget :
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps
  bootstrapFit : ∀ n, n < bootFuel → ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound (1 + n * c.segLen) k).length <
      c.tableLen
  crossingFit : ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound (crossingBase c bootFuel) k).length <
      c.tableLen
  laterFit : ∀ n, n < laterFuel → ∀ k, k < c.segLen →
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) n)
      (laterBase c bootFuel + n * c.segLen) k).length < c.tableLen
  finalPrefixFit :
    (rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel).length < c.tableLen
  finalFit : ∀ k, k < c.segLen →
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) k).length < c.tableLen
  finalLen : (finalRootTable c bootBound bootFuel laterFuel).length =
    c.tableLen

/-- All non-computational fields of the opening schedule reduce to arithmetic
once its finite evidence has been supplied. -/
theorem plattAlignedFirst_schedule
    (e : ScheduleFiniteEvidence plattAlignedFirst plattBootBound
      plattFirstBootFuel plattFirstLaterFuel) :
    ProductionCoreSchedule plattAlignedFirst plattBootBound
      plattFirstBootFuel plattFirstLaterFuel plattFirstMainFuel
      plattFirstDelta := by
  constructor
  case bootPrime => exact e.bootPrime
  case markBudget => exact e.markBudget
  case bootstrapFit => exact e.bootstrapFit
  case crossingFit => exact e.crossingFit
  case laterFit => exact e.laterFit
  case finalPrefixFit => exact e.finalPrefixFit
  case finalFit => exact e.finalFit
  case finalLen => exact e.finalLen
  all_goals
    simp [plattAlignedFirst, plattBootPrimes, plattBootBound,
      plattFirstBootFuel, plattFirstLaterFuel, plattFirstMainFuel,
      plattFirstDelta, Cfg.bootCount, Cfg.tableLen, Cfg.period,
      Cfg.rootSpan, Cfg.firstPrime, Cfg.rootLen, Cfg.arrayLen,
      Cfg.resultBase, Cfg.wDelta, crossingBase, laterBase, finalRootBound,
      mainBase, M] <;>
    omega

/-- All non-computational fields of the tail schedule likewise reduce to
arithmetic; the long sequence of three-cell root windows remains behind the
finite compiled-evidence boundary. -/
theorem plattAlignedTail_schedule
    (e : ScheduleFiniteEvidence plattAlignedTail plattBootBound
      plattTailBootFuel plattTailLaterFuel) :
    ProductionCoreSchedule plattAlignedTail plattBootBound
      plattTailBootFuel plattTailLaterFuel plattTailMainFuel
      plattTailDelta := by
  constructor
  case bootPrime => exact e.bootPrime
  case markBudget => exact e.markBudget
  case bootstrapFit => exact e.bootstrapFit
  case crossingFit => exact e.crossingFit
  case laterFit => exact e.laterFit
  case finalPrefixFit => exact e.finalPrefixFit
  case finalFit => exact e.finalFit
  case finalLen => exact e.finalLen
  all_goals
    simp [plattAlignedTail, plattBootPrimes, plattBootBound,
      plattTailBootFuel, plattTailLaterFuel, plattTailMainFuel,
      plattTailDelta, Cfg.bootCount, Cfg.tableLen, Cfg.period,
      Cfg.rootSpan, Cfg.firstPrime, Cfg.rootLen, Cfg.arrayLen,
      Cfg.resultBase, Cfg.wDelta, crossingBase, laterBase, finalRootBound,
      mainBase, M] <;>
    omega

end LeanCompCert.Ports.ArraySegMobiusPlattSchedule
