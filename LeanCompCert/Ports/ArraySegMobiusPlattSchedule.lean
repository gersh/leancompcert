import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Ports.ArraySegMobiusPlattConfig

/-!
# Finite certificate boundary for the aligned Platt schedules

`ProductionCoreSchedule` deliberately exposes every range guard used by the
symbolic segmented-sieve proof.  For the two literal paper configurations,
almost all of those fields are elementary numeral arithmetic.

The historical schedule used a strict table-capacity premise on every root
candidate.  That premise is stronger than the machine needs and is false once
the last prime (`87887`) has filled the table: the remaining sixteen marked
candidates through `87903` perform no store.  `ScheduleFiniteEvidence` below
states the correct executable guard: the current table may be full, but an
actual append must have spare capacity.  The legacy adapter is retained under
an explicit name while the generic root-window proof is migrated to this
weaker, faithful contract.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattSchedule

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattConfig

set_option maxRecDepth 10000

/-- Capacity condition used by the executable root-table step. -/
def RoomForStep (c : Cfg) (ps : List Nat) (n : Nat) : Prop :=
  ps.length ≤ c.tableLen ∧
    (unmarkedBool ps n = true → ps.length < c.tableLen)

/-- Correct finite, data-dependent remainder of a production schedule. -/
structure ScheduleFiniteEvidence (c : Cfg)
    (bootBound bootFuel laterFuel : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  markBudget :
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps
  bootstrapFit : ∀ n, n < bootFuel → ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound (1 + n * c.segLen) k).length <
      c.tableLen
  crossingFit : ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound
      (crossingBase c bootFuel) k).length < c.tableLen
  laterFit : ∀ n, n < laterFuel → ∀ k, k < c.segLen →
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) n)
      (laterBase c bootFuel + n * c.segLen) k).length < c.tableLen
  finalRoom : ∀ k, k < c.segLen →
    let ps := rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel
    RoomForStep c
      (rootScanFrom ps (laterBase c bootFuel + laterFuel * c.segLen) k)
      (laterBase c bootFuel + laterFuel * c.segLen + k)
  finalLen : (finalRootTable c bootBound bootFuel laterFuel).length =
    c.tableLen

/-- Obsolete strict-capacity contract, retained only to instantiate the
current generic `ProductionCoreSchedule` during its migration.  It cannot be
the final paper certificate because the table is legitimately full for the
last sixteen composite candidates. -/
structure LegacyScheduleFiniteEvidence (c : Cfg)
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
  case finalPrefixFit =>
    have h := (e.finalRoom 0 (by
      simp [plattAlignedFirst]))
    simpa [RoomForStep, rootScanFrom_zero] using h.1
  case finalFit =>
    intro k hk
    simpa [RoomForStep] using e.finalRoom k hk
  case finalLen => exact e.finalLen
  all_goals
    simp [plattAlignedFirst, plattBootPrimes, plattBootBound,
      plattFirstBootFuel, plattFirstLaterFuel, plattFirstMainFuel,
      plattFirstDelta, Cfg.bootCount, Cfg.tableLen, Cfg.period,
      Cfg.rootSpan, Cfg.firstPrime, Cfg.rootLen, Cfg.arrayLen,
      Cfg.resultBase, Cfg.wDelta, crossingBase, laterBase, finalRootBound,
      mainBase, M] <;>
    omega

/-- Legacy opening adapter for strict certificates generated before the final
machine-room condition was made explicit. -/
theorem plattAlignedFirst_legacySchedule
    (e : LegacyScheduleFiniteEvidence plattAlignedFirst plattBootBound
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
  case finalPrefixFit => exact Nat.le_of_lt e.finalPrefixFit
  case finalFit =>
    intro k hk
    exact ⟨Nat.le_of_lt (e.finalFit k hk), fun _ => e.finalFit k hk⟩
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
  case finalPrefixFit =>
    have h := (e.finalRoom 0 (by
      simp [plattAlignedTail]))
    simpa [RoomForStep, rootScanFrom_zero] using h.1
  case finalFit =>
    intro k hk
    simpa [RoomForStep] using e.finalRoom k hk
  case finalLen => exact e.finalLen
  all_goals
    simp [plattAlignedTail, plattBootPrimes, plattBootBound,
      plattTailBootFuel, plattTailLaterFuel, plattTailMainFuel,
      plattTailDelta, Cfg.bootCount, Cfg.tableLen, Cfg.period,
      Cfg.rootSpan, Cfg.firstPrime, Cfg.rootLen, Cfg.arrayLen,
      Cfg.resultBase, Cfg.wDelta, crossingBase, laterBase, finalRootBound,
      mainBase, M] <;>
    omega

/-- Legacy tail adapter for strict certificates. -/
theorem plattAlignedTail_legacySchedule
    (e : LegacyScheduleFiniteEvidence plattAlignedTail plattBootBound
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
  case finalPrefixFit => exact Nat.le_of_lt e.finalPrefixFit
  case finalFit =>
    intro k hk
    exact ⟨Nat.le_of_lt (e.finalFit k hk), fun _ => e.finalFit k hk⟩
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
