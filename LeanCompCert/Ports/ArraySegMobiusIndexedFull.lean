import LeanCompCert.Ports.ArraySegMobiusIndexedProgram

/-! # Complete production-indexed segmented-sieve core -/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedFull

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram

def crossingBase (c : Cfg) (bootFuel : Nat) : Nat :=
  1 + bootFuel * c.segLen

def crossingTable (c : Cfg) (bootBound bootFuel : Nat) : List Nat :=
  rootScanMixed c.bootPrimes bootBound (crossingBase c bootFuel) c.segLen

def laterBase (c : Cfg) (bootFuel : Nat) : Nat :=
  crossingBase c bootFuel + c.segLen

def finalRootTable (c : Cfg) (bootBound bootFuel laterFuel : Nat) :
    List Nat :=
  rootScanFrom
    (rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel)
    (laterBase c bootFuel + laterFuel * c.segLen) c.segLen

def finalRootBound (c : Cfg) (bootFuel laterFuel : Nat) : Nat :=
  laterBase c bootFuel + laterFuel * c.segLen + c.segLen - 1

/-- Consecutive later root windows retain every existing prime-table prefix. -/
theorem rootLaterWindows_has_prefix (c : Cfg) {boot full : List Nat}
    (hfull : ∃ tail, full = boot ++ tail) (w fuel : Nat) :
    ∃ tail, rootLaterWindows c full w fuel = boot ++ tail := by
  induction fuel with
  | zero => simpa using hfull
  | succ n ih =>
      rw [rootLaterWindows_succ]
      exact rootScanFrom_has_prefix ih _ _

/-- The complete production root table retains the configured bootstrap
prime list as a literal prefix. -/
theorem finalRootTable_has_boot_prefix (c : Cfg)
    (bootBound bootFuel laterFuel : Nat) :
    ∃ tail, finalRootTable c bootBound bootFuel laterFuel =
      c.bootPrimes ++ tail := by
  have hcross := rootScanMixed_has_prefix c.bootPrimes bootBound
    (crossingBase c bootFuel) c.segLen
  have hlater := rootLaterWindows_has_prefix c hcross
    (laterBase c bootFuel) laterFuel
  unfold finalRootTable
  exact rootScanFrom_has_prefix hlater _ _

/-- Hence a bootstrap table beginning with `firstPrime` gives the
source-shaped final table required by Mathlib-facing consumers. -/
theorem finalRootTable_shape (c : Cfg) (bootBound bootFuel laterFuel : Nat)
    (hboot : ∃ tail, c.bootPrimes = c.firstPrime :: tail) :
    ∃ tail, finalRootTable c bootBound bootFuel laterFuel =
      c.firstPrime :: tail := by
  obtain ⟨bootTail, hboot⟩ := hboot
  obtain ⟨tail, hfinal⟩ :=
    finalRootTable_has_boot_prefix c bootBound bootFuel laterFuel
  refine ⟨bootTail ++ tail, ?_⟩
  rw [hfinal, hboot]
  rfl

def mainBase (c : Cfg) (bootFuel laterFuel delta : Nat) : Nat :=
  ((laterBase c bootFuel + laterFuel * c.segLen) +
    ((c.segLen + delta) % M)) % M

/-- Finite schedule facts needed to instantiate the symbolic outer proof.
Every list-length and range field is decidable and can be discharged by a
LeanCompCert side-condition program for a concrete campaign. -/
structure ProductionCoreSchedule (c : Cfg)
    (bootBound bootFuel laterFuel mainFuel delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  tableLenPos : 0 < c.tableLen
  tableLenM : c.tableLen < M
  markPos : 0 < c.markSteps
  markM : c.markSteps < M
  periodM : c.period < M
  spanM : c.rootSpan < M
  spanPos : 0 < c.rootSpan
  firstPrimePos : 0 < c.firstPrime
  firstPrimeLeLen : c.firstPrime ≤ c.segLen
  firstPrimeLeBoot : c.firstPrime ≤ bootBound
  bootBoundM : bootBound < M
  bootBoundSqM : bootBound * bootBound < M
  segBootM : c.segLen + bootBound < M
  arrayM : c.arrayLen < M
  markBudget :
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps
  segLenPos : 0 < c.segLen
  bootTwo : 2 ≤ bootBound
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M

  bootstrapRange : bootFuel * c.period ≤ c.rootSpan - 1
  bootstrapBaseM : 1 + bootFuel * c.segLen < M
  bootstrapLastTwo : ∀ n, n < bootFuel →
    2 ≤ 1 + (n + 1) * c.segLen - 1
  bootstrapStartWithin : ∀ n, n < bootFuel →
    1 + n * c.segLen - 1 ≤ bootBound
  bootstrapWithin : ∀ n, n < bootFuel →
    1 + (n + 1) * c.segLen - 1 ≤ bootBound
  bootstrapCap : ∀ n, n < bootFuel →
    1 + (n + 1) * c.segLen - 1 ≤ c.rootCap
  bootstrapCover : ∀ n, n < bootFuel →
    1 + n * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1)
  bootFit : c.bootPrimes.length < c.tableLen
  bootstrapFit : ∀ n, n < bootFuel → ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound (1 + n * c.segLen) k).length <
      c.tableLen

  crossingRange : bootFuel * c.period + c.period ≤ c.rootSpan - 1
  crossingBaseM : crossingBase c bootFuel + c.segLen < M
  crossingStartWithin : crossingBase c bootFuel - 1 ≤ bootBound
  crossingLast : bootBound < crossingBase c bootFuel + c.segLen - 1
  crossingCap : crossingBase c bootFuel + c.segLen - 1 ≤ c.rootCap
  crossingCover : crossingBase c bootFuel + c.segLen <
    (bootBound + 1) * (bootBound + 1)
  crossingFit : ∀ k, k < c.segLen →
    (rootScanMixed c.bootPrimes bootBound (crossingBase c bootFuel) k).length <
      c.tableLen

  laterRange : (bootFuel + 1) * c.period + laterFuel * c.period ≤
    c.rootSpan - 1
  laterBaseM : laterBase c bootFuel + laterFuel * c.segLen < M
  laterCap : ∀ n, n < laterFuel →
    laterBase c bootFuel + (n + 1) * c.segLen - 1 ≤ c.rootCap
  laterCover : ∀ n, n < laterFuel →
    laterBase c bootFuel + n * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1)
  laterFit : ∀ n, n < laterFuel → ∀ k, k < c.segLen →
    let ps := rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) n
    (rootScanFrom ps (laterBase c bootFuel + n * c.segLen) k).length ≤
        c.tableLen ∧
      (unmarkedBool
          (rootScanFrom ps (laterBase c bootFuel + n * c.segLen) k)
          (laterBase c bootFuel + n * c.segLen + k) = true →
        (rootScanFrom ps
          (laterBase c bootFuel + n * c.segLen) k).length < c.tableLen)

  finalIndex : (bootFuel + 1) * c.period + laterFuel * c.period +
    c.period = c.rootSpan
  finalBaseM : laterBase c bootFuel + laterFuel * c.segLen + c.segLen < M
  finalCap : laterBase c bootFuel + (laterFuel + 1) * c.segLen - 1 ≤
    c.rootCap
  finalCover : laterBase c bootFuel + laterFuel * c.segLen + c.segLen <
    (bootBound + 1) * (bootBound + 1)
  finalPrefixFit :
    (rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel).length ≤ c.tableLen
  finalFit : ∀ k, k < c.segLen →
    let ps := rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel
    (rootScanFrom ps
      (laterBase c bootFuel + laterFuel * c.segLen) k).length ≤ c.tableLen ∧
      (unmarkedBool
          (rootScanFrom ps
            (laterBase c bootFuel + laterFuel * c.segLen) k)
          (laterBase c bootFuel + laterFuel * c.segLen + k) = true →
        (rootScanFrom ps
          (laterBase c bootFuel + laterFuel * c.segLen) k).length <
            c.tableLen)
  finalLen : (finalRootTable c bootBound bootFuel laterFuel).length =
    c.tableLen
  finalBoundSqM :
    finalRootBound c bootFuel laterFuel *
      finalRootBound c bootFuel laterFuel < M
  segFinalM : c.segLen + finalRootBound c bootFuel laterFuel < M
  mainIndexM : c.rootSpan + mainFuel * c.period < M
  mainBaseM : mainBase c bootFuel laterFuel delta +
    mainFuel * c.segLen < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete execution of the production sieve core, from its compiled
initializer through every root and main window at the actual global indices. -/
theorem indexedProductionCore_complete
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta) :
    let out := indexedWindowRun 0 c
      (bootFuel + 1 + (laterFuel + 1 + mainFuel)) (coreEntry c)
    let ps := finalRootTable c bootBound bootFuel laterFuel
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = mainBase c bootFuel laterFuel delta +
        mainFuel * c.segLen ∧
      out.regs rZero = 0 := by
  let entry := coreEntry c
  have hbootM : ∀ p, p ∈ c.bootPrimes → p < M := by
    intro p hp
    exact Nat.lt_of_le_of_lt (h.bootPrime.upper p hp) h.bootBoundM
  have hentry := coreEntry_complete c bootBound h.bootPrime h.bootLe
    hbootM h.arrayM
  have hbootPos : 0 < c.bootCount := by
    obtain ⟨tail, hshape⟩ := h.bootShape
    simp [Cfg.bootCount, hshape]
  have hboots := indexedWindowRun_bootstrap_complete c 0 entry
    c.bootPrimes bootBound 1 bootFuel hentry.table hentry.view
    hentry.position hentry.base hentry.zero hentry.cleared h.bootShape rfl
    (by simpa using h.bootstrapRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.bootstrapBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.bootstrapLastTwo h.bootstrapStartWithin h.bootstrapWithin
    h.bootstrapCap h.bootstrapCover h.bootFit h.bootstrapFit h.rootCapM
  let crossState := indexedWindowRun 0 c (bootFuel + 1) entry
  let crossW := crossingBase c bootFuel
  let crossed := crossingTable c bootBound bootFuel
  have hcross := indexedBootstrapWindows_mixed_complete c 0 entry
    c.bootPrimes bootBound 1 bootFuel hboots h.bootShape rfl
    (by simpa using h.crossingRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.crossingBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.crossingStartWithin h.crossingLast h.crossingCap h.crossingCover
    h.bootFit h.crossingFit h.rootCapM
  let idxCross := (bootFuel + 1) * c.period
  let laterW := laterBase c bootFuel
  have hlater := indexedWindowRun_later_root_complete_room c idxCross crossState
    c.bootPrimes crossed bootBound laterW laterFuel hcross.1
    h.bootPrime hcross.2.1 hcross.2.2.2.2.2.2 hcross.2.2.2.1
    hcross.2.2.2.2.1 hcross.2.2.2.2.2.1 hcross.2.2.1 h.bootShape
    rfl h.laterRange hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.laterBaseM h.arrayM h.markBudget h.segLenPos h.bootTwo (by
      have hlt := h.crossingLast
      dsimp only [laterW, laterBase, crossingBase]
      dsimp only [crossingBase] at hlt
      omega) h.laterCap h.laterCover h.laterFit h.rootCapM
  have hsuffix := indexedLaterWindows_then_main_complete_room c idxCross
    crossState c.bootPrimes crossed bootBound laterW laterFuel delta mainFuel
    hlater h.bootPrime h.bootShape rfl h.finalIndex hbootPos
    h.bootLe h.tableLenPos h.tableLenM h.markPos h.markM h.periodM h.spanM
    h.spanPos h.firstPrimePos h.firstPrimeLeLen h.firstPrimeLeBoot
    h.bootBoundM h.bootBoundSqM h.segBootM h.finalBaseM h.arrayM
    h.markBudget h.segLenPos h.bootTwo (by
      have hlt := h.crossingLast
      dsimp only [laterW, laterBase, crossingBase]
      dsimp only [crossingBase] at hlt
      omega) h.finalCap h.finalCover h.finalPrefixFit h.finalFit h.rootCapM
    h.deltaEq h.deltaM h.finalLen h.finalBoundSqM h.segFinalM h.mainIndexM
    h.mainBaseM
  have hcompose : indexedWindowRun 0 c
      (bootFuel + 1 + (laterFuel + 1 + mainFuel)) entry =
      indexedWindowRun idxCross c (laterFuel + 1 + mainFuel) crossState := by
    rw [indexedWindowRun_add]
    simpa only [idxCross, crossState, Nat.zero_add]
  rw [hcompose]
  simpa [finalRootTable, finalRootBound, mainBase, laterW, laterBase,
    crossW, crossingBase, crossed, crossingTable] using hsuffix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The production schedule stopped exactly at the root-to-main boundary.
This reuses the complete schedule proof with a zero-length main suffix. -/
theorem indexedProductionRoot_complete
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let out := indexedWindowRun 0 c rootFuel (coreEntry c)
    let ps := finalRootTable c bootBound bootFuel laterFuel
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = mainBase c bootFuel laterFuel delta ∧
      out.regs rZero = 0 := by
  let hroot : ProductionCoreSchedule c bootBound bootFuel laterFuel 0 delta :=
    { h with
      mainIndexM := by
        have hm := h.mainIndexM
        simp only [Nat.zero_mul, Nat.add_zero]
        omega
      mainBaseM := by
        have hm := h.mainBaseM
        simp only [Nat.zero_mul, Nat.add_zero]
        omega }
  have hcomplete := indexedProductionCore_complete c bootBound bootFuel
    laterFuel 0 delta hroot
  simpa only [Nat.add_zero, Nat.zero_mul] using hcomplete

end LeanCompCert.Ports.ArraySegMobiusIndexedFull
