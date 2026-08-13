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
open LeanCompCert.Ports.ArraySegMobiusIndexedRootWindows
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

/-- Finite side conditions for the common production shape in which the
entire root sieve occupies one mixed window and the unused suffix is rejected
by the compiled `rootCap` gate. -/
structure SingleMixedPaddedRootSchedule (c : Cfg)
    (bootBound valid delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  tableLenM : c.tableLen < M
  markPos : 0 < c.markSteps
  markM : c.markSteps < M
  periodM : c.period < M
  spanM : c.rootSpan < M
  firstPrimePos : 0 < c.firstPrime
  firstPrimeLeLen : c.firstPrime ≤ c.segLen
  firstPrimeLeBoot : c.firstPrime ≤ bootBound
  bootBoundM : bootBound < M
  bootBoundSqM : bootBound * bootBound < M
  segBootM : c.segLen + bootBound < M
  windowBaseM : 1 + c.segLen < M
  firstOffsetM : 1 + firstOffset 1 c.firstPrime < M
  arrayM : c.arrayLen < M
  markBudget :
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps
  bootTwo : 2 ≤ bootBound
  rootIndex : c.period = c.rootSpan
  bootStart : 1 - 1 ≤ bootBound
  bootLeCap : bootBound ≤ c.rootCap
  finalValid : 1 + valid - 1 = c.rootCap
  finalValidLt : valid < c.segLen
  finalCover : 1 + valid ≤ (bootBound + 1) * (bootBound + 1)
  bootFit : c.bootPrimes.length < c.tableLen
  finalFit : ∀ k, k < valid →
    let ps := rootScanMixed c.bootPrimes bootBound 1 k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + k) = true → ps.length < c.tableLen)
  finalCapFit :
    (rootScanMixed c.bootPrimes bootBound 1 valid).length ≤ c.tableLen
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete root-only production execution for one padded mixed window. -/
theorem indexedProductionRoot_single_mixed_padded_complete
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta) :
    let out := indexedWindowRun 0 c 1 (coreEntry c)
    let ps := rootScanMixed c.bootPrimes bootBound 1 valid
    RootTableInv c out ps c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rR = 0 ∧
      out.regs rW = (1 + ((c.segLen + delta) % M)) % M ∧
      out.regs rZero = 0 := by
  let entry := coreEntry c
  have hbootM : ∀ p, p ∈ c.bootPrimes → p < M := by
    intro p hp
    exact Nat.lt_of_le_of_lt (h.bootPrime.upper p hp) h.bootBoundM
  have hentry := coreEntry_complete c bootBound h.bootPrime h.bootLe
    hbootM h.arrayM
  obtain ⟨tail, hshape⟩ := h.bootShape
  have hbootPos : 0 < c.bootCount := by
    simp [Cfg.bootCount, hshape]
  have hwindow := indexedRootWindow_mixed_padded_transition c 0 entry tail
    bootBound 1 valid delta (by simpa [hshape] using hentry.table)
    (by simpa [hshape] using hentry.view) hentry.position hentry.base
    hentry.zero hentry.cleared (by simp [Cfg.bootCount, hshape])
    (by simpa using h.rootIndex) hbootPos h.bootLe h.tableLenM h.markPos h.markM h.periodM
    h.spanM h.firstPrimePos h.firstPrimeLeLen h.firstPrimeLeBoot
    h.bootBoundM h.bootBoundSqM h.segBootM h.windowBaseM h.firstOffsetM
    h.arrayM (by simpa [hshape] using h.markBudget) (by omega) h.bootTwo
    h.bootStart h.bootLeCap h.finalValid h.finalValidLt h.finalCover
    (by simpa [hshape] using h.bootFit)
    (by simpa [hshape] using h.finalFit)
    (by simpa [hshape] using h.finalCapFit) h.rootCapM h.deltaEq h.deltaM
  simpa only [indexedWindowRun, Nat.one_mul, hshape] using hwindow

/-- Finite side conditions for a sole historical root window whose final
cell is exactly `rootCap`. -/
structure SingleMixedCompleteRootSchedule (c : Cfg)
    (bootBound delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  tableLenM : c.tableLen < M
  markPos : 0 < c.markSteps
  markM : c.markSteps < M
  periodM : c.period < M
  spanM : c.rootSpan < M
  firstPrimePos : 0 < c.firstPrime
  firstPrimeLeLen : c.firstPrime ≤ c.segLen
  firstPrimeLeBoot : c.firstPrime ≤ bootBound
  bootBoundM : bootBound < M
  bootBoundSqM : bootBound * bootBound < M
  segBootM : c.segLen + bootBound < M
  windowBaseM : 1 + c.segLen < M
  firstOffsetM : 1 + firstOffset 1 c.firstPrime < M
  arrayM : c.arrayLen < M
  markBudget :
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps
  bootTwo : 2 ≤ bootBound
  rootIndex : c.period = c.rootSpan
  bootStart : 1 - 1 ≤ bootBound
  bootLtCap : bootBound < c.rootCap
  finalCap : 1 + c.segLen - 1 = c.rootCap
  finalCover : 1 + c.segLen < (bootBound + 1) * (bootBound + 1)
  bootFit : c.bootPrimes.length < c.tableLen
  finalFit : ∀ k, k < c.segLen →
    let ps := rootScanMixed c.bootPrimes bootBound 1 k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + k) = true → ps.length < c.tableLen)
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete root-only production execution for one exact mixed window. -/
theorem indexedProductionRoot_single_mixed_complete
    (c : Cfg) (bootBound delta : Nat)
    (h : SingleMixedCompleteRootSchedule c bootBound delta) :
    let out := indexedWindowRun 0 c 1 (coreEntry c)
    let ps := rootScanMixed c.bootPrimes bootBound 1 c.segLen
    RootTableInv c out ps c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rR = 0 ∧
      out.regs rW = (1 + ((c.segLen + delta) % M)) % M ∧
      out.regs rZero = 0 := by
  let entry := coreEntry c
  have hbootM : ∀ p, p ∈ c.bootPrimes → p < M := by
    intro p hp
    exact Nat.lt_of_le_of_lt (h.bootPrime.upper p hp) h.bootBoundM
  have hentry := coreEntry_complete c bootBound h.bootPrime h.bootLe
    hbootM h.arrayM
  obtain ⟨tail, hshape⟩ := h.bootShape
  have hbootPos : 0 < c.bootCount := by
    simp [Cfg.bootCount, hshape]
  have hwindow := indexedRootWindow_mixed_complete_transition c 0 entry tail
    bootBound 1 delta (by simpa [hshape] using hentry.table)
    (by simpa [hshape] using hentry.view) hentry.position hentry.base
    hentry.zero hentry.cleared (by simp [Cfg.bootCount, hshape])
    (by simpa using h.rootIndex) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.windowBaseM h.firstOffsetM h.arrayM
    (by simpa [hshape] using h.markBudget) (by omega) h.bootTwo h.bootStart
    (by rw [h.finalCap]; exact h.bootLtCap)
    (by rw [h.finalCap]; exact Nat.le_refl c.rootCap) h.finalCover
    (by simpa [hshape] using h.bootFit)
    (by simpa [hshape] using h.finalFit) h.rootCapM h.deltaEq h.deltaM
  simpa only [indexedWindowRun, Nat.one_mul, hshape, h.finalCap] using hwindow

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

/-- Root-only schedule for the general production case where the last
allocated segment is padded past `rootCap`.  `valid` is the exact number of
live candidates in that final segment. -/
structure PaddedProductionRootSchedule (c : Cfg)
    (bootBound bootFuel laterFuel valid delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  tableLenM : c.tableLen < M
  markPos : 0 < c.markSteps
  markM : c.markSteps < M
  periodM : c.period < M
  spanM : c.rootSpan < M
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
    1 + n * c.segLen + c.segLen < (bootBound + 1) * (bootBound + 1)
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
  finalValid : laterBase c bootFuel + laterFuel * c.segLen + valid - 1 =
    c.rootCap
  finalValidLt : valid < c.segLen
  finalCover : laterBase c bootFuel + laterFuel * c.segLen + valid <
    (bootBound + 1) * (bootBound + 1)
  finalPrefixFit :
    (rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel).length ≤ c.tableLen
  finalFit : ∀ k, k < valid →
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
  finalCapFit :
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) valid).length ≤
        c.tableLen
  finalLen :
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) valid).length = c.tableLen

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete root-only production execution for a padded final segment. -/
theorem indexedProductionRoot_padded_complete
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (h : PaddedProductionRootSchedule c bootBound bootFuel laterFuel valid delta) :
    let out := indexedWindowRun 0 c (bootFuel + 1 + (laterFuel + 1))
      (coreEntry c)
    let ps := rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) valid
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = mainBase c bootFuel laterFuel delta ∧
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
    h.bootstrapCap h.bootstrapCover (Nat.le_of_lt h.bootFit)
    (fun n hn k hk => ⟨Nat.le_of_lt (h.bootstrapFit n hn k hk),
      fun _ => h.bootstrapFit n hn k hk⟩) h.rootCapM
  let crossState := indexedWindowRun 0 c (bootFuel + 1) entry
  let crossed := crossingTable c bootBound bootFuel
  have hcross := indexedBootstrapWindows_mixed_complete c 0 entry
    c.bootPrimes bootBound 1 bootFuel hboots h.bootShape rfl
    (by simpa using h.crossingRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.crossingBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.crossingStartWithin h.crossingLast h.crossingCap h.crossingCover
    h.bootFit (fun k hk =>
      ⟨Nat.le_of_lt (h.crossingFit k hk), fun _ => h.crossingFit k hk⟩)
    h.rootCapM
  let idxCross := (bootFuel + 1) * c.period
  let laterW := laterBase c bootFuel
  have hlater := indexedWindowRun_later_root_complete_room c idxCross crossState
    c.bootPrimes crossed bootBound laterW laterFuel hcross.1 h.bootPrime
    hcross.2.1 hcross.2.2.2.2.2.2 hcross.2.2.2.1
    hcross.2.2.2.2.1 hcross.2.2.2.2.2.1 hcross.2.2.1 h.bootShape rfl
    h.laterRange hbootPos h.bootLe h.tableLenM h.markPos h.markM h.periodM
    h.spanM h.firstPrimePos h.firstPrimeLeLen h.firstPrimeLeBoot
    h.bootBoundM h.bootBoundSqM h.segBootM h.laterBaseM h.arrayM
    h.markBudget h.segLenPos h.bootTwo (by
      have hlt := h.crossingLast
      dsimp only [laterW, laterBase, crossingBase]
      dsimp only [crossingBase] at hlt
      omega) h.laterCap h.laterCover h.laterFit h.rootCapM
  have hfinal := indexedLaterWindows_final_padded_transition c idxCross
    crossState c.bootPrimes crossed bootBound laterW laterFuel valid delta
    hlater h.bootPrime h.bootShape rfl h.finalIndex hbootPos h.bootLe
    h.tableLenM h.markPos h.markM h.periodM h.spanM h.firstPrimePos
    h.firstPrimeLeLen h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM
    h.segBootM h.finalBaseM h.arrayM h.markBudget h.segLenPos h.bootTwo
    (by
      have hlt := h.crossingLast
      dsimp only [laterW, laterBase, crossingBase]
      dsimp only [crossingBase] at hlt
      omega) h.finalValid h.finalValidLt h.finalCover h.finalPrefixFit
    h.finalFit h.finalCapFit h.rootCapM h.deltaEq h.deltaM
  have hcompose : indexedWindowRun 0 c (bootFuel + 1 + (laterFuel + 1))
      entry = indexedWindowRun idxCross c (laterFuel + 1) crossState := by
    rw [indexedWindowRun_add]
    simpa only [idxCross, crossState, Nat.zero_add]
  rw [hcompose]
  refine ⟨hfinal.2.1, ?_, hfinal.2.2.1, ?_, hfinal.2.2.2.2⟩
  · simpa only [laterW, crossed, crossingTable] using
      hfinal.1.toMachineTableRep
  · simpa only [mainBase, laterW] using hfinal.2.2.2.1

/-- A padded final root window followed by the ordinary production main
windows.  Keeping the exact final prime table and bound in the schedule makes
the root-to-main splice independent of how many inert cells padded the last
root segment. -/
structure PaddedProductionCoreSchedule (c : Cfg)
    (bootBound bootFuel laterFuel valid mainFuel delta : Nat) : Prop
    extends PaddedProductionRootSchedule c bootBound bootFuel laterFuel valid
      delta where
  tableLenPos : 0 < c.tableLen
  spanPos : 0 < c.rootSpan
  finalPrime : PrimeTableInv
    (rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) valid)
    c.rootCap
  firstPrimeLeCap : c.firstPrime ≤ c.rootCap
  finalBoundSqM : c.rootCap * c.rootCap < M
  segFinalM : c.segLen + c.rootCap < M
  mainIndexM : c.rootSpan + mainFuel * c.period < M
  mainBaseM : mainBase c bootFuel laterFuel delta +
    mainFuel * c.segLen < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete production core for a root schedule whose final segment is
padded beyond `rootCap`. -/
theorem indexedPaddedProductionCore_complete
    (c : Cfg) (bootBound bootFuel laterFuel valid mainFuel delta : Nat)
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      mainFuel delta) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let out := indexedWindowRun 0 c (rootFuel + mainFuel) (coreEntry c)
    let ps := rootScanFrom
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) laterFuel)
      (laterBase c bootFuel + laterFuel * c.segLen) valid
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = mainBase c bootFuel laterFuel delta +
        mainFuel * c.segLen ∧
      out.regs rZero = 0 := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let rootOut := indexedWindowRun 0 c rootFuel (coreEntry c)
  let ps := rootScanFrom
    (rootLaterWindows c (crossingTable c bootBound bootFuel)
      (laterBase c bootFuel) laterFuel)
    (laterBase c bootFuel + laterFuel * c.segLen) valid
  have hroot := indexedProductionRoot_padded_complete c bootBound bootFuel
    laterFuel valid delta h.toPaddedProductionRootSchedule
  change
    (∀ j, j < c.segLen → machineCell c rootOut j = ⟨0, 0⟩) ∧
      MachineTableRep c rootOut ps ∧ rootOut.regs rR = 0 ∧
      rootOut.regs rW = mainBase c bootFuel laterFuel delta ∧
      rootOut.regs rZero = 0 at hroot
  have hrootIndex : rootFuel * c.period = c.rootSpan := by
    have hi := h.finalIndex
    dsimp only [rootFuel]
    simp only [Nat.add_mul, Nat.one_mul] at hi ⊢
    omega
  have hmain := indexedWindowRun_main_complete c c.rootSpan rootOut ps
    c.rootCap (mainBase c bootFuel laterFuel delta) mainFuel hroot.2.1
    h.finalPrime h.finalLen hroot.2.2.1 hroot.2.2.2.1
    hroot.2.2.2.2 hroot.1 (Nat.le_refl _) h.tableLenPos h.tableLenM
    h.markPos h.markM h.periodM h.mainIndexM h.spanM h.spanPos
    h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeCap h.rootCapM
    h.finalBoundSqM h.segFinalM h.mainBaseM h.arrayM
  have hcompose : indexedWindowRun 0 c (rootFuel + mainFuel) (coreEntry c) =
      indexedWindowRun c.rootSpan c mainFuel rootOut := by
    rw [indexedWindowRun_add]
    simpa only [rootOut, hrootIndex, Nat.zero_add]
  dsimp only
  rw [hcompose]
  exact hmain

/-- Schedule whose nonfinal root windows and final root window are all
covered by the fixed bootstrap table.  This is the genuine historical shape
of the tiny rows ending at `rootCap = bootBound`. -/
structure BootstrapFinalCoreSchedule (c : Cfg)
    (bootBound prefixFuel mainFuel delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  tableLen : c.bootPrimes.length = c.tableLen
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
  bootTwo : 2 ≤ bootBound
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M
  prefixRange : prefixFuel * c.period ≤ c.rootSpan - 1
  prefixBaseM : 1 + prefixFuel * c.segLen < M
  prefixLastTwo : ∀ n, n < prefixFuel →
    2 ≤ 1 + (n + 1) * c.segLen - 1
  prefixStartWithin : ∀ n, n < prefixFuel →
    1 + n * c.segLen - 1 ≤ bootBound
  prefixWithin : ∀ n, n < prefixFuel →
    1 + (n + 1) * c.segLen - 1 ≤ bootBound
  prefixCap : ∀ n, n < prefixFuel →
    1 + (n + 1) * c.segLen - 1 ≤ c.rootCap
  prefixCover : ∀ n, n < prefixFuel →
    1 + n * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1)
  prefixFit : ∀ n, n < prefixFuel → ∀ k, k < c.segLen →
    let ps := rootScanMixed c.bootPrimes bootBound
      (1 + n * c.segLen) k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + n * c.segLen + k) = true →
        ps.length < c.tableLen)
  finalIndex : (prefixFuel + 1) * c.period = c.rootSpan
  finalBaseM : 1 + prefixFuel * c.segLen + c.segLen < M
  finalLastTwo : 2 ≤ 1 + prefixFuel * c.segLen + c.segLen - 1
  finalWithin : 1 + prefixFuel * c.segLen + c.segLen - 1 ≤ bootBound
  finalCap : 1 + prefixFuel * c.segLen + c.segLen - 1 ≤ c.rootCap
  finalCover : 1 + prefixFuel * c.segLen + c.segLen <
    (bootBound + 1) * (bootBound + 1)
  finalFit : ∀ k, k < c.segLen →
    let ps := rootScanMixed c.bootPrimes bootBound
      (1 + prefixFuel * c.segLen) k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + prefixFuel * c.segLen + k) = true →
        ps.length < c.tableLen)
  transitionW :
    (1 + prefixFuel * c.segLen + ((c.segLen + delta) % M)) % M = c.lo
  mainIndexM : c.rootSpan + mainFuel * c.period < M
  mainBaseM : c.lo + mainFuel * c.segLen < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete core execution for a bootstrap-only historical root phase. -/
theorem indexedBootstrapFinalCore_complete
    (c : Cfg) (bootBound prefixFuel mainFuel delta : Nat)
    (h : BootstrapFinalCoreSchedule c bootBound prefixFuel mainFuel delta) :
    let rootFuel := prefixFuel + 1
    let out := indexedWindowRun 0 c (rootFuel + mainFuel) (coreEntry c)
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out c.bootPrimes ∧ out.regs rR = 0 ∧
      out.regs rW = c.lo + mainFuel * c.segLen ∧
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
  have hprefix := indexedWindowRun_bootstrap_complete c 0 entry
    c.bootPrimes bootBound 1 prefixFuel hentry.table hentry.view
    hentry.position hentry.base hentry.zero hentry.cleared h.bootShape rfl
    (by simpa using h.prefixRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.prefixBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.prefixLastTwo h.prefixStartWithin h.prefixWithin h.prefixCap
    h.prefixCover (Nat.le_of_eq h.tableLen) h.prefixFit h.rootCapM
  obtain ⟨tail, hshape⟩ := h.bootShape
  let beforeFinal := indexedWindowRun 0 c prefixFuel entry
  let finalW := 1 + prefixFuel * c.segLen
  have hfinal := indexedRootWindow_bootstrap_complete_transition c
    (prefixFuel * c.period) beforeFinal tail bootBound finalW delta
    (by simpa [beforeFinal, hshape] using hprefix.table)
    (by simpa [beforeFinal, hshape] using hprefix.view)
    (by simpa [beforeFinal] using hprefix.position)
    (by simpa [beforeFinal, finalW] using hprefix.base)
    (by simpa [beforeFinal] using hprefix.zero)
    (by simpa [beforeFinal] using hprefix.cleared)
    (by simpa [hshape] using (show c.bootPrimes.length = c.bootCount from rfl))
    (by simpa [Nat.add_mul] using h.finalIndex) hbootPos h.bootLe
    h.tableLenM h.markPos h.markM h.periodM
    h.spanM h.firstPrimePos h.firstPrimeLeLen h.firstPrimeLeBoot
    h.bootBoundM h.bootBoundSqM h.segBootM
    (by simpa [finalW, Nat.add_assoc] using h.finalBaseM)
    (by
      have hoff : firstOffset finalW c.firstPrime < c.firstPrime :=
        Nat.mod_lt _ h.firstPrimePos
      have hle : finalW + c.firstPrime ≤ finalW + c.segLen :=
        Nat.add_le_add_left h.firstPrimeLeLen finalW
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff finalW)
        (Nat.le_trans hle (Nat.le_of_lt (by
          simpa [finalW, Nat.add_assoc] using h.finalBaseM))))
    h.arrayM (by simpa [← hshape] using h.markBudget)
    (by dsimp [finalW]; omega) h.bootTwo
    (by have hh := h.finalWithin; dsimp only [finalW]; omega)
    (by simpa [finalW] using h.finalLastTwo)
    (by simpa [finalW] using h.finalWithin)
    (by simpa [finalW] using h.finalCap)
    (by simpa [finalW, Nat.add_assoc] using h.finalCover)
    (by simpa [← hshape] using (Nat.le_of_eq h.tableLen))
    (by simpa [← hshape, finalW] using h.finalFit) h.rootCapM
    h.deltaEq h.deltaM
  let rootOut := indexedWindowRun 0 c (prefixFuel + 1) entry
  have hroot :
      (∀ j, j < c.segLen → machineCell c rootOut j = ⟨0, 0⟩) ∧
      MachineTableRep c rootOut c.bootPrimes ∧ rootOut.regs rR = 0 ∧
      rootOut.regs rW = c.lo ∧ rootOut.regs rZero = 0 := by
    have hrootEq : rootOut =
        ArraySegMobiusIndexedRun.indexedBodyRun (prefixFuel * c.period) c
          c.period beforeFinal := by
      dsimp only [rootOut, beforeFinal]
      rw [indexedWindowRun_succ]
      simp only [Nat.zero_add]
    rw [hrootEq]
    have hf := hfinal
    rw [← hshape, h.transitionW] at hf
    exact ⟨hf.2.1, hf.1.toMachineTableRep, hf.2.2.1,
      hf.2.2.2.1, hf.2.2.2.2⟩
  have hmain := indexedWindowRun_main_complete c c.rootSpan rootOut
    c.bootPrimes bootBound c.lo mainFuel hroot.2.1 h.bootPrime h.tableLen
    hroot.2.2.1 hroot.2.2.2.1 hroot.2.2.2.2 hroot.1
    (Nat.le_refl _) h.tableLenPos h.tableLenM h.markPos h.markM h.periodM
    h.mainIndexM h.spanM h.spanPos h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM h.mainBaseM
    h.arrayM
  have hcompose : indexedWindowRun 0 c (prefixFuel + 1 + mainFuel) entry =
      indexedWindowRun c.rootSpan c mainFuel rootOut := by
    rw [indexedWindowRun_add]
    simpa only [rootOut, h.finalIndex, Nat.zero_add]
  dsimp only
  rw [hcompose]
  exact hmain

/-- Schedule with a bootstrap-only prefix and a final mixed window.  It
captures the historical `rootCap = 3`, `segLen = 1` rows where the first new
prime is discovered exactly at the root-to-main transition. -/
structure MixedFinalCoreSchedule (c : Cfg)
    (bootBound prefixFuel mainFuel delta : Nat) : Prop where
  bootPrime : PrimeTableInv c.bootPrimes bootBound
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  bootFit : c.bootPrimes.length < c.tableLen
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
  bootTwo : 2 ≤ bootBound
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M
  prefixRange : prefixFuel * c.period ≤ c.rootSpan - 1
  prefixBaseM : 1 + prefixFuel * c.segLen < M
  prefixLastTwo : ∀ n, n < prefixFuel →
    2 ≤ 1 + (n + 1) * c.segLen - 1
  prefixStartWithin : ∀ n, n < prefixFuel →
    1 + n * c.segLen - 1 ≤ bootBound
  prefixWithin : ∀ n, n < prefixFuel →
    1 + (n + 1) * c.segLen - 1 ≤ bootBound
  prefixCap : ∀ n, n < prefixFuel →
    1 + (n + 1) * c.segLen - 1 ≤ c.rootCap
  prefixCover : ∀ n, n < prefixFuel →
    1 + n * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1)
  prefixFit : ∀ n, n < prefixFuel → ∀ k, k < c.segLen →
    let ps := rootScanMixed c.bootPrimes bootBound
      (1 + n * c.segLen) k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + n * c.segLen + k) = true →
        ps.length < c.tableLen)
  finalIndex : (prefixFuel + 1) * c.period = c.rootSpan
  finalBaseM : 1 + prefixFuel * c.segLen + c.segLen < M
  finalStartWithin : 1 + prefixFuel * c.segLen - 1 ≤ bootBound
  finalBeyond : bootBound < 1 + prefixFuel * c.segLen + c.segLen - 1
  finalCap : 1 + prefixFuel * c.segLen + c.segLen - 1 ≤ c.rootCap
  finalCover : 1 + prefixFuel * c.segLen + c.segLen <
    (bootBound + 1) * (bootBound + 1)
  finalRoom : ∀ k, k < c.segLen →
    let ps := rootScanMixed c.bootPrimes bootBound
      (1 + prefixFuel * c.segLen) k
    ps.length ≤ c.tableLen ∧
      (unmarkedBool ps (1 + prefixFuel * c.segLen + k) = true →
        ps.length < c.tableLen)
  finalPrime : PrimeTableInv
    (rootScanMixed c.bootPrimes bootBound
      (1 + prefixFuel * c.segLen) c.segLen) c.rootCap
  finalLen :
    (rootScanMixed c.bootPrimes bootBound
      (1 + prefixFuel * c.segLen) c.segLen).length = c.tableLen
  firstPrimeLeCap : c.firstPrime ≤ c.rootCap
  finalBoundSqM : c.rootCap * c.rootCap < M
  segFinalM : c.segLen + c.rootCap < M
  transitionW :
    (1 + prefixFuel * c.segLen + ((c.segLen + delta) % M)) % M = c.lo
  mainIndexM : c.rootSpan + mainFuel * c.period < M
  mainBaseM : c.lo + mainFuel * c.segLen < M

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Complete core execution for a bootstrap prefix followed by one final
mixed root window. -/
theorem indexedMixedFinalCore_complete
    (c : Cfg) (bootBound prefixFuel mainFuel delta : Nat)
    (h : MixedFinalCoreSchedule c bootBound prefixFuel mainFuel delta) :
    let rootFuel := prefixFuel + 1
    let out := indexedWindowRun 0 c (rootFuel + mainFuel) (coreEntry c)
    let ps := rootScanMixed c.bootPrimes bootBound
      (1 + prefixFuel * c.segLen) c.segLen
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = c.lo + mainFuel * c.segLen ∧
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
  have hprefix := indexedWindowRun_bootstrap_complete c 0 entry
    c.bootPrimes bootBound 1 prefixFuel hentry.table hentry.view
    hentry.position hentry.base hentry.zero hentry.cleared h.bootShape rfl
    (by simpa using h.prefixRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.prefixBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.prefixLastTwo h.prefixStartWithin h.prefixWithin h.prefixCap
    h.prefixCover (Nat.le_of_lt h.bootFit) h.prefixFit h.rootCapM
  obtain ⟨tail, hshape⟩ := h.bootShape
  let beforeFinal := indexedWindowRun 0 c prefixFuel entry
  let finalW := 1 + prefixFuel * c.segLen
  have hfinal := indexedRootWindow_mixed_complete_transition c
    (prefixFuel * c.period) beforeFinal tail bootBound finalW delta
    (by simpa [beforeFinal, hshape] using hprefix.table)
    (by simpa [beforeFinal, hshape] using hprefix.view)
    (by simpa [beforeFinal] using hprefix.position)
    (by simpa [beforeFinal, finalW] using hprefix.base)
    (by simpa [beforeFinal] using hprefix.zero)
    (by simpa [beforeFinal] using hprefix.cleared)
    (by simpa [hshape] using (show c.bootPrimes.length = c.bootCount from rfl))
    (by simpa [Nat.add_mul] using h.finalIndex) hbootPos h.bootLe
    h.tableLenM h.markPos h.markM h.periodM h.spanM h.firstPrimePos
    h.firstPrimeLeLen h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM
    h.segBootM (by simpa [finalW, Nat.add_assoc] using h.finalBaseM)
    (by
      have hoff : firstOffset finalW c.firstPrime < c.firstPrime :=
        Nat.mod_lt _ h.firstPrimePos
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff finalW)
        (Nat.le_trans (Nat.add_le_add_left h.firstPrimeLeLen finalW)
          (Nat.le_of_lt (by
            simpa [finalW, Nat.add_assoc] using h.finalBaseM))))
    h.arrayM (by simpa [← hshape] using h.markBudget)
    (by dsimp [finalW]; omega) h.bootTwo
    (by simpa [finalW] using h.finalStartWithin)
    (by simpa [finalW] using h.finalBeyond)
    (by simpa [finalW] using h.finalCap)
    (by simpa [finalW, Nat.add_assoc] using h.finalCover)
    (by simpa [← hshape] using h.bootFit)
    (by simpa [← hshape, finalW] using h.finalRoom) h.rootCapM
    h.deltaEq h.deltaM
  let ps := rootScanMixed c.bootPrimes bootBound finalW c.segLen
  let rootOut := indexedWindowRun 0 c (prefixFuel + 1) entry
  have hroot :
      (∀ j, j < c.segLen → machineCell c rootOut j = ⟨0, 0⟩) ∧
      MachineTableRep c rootOut ps ∧ rootOut.regs rR = 0 ∧
      rootOut.regs rW = c.lo ∧ rootOut.regs rZero = 0 := by
    have hrootEq : rootOut =
        ArraySegMobiusIndexedRun.indexedBodyRun (prefixFuel * c.period) c
          c.period beforeFinal := by
      dsimp only [rootOut, beforeFinal]
      rw [indexedWindowRun_succ]
      simp only [Nat.zero_add]
    rw [hrootEq]
    have hf := hfinal
    rw [← hshape, h.transitionW] at hf
    exact ⟨hf.2.1, hf.1.toMachineTableRep, hf.2.2.1,
      hf.2.2.2.1, hf.2.2.2.2⟩
  have hmain := indexedWindowRun_main_complete c c.rootSpan rootOut ps
    c.rootCap c.lo mainFuel hroot.2.1 (by simpa [ps, finalW] using h.finalPrime)
    (by simpa [ps, finalW] using h.finalLen) hroot.2.2.1
    hroot.2.2.2.1 hroot.2.2.2.2 hroot.1 (Nat.le_refl _)
    h.tableLenPos h.tableLenM h.markPos h.markM h.periodM h.mainIndexM
    h.spanM h.spanPos h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeCap h.rootCapM h.finalBoundSqM h.segFinalM h.mainBaseM
    h.arrayM
  have hcompose : indexedWindowRun 0 c (prefixFuel + 1 + mainFuel) entry =
      indexedWindowRun c.rootSpan c mainFuel rootOut := by
    rw [indexedWindowRun_add]
    simpa only [rootOut, h.finalIndex, Nat.zero_add]
  dsimp only
  rw [hcompose]
  exact hmain

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
    h.bootstrapCap h.bootstrapCover (Nat.le_of_lt h.bootFit)
    (fun n hn k hk => ⟨Nat.le_of_lt (h.bootstrapFit n hn k hk),
      fun _ => h.bootstrapFit n hn k hk⟩) h.rootCapM
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
    h.bootFit (fun k hk =>
      ⟨Nat.le_of_lt (h.crossingFit k hk), fun _ => h.crossingFit k hk⟩)
    h.rootCapM
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
