import LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
import LeanCompCert.Ports.ArraySegMobiusIndexedFull

/-!
# Canonical symbolic root schedules

The production schedule structures contain many prefix-capacity fields.  They
are consequences of two exact prime-table invariants, not independent finite
computations.  This module proves that consequence for both the one-root and
padded multi-root geometries.  A campaign manifest is therefore responsible
only for scalar word/range facts and for signed count/budget observations.

No prime table or production interval is evaluated here.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanCompCert.Ports.ArraySegCanonicalSchedules

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence

/-- Exact prime tables are monotone in their bound at the level of length. -/
theorem primeTable_length_le_of_le {ps full : List Nat} {bound cap : Nat}
    (hps : PrimeTableInv ps bound) (hfull : PrimeTableInv full cap)
    (hbc : bound ≤ cap) : ps.length ≤ full.length := by
  rw [primeTable_length_eq_primeCount hps,
    primeTable_length_eq_primeCount hfull]
  exact (List.range_sublist.mpr (by omega)).countP_le

/-- A mixed root prefix fits an independently proved complete final table.
The already-covered branch uses strict bootstrap room directly, including
candidate `1`; the extending branch uses exact prime-table monotonicity. -/
theorem roomForStep_rootScanMixed_of_final
    {c : Cfg} {boot full : List Nat} {bootBound w k cap : Nat}
    (hboot : PrimeTableInv boot bootBound)
    (hfull : PrimeTableInv full cap)
    (htable : full.length = c.tableLen)
    (hbootLen : boot.length ≤ c.tableLen)
    (hbootStrict : boot.length < c.tableLen)
    (hw : w - 1 ≤ bootBound) (hwPos : 0 < w)
    (hbootTwo : 2 ≤ bootBound) (hnCap : w + k ≤ cap) :
    RoomForStep c (rootScanMixed boot bootBound w k) (w + k) := by
  by_cases hcovered : w + k ≤ bootBound
  · have hscan : rootScanMixed boot bootBound w k = boot :=
      rootScanMixed_eq_boot_of_le boot bootBound w k (by omega)
    rw [hscan]
    exact ⟨hbootLen, fun _ => hbootStrict⟩
  · have hprefix := rootScanMixed_primeTable (fuel := k) hboot hw hwPos
      hbootTwo
    have hmax : max bootBound (w + k - 1) = w + k - 1 := by omega
    rw [hmax] at hprefix
    exact roomForStep_of_finalPrimeTable (c := c) (full := full)
      (cap := cap) htable.symm hprefix hfull (by omega) (by omega) hnCap

/-- The corresponding capacity fact for a sequential root prefix. -/
theorem roomForStep_rootScanFrom_of_final
    {c : Cfg} {ps full : List Nat} {bound w k cap : Nat}
    (hprefix : PrimeTableInv ps bound) (hw : w = bound + 1)
    (hwTwo : 2 ≤ w) (hfull : PrimeTableInv full cap)
    (htable : full.length = c.tableLen) (hnCap : w + k ≤ cap) :
    RoomForStep c (rootScanFrom ps w k) (w + k) := by
  have hscan := rootScanFrom_primeTable (fuel := k) hprefix hw hwTwo
  exact roomForStep_of_finalPrimeTable (c := c) (full := full) (cap := cap)
    htable.symm hscan hfull (by omega) (by omega) hnCap

/-! ## One-root schedules -/

/-- Scalar, list-free part of a one-root production schedule. -/
structure SingleArithmetic (c : Cfg) (bootBound valid delta : Nat) : Prop where
  bootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail
  bootLe : c.bootCount ≤ c.tableLen
  bootFit : c.bootPrimes.length < c.tableLen
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
  rootCapM : c.rootCap < M
  deltaEq : c.wDelta = delta
  deltaM : delta < M

/-- Prime-table invariants discharge every data-dependent capacity field in
the one-root schedule. -/
theorem singleSchedule_of_primeTables
    (c : Cfg) (bootBound valid delta : Nat)
    (a : SingleArithmetic c bootBound valid delta)
    (hboot : PrimeTableInv c.bootPrimes bootBound)
    (full : List Nat) (hfull : PrimeTableInv full c.rootCap)
    (hfullLen : full.length = c.tableLen) :
    SingleMixedPaddedRootSchedule c bootBound valid delta := by
  have hfinal0 := rootScanMixed_primeTable (fuel := valid) hboot
    (w := 1) a.bootStart (by omega) a.bootTwo
  have hmax : max bootBound (1 + valid - 1) = c.rootCap := by
    rw [a.finalValid]
    exact Nat.max_eq_right a.bootLeCap
  have hfinal : PrimeTableInv
      (rootScanMixed c.bootPrimes bootBound 1 valid) c.rootCap := by
    simpa only [hmax] using hfinal0
  have hfinalEq : rootScanMixed c.bootPrimes bootBound 1 valid = full :=
    PrimeTableInv.eq hfinal hfull
  refine {
    bootPrime := hboot
    bootShape := a.bootShape
    bootLe := a.bootLe
    tableLenM := a.tableLenM
    markPos := a.markPos
    markM := a.markM
    periodM := a.periodM
    spanM := a.spanM
    firstPrimePos := a.firstPrimePos
    firstPrimeLeLen := a.firstPrimeLeLen
    firstPrimeLeBoot := a.firstPrimeLeBoot
    bootBoundM := a.bootBoundM
    bootBoundSqM := a.bootBoundSqM
    segBootM := a.segBootM
    windowBaseM := a.windowBaseM
    firstOffsetM := a.firstOffsetM
    arrayM := a.arrayM
    markBudget := a.markBudget
    bootTwo := a.bootTwo
    rootIndex := a.rootIndex
    bootStart := a.bootStart
    bootLeCap := a.bootLeCap
    finalValid := a.finalValid
    finalValidLt := a.finalValidLt
    finalCover := a.finalCover
    bootFit := a.bootFit
    finalFit := by
      intro k hk
      exact roomForStep_rootScanMixed_of_final hboot hfull hfullLen
        (Nat.le_of_lt a.bootFit) a.bootFit a.bootStart (by omega) a.bootTwo
        (by omega)
    finalCapFit := by
      rw [hfinalEq, hfullLen]
      exact Nat.le_refl _
    rootCapM := a.rootCapM
    deltaEq := a.deltaEq
    deltaM := a.deltaM }

/-! ## Padded multi-root schedules -/

/-- Scalar, list-free part of a padded multi-root production schedule. -/
structure MultiArithmetic (c : Cfg)
    (bootBound bootFuel laterFuel valid mainFuel delta : Nat) : Prop where
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
  crossingRange : bootFuel * c.period + c.period ≤ c.rootSpan - 1
  crossingBaseM : crossingBase c bootFuel + c.segLen < M
  crossingStartWithin : crossingBase c bootFuel - 1 ≤ bootBound
  crossingLast : bootBound < crossingBase c bootFuel + c.segLen - 1
  crossingCap : crossingBase c bootFuel + c.segLen - 1 ≤ c.rootCap
  crossingCover : crossingBase c bootFuel + c.segLen <
    (bootBound + 1) * (bootBound + 1)
  laterRange : (bootFuel + 1) * c.period + laterFuel * c.period ≤
    c.rootSpan - 1
  laterBaseM : laterBase c bootFuel + laterFuel * c.segLen < M
  laterCap : ∀ n, n < laterFuel →
    laterBase c bootFuel + (n + 1) * c.segLen - 1 ≤ c.rootCap
  laterCover : ∀ n, n < laterFuel →
    laterBase c bootFuel + n * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1)
  finalIndex : (bootFuel + 1) * c.period + laterFuel * c.period +
    c.period = c.rootSpan
  finalBaseM : laterBase c bootFuel + laterFuel * c.segLen + c.segLen < M
  finalValid : laterBase c bootFuel + laterFuel * c.segLen + valid - 1 =
    c.rootCap
  finalValidLt : valid < c.segLen
  finalCover : laterBase c bootFuel + laterFuel * c.segLen + valid <
    (bootBound + 1) * (bootBound + 1)
  firstPrimeLeCap : c.firstPrime ≤ c.rootCap
  finalBoundSqM : c.rootCap * c.rootCap < M
  segFinalM : c.segLen + c.rootCap < M
  mainIndexM : c.rootSpan + mainFuel * c.period < M
  mainBaseM : mainBase c bootFuel laterFuel delta +
    mainFuel * c.segLen < M

/-- Prime-table invariants discharge every prefix-capacity and final-length
field of a padded multi-root schedule. -/
theorem multiSchedule_of_primeTables
    (c : Cfg) (bootBound bootFuel laterFuel valid mainFuel delta : Nat)
    (a : MultiArithmetic c bootBound bootFuel laterFuel valid mainFuel delta)
    (hboot : PrimeTableInv c.bootPrimes bootBound)
    (full : List Nat) (hfull : PrimeTableInv full c.rootCap)
    (hfullLen : full.length = c.tableLen) :
    PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      mainFuel delta := by
  have hcross0 := rootScanMixed_primeTable (fuel := c.segLen) hboot
    a.crossingStartWithin (by simp only [crossingBase]; omega) a.bootTwo
  have hcrossMax : max bootBound
      (crossingBase c bootFuel + c.segLen - 1) =
        crossingBase c bootFuel + c.segLen - 1 :=
    Nat.max_eq_right (Nat.le_of_lt a.crossingLast)
  have hcross : PrimeTableInv (crossingTable c bootBound bootFuel)
      (crossingBase c bootFuel + c.segLen - 1) := by
    simpa only [crossingTable, hcrossMax] using hcross0
  have hcrossEndPos : 0 < crossingBase c bootFuel + c.segLen := by
    have := a.crossingLast
    have := a.bootTwo
    omega
  have hcrossEndTwo : 2 ≤ crossingBase c bootFuel + c.segLen := by
    have := a.crossingLast
    have := a.bootTwo
    omega
  have hlater (n : Nat) : PrimeTableInv
      (rootLaterWindows c (crossingTable c bootBound bootFuel)
        (laterBase c bootFuel) n)
      (laterBase c bootFuel + n * c.segLen - 1) := by
    apply rootLaterWindows_primeTable hcross
    · simp only [laterBase]
      have := hcrossEndPos
      omega
    · simp only [laterBase]
      omega
  have hfinal0 := rootScanFrom_primeTable (fuel := valid)
    (hlater laterFuel)
    (w := laterBase c bootFuel + laterFuel * c.segLen)
    (by
      simp only [laterBase]
      have := hcrossEndPos
      omega)
    (by
      simp only [laterBase]
      omega)
  have hfinal : PrimeTableInv
      (rootScanFrom
        (rootLaterWindows c (crossingTable c bootBound bootFuel)
          (laterBase c bootFuel) laterFuel)
        (laterBase c bootFuel + laterFuel * c.segLen) valid)
      c.rootCap := by
    rw [← a.finalValid]
    exact hfinal0
  have hfinalEq :
      rootScanFrom
        (rootLaterWindows c (crossingTable c bootBound bootFuel)
          (laterBase c bootFuel) laterFuel)
        (laterBase c bootFuel + laterFuel * c.segLen) valid = full :=
    PrimeTableInv.eq hfinal hfull
  refine {
    bootPrime := hboot
    bootShape := a.bootShape
    bootLe := a.bootLe
    tableLenPos := a.tableLenPos
    tableLenM := a.tableLenM
    markPos := a.markPos
    markM := a.markM
    periodM := a.periodM
    spanM := a.spanM
    spanPos := a.spanPos
    firstPrimePos := a.firstPrimePos
    firstPrimeLeLen := a.firstPrimeLeLen
    firstPrimeLeBoot := a.firstPrimeLeBoot
    bootBoundM := a.bootBoundM
    bootBoundSqM := a.bootBoundSqM
    segBootM := a.segBootM
    arrayM := a.arrayM
    markBudget := a.markBudget
    segLenPos := a.segLenPos
    bootTwo := a.bootTwo
    rootCapM := a.rootCapM
    deltaEq := a.deltaEq
    deltaM := a.deltaM
    bootstrapRange := a.bootstrapRange
    bootstrapBaseM := a.bootstrapBaseM
    bootstrapLastTwo := a.bootstrapLastTwo
    bootstrapStartWithin := a.bootstrapStartWithin
    bootstrapWithin := a.bootstrapWithin
    bootstrapCap := a.bootstrapCap
    bootstrapCover := a.bootstrapCover
    bootFit := Nat.le_of_lt a.bootFit
    bootstrapFit := by
      intro n hn k hk
      exact roomForStep_rootScanMixed_of_final hboot hfull hfullLen
        (Nat.le_of_lt a.bootFit) a.bootFit (a.bootstrapStartWithin n hn)
        (by omega) a.bootTwo (by
          have hcap := a.bootstrapCap n hn
          simp only [Nat.add_mul, Nat.one_mul] at hcap
          omega)
    crossingRange := a.crossingRange
    crossingBaseM := a.crossingBaseM
    crossingStartWithin := a.crossingStartWithin
    crossingLast := a.crossingLast
    crossingCap := a.crossingCap
    crossingCover := a.crossingCover
    crossingFit := by
      intro k hk
      exact roomForStep_rootScanMixed_of_final hboot hfull hfullLen
        (Nat.le_of_lt a.bootFit) a.bootFit a.crossingStartWithin
        (by simp only [crossingBase]; omega) a.bootTwo (by
          have := a.crossingCap
          omega)
    laterRange := a.laterRange
    laterBaseM := a.laterBaseM
    laterCap := a.laterCap
    laterCover := a.laterCover
    laterFit := by
      intro n hn k hk
      apply roomForStep_rootScanFrom_of_final (hlater n)
        (by
          simp only [laterBase]
          have := hcrossEndPos
          omega)
        (by
          simp only [laterBase]
          have := hcrossEndTwo
          omega) hfull
        hfullLen
      have hcap := a.laterCap n hn
      simp only [laterBase, Nat.add_mul, Nat.one_mul] at hcap ⊢
      have := hcrossEndPos
      omega
    finalIndex := a.finalIndex
    finalBaseM := a.finalBaseM
    finalValid := a.finalValid
    finalValidLt := a.finalValidLt
    finalCover := a.finalCover
    finalPrefixFit := by
      rw [← hfullLen]
      apply primeTable_length_le_of_le (hlater laterFuel) hfull
      have hvalid := a.finalValid
      simp only [laterBase] at hvalid ⊢
      have := hcrossEndPos
      omega
    finalFit := by
      intro k hk
      apply roomForStep_rootScanFrom_of_final (hlater laterFuel)
        (by
          simp only [laterBase]
          have := hcrossEndPos
          omega)
        (by
          simp only [laterBase]
          have := hcrossEndTwo
          omega) hfull
        hfullLen
      have hvalid := a.finalValid
      simp only [laterBase] at hvalid ⊢
      have := hcrossEndPos
      omega
    finalCapFit := by
      rw [hfinalEq, hfullLen]
      exact Nat.le_refl _
    finalLen := by
      rw [hfinalEq, hfullLen]
    finalPrime := hfinal
    firstPrimeLeCap := a.firstPrimeLeCap
    finalBoundSqM := a.finalBoundSqM
    segFinalM := a.segFinalM
    mainIndexM := a.mainIndexM
    mainBaseM := a.mainBaseM }

#print axioms singleSchedule_of_primeTables
#print axioms multiSchedule_of_primeTables

end LeanCompCert.Ports.ArraySegCanonicalSchedules
