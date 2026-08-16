import LeanCompCert.Ports.RS62AnchorScalar
import LeanCompCert.Ports.RS62CheckpointConfigCertificate

/-!
# CompCert certificates for the five large RS62 anchor segments

For every manifest row, two small compiled configuration programs establish
the exact prime-table length and marking budget, and the retained seven-stage
pipeline trace establishes the range endpoints.  The refinement theorem
below evaluates none of those ranges in Lean.
-/

namespace LeanCompCert.Ports.RS62AnchorCertificate

set_option maxRecDepth 100000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.RS62AnchorManifestData
open LeanCompCert.Ports.RS62AnchorScalar
open LeanCompCert.Ports.RS62CheckpointScalar

def sieveBound : Nat := 134

def rowPrimeCountComputation (row : Row) (hrow : row ∈ rows) :
    AComputation where
  program := sieveCountProgram sieveBound (row.rootCap + 1)
  wellFormed := sieveCountProgram_wf sieveBound (row.rootCap + 1)
  base := 0
  baseOk := by
    have hs := row_core row hrow
    unfold BaseOk
    exact ⟨Int.le_refl 0, Int.ofNat_le.mpr (by
      simpa [sieveCountProgram] using hs.countArrayBytesRoom)⟩
  name := s!"rs62-anchor-prime-count-{row.idx}"

axiom rs62AnchorPrimeCount_compcert_run (row : Row) (hrow : row ∈ rows) :
  (rowPrimeCountComputation row hrow).Returns ((row.mainCount : Nat) : Int)

theorem row_primeCount_eq (row : Row) (hrow : row ∈ rows) :
    primeCount (row.rootCap + 1) = row.mainCount := by
  have hs := row_core row hrow
  have hdenote : (rowPrimeCountComputation row hrow).program.denote =
      some (primeCount (row.rootCap + 1)) := by
    exact sieveCountProgram_denote sieveBound (row.rootCap + 1)
      hs.countLengthPositive hs.countLengthWord hs.countLoopWord
      hs.countSieveSquareWord hs.countSieveCoverage
  have hv := AComputation.value_of_returns
    (rowPrimeCountComputation row hrow) hdenote
    (rs62AnchorPrimeCount_compcert_run row hrow)
  omega

def rowMarkBudgetComputation (row : Row) (hrow : row ∈ rows) :
    AComputation where
  program := sieveWeightedBudgetProgram sieveBound (row.rootCap + 1)
    row.segLen 2 row.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf sieveBound
    (row.rootCap + 1) row.segLen 2 row.markSteps
  base := 0
  baseOk := by
    have hs := row_core row hrow
    unfold BaseOk
    exact ⟨Int.le_refl 0, Int.ofNat_le.mpr (by
      simpa [sieveWeightedBudgetProgram, sieveWeightedProgram] using
        hs.countArrayBytesRoom)⟩
  name := s!"rs62-anchor-mark-budget-{row.idx}"

axiom rs62AnchorMarkBudget_compcert_run (row : Row) (hrow : row ∈ rows) :
  (rowMarkBudgetComputation row hrow).Returns ((0 : Nat) : Int)

theorem row_primeWeightedSum_le (row : Row) (hrow : row ∈ rows) :
    primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤ row.markSteps := by
  have hs := row_core row hrow
  have hsegWord : row.segLen < M := by
    have hroom : row.segLen + row.rootCap < M := by
      simpa [RS62CheckpointManifestData.Row.cfg] using hs.segmentRootRoom
    omega
  have hdenote : (rowMarkBudgetComputation row hrow).program.denote =
      some (if primeWeightedSum (row.rootCap + 1) row.segLen 2 >
        row.markSteps then 1 else 0) := by
    exact sieveWeightedBudgetProgram_denote sieveBound
      (row.rootCap + 1) row.segLen 2 row.markSteps
      hs.countLengthPositive hs.countLengthWord hs.countLoopWord
      hs.countSieveSquareWord hs.countSieveCoverage hsegWord (by decide)
      hs.weightedProductWord hs.markStepsWord
  have hv := AComputation.value_of_returns
    (rowMarkBudgetComputation row hrow) hdenote
    (rs62AnchorMarkBudget_compcert_run row hrow)
  by_cases hle : primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤
      row.markSteps
  · exact hle
  · have hgt : primeWeightedSum (row.rootCap + 1) row.segLen 2 >
        row.markSteps := by omega
    simp [hgt] at hv

theorem row_schedule (row : Row) (hrow : row ∈ rows) :
    LeanCompCert.Ports.ArraySegMobiusIndexedFull.SingleMixedPaddedRootSchedule
      row.cfg 1000 row.rootCap row.cfg.wDelta :=
  LeanCompCert.Ports.RS62CheckpointConfigCertificate.schedule_of_compiled_configuration
    row (row_core row hrow)
      (row_primeCount_eq row hrow) (row_primeWeightedSum_le row hrow)

/-- The five memory-capped CompCert pipeline runs returned the exact retained
seven-stage traces. -/
axiom rs62AnchorCampaign_compcert_run (row : Row) (hrow : row ∈ rows) :
  LeanCompCert.Ports.RS62SegmentedReceipt.SegmentReceipt
    row.cfg row.SL row.SU row.lower row.upper

theorem row_source_loopE_verified (row : Row) (hrow : row ∈ rows) :
    LeanCompCert.Ports.RS62.loopE
      LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool
      row.cfg.segLen row.cfg.lo row.SL row.SU = (row.lower, row.upper) := by
  have hs := row_core row hrow
  have hschedule := row_schedule row hrow
  have hprime := rootScanMixed_primeTable
    (LeanCompCert.Ports.CanonicalPrimeTable.primesThrough_invariant 1000)
    (w := 1) (fuel := row.rootCap) (by omega) (by omega) (by omega)
  have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by
    have := hs.rootAtLeast1000
    omega
  have hlen :
      (rootScanMixed row.cfg.bootPrimes 1000 1 row.rootCap).length =
        row.cfg.tableLen := by
    rw [primeTable_length_eq_primeCount (hmax ▸ hprime),
      row_primeCount_eq row hrow]
    rfl
  have hbudget :
      ((rootScanMixed row.cfg.bootPrimes 1000 1 row.rootCap).map
        fun p => row.cfg.segLen / p + 2).sum ≤ row.cfg.markSteps := by
    rw [show (fun p => row.cfg.segLen / p + 2) =
        rowWeight row.segLen 2 from rfl,
      primeTable_weightedSum_eq_general (hmax ▸ hprime)]
    exact row_primeWeightedSum_le row hrow
  exact LeanCompCert.Ports.RS62SegmentedReceipt.source_loopE_of_segmentReceipt
    row.cfg 1000 row.rootCap row.cfg.wDelta row.SL row.SU row.lower row.upper
    hschedule hs.baseEq hlen hbudget hs.indexRoom hs.rootSquareRoom
    hs.segmentRootRoom hs.endpointWordRoom hs.aboveRoot hs.rootCoverage
    hs.startAtLeastThree hs.lowerWord hs.upperWord hs.endpointBound
    hs.arrayBytesRoom (rs62AnchorCampaign_compcert_run row hrow)

#print axioms row_source_loopE_verified

end LeanCompCert.Ports.RS62AnchorCertificate
