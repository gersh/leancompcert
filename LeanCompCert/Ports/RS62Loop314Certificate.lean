import LeanCompCert.Ports.RS62Loop314Receipt
import LeanCompCert.Ports.RS62CheckpointConfigCertificate

/-! # Production certificates for the two RS62 equation-(3.14) segments -/

namespace LeanCompCert.Ports.RS62Loop314Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.RS62CheckpointManifestData
open LeanCompCert.Ports.RS62CheckpointScalar
open LeanCompCert.Ports.RS62CheckpointConfigCertificate
open LeanCompCert.Ports.RS62Loop314Receipt

def row1 : Row := {
  idx := 31401, fuel := 4000000, lo := 2003, segLen := 3997998
  rootCap := 2001, mainCount := 303, markSteps := 9165664
  SL := 2139885700715063, SU := 2139885785157557
  lower := 4278927668938684, upper := 4278927827596134
}

def row2 : Row := {
  idx := 31402, fuel := 14500000, lo := 4000001, segLen := 10500000
  rootCap := 3808, mainCount := 529, markSteps := 24919311
  SL := 4278927668938684, SU := 4278927827596134
  lower := 4641426368539993, upper := 4641426537697523
}

abbrev cfg1 : Cfg := row1.cfg
abbrev cfg2 : Cfg := row2.cfg

private theorem row1_core : RowCore row1 := by
  constructor <;> decide
private theorem row2_core : RowCore row2 := by
  constructor <;> decide

def row1PrimeCountComputation : AComputation where
  program := sieveCountProgram 134 (row1.rootCap + 1)
  wellFormed := sieveCountProgram_wf 134 (row1.rootCap + 1)
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-314-config-prime-count-1"

def row2PrimeCountComputation : AComputation where
  program := sieveCountProgram 134 (row2.rootCap + 1)
  wellFormed := sieveCountProgram_wf 134 (row2.rootCap + 1)
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-314-config-prime-count-2"

def row1MarkBudgetComputation : AComputation where
  program := sieveWeightedBudgetProgram 134 (row1.rootCap + 1)
    row1.segLen 2 row1.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf 134 (row1.rootCap + 1)
    row1.segLen 2 row1.markSteps
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-314-config-mark-budget-1"

def row2MarkBudgetComputation : AComputation where
  program := sieveWeightedBudgetProgram 134 (row2.rootCap + 1)
    row2.segLen 2 row2.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf 134 (row2.rootCap + 1)
    row2.segLen 2 row2.markSteps
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-314-config-mark-budget-2"

axiom row1PrimeCount_compcert_run :
  row1PrimeCountComputation.Returns ((303 : Nat) : Int)
axiom row2PrimeCount_compcert_run :
  row2PrimeCountComputation.Returns ((529 : Nat) : Int)
axiom row1MarkBudget_compcert_run :
  row1MarkBudgetComputation.Returns ((0 : Nat) : Int)
axiom row2MarkBudget_compcert_run :
  row2MarkBudgetComputation.Returns ((0 : Nat) : Int)

private theorem row1_count : primeCount (row1.rootCap + 1) = row1.mainCount := by
  have hdenote : row1PrimeCountComputation.program.denote =
      some (primeCount (row1.rootCap + 1)) :=
    sieveCountProgram_denote 134 (row1.rootCap + 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns row1PrimeCountComputation hdenote
    row1PrimeCount_compcert_run
  simpa [row1] using hv.symm

private theorem row2_count : primeCount (row2.rootCap + 1) = row2.mainCount := by
  have hdenote : row2PrimeCountComputation.program.denote =
      some (primeCount (row2.rootCap + 1)) :=
    sieveCountProgram_denote 134 (row2.rootCap + 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns row2PrimeCountComputation hdenote
    row2PrimeCount_compcert_run
  simpa [row2] using hv.symm

private theorem row1_budget :
    primeWeightedSum (row1.rootCap + 1) row1.segLen 2 ≤ row1.markSteps := by
  have hdenote : row1MarkBudgetComputation.program.denote = some
      (if primeWeightedSum (row1.rootCap + 1) row1.segLen 2 > row1.markSteps
        then 1 else 0) :=
    sieveWeightedBudgetProgram_denote 134 (row1.rootCap + 1) row1.segLen 2
      row1.markSteps (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns row1MarkBudgetComputation hdenote
    row1MarkBudget_compcert_run
  apply Nat.le_of_not_lt
  intro hnot
  have hgt : primeWeightedSum (row1.rootCap + 1) row1.segLen 2 >
      row1.markSteps := hnot
  simp [hgt] at hv

private theorem row2_budget :
    primeWeightedSum (row2.rootCap + 1) row2.segLen 2 ≤ row2.markSteps := by
  have hdenote : row2MarkBudgetComputation.program.denote = some
      (if primeWeightedSum (row2.rootCap + 1) row2.segLen 2 > row2.markSteps
        then 1 else 0) :=
    sieveWeightedBudgetProgram_denote 134 (row2.rootCap + 1) row2.segLen 2
      row2.markSteps (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns row2MarkBudgetComputation hdenote
    row2MarkBudget_compcert_run
  apply Nat.le_of_not_lt
  intro hnot
  have hgt : primeWeightedSum (row2.rootCap + 1) row2.segLen 2 >
      row2.markSteps := hnot
  simp [hgt] at hv

private theorem fullPrime (row : Row) (hc : RowCore row) :
    PrimeTableInv
      (rootScanMixed row.cfg.bootPrimes 1000 1 row.rootCap) row.rootCap := by
  have hboot : PrimeTableInv row.cfg.bootPrimes 1000 := by
    simpa [Row.cfg, RS62CheckpointManifestData.bootstrapPrimes] using
      LeanCompCert.Ports.CanonicalPrimeTable.primesThrough_invariant 1000
  have hi := rootScanMixed_primeTable hboot (w := 1) (fuel := row.rootCap)
    (by omega) (by omega) (by omega)
  have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by
    have hroot := hc.rootAtLeast1000
    omega
  simpa only [hmax] using hi

private theorem row1_tableLength :
    (rootScanMixed cfg1.bootPrimes 1000 1 row1.rootCap).length =
      cfg1.tableLen := by
  rw [primeTable_length_eq_primeCount (fullPrime row1 row1_core), row1_count]
  rfl

private theorem row2_tableLength :
    (rootScanMixed cfg2.bootPrimes 1000 1 row2.rootCap).length =
      cfg2.tableLen := by
  rw [primeTable_length_eq_primeCount (fullPrime row2 row2_core), row2_count]
  rfl

private theorem row1_rootBudget :
    ((rootScanMixed cfg1.bootPrimes 1000 1 row1.rootCap).map
      fun p => cfg1.segLen / p + 2).sum ≤ cfg1.markSteps := by
  rw [show (fun p => cfg1.segLen / p + 2) =
      rowWeight cfg1.segLen 2 from rfl,
    primeTable_weightedSum_eq_general (fullPrime row1 row1_core)]
  exact row1_budget

private theorem row2_rootBudget :
    ((rootScanMixed cfg2.bootPrimes 1000 1 row2.rootCap).map
      fun p => cfg2.segLen / p + 2).sum ≤ cfg2.markSteps := by
  rw [show (fun p => cfg2.segLen / p + 2) =
      rowWeight cfg2.segLen 2 from rfl,
    primeTable_weightedSum_eq_general (fullPrime row2 row2_core)]
  exact row2_budget

private theorem row1_schedule :
    SingleMixedPaddedRootSchedule cfg1 1000 row1.rootCap cfg1.wDelta :=
  schedule_of_compiled_configuration row1 row1_core row1_count row1_budget

private theorem row2_schedule :
    SingleMixedPaddedRootSchedule cfg2 1000 row2.rootCap cfg2.wDelta :=
  schedule_of_compiled_configuration row2 row2_core row2_count row2_budget

/-- Retained accepting CompCert trace for `[2003, 4000001)`. -/
axiom segment1_compcert_run : SegmentReceipt cfg1
  2139885700715063 2139885785157557 546016165494919895 0
  0 4278927668938684 4278927827596134 18341868088443345231 60

/-- Retained accepting CompCert trace for `[4000001, 14500001)`. -/
axiom segment2_compcert_run : SegmentReceipt cfg2
  4278927668938684 4278927827596134 18341868088443345231 60
  0 4641426368539993 4641426537697523 3526312244967428556 221

theorem segment1_loop314 :
    LeanCompCert.Ports.RS62Loop314Sound.loop314
      RS62SegmentedPrimeMask.isPrimeBool 3997998 2003
        2139885700715063 2139885785157557 546016165494919895 =
      some (4278927668938684, 4278927827596134,
        LeanCompCert.Ports.RS62Loop314Sound.wval
          (18341868088443345231, 60)) := by
  exact source_loop314_of_segmentReceipt cfg1 1000 row1.rootCap cfg1.wDelta
    2139885700715063 2139885785157557 546016165494919895 0
    4278927668938684 4278927827596134 18341868088443345231 60
    row1_schedule (by decide) row1_tableLength row1_rootBudget
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) segment1_compcert_run

theorem segment2_loop314 :
    LeanCompCert.Ports.RS62Loop314Sound.loop314
      RS62SegmentedPrimeMask.isPrimeBool 10500000 4000001
        4278927668938684 4278927827596134
        (LeanCompCert.Ports.RS62Loop314Sound.wval
          (18341868088443345231, 60)) =
      some (4641426368539993, 4641426537697523,
        LeanCompCert.Ports.RS62Loop314Sound.wval
          (3526312244967428556, 221)) := by
  exact source_loop314_of_segmentReceipt cfg2 1000 row2.rootCap cfg2.wDelta
    4278927668938684 4278927827596134 18341868088443345231 60
    4641426368539993 4641426537697523 3526312244967428556 221
    row2_schedule (by decide) row2_tableLength row2_rootBudget
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) segment2_compcert_run

#print axioms segment1_loop314
#print axioms segment2_loop314

end LeanCompCert.Ports.RS62Loop314Certificate
