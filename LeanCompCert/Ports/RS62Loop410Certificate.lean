import LeanCompCert.Ports.RS62Loop410Receipt
import LeanCompCert.Ports.RS62CheckpointConfigCertificate
import LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence

/-!
# Production CompCert certificate for RS62 equation (4.10)

The only production-scale assumptions in this module are physical CompCert
run receipts.  All translation from those receipts to the symbolic source
fold is proved by the generic compiler and segmented-sieve refinements.
-/

namespace LeanCompCert.Ports.RS62Loop410Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.RS62CheckpointManifestData
open LeanCompCert.Ports.RS62CheckpointScalar
open LeanCompCert.Ports.RS62CheckpointConfigCertificate
open LeanCompCert.Ports.RS62Loop410Receipt

def row : Row := {
  idx := 410, fuel := 100000000, lo := 99991, segLen := 99900010
  rootCap := 10000, mainCount := 1229, markSteps := 248059571
  SL := 3240575047941118, SU := 3240575047941118
  lower := 5184960590949722, upper := 9234827679873124
}

abbrev cfg : Cfg := row.cfg

private theorem row_core : RowCore row := by
  constructor <;> decide

def primeCountComputation : AComputation where
  program := sieveCountProgram 134 (row.rootCap + 1)
  wellFormed := sieveCountProgram_wf 134 (row.rootCap + 1)
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-410-config-prime-count"

def markBudgetComputation : AComputation where
  program := sieveWeightedBudgetProgram 134 (row.rootCap + 1)
    row.segLen 2 row.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf 134 (row.rootCap + 1)
    row.segLen 2 row.markSteps
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-410-config-mark-budget"

/-- Physical CompCert return word of the configuration prime-count run. -/
axiom primeCount_compcert_run :
  primeCountComputation.Returns ((1229 : Nat) : Int)

/-- Physical CompCert zero verdict for the exact marking-budget run. -/
axiom markBudget_compcert_run :
  markBudgetComputation.Returns ((0 : Nat) : Int)

private theorem count_eq : primeCount (row.rootCap + 1) = row.mainCount := by
  have hdenote : primeCountComputation.program.denote =
      some (primeCount (row.rootCap + 1)) :=
    sieveCountProgram_denote 134 (row.rootCap + 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns primeCountComputation hdenote
    primeCount_compcert_run
  simpa [row] using hv.symm

private theorem budget_le :
    primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤ row.markSteps := by
  have hdenote : markBudgetComputation.program.denote = some
      (if primeWeightedSum (row.rootCap + 1) row.segLen 2 > row.markSteps
        then 1 else 0) :=
    sieveWeightedBudgetProgram_denote 134 (row.rootCap + 1) row.segLen 2
      row.markSteps (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns markBudgetComputation hdenote
    markBudget_compcert_run
  apply Nat.le_of_not_lt
  intro hnot
  have hgt : primeWeightedSum (row.rootCap + 1) row.segLen 2 > row.markSteps :=
    hnot
  simp [hgt] at hv

private theorem schedule :
    SingleMixedPaddedRootSchedule cfg 1000 row.rootCap cfg.wDelta :=
  schedule_of_compiled_configuration row row_core count_eq budget_le

private theorem fullPrime : PrimeTableInv
    (rootScanMixed cfg.bootPrimes 1000 1 row.rootCap) row.rootCap := by
  have hboot : PrimeTableInv cfg.bootPrimes 1000 := by
    simpa [Row.cfg, RS62CheckpointManifestData.bootstrapPrimes] using
      LeanCompCert.Ports.CanonicalPrimeTable.primesThrough_invariant 1000
  have hi := rootScanMixed_primeTable hboot (w := 1) (fuel := row.rootCap)
    (by decide) (by decide) (by decide)
  simpa [row] using hi

private theorem tableLength :
    (rootScanMixed cfg.bootPrimes 1000 1 row.rootCap).length = cfg.tableLen := by
  rw [primeTable_length_eq_primeCount fullPrime, count_eq]
  rfl

private theorem rootBudget :
    ((rootScanMixed cfg.bootPrimes 1000 1 row.rootCap).map
      fun p => cfg.segLen / p + 2).sum ≤ cfg.markSteps := by
  rw [show (fun p => cfg.segLen / p + 2) =
      rowWeight cfg.segLen 2 from rfl,
    primeTable_weightedSum_eq_general fullPrime]
  exact budget_le

/-- Retained accepting CompCert trace for `[99991, 100000001)`. -/
axiom segment_compcert_run : SegmentReceipt cfg
  3240575047941118 5773442372576424 316 99990 99989
  0 5184960590949722 9234827679873124

/-- The production trace denotes the paper-faithful source recurrence and
checks every strict equation-(4.10) guard. -/
theorem production_sourceFold :
    ∃ arr,
      LeanCompCert.Ports.RS62PrimeMaskLadder.MaskCorrect
        LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool
        arr 99991 99900010 ∧
      let initial : LeanCompCert.Ports.RS62Loop410Sound.State410 :=
        ⟨3240575047941118, 3240575047941118, 5773442372576424, 316, 0⟩
      let src := LeanCompCert.Ports.RS62Loop410Sound.sourceFold
        arr 99991 99900010 initial
      src.logL = 5184960590949722 ∧
        src.product = 9234827679873124 ∧ src.bad = 0 ∧
        LeanCompCert.Ports.RS62Loop410Sound.CellGuards
          arr 99991 99900010 initial := by
  exact sourceFold_of_segmentReceipt cfg 1000 row.rootCap cfg.wDelta
    3240575047941118 5773442372576424 316 99990 99989
    5184960590949722 9234827679873124 schedule (by decide) tableLength
    rootBudget
    (hIdxM := by decide) (hRootSqM := by decide)
    (hSegRootM := by decide) (hLoSegM := by decide)
    (hAboveRoot := by decide) (hCovered := by decide)
    (hn0 := by decide) (hEnd := by decide)
    (hSL := by decide) (hP := by decide) (hsqrt0 := by decide)
    (hden0 := by decide) (hnm20 := by decide)
    (hsqrtInit := by
      change 316 = Nat.sqrt 99991
      exact LeanCompCert.Verified.SqrtEquiv.sqrt_unique (by decide) (by decide))
    (hdenInit := by change 99990 = 99991 - 1; decide)
    (hnm2Init := by change 99989 = 99991 - 2; decide)
    (hBytes := by decide) segment_compcert_run

/-! ## Compiled seed fold `[2003, 99991)`

The paper's old replay bundle stored the exact numerator and denominator of
the primorial quotient below `99991`.  For the consumer only an upper bound
is needed.  This shorter compiled fold starts from an ordinary-kernel exact
endpoint at `2003` and propagates an upward-rounded fixed-point product.
The deliberately large logarithm seed makes the otherwise irrelevant
equation-(4.10) guard pass throughout this product-only use of the consumer.
-/

def seedRow : Row := {
  idx := 4102003, fuel := 97988, lo := 2003, segLen := 97988
  rootCap := 1009, mainCount := 169, markSteps := 215736
  SL := 1000000000000000000, SU := 1000000000000000000
  lower := 1001100689307500039, upper := 5773442372576424
}

abbrev seedCfg : Cfg := seedRow.cfg

private theorem seedRow_core : RowCore seedRow := by
  constructor <;> decide

def seedPrimeCountComputation : AComputation where
  program := sieveCountProgram 134 (seedRow.rootCap + 1)
  wellFormed := sieveCountProgram_wf 134 (seedRow.rootCap + 1)
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-410-seed-prime-count"

def seedMarkBudgetComputation : AComputation where
  program := sieveWeightedBudgetProgram 134 (seedRow.rootCap + 1)
    seedRow.segLen 2 seedRow.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf 134 (seedRow.rootCap + 1)
    seedRow.segLen 2 seedRow.markSteps
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      decide
  name := "rs62-410-seed-mark-budget"

/-- Physical CompCert result of the seed configuration prime count. -/
axiom seedPrimeCount_compcert_run :
  seedPrimeCountComputation.Returns ((169 : Nat) : Int)

/-- Physical CompCert zero verdict for the seed marking budget. -/
axiom seedMarkBudget_compcert_run :
  seedMarkBudgetComputation.Returns ((0 : Nat) : Int)

private theorem seedCount_eq :
    primeCount (seedRow.rootCap + 1) = seedRow.mainCount := by
  have hdenote : seedPrimeCountComputation.program.denote =
      some (primeCount (seedRow.rootCap + 1)) :=
    sieveCountProgram_denote 134 (seedRow.rootCap + 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns seedPrimeCountComputation hdenote
    seedPrimeCount_compcert_run
  simpa [seedRow] using hv.symm

private theorem seedBudget_le :
    primeWeightedSum (seedRow.rootCap + 1) seedRow.segLen 2 ≤
      seedRow.markSteps := by
  have hdenote : seedMarkBudgetComputation.program.denote = some
      (if primeWeightedSum (seedRow.rootCap + 1) seedRow.segLen 2 >
          seedRow.markSteps then 1 else 0) :=
    sieveWeightedBudgetProgram_denote 134 (seedRow.rootCap + 1)
      seedRow.segLen 2 seedRow.markSteps
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv := AComputation.value_of_returns seedMarkBudgetComputation hdenote
    seedMarkBudget_compcert_run
  apply Nat.le_of_not_lt
  intro hnot
  have hgt : primeWeightedSum (seedRow.rootCap + 1) seedRow.segLen 2 >
      seedRow.markSteps := hnot
  simp [hgt] at hv

private theorem seedSchedule :
    SingleMixedPaddedRootSchedule seedCfg 1000 seedRow.rootCap seedCfg.wDelta :=
  schedule_of_compiled_configuration seedRow seedRow_core seedCount_eq seedBudget_le

private theorem seedFullPrime : PrimeTableInv
    (rootScanMixed seedCfg.bootPrimes 1000 1 seedRow.rootCap)
      seedRow.rootCap := by
  have hboot : PrimeTableInv seedCfg.bootPrimes 1000 := by
    simpa [Row.cfg, RS62CheckpointManifestData.bootstrapPrimes] using
      LeanCompCert.Ports.CanonicalPrimeTable.primesThrough_invariant 1000
  have hi := rootScanMixed_primeTable hboot (w := 1)
    (fuel := seedRow.rootCap) (by decide) (by decide) (by decide)
  simpa [seedRow] using hi

private theorem seedTableLength :
    (rootScanMixed seedCfg.bootPrimes 1000 1 seedRow.rootCap).length =
      seedCfg.tableLen := by
  rw [primeTable_length_eq_primeCount seedFullPrime, seedCount_eq]
  rfl

private theorem seedRootBudget :
    ((rootScanMixed seedCfg.bootPrimes 1000 1 seedRow.rootCap).map
      fun p => seedCfg.segLen / p + 2).sum ≤ seedCfg.markSteps := by
  rw [show (fun p => seedCfg.segLen / p + 2) =
      rowWeight seedCfg.segLen 2 from rfl,
    primeTable_weightedSum_eq_general seedFullPrime]
  exact seedBudget_le

/-- Retained accepting CompCert trace for the rounded product seed fold. -/
axiom seedSegment_compcert_run : SegmentReceipt seedCfg
  1000000000000000000 3820670970257713 44 2002 2001
  0 1001100689307500039 5773442372576424

/-- The compiled seed trace denotes the rounded source recurrence over every
integer in `[2003, 99991)`, with a mathematically correct prime mask. -/
theorem seed_sourceFold :
    ∃ arr,
      LeanCompCert.Ports.RS62PrimeMaskLadder.MaskCorrect
        LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool
        arr 2003 97988 ∧
      let initial : LeanCompCert.Ports.RS62Loop410Sound.State410 :=
        ⟨1000000000000000000, 1000000000000000000,
          3820670970257713, 44, 0⟩
      let src := LeanCompCert.Ports.RS62Loop410Sound.sourceFold
        arr 2003 97988 initial
      src.logL = 1001100689307500039 ∧
        src.product = 5773442372576424 ∧ src.bad = 0 ∧
        LeanCompCert.Ports.RS62Loop410Sound.CellGuards
          arr 2003 97988 initial := by
  exact sourceFold_of_segmentReceipt seedCfg 1000 seedRow.rootCap seedCfg.wDelta
    1000000000000000000 3820670970257713 44 2002 2001
    1001100689307500039 5773442372576424 seedSchedule (by decide)
    seedTableLength seedRootBudget
    (hIdxM := by decide) (hRootSqM := by decide)
    (hSegRootM := by decide) (hLoSegM := by decide)
    (hAboveRoot := by decide) (hCovered := by decide)
    (hn0 := by decide) (hEnd := by decide)
    (hSL := by decide) (hP := by decide) (hsqrt0 := by decide)
    (hden0 := by decide) (hnm20 := by decide)
    (hsqrtInit := by
      change 44 = Nat.sqrt 2003
      exact LeanCompCert.Verified.SqrtEquiv.sqrt_unique (by decide) (by decide))
    (hdenInit := by decide) (hnm2Init := by decide)
    (hBytes := by decide) seedSegment_compcert_run

#print axioms production_sourceFold
#print axioms seed_sourceFold

end LeanCompCert.Ports.RS62Loop410Certificate
