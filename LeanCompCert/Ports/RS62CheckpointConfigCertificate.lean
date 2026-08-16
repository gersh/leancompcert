import LeanCompCert.Ports.RS62CheckpointScalar
import LeanCompCert.Ports.RS62CheckpointCertificate
import LeanCompCert.Ports.ArraySieveCount
import LeanCompCert.Ports.ArraySieveWeightedSum
import LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
import LeanCompCert.Verified.ArrayComputation

/-!
# Compiled configuration certificates for the RS62 checkpoint campaign

The long segmented pipeline needs an exact prime-table length and a tight
weighted marking budget for each of its 120 rows.  Both facts are obtained
from proved array-sieve denotations and physical CompCert run receipts.  Lean
checks only the small scalar side conditions and the generic refinement
theorems; it does not enumerate the production prime ranges.

The uniform sieve bound `134` suffices because every row has
`rootCap + 1 <= 18002 <= 136^2`.
-/

namespace LeanCompCert.Ports.RS62CheckpointConfigCertificate

set_option maxRecDepth 100000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.CanonicalPrimeTable
open LeanCompCert.Ports.RS62CheckpointManifestData
open LeanCompCert.Ports.RS62CheckpointScalar
open LeanCompCert.Ports.RS62CheckpointCertificate

def sieveBound : Nat := 134

private theorem row_count_side_conditions (row : Row) (hrow : row ∈ rows) :
    0 < row.rootCap + 1 ∧
    row.rootCap + 1 < M ∧
    (sieveBound + 1) * (row.rootCap + 1) < M ∧
    (sieveBound + 2) * (sieveBound + 2) < M ∧
    row.rootCap + 1 ≤ (sieveBound + 2) * (sieveBound + 2) ∧
    8 * (row.rootCap + 1) ≤ M := by
  have hs := row_scalar row hrow
  unfold RowScalar at hs
  rcases hs with ⟨_, hroot, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hpos, hlenM, _, _, _, _, hbytes⟩
  unfold sieveBound
  constructor
  · exact hpos
  constructor
  · exact hlenM
  constructor
  · omega
  constructor
  · decide
  constructor
  · omega
  · exact hbytes

private theorem row_budget_side_conditions (row : Row) (hrow : row ∈ rows) :
    0 < row.rootCap + 1 ∧
    row.rootCap + 1 < M ∧
    (sieveBound + 1) * (row.rootCap + 1) < M ∧
    (sieveBound + 2) * (sieveBound + 2) < M ∧
    row.rootCap + 1 ≤ (sieveBound + 2) * (sieveBound + 2) ∧
    row.segLen < M ∧ 2 < M ∧
    (row.rootCap + 1) * (row.segLen + 2) < M ∧
    row.markSteps < M ∧
    8 * (row.rootCap + 1) ≤ M := by
  have hs := row_scalar row hrow
  unfold RowScalar at hs
  rcases hs with ⟨_, _, hsegPos, _, _, _, _, hmark, _, _, _, _, _, _, _,
    _, _, _, _, _, hpos, hlenM, _, _, _, hweighted, hbytes⟩
  have hMbig : 10000000 < M := by decide
  unfold sieveBound
  exact ⟨hpos, hlenM, by omega, by decide, by omega, by omega, by decide,
    hweighted, by omega, hbytes⟩

/-- Proved prime-count program for one manifest row. -/
def rowPrimeCountComputation (row : Row) (hrow : row ∈ rows) :
    AComputation where
  program := sieveCountProgram sieveBound (row.rootCap + 1)
  wellFormed := sieveCountProgram_wf sieveBound (row.rootCap + 1)
  base := 0
  baseOk := by
    have hs := row_count_side_conditions row hrow
    unfold BaseOk
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      simpa [sieveCountProgram] using hs.2.2.2.2.2
  name := s!"rs62-config-prime-count-{row.idx}"

/-- Physical return word of the CompCert prime-count program. -/
axiom rs62PrimeCount_compcert_run (row : Row) (hrow : row ∈ rows) :
  (rowPrimeCountComputation row hrow).Returns ((row.mainCount : Nat) : Int)

theorem row_primeCount_eq (row : Row) (hrow : row ∈ rows) :
    primeCount (row.rootCap + 1) = row.mainCount := by
  have hs := row_count_side_conditions row hrow
  have hdenote : (rowPrimeCountComputation row hrow).program.denote =
      some (primeCount (row.rootCap + 1)) := by
    exact sieveCountProgram_denote sieveBound (row.rootCap + 1)
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
  have hv := AComputation.value_of_returns
    (rowPrimeCountComputation row hrow) hdenote
    (rs62PrimeCount_compcert_run row hrow)
  omega

/-- Proved zero/one weighted-prime budget verdict for one manifest row. -/
def rowMarkBudgetComputation (row : Row) (hrow : row ∈ rows) :
    AComputation where
  program := sieveWeightedBudgetProgram sieveBound (row.rootCap + 1)
    row.segLen 2 row.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf sieveBound
    (row.rootCap + 1) row.segLen 2 row.markSteps
  base := 0
  baseOk := by
    have hs := row_budget_side_conditions row hrow
    unfold BaseOk
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      simpa [sieveWeightedBudgetProgram, sieveWeightedProgram] using
        hs.2.2.2.2.2.2.2.2.2
  name := s!"rs62-config-mark-budget-{row.idx}"

/-- Physical zero verdict of the CompCert weighted-prime program. -/
axiom rs62MarkBudget_compcert_run (row : Row) (hrow : row ∈ rows) :
  (rowMarkBudgetComputation row hrow).Returns ((0 : Nat) : Int)

theorem row_primeWeightedSum_le (row : Row) (hrow : row ∈ rows) :
    primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤ row.markSteps := by
  have hs := row_budget_side_conditions row hrow
  have hdenote : (rowMarkBudgetComputation row hrow).program.denote =
      some (if primeWeightedSum (row.rootCap + 1) row.segLen 2 >
        row.markSteps then 1 else 0) := by
    exact sieveWeightedBudgetProgram_denote sieveBound
      (row.rootCap + 1) row.segLen 2 row.markSteps
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      hs.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.1
  have hv := AComputation.value_of_returns
    (rowMarkBudgetComputation row hrow) hdenote
    (rs62MarkBudget_compcert_run row hrow)
  by_cases hle : primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤
      row.markSteps
  · exact hle
  · have hgt : primeWeightedSum (row.rootCap + 1) row.segLen 2 >
        row.markSteps := by omega
    simp [hgt] at hv

private theorem bootstrap_shape :
    ∃ tail, bootstrapPrimes = 2 :: tail := by
  have hprime : PrimeTableInv bootstrapPrimes 1000 := by
    exact primesThrough_invariant 1000
  have htwoPrime : IsPrime 2 := by decide
  have htwo : 2 ∈ bootstrapPrimes :=
    hprime.complete 2 htwoPrime (by omega)
  cases hlist : bootstrapPrimes with
  | nil => simp [hlist] at htwo
  | cons p tail =>
      have hpMem : p ∈ bootstrapPrimes := by simp [hlist]
      have hpTwo : 2 ≤ p := (hprime.sound p hpMem).two_le
      have hcases : p = 2 ∨ 2 ∈ tail := by
        have : 2 = p ∨ 2 ∈ tail := by simpa [hlist] using htwo
        exact this.imp Eq.symm id
      have hpEq : p = 2 := by
        rcases hcases with hpEq | htail
        · exact hpEq
        · have hord := hprime.ordered
          rw [hlist] at hord
          have hpLt : p < 2 := (List.pairwise_cons.mp hord).1 2 htail
          omega
      subst p
      exact ⟨tail, rfl⟩

/-- The two compiled scalar results supply the exact one-window root schedule
used by the generic segmented pipeline proof. -/
theorem row_schedule (row : Row) (hrow : row ∈ rows) :
    SingleMixedPaddedRootSchedule row.cfg 1000 row.rootCap row.cfg.wDelta := by
  let c := row.cfg
  let full := rootScanMixed c.bootPrimes 1000 1 row.rootCap
  have hs := row_scalar row hrow
  unfold RowScalar at hs
  rcases hs with ⟨hrootLo, hrootHi, hsegPos, hsegHi, hlo, hend,
    hcountUpper, hmarkSmall, hbase, hindex, hrootSq, hsegRoot,
    hendpointWord, habove, hcoverage, hthree, hSL, hSU, hendpointBound,
    harrayBytes, hcountPos, hcountM, hcountLoop, hbootSquare,
    hcountCover, hweightedFit, hcountBytes⟩
  have hbootPrime : PrimeTableInv c.bootPrimes 1000 := by
    simpa [c, Row.cfg, bootstrapPrimes] using primesThrough_invariant 1000
  have hshape : ∃ tail, c.bootPrimes = c.firstPrime :: tail := by
    obtain ⟨tail, hboot⟩ := bootstrap_shape
    refine ⟨tail, ?_⟩
    simp [c, Row.cfg, hboot, Cfg.firstPrime]
  have hfullPrime : PrimeTableInv full row.rootCap := by
    have hi := rootScanMixed_primeTable hbootPrime (w := 1)
      (fuel := row.rootCap) (by omega) (by omega) (by omega)
    have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by omega
    simpa only [full, hmax] using hi
  have hfullLen : full.length = row.mainCount := by
    rw [primeTable_length_eq_primeCount hfullPrime, row_primeCount_eq row hrow]
  have hfullBudget :
      (full.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    rw [show (fun p => c.segLen / p + 2) =
        rowWeight c.segLen 2 from rfl,
      primeTable_weightedSum_eq_general hfullPrime]
    simpa [c, Row.cfg] using row_primeWeightedSum_le row hrow
  have hbounds := row_bounds row hrow
  unfold RowBounds at hbounds
  rcases hbounds with ⟨hrootStrong, _, _, _, _, _, hmainSmall, _, _, _, _⟩
  obtain ⟨scanTail, hprefix⟩ :=
    rootScanMixed_has_prefix c.bootPrimes 1000 1 row.rootCap
  have hprefix' : full = c.bootPrimes ++ scanTail := hprefix
  have hbootBudget :
      (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    rw [hprefix', List.map_append, List.sum_append] at hfullBudget
    omega
  have hmarkPos : 0 < c.markSteps := by
    have hpositive :
        0 < (c.bootPrimes.map fun p => c.segLen / p + 2).sum := by
      obtain ⟨tail, hboot⟩ := hshape
      rw [hboot]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_pos_left
        (Nat.add_pos_right (c.segLen / c.firstPrime) Nat.zero_lt_two) _
    exact Nat.lt_of_lt_of_le hpositive hbootBudget
  have hbootFit : c.bootPrimes.length < full.length := by
    have hp1009 : IsPrime 1009 := by decide
    have hmemFull : 1009 ∈ full :=
      hfullPrime.complete 1009 hp1009 (by omega)
    have hnotBoot : 1009 ∉ c.bootPrimes := by
      intro hmem
      have := hbootPrime.upper 1009 hmem
      omega
    have htail : scanTail ≠ [] := by
      intro hnil
      subst scanTail
      simp only [List.append_nil] at hprefix'
      exact hnotBoot (hprefix' ▸ hmemFull)
    cases htailList : scanTail with
    | nil => exact False.elim (htail htailList)
    | cons a tail =>
        rw [hprefix', List.length_append, htailList]
        simp
  have hfirst : c.firstPrime = 2 := by
    obtain ⟨tail, hboot⟩ := bootstrap_shape
    simp [c, Row.cfg, hboot, Cfg.firstPrime]
  refine
    { bootPrime := hbootPrime
      bootShape := hshape
      bootLe := by rw [hfullLen] at hbootFit; exact Nat.le_of_lt hbootFit
      tableLenM := by simp [c, Cfg.tableLen, Row.cfg]; omega
      markPos := hmarkPos
      markM := by simpa [c, Row.cfg] using Nat.lt_trans hmarkSmall (by decide)
      periodM := by
        have : row.cfg.rootSpan < M := by omega
        simpa [c, Row.cfg, Cfg.rootSpan] using this
      spanM := by
        have : row.cfg.rootSpan < M := by omega
        simpa [c] using this
      firstPrimePos := by rw [hfirst]; omega
      firstPrimeLeLen := by
        rw [hfirst]
        simpa [c, Row.cfg] using (show 2 ≤ row.segLen by omega)
      firstPrimeLeBoot := by rw [hfirst]; omega
      bootBoundM := by decide
      bootBoundSqM := by decide
      segBootM := by
        have : row.segLen + 1000 ≤ row.segLen + row.rootCap := by omega
        have : row.segLen + 1000 < M := Nat.lt_of_le_of_lt this (by
          simpa [c, Row.cfg] using hsegRoot)
        simpa [c, Row.cfg] using this
      windowBaseM := by simp [c, Row.cfg]; omega
      firstOffsetM := by rw [hfirst]; simp [firstOffset]; decide
      arrayM := by omega
      markBudget := hbootBudget
      bootTwo := by omega
      rootIndex := by simp [c, Row.cfg, Cfg.rootSpan]
      bootStart := by omega
      bootLeCap := hrootLo
      finalValid := by simp [c, Row.cfg]
      finalValidLt := by simp [c, Row.cfg]; omega
      finalCover := by simp [c, Row.cfg]; omega
      bootFit := by
        rw [hfullLen] at hbootFit
        simpa [c, Cfg.tableLen, Row.cfg] using hbootFit
      finalFit := by
        intro k hk
        by_cases hcovered : 1 + k ≤ 1000
        · have hscan : rootScanMixed c.bootPrimes 1000 1 k =
              c.bootPrimes := rootScanMixed_eq_boot_of_le _ _ _ _ (by omega)
          rw [hscan]
          have hb : c.bootPrimes.length < c.tableLen := by
            rw [hfullLen] at hbootFit
            simpa [c, Cfg.tableLen, Row.cfg] using hbootFit
          exact ⟨Nat.le_of_lt hb, fun _ => hb⟩
        · have hprefixPrime : PrimeTableInv
              (rootScanMixed c.bootPrimes 1000 1 k) k := by
            have hi := rootScanMixed_primeTable hbootPrime
              (w := 1) (fuel := k) (by omega) (by omega) (by omega)
            have hmax : max 1000 (1 + k - 1) = k := by omega
            simpa only [hmax] using hi
          apply roomForStep_of_finalPrimeTable
            (full := full) (cap := row.rootCap)
          · rw [hfullLen]
            simp [c, Cfg.tableLen, Row.cfg]
          · exact hprefixPrime
          · exact hfullPrime
          · omega
          · omega
          · omega
      finalCapFit := by
        rw [hfullLen]
        simp [c, Cfg.tableLen, Row.cfg]
      rootCapM := by omega
      deltaEq := rfl
      deltaM := Nat.mod_lt _ (by decide) }

/-- Campaign-independent schedule construction from compiled prime-count and
weighted-budget evidence plus the cheap `RowCore` facts. -/
theorem schedule_of_compiled_configuration
    (row : Row) (hs : RowCore row)
    (hcountEq : primeCount (row.rootCap + 1) = row.mainCount)
    (hweighted : primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤
      row.markSteps) :
    SingleMixedPaddedRootSchedule row.cfg 1000 row.rootCap row.cfg.wDelta := by
  let c := row.cfg
  let full := rootScanMixed c.bootPrimes 1000 1 row.rootCap
  have hrootLo := hs.rootAtLeast1000
  have hroot1009 := hs.rootAtLeast1009
  have hsegPos := hs.segmentPositive
  have hsegTwo := hs.segmentAtLeastTwo
  have hrootBelowSeg := hs.rootBelowSegment
  have hrootBootCover := hs.rootBootstrapCoverage
  have hindex := hs.indexRoom
  have hsegRoot := hs.segmentRootRoom
  have hendpointWord := hs.endpointWordRoom
  have harrayBytes := hs.arrayBytesRoom
  have hmainWord := hs.mainCountWord
  have hmarkWord := hs.markStepsWord
  have hcountWord := hs.countLengthWord
  have hbootPrime : PrimeTableInv c.bootPrimes 1000 := by
    simpa [c, Row.cfg, bootstrapPrimes] using primesThrough_invariant 1000
  have hshape : ∃ tail, c.bootPrimes = c.firstPrime :: tail := by
    obtain ⟨tail, hboot⟩ := bootstrap_shape
    refine ⟨tail, ?_⟩
    simp [c, Row.cfg, hboot, Cfg.firstPrime]
  have hfullPrime : PrimeTableInv full row.rootCap := by
    have hi := rootScanMixed_primeTable hbootPrime (w := 1)
      (fuel := row.rootCap) (by omega) (by omega) (by omega)
    have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by
      omega
    simpa only [full, hmax] using hi
  have hfullLen : full.length = row.mainCount := by
    rw [primeTable_length_eq_primeCount hfullPrime, hcountEq]
  have hfullBudget :
      (full.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    rw [show (fun p => c.segLen / p + 2) =
        rowWeight c.segLen 2 from rfl,
      primeTable_weightedSum_eq_general hfullPrime]
    simpa [c, Row.cfg] using hweighted
  obtain ⟨scanTail, hprefix⟩ :=
    rootScanMixed_has_prefix c.bootPrimes 1000 1 row.rootCap
  have hprefix' : full = c.bootPrimes ++ scanTail := hprefix
  have hbootBudget :
      (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    rw [hprefix', List.map_append, List.sum_append] at hfullBudget
    omega
  have hmarkPos : 0 < c.markSteps := by
    have hpositive :
        0 < (c.bootPrimes.map fun p => c.segLen / p + 2).sum := by
      obtain ⟨tail, hboot⟩ := hshape
      rw [hboot]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_pos_left
        (Nat.add_pos_right (c.segLen / c.firstPrime) Nat.zero_lt_two) _
    exact Nat.lt_of_lt_of_le hpositive hbootBudget
  have hbootFit : c.bootPrimes.length < full.length := by
    have hp1009 : IsPrime 1009 := by decide
    have hmemFull : 1009 ∈ full :=
      hfullPrime.complete 1009 hp1009 (by omega)
    have hnotBoot : 1009 ∉ c.bootPrimes := by
      intro hmem
      have := hbootPrime.upper 1009 hmem
      omega
    have htail : scanTail ≠ [] := by
      intro hnil
      subst scanTail
      simp only [List.append_nil] at hprefix'
      exact hnotBoot (hprefix' ▸ hmemFull)
    cases htailList : scanTail with
    | nil => exact False.elim (htail htailList)
    | cons a tail =>
        rw [hprefix', List.length_append, htailList]
        simp
  have hfirst : c.firstPrime = 2 := by
    obtain ⟨tail, hboot⟩ := bootstrap_shape
    simp [c, Row.cfg, hboot, Cfg.firstPrime]
  refine
    { bootPrime := hbootPrime
      bootShape := hshape
      bootLe := by rw [hfullLen] at hbootFit; exact Nat.le_of_lt hbootFit
      tableLenM := by simpa [c, Cfg.tableLen, Row.cfg] using hmainWord
      markPos := hmarkPos
      markM := by simpa [c, Row.cfg] using hmarkWord
      periodM := by
        have : row.cfg.rootSpan < M := by omega
        simpa [c, Row.cfg, Cfg.rootSpan] using this
      spanM := by
        have : row.cfg.rootSpan < M := by omega
        simpa [c] using this
      firstPrimePos := by rw [hfirst]; omega
      firstPrimeLeLen := by
        rw [hfirst]
        simpa [c, Row.cfg] using hsegTwo
      firstPrimeLeBoot := by rw [hfirst]; omega
      bootBoundM := by decide
      bootBoundSqM := by decide
      segBootM := by
        have : row.segLen + 1000 ≤ row.segLen + row.rootCap := by omega
        have : row.segLen + 1000 < M := Nat.lt_of_le_of_lt this (by
          simpa [c, Row.cfg] using hsegRoot)
        simpa [c, Row.cfg] using this
      windowBaseM := by
        have := hendpointWord
        simp [c, Row.cfg] at *
        omega
      firstOffsetM := by rw [hfirst]; simp [firstOffset]; decide
      arrayM := by
        have := harrayBytes
        omega
      markBudget := hbootBudget
      bootTwo := by omega
      rootIndex := by simp [c, Row.cfg, Cfg.rootSpan]
      bootStart := by omega
      bootLeCap := hrootLo
      finalValid := by simp [c, Row.cfg]
      finalValidLt := by simpa [c, Row.cfg] using hrootBelowSeg
      finalCover := by simpa [c, Row.cfg] using hrootBootCover
      bootFit := by
        rw [hfullLen] at hbootFit
        simpa [c, Cfg.tableLen, Row.cfg] using hbootFit
      finalFit := by
        intro k hk
        by_cases hcovered : 1 + k ≤ 1000
        · have hscan : rootScanMixed c.bootPrimes 1000 1 k =
              c.bootPrimes := rootScanMixed_eq_boot_of_le _ _ _ _ (by omega)
          rw [hscan]
          have hb : c.bootPrimes.length < c.tableLen := by
            rw [hfullLen] at hbootFit
            simpa [c, Cfg.tableLen, Row.cfg] using hbootFit
          exact ⟨Nat.le_of_lt hb, fun _ => hb⟩
        · have hprefixPrime : PrimeTableInv
              (rootScanMixed c.bootPrimes 1000 1 k) k := by
            have hi := rootScanMixed_primeTable hbootPrime
              (w := 1) (fuel := k) (by omega) (by omega) (by omega)
            have hmax : max 1000 (1 + k - 1) = k := by omega
            simpa only [hmax] using hi
          apply roomForStep_of_finalPrimeTable
            (full := full) (cap := row.rootCap)
          · rw [hfullLen]
            simp [c, Cfg.tableLen, Row.cfg]
          · exact hprefixPrime
          · exact hfullPrime
          · omega
          · omega
          · omega
      finalCapFit := by
        rw [hfullLen]
        simp [c, Cfg.tableLen, Row.cfg]
      rootCapM := by omega
      deltaEq := rfl
      deltaM := Nat.mod_lt _ (by decide) }

theorem row_hasConfigurationCertificate (row : Row) (hrow : row ∈ rows) :
    HasConfigurationCertificate row := by
  refine ⟨1000, row.rootCap, row.cfg.wDelta, ?_⟩
  exact
    { schedule := row_schedule row hrow
      baseEq := (row_scalar row hrow).2.2.2.2.2.2.2.2.1
      tableLength := by
        have hp := (row_schedule row hrow).finalCapFit
        have hlen := row_primeCount_eq row hrow
        have hprime := rootScanMixed_primeTable
          (primesThrough_invariant 1000) (w := 1) (fuel := row.rootCap)
          (by omega) (by omega) (by omega)
        have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by
          have := (row_scalar row hrow).1
          omega
        rw [primeTable_length_eq_primeCount (hmax ▸ hprime), hlen]
        rfl
      markBudget := by
        have hprime := rootScanMixed_primeTable
          (primesThrough_invariant 1000) (w := 1) (fuel := row.rootCap)
          (by omega) (by omega) (by omega)
        have hmax : max 1000 (1 + row.rootCap - 1) = row.rootCap := by
          have := (row_scalar row hrow).1
          omega
        rw [show (fun p => row.cfg.segLen / p + 2) =
            rowWeight row.segLen 2 from rfl,
          primeTable_weightedSum_eq_general (hmax ▸ hprime)]
        exact row_primeWeightedSum_le row hrow
      indexRoom := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.1
      rootSquareRoom := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.1
      segmentRootRoom := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.1
      endpointWordRoom := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.1
      aboveRoot := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rootCoverage := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      startAtLeastThree := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      lowerWord := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      upperWord := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      endpointBound := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      arrayBytesRoom := (row_scalar row hrow).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 }

/-- Every retained RS62 trace now has its compiled configuration evidence. -/
theorem row_source_loopE_verified (row : Row) (hrow : row ∈ rows) :
    LeanCompCert.Ports.RS62.loopE
      RS62SegmentedPrimeMask.isPrimeBool row.cfg.segLen row.cfg.lo
      row.SL row.SU = (row.lower, row.upper) :=
  row_source_loopE row hrow (row_hasConfigurationCertificate row hrow)

end LeanCompCert.Ports.RS62CheckpointConfigCertificate
