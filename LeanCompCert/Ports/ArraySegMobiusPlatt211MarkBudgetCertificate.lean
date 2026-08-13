import LeanCompCert.Ports.ArraySegMobiusPlatt211HistoricalCore
import LeanCompCert.Verified.ArrayComputation

/-!
# Compiled full-table marking budgets for Platt (2.11)

The retained production rows after the separately certified prefix through
candidate `100` use a complete prime table through `row.rootCap`.  This file
packages the proved weighted-prime sieve as a zero/one CompCert verdict for
each such row.  A zero receipt establishes the exact numerical hypothesis
consumed by the segmented marking theorem; Lean never reduces the large
prime list or invokes `native_decide`.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211MarkBudgetCertificate

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
open LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

/-- Scalar machine bounds for the independent weighted-sieve verdict.  They
are kept separate from the physical run receipt: this closed check contains
only manifest arithmetic and no prime enumeration. -/
def markBudgetScalar (row : Row) : Prop :=
  75 ≤ row.idx →
    0 < row.rootCap + 1 ∧
    row.rootCap + 1 < M ∧
    (row.bootBound + 1) * (row.rootCap + 1) < M ∧
    (row.bootBound + 2) * (row.bootBound + 2) < M ∧
    row.rootCap + 1 ≤ (row.bootBound + 2) * (row.bootBound + 2) ∧
    row.segLen < M ∧ 2 < M ∧
    (row.rootCap + 1) * (row.segLen + 2) < M ∧
    row.markSteps < M ∧
    8 * (row.rootCap + 1) ≤ M

instance (row : Row) : Decidable (markBudgetScalar row) := by
  unfold markBudgetScalar
  infer_instance

def markBudgetScalarsOK : Bool :=
  rows.all fun row => decide (markBudgetScalar row)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem markBudgetScalars_ok : markBudgetScalarsOK = true := by
  decide

theorem row_markBudgetScalar (row : Row) (hrow : row ∈ rows)
    (hpost : 75 ≤ row.idx) :
    0 < row.rootCap + 1 ∧
    row.rootCap + 1 < M ∧
    (row.bootBound + 1) * (row.rootCap + 1) < M ∧
    (row.bootBound + 2) * (row.bootBound + 2) < M ∧
    row.rootCap + 1 ≤ (row.bootBound + 2) * (row.bootBound + 2) ∧
    row.segLen < M ∧ 2 < M ∧
    (row.rootCap + 1) * (row.segLen + 2) < M ∧
    row.markSteps < M ∧
    8 * (row.rootCap + 1) ≤ M := by
  have hbool := (List.all_eq_true.mp markBudgetScalars_ok) row hrow
  exact (of_decide_eq_true hbool) hpost

/-- The closed weighted-prime budget verdict for one post-prefix row. -/
def rowMarkBudgetComputation (row : Row) (hrow : row ∈ rows)
    (hpost : 75 ≤ row.idx) : AComputation where
  program := sieveWeightedBudgetProgram row.bootBound (row.rootCap + 1)
    row.segLen 2 row.markSteps
  wellFormed := sieveWeightedBudgetProgram_wf row.bootBound
    (row.rootCap + 1) row.segLen 2 row.markSteps
  base := 0
  baseOk := by
    have hs := row_markBudgetScalar row hrow hpost
    unfold BaseOk
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      simpa [sieveWeightedBudgetProgram, sieveWeightedProgram] using
        hs.2.2.2.2.2.2.2.2.2
  name := s!"platt211-mark-budget-{row.idx}"

/-- Physical CompCert verdict for every retained row after the independently
certified `[1,100]` prefix.  The corresponding batch emitter runs precisely
`rowMarkBudgetComputation` and requires return word zero. -/
axiom platt211MarkBudget_compcert_run (row : Row) (hrow : row ∈ rows)
    (hpost : 75 ≤ row.idx) :
  (rowMarkBudgetComputation row hrow hpost).Returns ((0 : Nat) : Int)

/-- The compiled verdict proves the canonical weighted prime sum fits the
literal production allowance. -/
theorem row_primeWeightedSum_le (row : Row) (hrow : row ∈ rows)
    (hpost : 75 ≤ row.idx) :
    primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤ row.markSteps := by
  have hs := row_markBudgetScalar row hrow hpost
  have hdenote :
      (rowMarkBudgetComputation row hrow hpost).program.denote =
        some (if primeWeightedSum (row.rootCap + 1) row.segLen 2 >
          row.markSteps then 1 else 0) := by
    exact sieveWeightedBudgetProgram_denote row.bootBound
      (row.rootCap + 1) row.segLen 2 row.markSteps
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      hs.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.1
  have hv := AComputation.value_of_returns
    (rowMarkBudgetComputation row hrow hpost) hdenote
    (platt211MarkBudget_compcert_run row hrow hpost)
  by_cases hle : primeWeightedSum (row.rootCap + 1) row.segLen 2 ≤
      row.markSteps
  · exact hle
  · have hgt : primeWeightedSum (row.rootCap + 1) row.segLen 2 >
        row.markSteps := by omega
    simp [hgt] at hv

/-- Consumer-shaped form: every exact prime table through the row's root cap
fits the marking loop. -/
theorem row_primeTable_markBudget {ps : List Nat} (row : Row)
    (hrow : row ∈ rows) (hpost : 75 ≤ row.idx)
    (hprime : PrimeTableInv ps row.rootCap) :
    (ps.map fun p => row.segLen / p + 2).sum ≤ row.markSteps := by
  rw [show (fun p => row.segLen / p + 2) = rowWeight row.segLen 2 from rfl,
    primeTable_weightedSum_eq_general hprime]
  exact row_primeWeightedSum_le row hrow hpost

/-! ## Post-prefix schedule classification -/

/-- Cheap, list-free routing data for the historical rows beginning at
candidate `101`.  The endpoint comparison is non-strict: when `hi + 1` is
exactly `(rootCap + 1)^2`, every live candidate is still strictly below that
square. -/
def postScheduleScalar (row : Row) : Prop :=
  let c := rowCfg row
  75 ≤ row.idx →
    0 < c.lo ∧ row.seed < M ∧ row.bootBound ≤ row.rootCap ∧
    c.firstPrime ≤ c.segLen ∧
    c.rootCap + 1 < (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.lo + c.segCount * c.segLen ≤ (c.rootCap + 1) ^ 2 ∧
    (row.rootCount = 1 ∨
      (row.rootCount ≠ 1 ∧ row.bootBound < row.rootCap ∧
        row.rootCount = historicalBootFuel row + 2 +
          historicalLaterFuel row ∧
        (historicalFinalValid row = row.segLen ∨
          (0 < historicalFinalValid row ∧
            historicalFinalValid row < c.segLen))))

instance (row : Row) : Decidable (postScheduleScalar row) := by
  unfold postScheduleScalar
  infer_instance

def postSchedulesOK : Bool :=
  rows.all fun row => decide (postScheduleScalar row)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem postSchedules_ok : postSchedulesOK = true := by
  decide

theorem row_postScheduleScalar (row : Row) (hrow : row ∈ rows)
    (hpost : 75 ≤ row.idx) :
    let c := rowCfg row
    0 < c.lo ∧ row.seed < M ∧ row.bootBound ≤ row.rootCap ∧
    c.firstPrime ≤ c.segLen ∧
    c.rootCap + 1 < (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.lo + c.segCount * c.segLen ≤ (c.rootCap + 1) ^ 2 ∧
    (row.rootCount = 1 ∨
      (row.rootCount ≠ 1 ∧ row.bootBound < row.rootCap ∧
        row.rootCount = historicalBootFuel row + 2 +
          historicalLaterFuel row ∧
        (historicalFinalValid row = row.segLen ∨
          (0 < historicalFinalValid row ∧
            historicalFinalValid row < c.segLen)))) := by
  have hbool := (List.all_eq_true.mp postSchedules_ok) row hrow
  exact (of_decide_eq_true hbool) hpost

end LeanCompCert.Ports.ArraySegMobiusPlatt211MarkBudgetCertificate
