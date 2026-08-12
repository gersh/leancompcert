import LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate
import LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence

/-!
# First finite schedule layer for Platt (2.11)

The production manifest records enough compact configuration data to rebuild
each root schedule.  This file checks the inexpensive bootstrap part in the
ordinary kernel: the literal bootstrap list is exactly the transparent prime
scan through `bootBound`, and its complete marking allowance fits the emitted
budget.  The much larger final-table/capacity certificate is deliberately a
separate LeanCompCert computation.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule

open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest

def bootPairOK (row : Row) : Bool :=
  decide (
    (row.bootBound = 2 ∧ row.bootCount = 1) ∨
    (row.bootBound = 3 ∧ row.bootCount = 2) ∨
    (row.bootBound = 4 ∧ row.bootCount = 2) ∨
    (row.bootBound = 5 ∧ row.bootCount = 3) ∨
    (row.bootBound = 6 ∧ row.bootCount = 3) ∨
    (row.bootBound = 9 ∧ row.bootCount = 4) ∨
    (row.bootBound = 10 ∧ row.bootCount = 4) ∨
    (row.bootBound = 31 ∧ row.bootCount = 11) ∨
    (row.bootBound = 100 ∧ row.bootCount = 25) ∨
    (row.bootBound = 316 ∧ row.bootCount = 65) ∨
    (row.bootBound = 1000 ∧ row.bootCount = 168))

def bootBudgetConfigOK (row : Row) : Bool :=
  decide (
    (row.segLen = 1 ∧ row.bootCount = 1 ∧ row.bootBudget = 2) ∨
    (row.segLen = 1 ∧ row.bootCount = 2 ∧ row.bootBudget = 4) ∨
    (row.segLen = 2 ∧ row.bootCount = 1 ∧ row.bootBudget = 3) ∨
    (row.segLen = 2 ∧ row.bootCount = 2 ∧ row.bootBudget = 5) ∨
    (row.segLen = 10 ∧ row.bootCount = 2 ∧ row.bootBudget = 12) ∨
    (row.segLen = 10 ∧ row.bootCount = 3 ∧ row.bootBudget = 16) ∨
    (row.segLen = 20 ∧ row.bootCount = 3 ∧ row.bootBudget = 26) ∨
    (row.segLen = 90 ∧ row.bootCount = 4 ∧ row.bootBudget = 113) ∨
    (row.segLen = 100 ∧ row.bootCount = 4 ∧ row.bootBudget = 125) ∨
    (row.segLen = 1000 ∧ row.bootCount = 11 ∧ row.bootBudget = 1582) ∨
    (row.segLen = 10000 ∧ row.bootCount = 25 ∧ row.bootBudget = 18066) ∨
    (row.segLen = 100000 ∧ row.bootCount = 65 ∧ row.bootBudget = 202349) ∨
    (row.segLen = 1000000 ∧ row.bootCount = 168 ∧ row.bootBudget = 2198343))

def bootBudgetBoundOK (row : Row) : Bool :=
  decide (row.bootBudget ≤ row.markSteps)

def bootPairsOK : Bool := rows.all bootPairOK
def bootBudgetConfigsOK : Bool := rows.all bootBudgetConfigOK
def bootBudgetBoundsOK : Bool := rows.all bootBudgetBoundOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem bootPairs_ok : bootPairsOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem bootBudgetConfigs_ok : bootBudgetConfigsOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem bootBudgetBounds_ok : bootBudgetBoundsOK = true := by decide

theorem row_bootBound_two (row : Row) (hrow : row ∈ rows) :
    2 ≤ row.bootBound := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, hboot, _, _, _⟩
  rcases hboot with hboot | hboot
  · omega
  · exact hboot.1

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
/-- The bootstrap list of every retained row is exactly the finite prime
table through its recorded bound. -/
theorem row_bootPrime (row : Row) (hrow : row ∈ rows) :
    PrimeTableInv (rowCfg row).bootPrimes row.bootBound := by
  have hall := (List.all_eq_true.mp bootPairs_ok) row hrow
  have hpair := of_decide_eq_true hall
  have heq : rootScanFrom [] 2 (row.bootBound - 1) =
      (rowCfg row).bootPrimes := by
    rcases hpair with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hbound, hcount⟩ <;>
      simp [rowCfg, hbound, hcount] <;> decide
  have hinv := rootScanFrom_primeTable (fuel := row.bootBound - 1)
    (ArraySegMobiusPrimeTable.empty) (w := 2) (by decide) (by decide)
  have hbound : 1 + (row.bootBound - 1) = row.bootBound := by
    have := row_bootBound_two row hrow
    omega
  simpa [heq, hbound] using hinv

theorem row_bootBudget (row : Row) (hrow : row ∈ rows) :
    ((rowCfg row).bootPrimes.map fun p => row.segLen / p + 2).sum ≤
      row.markSteps := by
  have hconfig := of_decide_eq_true
    ((List.all_eq_true.mp bootBudgetConfigs_ok) row hrow)
  have heq : ((rowCfg row).bootPrimes.map fun p => row.segLen / p + 2).sum =
      row.bootBudget := by
    rcases hconfig with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨hseg, hcount, hbudget⟩ <;>
      simp [rowCfg, hseg, hcount, hbudget] <;> decide
  rw [heq]
  exact of_decide_eq_true
    ((List.all_eq_true.mp bootBudgetBounds_ok) row hrow)

#print axioms bootPairs_ok
#print axioms bootBudgetConfigs_ok
#print axioms bootBudgetBounds_ok
#print axioms row_bootPrime
#print axioms row_bootBudget

end LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
