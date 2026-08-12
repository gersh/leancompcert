import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckCompile
import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckSpec
import LeanCompCert.Verified.Package

/-!
# CompCert run certificate for the production CDEM Abel marking budget

The sole admission is the physical result of compiling and running the exact
rolled `Reflect.Program`.  The verified compiler/lowering bridge and the
source re-blocking theorem then identify that word with `budgetAtMod len`.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetProductionCertificate

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

set_option maxRecDepth 20000000

def productionComputation : Computation :=
  program.toComputation "CDEMAbelMarkBudgetProduction" program_wf

/-- CompCert 3.17 returned the independently recorded production marking
budget after `88,701,405` rolled scalar rounds. -/
axiom cdemAbelMarkBudget_compcert_run :
  productionComputation.Returns ((8723967 : Nat) : Int)

theorem program_denote_production : program.denote = some 8723967 := by
  exact (toComputation_returns program "CDEMAbelMarkBudgetProduction"
    program_wf 8723967).mp cdemAbelMarkBudget_compcert_run

theorem budgetAtMod_production : budgetAtMod len = 8723967 := by
  have h : some (budgetAtMod len) = some 8723967 :=
    program_denote_budgetAtMod.symm.trans program_denote_production
  exact Option.some.inj h

theorem budgetAt_production : budgetAt len = 8723967 := by
  have h := budgetAtMod_production
  rw [budgetAtMod_eq, Nat.mod_eq_of_lt budgetAt_len_lt_M] at h
  exact h

end LeanCompCert.Ports.CDEMAbelMarkBudgetProductionCertificate
