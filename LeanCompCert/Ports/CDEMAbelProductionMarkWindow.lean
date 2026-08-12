import LeanCompCert.Ports.CDEMAbelProductionMarkEntry
import LeanCompCert.Ports.CDEMAbelProductionMarkTable
import LeanCompCert.Ports.CDEMAbelMarkPlaneBudget

/-! # Production CDEM marking-window certificate -/

namespace LeanCompCert.Ports.CDEMAbelProductionMarkWindow

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelMarkPlane
open LeanCompCert.Ports.CDEMAbelMarkPlaneBudget
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionMarkEntry
open LeanCompCert.Ports.CDEMAbelProductionMarkTable

/-- The complete production `markSteps` block computes one exact finite
`Ref.deltaF` window.  The sole premise is the separately compiled scalar
budget certificate; the literal prime and sieve certificates stay behind
their small `.olean` interfaces. -/
theorem production_full_mark_window_eq_deltaF
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    ∀ j, j < productionCfg.segLen →
      out.arr (j + productionCfg.winBase) =
        (productionAfterSieve.arr (j + productionCfg.winBase) +
          Ref.deltaF productionCfg.kBound (1 + j)) % M := by
  apply bodyIterFrom_full_mark_window_eq_deltaF_of_compact_budget productionCfg
    productionCfg.sieveLen productionAfterSieve 1
    productionFirstMark_rep productionAfterSieve_table_live
    (fun j _ => productionAfterSieve_state.2.2
      (j + productionCfg.winBase))
  · change 25987624 < M
    decide
  · change 17142466 < M
    decide
  · omega
  · change 0 < 8845158
    decide
  · change 8845158 < M
    decide
  · change 0 < 1000000
    decide
  · change 1000000 < M
    decide
  · change 2 ≤ 199330
    decide
  · change 199330 < M
    decide
  · exact hbudget
  · change 199331 < M
    decide
  · change 1199330 < M
    decide
  · change 1199417 < M
    decide
  · change 70845158 < M
    decide
  · change 1 < M
    decide

/-- Compact first-cell projection of the complete production marking window.
This keeps the large configuration and dependent universal theorem behind a
small cached interface. -/
theorem production_full_mark_first_cell
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.arr (0 + productionCfg.winBase) =
      (productionAfterSieve.arr (0 + productionCfg.winBase) +
        Ref.deltaF productionCfg.kBound (1 + 0)) % M :=
  production_full_mark_window_eq_deltaF hbudget 0
    (by change 0 < 1000000; decide)

/-- Compact second-cell projection used by the first active handoff. -/
theorem production_full_mark_second_cell
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.arr (1 + productionCfg.winBase) =
      (productionAfterSieve.arr (1 + productionCfg.winBase) +
        Ref.deltaF productionCfg.kBound (1 + 1)) % M :=
  production_full_mark_window_eq_deltaF hbudget 1
    (by change 1 < 1000000; decide)

end LeanCompCert.Ports.CDEMAbelProductionMarkWindow
