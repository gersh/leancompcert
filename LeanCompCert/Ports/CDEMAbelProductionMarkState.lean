import LeanCompCert.Ports.CDEMAbelProductionMarkWindow

/-! # Production CDEM state after the complete marking block -/

namespace LeanCompCert.Ports.CDEMAbelProductionMarkState

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkPlaneBudget
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionMarkEntry
open LeanCompCert.Ports.CDEMAbelProductionMarkTable

/-- Exact pure marking-state representation after all production marking
iterations, including the certified terminal slack. -/
theorem production_full_mark_state :
    MarkStateRep productionCfg 1 productionCfg.markSteps
      ((MarkState.first productionCfg productionAfterSieve).iter productionCfg
        1 (productionCfg.markSteps - 1))
      (bodyIterFrom productionCfg productionCfg.sieveLen
        productionCfg.markSteps productionAfterSieve) := by
  apply bodyIterFrom_full_mark_state productionCfg productionCfg.sieveLen
    productionAfterSieve 1 productionFirstMark_rep
    productionAfterSieve_table_live
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
  · change 0 < 199330
    decide
  · change 199330 < M
    decide
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

/-- Source-visible register state at the first accumulation iteration. -/
theorem productionAfterMark_cursor :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.regs rR = productionCfg.markSteps ∧
      out.regs rW = 1 ∧ out.regs rC = 0 ∧ out.regs rZero = 0 := by
  exact ⟨production_full_mark_state.periodCursor,
    production_full_mark_state.window, production_full_mark_state.cell,
    production_full_mark_state.zero⟩

/-- Every register and array cell remains a valid machine word at the first
accumulation iteration. -/
theorem productionAfterMark_word :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    (∀ j, out.regs j < M) ∧ ∀ j, out.arr j < M := by
  exact bodyIterFrom_word productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
    productionAfterSieve_state.2.1 productionAfterSieve_state.2.2

end LeanCompCert.Ports.CDEMAbelProductionMarkState
