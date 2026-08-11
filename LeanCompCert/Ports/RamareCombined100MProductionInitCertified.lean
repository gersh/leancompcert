import LeanCompCert.Ports.RamareCombined100MProductionInitBase

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.ArrayState (AState initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun)

/-- The production initializer expressed with the independently certified
literal prime table. -/
def certifiedProductionInitState : AState :=
  arun 0 initialAState certifiedProductionCursorCfg.init

theorem productionInitState_eq_certified :
    productionInitState = certifiedProductionInitState := by
  rfl

/-- Literal-table form of the initializer lookup theorem. -/
theorem certifiedProductionInitState_table (pi : Nat)
    (hpi : pi ≤ certifiedProductionCursorCfg.tableLen) :
    certifiedProductionInitState.arr
        (certifiedProductionCursorCfg.tableBase + pi) =
      certifiedProductionPowerTable pi := by
  unfold certifiedProductionInitState
  apply arun_cfg_init_table certifiedProductionCursorCfg
    certifiedProductionPowerTable pi
  · intro x hx
    rw [← productionCursorCfg_eq_certified] at hx
    exact productionTableCells_word x hx
  · rw [← productionCursorCfg_eq_certified,
      ← productionPowerTable_eq_certified]
    apply productionTableCell_mem
    simpa [productionCursorCfg_eq_certified] using hpi
  · intro x hx haddr
    rw [← productionCursorCfg_eq_certified] at hx haddr
    rw [← productionPowerTable_eq_certified]
    apply productionTableCells_value
    · simpa [productionCursorCfg_eq_certified] using hpi
    · exact hx
    · exact haddr

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
