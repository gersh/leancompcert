import LeanCompCert.Ports.RamareCombined100MProductionInitBaseA
import LeanCompCert.Ports.RamareCombined100MProductionInitTableGeneric

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionTableCells_value
    (pi : Nat) (hpi : pi ≤ productionCursorCfg.tableLen)
    (x : Nat × Nat) (hx : x ∈ productionCursorCfg.tableCells)
    (haddr : x.1 = productionCursorCfg.tableBase + pi) :
    x.2 = productionPowerTable pi := by
  change x.2 = productionCursorCfg.table[pi]?.getD 1
  apply tableCells_value_generic productionCursorCfg.table
    productionCursorCfg.tableBase pi
  · simpa [Cfg.tableLen] using hpi
  · simpa only [Cfg.tableCells, Cfg.tableLen] using hx
  · exact haddr


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
