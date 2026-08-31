import LeanCompCert.Ports.RamareCombined100MShapeHostProductionMarkAddresses
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionMarkAdvanceGuards
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionMarkClassAddresses

/-!
# Production marking-phase shape-host guards

Only previously compiled field theorems are assembled here.  In particular,
this file does not reduce `powerCellRun` or either production loop.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionMarkGuards
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable
      (powerCellRun productionCursorCfg round w i
        productionPowerTable initial).cursor)
    (len k : Nat) (hround : round < productionCursorCfg.markSteps)
    (hplanes : 13 * productionCursorCfg.segLen < len)
    (htableAlloc : productionCursorCfg.tableLen +
      productionCursorCfg.tableBase < len) :
    Guards productionCursorCfg len k s := by
  have ha := productionMarkAdvanceGuards h hbounds len k hround htableAlloc
  exact {
    tableHead_ne := productionTableHead_word.1
    tableHead_word := productionTableHead_word.2
    markAddresses := productionMarkAddresses h len k hround hplanes
    tableAddress := ha.1
    nextPower_ne := ha.2
    classAddresses := productionMarkClassAddresses h len k hround hplanes
  }

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
