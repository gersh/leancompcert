import LeanCompCert.Ports.RamareCombined100MPowerCellSchedulePrefixBoundsB
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleTerminalGeneric

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Any production run which has reached the sentinel is the same complete
selected-cell state as the compact phase-chain endpoint.  Totality of the
natural-number order and terminal fixed-point slack avoid comparing either
fuel by reduction. -/
theorem productionPowerCellRun_eq_phase_of_cursor_exhausted
    (fuel w i : Nat)
    (hpi : (powerCellRun productionCursorCfg fuel w i productionPowerTable
      (productionInitialPowerCell w)).cursor.pi =
        productionCursorCfg.tableLen) :
    powerCellRun productionCursorCfg fuel w i productionPowerTable
        (productionInitialPowerCell w) =
      powerCellRun productionCursorCfg
        (powerPhaseChainFuel productionCursorCfg.segLen w
          productionPowerPhases)
        w i productionPowerTable (productionInitialPowerCell w) := by
  have hhi : 1 ≤ productionCursorCfg.hi := by
    change 1 ≤ 100000000
    omega
  let c := productionCursorCfg
  let initial := productionInitialPowerCell w
  let total := powerPhaseChainFuel c.segLen w productionPowerPhases
  have hfinalTerminal : (powerCellRun c fuel w i productionPowerTable initial).cursor =
      { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 } := by
    apply powerCellRun_terminal_shape c fuel w i productionPowerTable initial
      (productionInitialPowerCell_terminal_shape w)
      productionPowerTable_sentinel
    · exact hhi
    · exact hpi
  have hendpointTerminal :
      (powerCellRun c total w i productionPowerTable initial).cursor =
      { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 } := by
    exact productionPowerCellRun_phase_terminal w i
  exact powerCellRun_eq_of_terminal c fuel total w i productionPowerTable
    initial hhi hfinalTerminal hendpointTerminal



end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
