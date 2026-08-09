import LeanCompCert.Ports.RamareCombined100MCursorMachine

/-!
# Exact production phase witness for the Ramaré 100-million cursor

The generic power-aware cursor machine compiles cheaply.  This separate
module contains the one deliberately larger kernel check which materializes
the closed production descriptor.  Splitting it keeps ordinary refinement
development and downstream generic users away from that high-water check.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def productionCursorCfg : Cfg :=
  Cfg.ofChain 10001 999900 100 100000000

def productionPowerPhases : List PowerPhase :=
  tablePowerPhases productionCursorCfg.hi productionCursorCfg.table

def productionPowerTable (pi : Nat) : Nat :=
  (productionCursorCfg.table[pi]?).getD 1

set_option maxRecDepth 20000 in
/-- Kernel-checked finite witness that the exact production phase list takes
only the emitted bump/load branches and ends at the explicit sentinel.  This
checks a few thousand phase descriptors, never the 3.26-million-round mark
loop. -/
theorem productionPowerPhaseChain :
    PowerPhaseChain productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable productionPowerPhases := by
  apply PowerPhaseChain.of_check
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
