import LeanCompCert.Ports.RamareCombined100MCellBounds

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

/-- The production mark counter is word-safe without reducing its
3.26-million-round emit-time budget computation in the kernel. -/
theorem productionCursorCfg_markSteps_lt_word :
    productionCursorCfg.markSteps < LeanCompCert.Verified.Reflect.M := by
  exact Cfg.ofChain_markSteps_lt_word 10001 999900 100 100000000

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
