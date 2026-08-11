import LeanCompCert.Ports.RamareCombined100MWholeSweepInvariant
import LeanCompCert.Ports.RamareCombined100MWholeSweepInitGeneric

/-!
# Production initializer equivalence

The executable whole-sweep initializer uses the certified literal prime table.
This separately compiled seam proves that it denotes the initializer emitted
by the original generated production descriptor.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

open LeanCompCert.Verified.ArrayState (initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun)
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionPhysicalInitState_eq_generated
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed) :
    productionPhysicalInitState logs seed =
      arun 0 initialAState
        (LambdaPsiSweep.init
          ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg) seed) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  unfold productionPhysicalInitState
  rw [← productionCursorCfg_eq_certified]
  change seededInitState c seed productionInitState =
    arun 0 initialAState (LambdaPsiSweep.init c seed)
  exact (lambdaPsi_init_run_eq c seed productionInitState
    productionInitState_eq_generated).symm

end LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant
