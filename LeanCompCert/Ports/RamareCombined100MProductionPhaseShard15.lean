import LeanCompCert.Ports.RamareCombined100MProductionPhaseCheck

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
set_option maxRecDepth 20000 in
theorem productionPowerPhaseShard15 :
    productionPowerPhaseShardOK 2560 72 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem productionPowerPhaseEdgeChecks_drop_2632 :
    (productionPowerPhaseEdgeChecks.drop 2632).all id = true := by
  decide +kernel
end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
