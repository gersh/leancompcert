import LeanCompCert.Ports.RamareCombined100MProductionPhaseCheck

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
set_option maxRecDepth 20000 in
theorem productionPowerPhaseShard14 :
    productionPowerPhaseShardOK 2496 64 = true := by
  decide +kernel
end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
