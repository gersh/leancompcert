import LeanCompCert.Ports.RamareCombined100MProductionPhaseCheck

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 20000 in
theorem productionPowerPhaseShard10 :
    productionPowerPhaseShardOK 2048 128 = true := by
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
