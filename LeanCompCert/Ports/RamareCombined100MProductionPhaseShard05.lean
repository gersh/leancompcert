import LeanCompCert.Ports.RamareCombined100MProductionPhaseCheck

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 20000 in
theorem productionPowerPhaseShard05 :
    productionPowerPhaseShardOK 1280 256 = true := by
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
