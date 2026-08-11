import LeanCompCert.Ports.RamareCombined100MLambdaPsiSweep

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

set_option maxRecDepth 120000 in
set_option maxHeartbeats 8000000 in
example : (program smokeCfg smokeSeed).denote = some 0 := by decide

end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep
