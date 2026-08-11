import LeanCompCert.Ports.RamareCombined100MLogSweep

namespace LeanCompCert.Ports.RamareCombined100M.LogSweep

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (smokeProbe rLogU).denote = some expectedU := by decide

end LeanCompCert.Ports.RamareCombined100M.LogSweep
