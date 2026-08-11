import LeanCompCert.Ports.RamareCombined100MShapeSieve

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeRest).denote = some 15 := by decide

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
