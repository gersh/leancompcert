import LeanCompCert.Ports.RamareCombined100MShapeSieve

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-! The last cell is `30 = 2 * 3 * 5`; the convention keeps the first two
prime powers and leaves the third in `tail`. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeP).denote = some 2 := by decide

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
