import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleLength

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
open LeanCompCert.Verified.Reflect (M)

theorem production_hi_pos : 0 < productionCursorCfg.hi := by
  change 0 < 100000000
  decide +kernel

theorem production_hi_word : productionCursorCfg.hi < M := by
  change 100000000 < M
  decide +kernel

theorem production_hi_sq_word :
    productionCursorCfg.hi * productionCursorCfg.hi < M := by
  change 100000000 * 100000000 < M
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
