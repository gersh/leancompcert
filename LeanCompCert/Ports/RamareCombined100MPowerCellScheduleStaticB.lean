import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleStaticA

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
open LeanCompCert.Verified.Reflect (M)

theorem production_tableLen_succ_word :
    productionCursorCfg.tableLen + 1 < M := by
  have hsmall : 10001 + 1 < M := by decide +kernel
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right productionCursorCfg_tableLen_le_10001 1) hsmall

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
