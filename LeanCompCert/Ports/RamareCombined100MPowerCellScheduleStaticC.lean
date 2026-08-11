import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleStaticB

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
open LeanCompCert.Verified.Reflect (M)

theorem production_table_end_word :
    productionCursorCfg.tableLen + productionCursorCfg.tableBase < M := by
  have hbase : productionCursorCfg.tableBase = 14 * 999900 := rfl
  rw [hbase]
  have hsmall : 10001 + 14 * 999900 < M := by decide +kernel
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right productionCursorCfg_tableLen_le_10001
      (14 * 999900)) hsmall

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
