import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleCursorBounds

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionCursorCfg_tableLen_le_10001 :
    productionCursorCfg.tableLen ≤ 10001 := by
  change productionCursorCfg.table.length ≤ 10001
  calc
    productionCursorCfg.table.length = productionPrimeTable.length :=
      congrArg List.length productionCursorCfg_table_eq
    _ = (trialPrimesBelow 10001).length :=
      congrArg List.length trialPrimesBelow_10001_eq_productionPrimeTable.symm
    _ ≤ 10001 := by
      simpa only [trialPrimesBelow, List.length_range] using
        List.length_filter_le trialPrime (List.range 10001)

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
