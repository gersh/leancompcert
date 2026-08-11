import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleStaticC

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve
open LeanCompCert.Verified.Reflect (M)

theorem production_cursor_span_word :
    productionCursorCfg.segLen + 2 * productionCursorCfg.hi < M := by
  change 999900 + 2 * 100000000 < M
  decide +kernel

/-- Closed production-scale word facts that do not require evaluating the
prime table or mark budget. -/
theorem productionCursorStaticWordBounds :
    0 < productionCursorCfg.hi ∧
      productionCursorCfg.hi < M ∧
      productionCursorCfg.hi * productionCursorCfg.hi < M ∧
      productionCursorCfg.tableLen + 1 < M ∧
      productionCursorCfg.tableLen + productionCursorCfg.tableBase < M ∧
      productionCursorCfg.segLen + 2 * productionCursorCfg.hi < M :=
  ⟨production_hi_pos, production_hi_word, production_hi_sq_word,
    production_tableLen_succ_word, production_table_end_word,
    production_cursor_span_word⟩

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
