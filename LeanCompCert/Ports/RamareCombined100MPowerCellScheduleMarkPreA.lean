import LeanCompCert.Ports.RamareCombined100MPowerCellSchedulePrefixBounds

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.Reflect (M)

/-- Every live selected round of the production cursor has the exact local
word precondition needed by the emitted cell update.  Rounds beyond the
compact phase-chain endpoint are the non-live sentinel, so the proof remains
symbolic even when `round` ranges over the larger fixed marking budget. -/
theorem productionPowerCellRun_markPre
    (w i round : Nat)
    (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi) :
    let pure := powerCellRun productionCursorCfg round w i
      productionPowerTable (productionInitialPowerCell w)
    pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
      PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell := by
  dsimp only
  let total := powerPhaseChainFuel productionCursorCfg.segLen w
    productionPowerPhases
  let initial := productionInitialPowerCell w
  let pure := powerCellRun productionCursorCfg round w i
    productionPowerTable initial
  intro hlive _hji
  exact powerCellRun_markPre_of_endpoint_bounds productionCursorCfg round total
    w i productionPowerTable initial (by
      change 0 < 100000000
      omega)
    (by simpa [initial] using productionInitialPowerCell_cursor_bounds w)
    (by simpa [initial] using productionInitialPowerCell_base_le_10000 w)
    (fun pi _hpi => productionPowerTable_le_10000 pi)
    (by simpa [total, initial] using
      productionPowerCellRun_phase_bounds w i hi hnpos hnglobal)
    (by simpa [total, initial] using productionPowerCellRun_phase_terminal w i)
    hlive

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
