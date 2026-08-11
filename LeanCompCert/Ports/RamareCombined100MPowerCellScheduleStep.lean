import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

set_option maxRecDepth 2000
set_option maxHeartbeats 800000
/-- One actual emitted marking body preserves the simultaneous production
invariant and advances the pure selected-cell run by one step. -/
theorem ProductionMarkStateInv.step
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (k : Nat) (hi : i < productionCursorCfg.segLen)
    (hround : round < productionCursorCfg.markSteps)
    (hwM : w < M)
    (hinitial : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable initial.cursor)
    (hmark :
      let pure := powerCellRun productionCursorCfg round w i
        productionPowerTable initial
      pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
        PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell) :
    ProductionMarkStateInv w i (round + 1) initial
      (arun k s productionCursorCfg.body) := by
  let c := productionCursorCfg
  let pure := powerCellRun c round w i productionPowerTable initial
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let out := arun k s c.body
  have hhiPos : 0 < c.hi := productionCursorStaticWordBounds.1
  have hbounds : PowerCursorBounds c.segLen c.hi c.tableLen
      productionPowerTable pure.cursor := by
    exact powerCellRun_cursor_bounds c round w i productionPowerTable
      initial hinitial hhiPos
  have hresetState : machinePowerCellState c i reset = pure := by
    simpa [c, pure, phased, reset] using h.phaseReset_observable hbounds k
  have hcur : machinePowerCursor reset = pure.cursor :=
    congrArg PowerCellState.cursor hresetState
  have hresetW : reset.regs rW = w := by
    exact (arun_frame k rW c.markResetBody (by rfl) phased).trans
      ((arun_frame k rW (lift c.markPhaseBody) (by rfl) s).trans h.window_eq)
  have hroundS : s.regs rR < c.markSteps := by
    rw [h.round_eq]
    exact hround
  have hviolS : s.regs rViol ≤ s.regs rR := by
    rw [h.round_eq]
    exact h.viol_le
  have hvmarkS : s.regs rVMark ≤ s.regs rR := by
    rw [h.round_eq]
    exact h.vmark_le
  have hadvance := productionAdvanceWordPre_after_mark_prefix k s
    pure.cursor hroundS (by simpa [c, phased, reset] using hcur)
    hbounds h.table hviolS hvmarkS
  rcases productionStaticPlaneWordBounds with
    ⟨_hseg, h7, h8, h9, h10, h11, h12, h13⟩
  have hlive : pure.cursor.j < c.segLen →
      pure.cursor.j < M ∧ pure.cursor.j + c.segLen < M ∧
      pure.cursor.j + 2 * c.segLen < M ∧
      pure.cursor.j + 3 * c.segLen < M ∧
      pure.cursor.j + 4 * c.segLen < M ∧
      pure.cursor.j + 5 * c.segLen < M ∧
      pure.cursor.j + 6 * c.segLen < M := by
    intro hj
    exact productionLivePlaneWordBounds hj
  have hmarkReset : pure.cursor.j < c.segLen → pure.cursor.j = i →
      PlaneCellMarkPre (reset.regs rPow) (reset.regs rBase)
        (c.readPlaneCell (reset.regs rJ) reset) := by
    intro hj hji
    have hpow := congrArg PowerCursor.pow hcur
    have hbase := congrArg PowerCursor.base hcur
    have hjreg := congrArg PowerCursor.j hcur
    change reset.regs rPow = pure.cursor.pow at hpow
    change reset.regs rBase = pure.cursor.base at hbase
    change reset.regs rJ = pure.cursor.j at hjreg
    have hcell := congrArg PowerCellState.cell hresetState
    change c.readPlaneCell i reset = pure.cell at hcell
    rw [hpow, hbase, hjreg, hji, hcell]
    exact hmark hj hji
  have hbody := c.body_mark_powerCell_run k s productionPowerTable i
    hroundS productionCursorCfg_markSteps_lt_word hi pure.cursor
    (by simpa [phased, reset] using hcur) hlive
    h7 h8 h9 h10 h11 h12 h13
    (by simpa [phased, reset] using hmarkReset)
    (by simpa [phased, reset] using hadvance) hbounds.pi_le
  have hbodyState : machinePowerCellState c i out =
      powerCellStep c w i productionPowerTable pure := by
    simpa [out, phased, reset, hresetW, hresetState] using hbody
  have houtPi : out.regs rPi =
      (powerCellStep c w i productionPowerTable pure).cursor.pi := by
    have heq := congrArg (fun st => st.cursor.pi) hbodyState
    simpa [machinePowerCellState, machinePowerCursor] using heq
  have hpos := c.body_mark_position k s hroundS (by
      change 0 < 999900
      omega) productionCursorCfg_period_lt_word (by simpa [h.window_eq] using hwM)
  dsimp only at hpos
  have houtR : out.regs rR = round + 1 := by
    rw [hpos.1, h.round_eq]
  have houtW : out.regs rW = w := hpos.2.trans h.window_eq
  have hcounter := c.body_mark_counter_bounds k s productionPowerTable
    hroundS productionCursorCfg_markSteps_lt_word (by
      change 0 < 999900
      omega) productionCursorCfg_period_lt_word
    (by simpa [h.window_eq] using hwM) hviolS hvmarkS
    (by simpa [phased, reset] using hadvance)
  dsimp only at hcounter
  have hvmarkEq : out.regs rVMark = s.regs rVMark +
      c.budgetFailure round
        (powerCellStep c w i productionPowerTable pure).cursor.pi := by
    rw [hcounter.2.2.2, h.round_eq, houtPi]
  have hviolEq : out.regs rViol = s.regs rViol +
      c.budgetFailure round
        (powerCellStep c w i productionPowerTable pure).cursor.pi := by
    rw [hcounter.2.2.1, h.round_eq, houtPi]
  have houtReset : resetPowerCellState c i out =
      powerCellRun c (round + 1) w i productionPowerTable initial := by
    rw [resetPowerCellState_eq_machinePowerCellState c i out (by
      rw [houtR]
      omega)]
    rw [hbodyState]
    rfl
  dsimp only [c, out] at houtR houtW houtReset
  refine {
    observable := ?_
    table := ?_
    round_eq := houtR
    window_eq := houtW
    viol_le := ?_
    vmark_le := ?_
    vmark_le_viol := ?_
    last_failure_le := ?_ }
  · exact houtReset
  · intro pi hpi
    have hframe := c.body_mark_table_frame k s
      (pi + c.tableBase) hroundS productionCursorCfg_markSteps_lt_word
      (by change 0 < 999900; omega) pure.cursor
      (by simpa [phased, reset] using hcur) hlive
      h7 h8 h9 h10 h11 h12 h13 (by omega)
    exact hframe.trans (h.table pi hpi)
  · rw [hpos.1, h.round_eq] at hcounter
    exact hcounter.1
  · rw [hpos.1, h.round_eq] at hcounter
    exact hcounter.2.1
  · rw [hvmarkEq, hviolEq]
    exact Nat.add_le_add_right h.vmark_le_viol _
  · intro _hpositive
    have hfailure : c.budgetFailure round
        (powerCellStep c w i productionPowerTable pure).cursor.pi ≤
        out.regs rVMark := by
      rw [hvmarkEq]
      omega
    simpa only [Nat.add_sub_cancel, powerCellRun_succ, c, out, pure]
      using hfailure


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
