import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleMarkPre

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Simultaneous machine invariant for one production marking window.  The
reset projection makes round zero and all later nonzero rounds uniform. -/
structure ProductionMarkStateInv
    (w i round : Nat) (initial : PowerCellState) (s : AState) : Prop where
  observable :
    resetPowerCellState productionCursorCfg i s =
      powerCellRun productionCursorCfg round w i productionPowerTable initial
  table : ∀ pi, pi ≤ productionCursorCfg.tableLen →
    s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi
  round_eq : s.regs rR = round
  window_eq : s.regs rW = w
  viol_le : s.regs rViol ≤ round
  vmark_le : s.regs rVMark ≤ round
  vmark_le_viol : s.regs rVMark ≤ s.regs rViol
  last_failure_le : 0 < round →
    productionCursorCfg.budgetFailure (round - 1)
      (powerCellRun productionCursorCfg round w i
        productionPowerTable initial).cursor.pi ≤ s.regs rVMark

/-- Any period-boundary state with an empty selected plane cell, the intact
production table, and zero failure counters is a valid fresh-window marking
state.  Unlike `productionInitState_markInv`, this constructor does not refer
to the program initializer, so it can be reused after a completed
classification sweep. -/
theorem productionWindowStart_markInv
    (w i : Nat) (s : AState)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0) :
    ProductionMarkStateInv w i 0 (productionInitialPowerCell w) s := by
  refine {
    observable := ?_
    table := htable
    round_eq := hround
    window_eq := hwindow
    viol_le := ?_
    vmark_le := ?_
    vmark_le_viol := ?_
    last_failure_le := ?_ }
  · apply PowerCellState.ext
    · simp only [resetPowerCellState, resetPowerCursor, hround, if_pos,
        productionInitialPowerCell]
      rw [productionPowerPhases_head, productionTable_head, hwindow]
      rfl
    · exact hempty
  · omega
  · omega
  · omega
  · omega

/-- The emitted phase/reset prefix realizes the reset projection recorded by
the simultaneous invariant. -/
theorem ProductionMarkStateInv.phaseReset_observable
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable
      (powerCellRun productionCursorCfg round w i
        productionPowerTable initial).cursor)
    (k : Nat) :
    let phased := arun k s (lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    machinePowerCellState productionCursorCfg i reset =
      powerCellRun productionCursorCfg round w i
        productionPowerTable initial := by
  let c := productionCursorCfg
  let pure := powerCellRun c round w i productionPowerTable initial
  have hmachineCursor (hn : s.regs rR ≠ 0) :
      machinePowerCursor s = pure.cursor := by
    have heq : machinePowerCellState c i s = pure := by
      rw [← resetPowerCellState_eq_machinePowerCellState c i s hn]
      exact h.observable
    exact congrArg PowerCellState.cursor heq
  rcases productionCursorStaticWordBounds with
    ⟨_hhiPos, hhiWord, _hhiSq, hK1, _haddr, hjpow⟩
  rcases productionTableHead_word with ⟨hp0, hp0M⟩
  have hreset := c.markPhaseResetBody_machinePowerCellState k s i
    productionCursorCfg_markSteps_lt_word hp0 hp0M
    (by
      intro hn
      have heq := congrArg PowerCursor.pi (hmachineCursor hn)
      change s.regs rPi = pure.cursor.pi at heq
      rw [heq]
      have hpi := hbounds.pi_le
      change pure.cursor.pi ≤ productionCursorCfg.tableLen at hpi
      omega)
    (by
      intro hn
      have heq := congrArg PowerCursor.pow (hmachineCursor hn)
      change s.regs rPow = pure.cursor.pow at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.pow_le hhiWord)
    (by
      intro hn
      have heq := congrArg PowerCursor.base (hmachineCursor hn)
      change s.regs rBase = pure.cursor.base at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.base_le hhiWord)
    (by
      intro hn
      have heq := congrArg PowerCursor.j (hmachineCursor hn)
      change s.regs rJ = pure.cursor.j at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.j_le (by omega))
  rw [Cfg.markPhaseResetBody, arun_append] at hreset
  simpa [c, pure] using hreset.trans h.observable

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
