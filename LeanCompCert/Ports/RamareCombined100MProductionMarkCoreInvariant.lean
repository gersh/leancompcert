import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant

/-!
# Policy-independent production marking invariant

This is the lightweight physical cursor invariant used by the fail-closed V3
wrapper.  It lives with the source program so totality proofs can depend on
the exact same state relation without importing the receipt/shard layer.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)

structure ProductionMarkCoreInv
    (w i round : Nat) (initial : PowerCellState) (s : AState) : Prop where
  observable :
    resetPowerCellState productionCursorCfg i s =
      powerCellRun productionCursorCfg round w i productionPowerTable initial
  table : ∀ pi, pi ≤ productionCursorCfg.tableLen →
    s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi
  round_eq : s.regs rR = round
  window_eq : s.regs rW = w
  zero_eq : s.regs 0 = 0
  vshape_zero : s.regs rVShape = 0
  seen_zero : s.regs rSeen = 0
  viol_le : s.regs rViol ≤ round
  vmark_le : s.regs rVMark ≤ round
  last_failure_le : 0 < round →
    productionCursorCfg.budgetFailure (round - 1)
      (powerCellRun productionCursorCfg round w i
      productionPowerTable initial).cursor.pi ≤ s.regs rVMark

theorem ProductionMarkCoreInv.cursor_exhausted_of_vmark_zero
    {w i : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkCoreInv w i productionCursorCfg.markSteps initial s)
    (hzero : s.regs rVMark = 0) :
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps w i
      productionPowerTable initial).cursor.pi =
        productionCursorCfg.tableLen := by
  let pi := (powerCellRun productionCursorCfg
    productionCursorCfg.markSteps w i productionPowerTable initial).cursor.pi
  have hfailure := h.last_failure_le productionCursorCfg_markSteps_pos
  change productionCursorCfg.budgetFailure
    (productionCursorCfg.markSteps - 1) pi ≤ s.regs rVMark at hfailure
  by_cases heq : pi = productionCursorCfg.tableLen
  · simpa only [pi] using heq
  · have hone : productionCursorCfg.budgetFailure
        (productionCursorCfg.markSteps - 1) pi = 1 := by
      simp [Cfg.budgetFailure, eqBit, neBit, heq]
    rw [hone, hzero] at hfailure
    omega

theorem productionWindowStart_markCoreInv
    (w i : Nat) (s : AState)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hzero : s.regs 0 = 0)
    (hvshape : s.regs rVShape = 0)
    (hseen : s.regs rSeen = 0)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0) :
    ProductionMarkCoreInv w i 0 (productionInitialPowerCell w) s := by
  refine {
    observable := ?_
    table := htable
    round_eq := hround
    window_eq := hwindow
    zero_eq := hzero
    vshape_zero := hvshape
    seen_zero := hseen
    viol_le := by omega
    vmark_le := by omega
    last_failure_le := by omega }
  apply PowerCellState.ext
  · simp only [resetPowerCellState, resetPowerCursor, hround, if_pos,
      productionInitialPowerCell]
    rw [productionPowerPhases_head, productionTable_head, hwindow]
    rfl
  · exact hempty

theorem ProductionMarkCoreInv.phaseReset_observable
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkCoreInv w i round initial s)
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
