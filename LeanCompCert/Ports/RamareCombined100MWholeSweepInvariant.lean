import LeanCompCert.Ports.RamareCombined100MProductionInit
import LeanCompCert.Ports.RamareCombined100MBodyRefinement

/-!
# Whole-sweep invariant for the physical Ramaré program

The selected-cell marking proof was originally stated for the shape-sieve
body alone.  The production program executes the larger lambda/psi body on
every round.  This module proves that its arithmetic suffix frames the entire
marking invariant, then lifts the closed production marking induction to the
literal body used by `AProgram` and to an arbitrary window-boundary state.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-- The log/lambda/psi suffix writes neither the persistent power cursor nor
the seven-plane array.  It therefore preserves the complete selected-cell
marking invariant. -/
theorem ProductionMarkStateInv.arithmetic_frame
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (c : LambdaPsiSweep.Cfg) (k : Nat) :
    ProductionMarkStateInv w i round initial
      (arun k s (LambdaPsiSweep.arithmeticBody c)) := by
  let out := arun k s (LambdaPsiSweep.arithmeticBody c)
  have hreg (j : Nat)
      (hj : LambdaPsiSweep.ablockWritesReg j
        (LambdaPsiSweep.arithmeticBody c) = false) :
      out.regs j = s.regs j := by
    exact LambdaPsiSweep.arun_reg_frame k j
      (LambdaPsiSweep.arithmeticBody c) s hj
  have harr : out.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (LambdaPsiSweep.arithmeticBody c) s (by rfl)
  refine {
    observable := ?_
    table := ?_
    round_eq := ?_
    window_eq := ?_
    viol_le := ?_
    vmark_le := ?_
    last_failure_le := ?_ }
  · have hreset : resetPowerCellState productionCursorCfg i out =
        resetPowerCellState productionCursorCfg i s := by
      apply PowerCellState.ext
      · unfold resetPowerCellState resetPowerCursor machinePowerCursor
        rw [hreg rR (by rfl), hreg rW (by rfl), hreg rPi (by rfl),
          hreg rPow (by rfl), hreg rBase (by rfl), hreg rJ (by rfl)]
      · unfold resetPowerCellState Cfg.readPlaneCell
        rw [harr]
    exact hreset.trans h.observable
  · intro pi hpi
    rw [harr]
    exact h.table pi hpi
  · exact (hreg rR (by rfl)).trans h.round_eq
  · exact (hreg rW (by rfl)).trans h.window_eq
  · rw [hreg rViol (by rfl)]
    exact h.viol_le
  · rw [hreg rVMark (by rfl)]
    exact h.vmark_le
  · intro hpositive
    rw [hreg rVMark (by rfl)]
    exact h.last_failure_le hpositive

/-- One marking-phase iteration of the literal production lambda/psi body
advances the selected-cell invariant exactly as the shape-only body does. -/
theorem ProductionMarkStateInv.fullBody_step
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (logs : List LogCell) (k : Nat)
    (hi : i < productionCursorCfg.segLen)
    (hround : round < productionCursorCfg.markSteps)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hinitial : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable initial.cursor)
    (hmark :
      let pure := powerCellRun productionCursorCfg round w i
        productionPowerTable initial
      pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
        PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i (round + 1) initial
      (arun k s (LambdaPsiSweep.body c)) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  have hshape := h.step k hi hround hwM hinitial hmark
  have hframe := ProductionMarkStateInv.arithmetic_frame hshape c k
  dsimp only
  rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
  simpa only [c, ShapeSieve.Cfg.body, arun_append, List.append_assoc]
    using hframe

/-- The real production body, including its inactive arithmetic suffix,
preserves the closed marking invariant for every symbolic prefix of an
arbitrary production window. -/
theorem productionFullBodyMarkStateInv_run_closed
    (logs : List LogCell) (k w i fuel : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hfuel : fuel ≤ productionCursorCfg.markSteps)
    (h0 : ProductionMarkStateInv w i 0
      (productionInitialPowerCell w) s) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i fuel (productionInitialPowerCell w)
      (BodyRefinement.bodyRun k c fuel s) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  induction fuel with
  | zero => simpa [c] using h0
  | succ fuel ih =>
      have hprev := ih (by omega)
      have hnext := ProductionMarkStateInv.fullBody_step hprev logs k hi
        (by omega) hwM
        (productionInitialPowerCell_cursor_bounds w)
        (productionPowerCellRun_markPre w i fuel hi hnpos hnglobal)
      simpa [c, BodyRefinement.bodyRun] using hnext

/-- A generic zero-counter window boundary can run the complete physical
marking phase; no reference to the original program initializer remains. -/
theorem productionWindow_markInv
    (logs : List LogCell) (k w i : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i productionCursorCfg.markSteps
      (productionInitialPowerCell w)
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s) := by
  exact productionFullBodyMarkStateInv_run_closed logs k w i
    productionCursorCfg.markSteps s hi hwM hnpos hnglobal (Nat.le_refl _)
    (productionWindowStart_markInv w i s hround hwindow htable hempty
      hviol hvmark)

/-- If the physical mark-failure counter remains zero, the selected cell at
the end of the real marking phase is exactly the complete source row fold. -/
theorem productionWindow_cell_eq_cursorRows
    (logs : List LogCell) (k w i : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0)
    (hzero :
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s).regs
        rVMark = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    productionCursorCfg.readPlaneCell i
        (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s) =
      cursorRowsFold productionCursorCfg.segLen w i
        (factorRows productionCursorCfg.table) emptyPlaneCell := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let out := BodyRefinement.bodyRun k c productionCursorCfg.markSteps s
  have hinv := productionWindow_markInv logs k w i s hi hwM hnpos hnglobal
    hround hwindow htable hempty hviol hvmark
  have hcell := congrArg PowerCellState.cell hinv.observable
  change productionCursorCfg.readPlaneCell i out =
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps w i
      productionPowerTable (productionInitialPowerCell w)).cell at hcell
  dsimp only
  change productionCursorCfg.readPlaneCell i out =
    cursorRowsFold productionCursorCfg.segLen w i
      (factorRows productionCursorCfg.table) emptyPlaneCell
  rw [hcell]
  apply productionPowerCellRun_cell_eq_cursorRows_of_exhausted
    productionCursorCfg.markSteps w i hi hnpos hnglobal
  exact hinv.cursor_exhausted_of_vmark_zero hzero

end LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant
