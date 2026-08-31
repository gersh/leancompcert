import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassSweepCursor

/-!
# Cursor side of the production marking/classification seam

The public zero mark-failure result implies that the pure production cursor
reached its sentinel.  The existing marking invariant then identifies the
actual machine cursor at the classification boundary with that terminal
cursor, without evaluating the marking loop.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionWindow_classStart_cursor
    (logs : List LogCell) (k w : Nat) (s : AState)
    (hwM : w < M)
    (hn : ∀ i, i < productionCursorCfg.segLen → 0 < w + i)
    (hN : ∀ i, i < productionCursorCfg.segLen →
      w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0) (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : ∀ i, i < productionCursorCfg.segLen →
      productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0) (hvmark : s.regs rVMark = 0)
    (hmarkZero :
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun
      k c productionCursorCfg.markSteps s
    ProductionClassCursorInv 0 marked := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let marked := BodyRefinement.bodyRun k c productionCursorCfg.markSteps s
  have hi : 0 < productionCursorCfg.segLen := by
    change 0 < 999900
    omega
  have hinv := WholeSweepInvariant.productionWindow_markInv
    logs k w 0 s hi hwM (hn 0 hi) (hN 0 hi)
    hround hwindow htable (hempty 0 hi) hviol hvmark
  dsimp only at hinv hmarkZero
  have hviolZero : marked.regs rViol = 0 := by
    simpa only [marked, c] using hmarkZero
  have hvmarkZero : marked.regs rVMark = 0 := by
    have hle := hinv.vmark_le_viol
    change marked.regs rVMark ≤ marked.regs rViol at hle
    omega
  have hpi := hinv.cursor_exhausted_of_vmark_zero hvmarkZero
  have hpureEq := productionPowerCellRun_eq_phase_of_cursor_exhausted
    productionCursorCfg.markSteps w 0 hpi
  have hpureTerminal :
      (powerCellRun productionCursorCfg productionCursorCfg.markSteps
        w 0 productionPowerTable (productionInitialPowerCell w)).cursor =
        productionTerminalCursor := by
    rw [hpureEq]
    simpa [productionTerminalCursor, productionClassCursor] using
      productionPowerCellRun_phase_terminal w 0
  have hmarkedR : marked.regs rR = productionCursorCfg.markSteps :=
    hinv.round_eq
  have hmarkedRNe : marked.regs rR ≠ 0 := by
    rw [hmarkedR]
    exact Nat.ne_of_gt productionCursorCfg_markSteps_pos
  have hobs := hinv.observable
  rw [resetPowerCellState_eq_machinePowerCellState
    productionCursorCfg 0 marked hmarkedRNe] at hobs
  have hmachinePure := congrArg PowerCellState.cursor hobs
  apply ProductionClassCursorInv.start
  exact hmachinePure.trans hpureTerminal

/-- The existing source-level cell relation and the split cursor state start
together at the exact marking/classification boundary. -/
theorem productionWindow_classStart_withCursor
    (logs : List LogCell) (k w : Nat) (s : AState)
    (hwM : w < M) (hwindowM : w + productionCursorCfg.segLen < M)
    (hn : ∀ i, i < productionCursorCfg.segLen → 0 < w + i)
    (hN : ∀ i, i < productionCursorCfg.segLen →
      w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0) (hwindow : s.regs rW = w)
    (hzero : s.regs 0 = 0)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : ∀ i, i < productionCursorCfg.segLen →
      productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0) (hvmark : s.regs rVMark = 0)
    (hmarkZero :
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun k c productionCursorCfg.markSteps s
    ProductionClassSweepCursorInv w 0
      (marked.regs rViol) (marked.regs rVMark)
      (marked.regs rVShape) (marked.regs rSeen) marked := by
  refine ⟨productionWindow_classStart logs k w s hwM hwindowM hn hN
    hround hwindow hzero htable hempty hviol hvmark hmarkZero,
    productionWindow_classStart_cursor logs k w s hwM hn hN
      hround hwindow htable hempty hviol hvmark hmarkZero⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
