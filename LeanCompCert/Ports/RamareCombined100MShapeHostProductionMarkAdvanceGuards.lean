import LeanCompCert.Ports.RamareCombined100MShapeHostAdvanceGuards
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionMarkAdvanceGuards
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable
      (powerCellRun productionCursorCfg round w i
        productionPowerTable initial).cursor)
    (len k : Nat) (hround : round < productionCursorCfg.markSteps)
    (htableAlloc : productionCursorCfg.tableLen +
      productionCursorCfg.tableBase < len) :
    let phased := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let marked := arun k reset productionCursorCfg.markCellPrefix
    let selected := arun k marked productionCursorCfg.markAdvanceSelectBody
    let loaded := arun k selected productionCursorCfg.markAdvanceLoadBody
    (arun k selected (markAdvanceLoadPrefix productionCursorCfg)).regs 95 < len ∧
      (arun k loaded Cfg.markAdvanceValueBody).regs rPow ≠ 0 := by
  let pure := powerCellRun productionCursorCfg round w i
    productionPowerTable initial
  have hstate := h.phaseReset_observable hbounds k
  have hcur :
      let phased := arun k s
        (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
      let reset := arun k phased productionCursorCfg.markResetBody
      machinePowerCursor reset = pure.cursor := by
    exact congrArg PowerCellState.cursor hstate
  have hroundS : s.regs rR < productionCursorCfg.markSteps := by
    rw [h.round_eq]
    exact hround
  have hviol : s.regs rViol ≤ s.regs rR := by rw [h.round_eq]; exact h.viol_le
  have hvmark : s.regs rVMark ≤ s.regs rR := by rw [h.round_eq]; exact h.vmark_le
  have hpre := productionAdvanceWordPre_after_mark_prefix k s pure.cursor
    hroundS hcur hbounds h.table hviol hvmark
  dsimp only at hpre ⊢
  let phased := arun k s
    (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
  let reset := arun k phased productionCursorCfg.markResetBody
  let marked := arun k reset productionCursorCfg.markCellPrefix
  exact ⟨tableAddress_lt_of_advanceWordPre productionCursorCfg len k marked
      productionPowerTable hpre htableAlloc,
    nextPower_ne_of_advanceWordPre productionCursorCfg k marked
      productionPowerTable hpre⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
