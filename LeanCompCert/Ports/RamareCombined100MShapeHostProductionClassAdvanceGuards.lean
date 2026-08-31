import LeanCompCert.Ports.RamareCombined100MShapeHostAdvanceGuards
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorStart

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionClassAdvanceGuards
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s)
    (len k : Nat) (hfuel : fuel < productionCursorCfg.segLen)
    (hviolM : baseViol < M) (hvmarkM : baseVMark < M)
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
  have hfuelNe : fuel ≠ productionCursorCfg.segLen := Nat.ne_of_lt hfuel
  have hclass : productionCursorCfg.markSteps ≤ s.regs rR := by
    rw [h.sweep.round_eq, if_neg hfuelNe]
    omega
  have hviol : s.regs rViol < M := by rw [h.sweep.viol_eq]; exact hviolM
  have hvmark : s.regs rVMark < M := by rw [h.sweep.vmark_eq]; exact hvmarkM
  have hcut := productionClassAdvanceWordPre fuel k s (Nat.le_of_lt hfuel)
    hclass h.cursor.machineCursor hviol hvmark
  dsimp only at hcut ⊢
  let phased := arun k s
    (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
  let reset := arun k phased productionCursorCfg.markResetBody
  let marked := arun k reset productionCursorCfg.markCellPrefix
  exact ⟨tableAddress_lt_of_advanceWordPre productionCursorCfg len k marked
      (fun pi => marked.arr (pi + productionCursorCfg.tableBase)) hcut.1
      htableAlloc,
    nextPower_ne_of_advanceWordPre productionCursorCfg k marked
      (fun pi => marked.arr (pi + productionCursorCfg.tableBase)) hcut.1⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
