import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassAdvance
import LeanCompCert.Ports.RamareCombined100MShapeHostClassAdvancePi

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionClassMarkBody_pi
    (fuel k : Nat) (s : AState)
    (hfuel : fuel < productionCursorCfg.segLen)
    (hclass : productionCursorCfg.markSteps ≤ s.regs rR)
    (hcursor : machinePowerCursor s = productionClassCursor fuel)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    (arun k s productionCursorCfg.markBody).regs rPi =
      productionCursorCfg.tableLen := by
  let c := productionCursorCfg
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let marked := arun k reset c.markCellPrefix
  have hcut := productionClassAdvanceWordPre fuel k s
    (Nat.le_of_lt hfuel) hclass hcursor hviol hvmark
  dsimp only at hcut
  let hpre := hcut.1
  have hmCursor : machinePowerCursor marked = productionClassCursor fuel :=
    hcut.2.1
  have hm10 : marked.regs 10 = 0 := hcut.2.2.1
  have hm25 : marked.regs 25 = 1 := hcut.2.2.2
  have hmPi : marked.regs rPi = c.tableLen := congrArg PowerCursor.pi hmCursor
  have hmPow : marked.regs rPow = 1 := congrArg PowerCursor.pow hmCursor
  have hmBase : marked.regs rBase = 1 := congrArg PowerCursor.base hmCursor
  have haPi := classAdvance_pi c k marked
    (fun pi => marked.arr (pi + c.tableBase)) hpre hm10 hm25
    hmPi hmPow hmBase
  rw [show productionCursorCfg.markBody = c.markBody by rfl,
    c.markBody_eq_phase_reset_active, arun_append, arun_append]
  change (arun k reset c.markActiveBody).regs rPi = _
  rw [Cfg.markActiveBody, arun_append, haPi]

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
