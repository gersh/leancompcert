import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassAdvance
import LeanCompCert.Ports.RamareCombined100MShapeHostClassAdvanceJ

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionClassMarkBody_j
    (fuel k : Nat) (s : AState) (hfuel : fuel < productionCursorCfg.segLen)
    (hclass : productionCursorCfg.markSteps ≤ s.regs rR)
    (hcursor : machinePowerCursor s = productionClassCursor fuel)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    (arun k s productionCursorCfg.markBody).regs rJ =
      productionCursorCfg.segLen + 1 + (fuel + 1) := by
  let c := productionCursorCfg
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let marked := arun k reset c.markCellPrefix
  have hcut := productionClassAdvanceWordPre fuel k s (Nat.le_of_lt hfuel)
    hclass hcursor hviol hvmark
  dsimp only at hcut
  let hpre := hcut.1
  have hmCursor : machinePowerCursor marked = productionClassCursor fuel := hcut.2.1
  have hmJ : marked.regs rJ = c.segLen + 1 + fuel :=
    congrArg PowerCursor.j hmCursor
  have haJ := classAdvance_j c k marked
    (fun pi => marked.arr (pi + c.tableBase)) hpre hcut.2.2.1 hcut.2.2.2
    (congrArg PowerCursor.pi hmCursor) (congrArg PowerCursor.pow hmCursor)
    (congrArg PowerCursor.base hmCursor) _ hmJ
  rw [show productionCursorCfg.markBody = c.markBody by rfl,
    c.markBody_eq_phase_reset_active, arun_append, arun_append]
  change (arun k reset c.markActiveBody).regs rJ =
    c.segLen + 1 + (fuel + 1)
  rw [Cfg.markActiveBody, arun_append, haJ]
  omega

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
