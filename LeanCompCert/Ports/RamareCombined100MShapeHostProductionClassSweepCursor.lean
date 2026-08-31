import LeanCompCert.Ports.RamareCombined100MClassificationSweep
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorInvariant

/-!
# Classification sweep with the split cursor invariant

This wrapper strengthens the existing semantic classification invariant
without enlarging its already substantial record.  The cursor component is
proved independently and exposes the two host-totality facts requested by the
advance block.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

structure ProductionClassSweepCursorInv
    (w fuel baseViol baseVMark baseVShape baseSeen : Nat)
    (s : AState) : Prop where
  sweep : ProductionClassSweepInv w fuel
    baseViol baseVMark baseVShape baseSeen s
  cursor : ProductionClassCursorInv fuel s

theorem ProductionClassSweepCursorInv.pi_le
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s) :
    s.regs rPi ≤ productionCursorCfg.tableLen := h.cursor.pi_le

theorem ProductionClassSweepCursorInv.pow_ne
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s) :
    s.regs rPow ≠ 0 := h.cursor.pow_ne

set_option maxRecDepth 10000 in
theorem ProductionClassSweepCursorInv.step
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s)
    (logs : List LogCell) (k : Nat)
    (hfuel : fuel < productionCursorCfg.segLen)
    (hn : 0 < w + fuel) (hN : w + fuel ≤ productionCursorCfg.hi)
    (hviolM : baseViol < M) (hvmarkM : baseVMark < M)
    (hvshapeM : baseVShape < M)
    (hseenM : baseSeen + productionCursorCfg.segLen < M) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionClassSweepCursorInv w (fuel + 1)
      baseViol baseVMark baseVShape baseSeen
      (arun k s (LambdaPsiSweep.body c)) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  have hfuelNe : fuel ≠ productionCursorCfg.segLen := Nat.ne_of_lt hfuel
  have hround : s.regs rR = productionCursorCfg.markSteps + fuel := by
    rw [h.sweep.round_eq, if_neg hfuelNe]
  have hclass : productionCursorCfg.markSteps ≤ s.regs rR := by
    rw [hround]
    omega
  have hviol : s.regs rViol < M := by rw [h.sweep.viol_eq]; exact hviolM
  have hvmark : s.regs rVMark < M := by rw [h.sweep.vmark_eq]; exact hvmarkM
  refine ⟨h.sweep.step logs k hfuel hn hN hviolM hvmarkM hvshapeM hseenM,
    h.cursor.step logs k hfuel hclass hviol hvmark⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
