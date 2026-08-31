import LeanCompCert.Ports.RamareCombined100MShapeHostClassAddresses
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorStart

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionClassAddresses
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s)
    (len k : Nat) (hfuel : fuel < productionCursorCfg.segLen)
    (hN : w + fuel ≤ productionCursorCfg.hi)
    (hplanes : 13 * productionCursorCfg.segLen < len) :
    let marked := arun k s productionCursorCfg.markBody
    let addressed := arun k marked productionCursorCfg.classAddressBody
    addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
      addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
      addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
      addressed.regs 138 < len := by
  have hfuelNe : fuel ≠ productionCursorCfg.segLen := Nat.ne_of_lt hfuel
  have hround : s.regs rR = productionCursorCfg.markSteps + fuel := by
    rw [h.sweep.round_eq, if_neg hfuelNe]
  have hclass : productionCursorCfg.markSteps ≤ s.regs rR := by
    rw [hround]
    omega
  have hwindow : s.regs rW = w := by
    rw [h.sweep.window_eq, if_neg hfuelNe]
  have hR : s.regs rR < M := by
    rw [hround]
    have hp := productionCursorCfg_period_lt_word
    unfold Cfg.period at hp
    omega
  have hsum :
      s.regs rR - productionCursorCfg.markSteps + s.regs rW < M := by
    rw [hround, hwindow]
    simp only [Nat.add_sub_cancel_left]
    have hhi := productionCursorStaticWordBounds.2.1
    omega
  have hb (a : Nat) (ha : a ≤ 6) :
      s.regs rR - productionCursorCfg.markSteps +
        a * productionCursorCfg.segLen < M := by
    rw [hround]
    simp only [Nat.add_sub_cancel_left]
    change fuel + a * 999900 < M
    change fuel < 999900 at hfuel
    have hword : 7 * 999900 < M := by decide
    omega
  have hl (a : Nat) (ha : a ≤ 6) :
      s.regs rR - productionCursorCfg.markSteps +
        a * productionCursorCfg.segLen < len := by
    rw [hround]
    simp only [Nat.add_sub_cancel_left]
    change fuel + a * 999900 < len
    change fuel < 999900 at hfuel
    change 13 * 999900 < len at hplanes
    omega
  exact classAddresses_lt_of_classRound productionCursorCfg len k s hclass
    productionCursorCfg_markSteps_lt_word hR hsum
    (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega))
    (hb 4 (by omega)) (hb 5 (by omega)) (hb 6 (by omega))
    (hl 0 (by omega)) (by simpa using hl 1 (by omega))
    (hl 2 (by omega)) (hl 3 (by omega)) (hl 4 (by omega))
    (hl 5 (by omega)) (hl 6 (by omega))

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
