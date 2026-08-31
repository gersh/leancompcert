import LeanCompCert.Ports.RamareCombined100MShapeHostMarkAddresses
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorStart

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionClassMarkAddresses
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s)
    (len k : Nat) (hfuel : fuel < productionCursorCfg.segLen)
    (hplanes : 13 * productionCursorCfg.segLen < len) :
    let phased := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let addressed := arun k reset productionCursorCfg.markAddressBody
    addressed.regs 30 < len ∧ addressed.regs 31 < len ∧
      addressed.regs 32 < len ∧ addressed.regs 33 < len ∧
      addressed.regs 34 < len ∧ addressed.regs 35 < len ∧
      addressed.regs 36 < len := by
  have hfuelNe : fuel ≠ productionCursorCfg.segLen := Nat.ne_of_lt hfuel
  have hround : productionCursorCfg.markSteps ≤ s.regs rR := by
    rw [h.sweep.round_eq, if_neg hfuelNe]
    omega
  rcases productionStaticPlaneWordBounds with
    ⟨_, h7, h8, h9, h10, h11, h12, h13⟩
  exact markAddresses_lt_of_classRound productionCursorCfg len k s hround
    productionCursorCfg_markSteps_lt_word hplanes
    h7 h8 h9 h10 h11 h12 h13

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
