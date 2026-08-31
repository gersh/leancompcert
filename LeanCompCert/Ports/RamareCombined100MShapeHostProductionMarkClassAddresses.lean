import LeanCompCert.Ports.RamareCombined100MShapeHostClassAddresses
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionMarkClassAddresses
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (len k : Nat) (hround : round < productionCursorCfg.markSteps)
    (hplanes : 13 * productionCursorCfg.segLen < len) :
    let marked := arun k s productionCursorCfg.markBody
    let addressed := arun k marked productionCursorCfg.classAddressBody
    addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
      addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
      addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
      addressed.regs 138 < len := by
  have hroundS : s.regs rR < productionCursorCfg.markSteps := by
    rw [h.round_eq]
    exact hround
  rcases productionStaticPlaneWordBounds with
    ⟨_, h7, h8, h9, h10, h11, h12, h13⟩
  exact classAddresses_lt_of_markRound productionCursorCfg len k s hroundS
    productionCursorCfg_markSteps_lt_word hplanes
    h7 h8 h9 h10 h11 h12 h13

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
