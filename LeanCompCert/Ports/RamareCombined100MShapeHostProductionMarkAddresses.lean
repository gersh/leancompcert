import LeanCompCert.Ports.RamareCombined100MShapeHostMarkAddresses
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionMarkAddresses
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (len k : Nat) (hround : round < productionCursorCfg.markSteps)
    (hplanes : 13 * productionCursorCfg.segLen < len) :
    let phased := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let addressed := arun k reset productionCursorCfg.markAddressBody
    addressed.regs 30 < len ∧ addressed.regs 31 < len ∧
      addressed.regs 32 < len ∧ addressed.regs 33 < len ∧
      addressed.regs 34 < len ∧ addressed.regs 35 < len ∧
      addressed.regs 36 < len := by
  have hroundS : s.regs rR < productionCursorCfg.markSteps := by
    rw [h.round_eq]
    exact hround
  rcases productionStaticPlaneWordBounds with
    ⟨_, h7, h8, h9, h10, h11, h12, h13⟩
  exact markAddresses_lt_of_markRound productionCursorCfg len k s hroundS
    productionCursorCfg_markSteps_lt_word hplanes
    (fun _ hj => productionLivePlaneWordBounds hj)
    h7 h8 h9 h10 h11 h12 h13

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
