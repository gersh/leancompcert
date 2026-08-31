import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassMarkAddresses
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassAdvanceGuards
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassAddresses

/-!
# Production class-phase shape-host guards

This is deliberately only an assembly theorem.  Each dynamic address and
divisor cut is proved in a separate module, so elaborating this theorem does
not unfold the production marking/classification transition.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem productionClassGuards
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepCursorInv w fuel
      baseViol baseVMark baseVShape baseSeen s)
    (len k : Nat) (hfuel : fuel < productionCursorCfg.segLen)
    (hN : w + fuel ≤ productionCursorCfg.hi)
    (hviolM : baseViol < M) (hvmarkM : baseVMark < M)
    (hplanes : 13 * productionCursorCfg.segLen < len)
    (htableAlloc : productionCursorCfg.tableLen +
      productionCursorCfg.tableBase < len) :
    Guards productionCursorCfg len k s := by
  have ha := productionClassAdvanceGuards h len k hfuel
    hviolM hvmarkM htableAlloc
  exact {
    tableHead_ne := productionTableHead_word.1
    tableHead_word := productionTableHead_word.2
    markAddresses := productionClassMarkAddresses h len k hfuel hplanes
    tableAddress := ha.1
    nextPower_ne := ha.2
    classAddresses := productionClassAddresses h len k hfuel hN hplanes
  }

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
