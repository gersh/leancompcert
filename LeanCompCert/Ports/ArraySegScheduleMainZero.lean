import LeanCompCert.Ports.ArraySegCanonicalSchedules

/-!
# Forgetting ordinary main windows from a padded root schedule

The root-table producer is often reused by a caller that runs a different
main-window consumer.  A schedule proved with any positive (or zero) ordinary
main fuel therefore canonically yields the same root schedule with main fuel
zero.  No program is evaluated here.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.ArraySegScheduleMainZero

open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedFull

/-- Retain all root-production facts and forget the ordinary main suffix. -/
theorem mainZero {c : Cfg} {bootBound bootFuel laterFuel valid mainFuel delta : Nat}
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      mainFuel delta) :
    PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid 0
      delta := by
  refine { h with
    mainIndexM := ?_
    mainBaseM := ?_ }
  · simpa using h.spanM
  · have hle : mainBase c bootFuel laterFuel delta ≤
        mainBase c bootFuel laterFuel delta + mainFuel * c.segLen :=
      Nat.le_add_right _ _
    have hlt := Nat.lt_of_le_of_lt hle h.mainBaseM
    simpa using hlt

#print axioms mainZero

end LeanCompCert.Ports.ArraySegScheduleMainZero
