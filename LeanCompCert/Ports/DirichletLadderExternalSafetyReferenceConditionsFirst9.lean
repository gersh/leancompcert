import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsFlag9Literal

/-! The first nine reference conditions follow from the literal body result. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem noFailures_take9_of_take8_and_flag9
    {conditions : List Bool}
    (h8 : NoFailures (conditions.take 8))
    (h9 : NoFailures ((conditions.drop 8).take 1)) :
    NoFailures (conditions.take 9) := by
  rw [show conditions.take 9 =
      conditions.take 8 ++ (conditions.drop 8).take 1 by
    simpa using (List.take_add (l := conditions) (i := 8) (j := 1))]
  intro b hb
  rw [List.mem_append] at hb
  exact hb.elim (h8 b) (h9 b)

theorem historicalBody_take9_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).take 9) := by
  exact noFailures_take9_of_take8_and_flag9
    (historicalBody_take8_noFailures_of_zero c words idx before st hidx hstatic
      hsafe hbudget hrel hbodyZero)
    (historicalBody_flag9_noFailure_of_zero c words idx before st hidx hstatic
      hsafe hbudget hrel hbodyZero)

end LeanCompCert.Ports.DirichletLadderExternalSafety
