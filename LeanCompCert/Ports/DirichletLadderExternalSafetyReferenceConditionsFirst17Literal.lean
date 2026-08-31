import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsThrough17
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsDigestLiteral

/-! Contiguous literal-body discharge of reference flags 1--17. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem NoFailures.take17_of_slices {conditions : List Bool}
    (h15 : NoFailures (conditions.take 15))
    (h16 : NoFailures ((conditions.drop 15).take 1))
    (h17 : NoFailures ((conditions.drop 16).take 1)) :
    NoFailures (conditions.take 17) := by
  rw [show conditions.take 17 =
      conditions.take 15 ++ ((conditions.drop 15).take 1 ++
        (conditions.drop 16).take 1) by
    calc
      conditions.take 17 = conditions.take 15 ++
          (conditions.drop 15).take 2 := by
        simpa using (List.take_add (l := conditions) (i := 15) (j := 2))
      _ = conditions.take 15 ++ ((conditions.drop 15).take 1 ++
          (conditions.drop 16).take 1) := by
        rw [show (conditions.drop 15).take 2 =
            (conditions.drop 15).take 1 ++
              (conditions.drop 16).take 1 by
          simpa only [List.drop_drop] using (List.take_add
            (l := conditions.drop 15) (i := 1) (j := 1))]]
  intro b hb
  simp only [List.mem_append] at hb
  exact hb.elim (h15 b) fun hb' => hb'.elim (h16 b) (h17 b)

theorem historicalBody_take17_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).take 17) := by
  have outer := historicalBody_take15_and_flag17_noFailures_of_zero
    c words idx before st hidx hstatic hsafe hbudget hrel hbodyZero
  have digest := historicalBody_digest_noFailure_of_zero
    c words idx before st hidx hstatic hsafe hbudget hrel hbodyZero
  exact NoFailures.take17_of_slices outer.1 digest outer.2

end LeanCompCert.Ports.DirichletLadderExternalSafety
