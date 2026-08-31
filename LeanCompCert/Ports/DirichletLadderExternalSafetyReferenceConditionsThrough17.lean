import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsMainLiteral

/-! Literal-body discharge through flag 17, with digest flag 16 kept separate. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem NoFailures.take {conditions : List Bool}
    (h : NoFailures conditions) (n : Nat) : NoFailures (conditions.take n) := by
  intro b hb
  exact h b (List.mem_of_mem_take hb)

theorem NoFailures.drop {conditions : List Bool}
    (h : NoFailures conditions) (n : Nat) : NoFailures (conditions.drop n) := by
  intro b hb
  exact h b (List.mem_of_mem_drop hb)

theorem referenceMainConditions_take6
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (referenceMainConditions c words st idx).take 6 =
      ((referenceConditions c words st idx).drop 9).take 6 := by rfl

theorem referenceMainConditions_flag17
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    ((referenceMainConditions c words st idx).drop 6).take 1 =
      ((referenceConditions c words st idx).drop 16).take 1 := by rfl

theorem historicalBody_take15_and_flag17_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).take 15) ∧
      NoFailures (((referenceConditions c words st idx).drop 16).take 1) := by
  have h9 := historicalBody_take9_noFailures_of_zero c words idx before st
    hidx hstatic hsafe hbudget hrel hbodyZero
  have hm := historicalBody_main_noFailures_of_zero c words idx before st
    hidx hstatic hsafe hbudget hrel hbodyZero
  have hm6 : NoFailures
      (((referenceConditions c words st idx).drop 9).take 6) := by
    have ht := hm.take 6
    rw [referenceMainConditions_take6] at ht
    exact ht
  have h15 : NoFailures ((referenceConditions c words st idx).take 15) := by
    rw [show (referenceConditions c words st idx).take 15 =
        (referenceConditions c words st idx).take 9 ++
          ((referenceConditions c words st idx).drop 9).take 6 by
      simpa using (List.take_add
        (l := referenceConditions c words st idx) (i := 9) (j := 6))]
    intro b hb
    rw [List.mem_append] at hb
    exact hb.elim (h9 b) (hm6 b)
  have h17 : NoFailures
      (((referenceConditions c words st idx).drop 16).take 1) := by
    have hd := (hm.drop 6).take 1
    rw [referenceMainConditions_flag17] at hd
    exact hd
  exact ⟨h15, h17⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety
