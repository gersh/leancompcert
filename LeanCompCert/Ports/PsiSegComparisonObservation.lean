import LeanCompCert.Ports.PsiSegClauseTelescope

/-!
# Pointwise observations from the segmented psi failure trace

The telescope records the exact failure bits emitted by the production
comparison blocks.  This module turns a zero live bit back into the ordinary
integer inequality tested at that event.  It evaluates no campaign range.
-/

namespace LeanCompCert.Ports.PsiSegComparisonObservation

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.PsiSegSieve
open LeanCompCert.Ports.PsiSegClauseCheck
open LeanCompCert.Ports.PsiSegClauseTelescope

/-- A zero live lower failure bit is exactly the non-strict lower comparison
at the literal `beforeLower` boundary. -/
theorem lowerBound_of_failureAt_zero (c : PsiCfg) (idx : Nat) (s : AState)
    (hfin : (beforeLower c idx s).regs 285 = 1)
    (hzero : lowerFailureAt c idx s = 0) :
    bias16Of c.sc - lowerThreshold c.sc ((beforeLower c idx s).regs rSq) ≤
      shiftedD ((beforeLower c idx s).regs rDlo)
        ((beforeLower c idx s).regs rDhi) := by
  apply Nat.le_of_not_gt
  intro hlt
  simp [lowerFailureAt, lowerFailure, hfin, hlt] at hzero

/-- A zero live upper failure bit is exactly the unsigned 128-bit comparison
at the literal `beforeUpperCompare` boundary. -/
theorem upperPairBound_of_failureAt_zero (c : PsiCfg) (idx : Nat) (s : AState)
    (hfin : (beforeUpperCompare c idx s).regs 285 = 1)
    (haLo : (beforeUpperCompare c idx s).regs 410 < M)
    (hbLo : (beforeUpperCompare c idx s).regs 428 < M)
    (hzero : upperFailureAt c idx s = 0) :
    pairValue ((beforeUpperCompare c idx s).regs 410)
        ((beforeUpperCompare c idx s).regs 414) ≤
      pairValue ((beforeUpperCompare c idx s).regs 428)
        ((beforeUpperCompare c idx s).regs 431) := by
  have hpass : pairGreater ((beforeUpperCompare c idx s).regs 410)
      ((beforeUpperCompare c idx s).regs 414)
      ((beforeUpperCompare c idx s).regs 428)
      ((beforeUpperCompare c idx s).regs 431) = false := by
    cases hp : pairGreater ((beforeUpperCompare c idx s).regs 410)
        ((beforeUpperCompare c idx s).regs 414)
        ((beforeUpperCompare c idx s).regs 428)
        ((beforeUpperCompare c idx s).regs 431)
    · rfl
    · simp [upperFailureAt, upperFailure, hfin, hp] at hzero
  exact pairValue_le_of_not_greater _ _ _ _ haLo hbLo hpass

#print axioms lowerBound_of_failureAt_zero
#print axioms upperPairBound_of_failureAt_zero

end LeanCompCert.Ports.PsiSegComparisonObservation
