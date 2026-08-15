import LeanCompCert.Ports.PsiRuntimePrimeLogInitSemantics

/-!
# Reset/preserve plus one compiled psi fixed-log round

This module composes the small reset/preserve proof with the already verified
literal round.  It gives one symbolic recurrence step without evaluating any
prime table or production loop.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.LogFixed

/-- The first compiled round installs the normalized prime and performs the
first exact fixed-log recurrence step. -/
theorem psiPrimeLogCore_start_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (n e : Nat)
    (hstart : s.regs 12 = 1) (hn : s.regs 16 = n) (he : s.regs 18 = e)
    (he62 : e ≤ 62)
    (hxlo : B62 ≤ n <<< (62 - e))
    (hxhi : n <<< (62 - e) < B63) :
    let out := arun index s (psiPrimeLogCore m)
    out.regs primeXm = (logIter (n <<< (62 - e)) 1).1 ∧
      out.regs primeAa = (logIter (n <<< (62 - e)) 1).2 ∧
      out.arr = s.arr := by
  have hnormM : n <<< (62 - e) < M :=
    Nat.lt_trans hxhi (by decide)
  let mid := arun index s (psiPrimeLogInit m)
  have hi := psiPrimeLogInit_start_run m index s n e hstart hn he
    he62 hnormM
  have hr := psiPrimeLogRound_run_of_range m index mid
    (n <<< (62 - e)) 0 hi.1 hi.2.1 hxlo hxhi (by decide)
  rw [psiPrimeLogCore_eq_stages, arun_append]
  exact ⟨by simpa only [logIter, logStep] using hr.1,
    by simpa only [logIter, logStep, Nat.shiftLeft_eq, Nat.zero_mul,
      Nat.mul_zero, Nat.zero_add]
      using hr.2.1,
    hr.2.2.trans hi.2.2⟩

/-- A later compiled round preserves the recurrence state and advances it by
one. -/
theorem psiPrimeLogCore_continue_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (n e x0 j : Nat)
    (hstart : s.regs 12 = 0) (hn : s.regs 16 = n) (he : s.regs 18 = e)
    (hx : s.regs primeXm = (logIter x0 j).1)
    (ha : s.regs primeAa = (logIter x0 j).2)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) (hj : j < 62) :
    let out := arun index s (psiPrimeLogCore m)
    out.regs primeXm = (logIter x0 (j + 1)).1 ∧
      out.regs primeAa = (logIter x0 (j + 1)).2 ∧
      out.arr = s.arr := by
  have hrange := psiPrimeLog_logIter_fst_range x0 hxlo hxhi j
  have haLt := logIter_snd_lt_two_pow x0 j
  have haBound : (logIter x0 j).2 < B62 := by
    have hjPow : 2 ^ j ≤ 2 ^ 61 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : (2 : Nat) ^ 61 < B62 := by decide
    omega
  have hxM : (logIter x0 j).1 < M :=
    Nat.lt_trans hrange.2 (by decide)
  have haM : (logIter x0 j).2 < M :=
    Nat.lt_trans haBound (by decide)
  let mid := arun index s (psiPrimeLogInit m)
  have hi := psiPrimeLogInit_continue_run m index s n e
    (logIter x0 j).1 (logIter x0 j).2 hstart hn he hx ha he62 hnorm
    hxM haM
  have hr := psiPrimeLogRound_run_of_range m index mid
    (logIter x0 j).1 (logIter x0 j).2 hi.1 hi.2.1
    hrange.1 hrange.2 haBound
  rw [psiPrimeLogCore_eq_stages, arun_append]
  exact ⟨by simpa only [logIter, logStep] using hr.1,
    by simpa only [logIter, logStep, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mul_comm] using hr.2.1,
    hr.2.2.trans hi.2.2⟩

#print axioms psiPrimeLogCore_start_run
#print axioms psiPrimeLogCore_continue_run

end LeanCompCert.Ports.PsiSegSieve
