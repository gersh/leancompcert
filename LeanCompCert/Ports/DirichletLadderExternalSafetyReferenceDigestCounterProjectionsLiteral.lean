import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMiddleZeroLiteral

/-! Small projections from the literal-body late counter telescope. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalDigestInput_zero_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (historicalDigestInput c idx
      (historicalEarlyOutput c idx before)).regs rViol = 0 := by
  have zeros := historicalLate_counterZeros_of_body_zero c idx before
    hearlyZero hbodyZero
  rw [historicalDigestInput_eq_late_prefix]
  exact zeros.flag23

set_option maxHeartbeats 1000000 in
theorem historicalDigestBlock_zero_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (arun idx (historicalDigestInput c idx
      (historicalEarlyOutput c idx before))
      [digestMulInstr, digestAddInstr, digestCompareInstr,
        digestBumpInstr]).regs rViol = 0 := by
  have zeros := historicalLate_counterZeros_of_body_zero c idx before
    hearlyZero hbodyZero
  rw [historicalDigestInput_eq_late_prefix]
  simpa only [historicalLateFlags, arun_append] using zeros.digest

theorem historicalDigest_source_noFailures_of_body_zero
    (c : Cfg) (words : List Nat) (st : RefState)
    (idx : Nat) (before : AState)
    (hprev : (historicalEarlyOutput c idx before).regs rPrevDig = st.prevDig)
    (hbits : (historicalEarlyOutput c idx before).regs 26 =
      words.getD (recW * idx + 5) 0)
    (hdig : (historicalEarlyOutput c idx before).regs 158 =
      words.getD (recW * idx + 12) 0)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures (((referenceConditions c words st idx).drop 15).take 1) := by
  apply historicalDigest_slice_noFailures c words st idx
    (historicalDigestInput c idx (historicalEarlyOutput c idx before))
  · rw [historicalDigestInput_prevDig]
    exact hprev
  · rw [historicalDigestInput_bits]
    exact hbits
  · rw [historicalDigestInput_digest]
    exact hdig
  · exact historicalDigestInput_zero_of_body_zero c idx before
      hearlyZero hbodyZero
  · exact historicalDigestBlock_zero_of_body_zero c idx before
      hearlyZero hbodyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety
