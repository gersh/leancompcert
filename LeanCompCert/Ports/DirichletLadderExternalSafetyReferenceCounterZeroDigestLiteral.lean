import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceDigestCounterProjectionsLiteral

/-! Literal-body counter telescope to the digest input/output cuts. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

set_option maxHeartbeats 1000000 in
theorem historicalDigest_counterZeros_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero :
      (arun idx (arun idx before (historicalLoad c))
        (historicalEarly c)).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (historicalDigestInput c idx
      (arun idx (arun idx before (historicalLoad c))
        (historicalEarly c))).regs rViol = 0 ∧
      (arun idx (historicalDigestInput c idx
        (arun idx (arun idx before (historicalLoad c))
          (historicalEarly c)))
        [digestMulInstr, digestAddInstr, digestCompareInstr,
        digestBumpInstr]).regs rViol = 0 := by
  constructor
  · simpa only [historicalEarlyOutput, historicalLoadedOutput] using
      historicalDigestInput_zero_of_body_zero c idx before
        hearlyZero hbodyZero
  · simpa only [historicalEarlyOutput, historicalLoadedOutput] using
      historicalDigestBlock_zero_of_body_zero c idx before
        hearlyZero hbodyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety
