import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddleFrames

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalMiddleFlags_machine_bounds_adapter
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 3 < M) :
    n ≤ (arun idx s (historicalMiddleFlags c)).regs rViol ∧
      (arun idx s (historicalMiddleFlags c)).regs rViol ≤ n + 3 :=
  historicalMiddleFlags_machine_bounds c idx n s hv hgate hNoWrap

end LeanCompCert.Ports.DirichletLadderExternalSafety
