import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneUpdateFrame

/-! The second, source-identical half of the post-flag-8 counter telescope. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalPostEarlyTail (c : Cfg) : List AInstr :=
  historicalMiddleLate c ++ historicalUpdateTail c

theorem historicalPostEarlyTail_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1)
    (h48 : s.regs 48 ≤ 1) (hNoWrap : n + 9 < M) :
    n ≤ (arun idx s (historicalPostEarlyTail c)).regs rViol ∧
      (arun idx s (historicalPostEarlyTail c)).regs rViol ≤ n + 9 := by
  have b := historicalMiddleLate_machine_bounds c idx n s hv h33 h34 h48 hNoWrap
  rw [historicalPostEarlyTail, arun_append, historicalUpdateTail_frame,
    historicalMiddleLate_run_eq]
  exact b

end LeanCompCert.Ports.DirichletLadderExternalSafety
