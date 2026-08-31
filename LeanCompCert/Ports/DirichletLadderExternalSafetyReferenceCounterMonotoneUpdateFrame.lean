import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddleLate

/-! The historical state-update suffix does not write the violation counter. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalUpdateTail (c : Cfg) : List AInstr :=
  historicalStateMux c ++ historicalStateCopies c

theorem historicalUpdateTail_frame (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalUpdateTail c)).regs rViol = s.regs rViol := by
  rw [historicalUpdateTail, arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalStateCopies c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalStateMux c) (by rfl)]

end LeanCompCert.Ports.DirichletLadderExternalSafety
