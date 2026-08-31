import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotonePostEarlyHead
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotonePostEarlyTail

/-! Quantitative telescope from the end of flag 8 to the body output. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalPostEarly (c : Cfg) : List AInstr :=
  historicalPostEarlyHead c ++ historicalPostEarlyTail c

theorem historicalPostEarly_eq_source_parts (c : Cfg) :
    historicalPostEarly c =
      historicalDerived c ++ historicalMainFlags c ++
      historicalMiddleFlags c ++ historicalLateFlags c ++
      historicalStateMux c ++ historicalStateCopies c := by
  simp only [historicalPostEarly, historicalPostEarlyHead,
    historicalPostEarlyTail, historicalMiddleLate, historicalUpdateTail,
    List.append_assoc]

theorem historicalPostEarly_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1)
    (h48 : s.regs 48 ≤ 1) (hNoWrap : n + 17 < M) :
    n ≤ (arun idx s (historicalPostEarly c)).regs rViol ∧
      (arun idx s (historicalPostEarly c)).regs rViol ≤ n + 17 := by
  have bh := historicalPostEarlyHead_machine_bounds c idx n s hv h33 h34 h48
    (by omega)
  have bt := historicalPostEarlyTail_machine_bounds c idx
    ((arun idx s (historicalPostEarlyHead c)).regs rViol)
    (arun idx s (historicalPostEarlyHead c)) rfl bh.2.2.1 bh.2.2.2.1
    bh.2.2.2.2 (by omega)
  rw [historicalPostEarly, arun_append]
  constructor <;> omega

end LeanCompCert.Ports.DirichletLadderExternalSafety
