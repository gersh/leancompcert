import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddleFrames

/-! Quantitative counter telescope through the middle and late flag blocks. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalMiddleLate (c : Cfg) : List AInstr :=
  historicalMiddleFlags c ++ historicalLateFlags c

set_option maxHeartbeats 1000000 in
theorem historicalMiddleLate_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1)
    (h48 : s.regs 48 ≤ 1) (hNoWrap : n + 9 < M) :
    n ≤ (arun idx (arun idx s (historicalMiddleFlags c))
      (historicalLateFlags c)).regs rViol ∧
    (arun idx (arun idx s (historicalMiddleFlags c))
      (historicalLateFlags c)).regs rViol ≤ n + 9 := by
  have b1 := historicalMiddleFlags_machine_bounds c idx n s hv h48 (by omega)
  have g33 : (arun idx s (historicalMiddleFlags c)).regs 33 ≤ 1 := by
    rw [historicalMiddleFlags_frame33]
    exact h33
  have g34 : (arun idx s (historicalMiddleFlags c)).regs 34 ≤ 1 := by
    rw [historicalMiddleFlags_frame34]
    exact h34
  have g48 : (arun idx s (historicalMiddleFlags c)).regs 48 ≤ 1 := by
    rw [historicalMiddleFlags_frame48]
    exact h48
  have b2 := historicalLateFlags_machine_bounds c idx
    ((arun idx s (historicalMiddleFlags c)).regs rViol)
    (arun idx s (historicalMiddleFlags c)) rfl g33 g34 g48 (by omega)
  constructor <;> omega

theorem historicalMiddleLate_run_eq (c : Cfg) (idx : Nat) (s : AState) :
    arun idx s (historicalMiddleLate c) =
      arun idx (arun idx s (historicalMiddleFlags c))
        (historicalLateFlags c) := by
  simp only [historicalMiddleLate, arun_append]

end LeanCompCert.Ports.DirichletLadderExternalSafety
