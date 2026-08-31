import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLateOutputZeroLiteral

/-! Literal-body zero and Boolean gates at the middle/late source cut. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalMiddleZeroGates (c : Cfg) (idx : Nat) (before : AState) :
    Prop where
  mainZero : (historicalMainOutput c idx before).regs rViol = 0
  zero : (historicalMiddleOutput c idx before).regs rViol = 0
  gate33 : (historicalMiddleOutput c idx before).regs 33 ≤ 1
  gate34 : (historicalMiddleOutput c idx before).regs 34 ≤ 1
  gate48 : (historicalMiddleOutput c idx before).regs 48 ≤ 1
  lateZero : (historicalLateOutput c idx before).regs rViol = 0

structure HistoricalMiddleGates (c : Cfg) (idx : Nat) (before : AState) : Prop where
  main48 : (historicalMainOutput c idx before).regs 48 ≤ 1
  middle33 : (historicalMiddleOutput c idx before).regs 33 ≤ 1
  middle34 : (historicalMiddleOutput c idx before).regs 34 ≤ 1
  middle48 : (historicalMiddleOutput c idx before).regs 48 ≤ 1

set_option maxHeartbeats 1000000 in
theorem historicalMiddle_gates_of_early_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0) :
    HistoricalMiddleGates c idx before := by
  have gatesEarly := historicalEarly_gate_bits c idx
    (historicalLoadedOutput c idx before)
  change (historicalEarlyOutput c idx before).regs 33 ≤ 1 ∧
    (historicalEarlyOutput c idx before).regs 34 ≤ 1 ∧
    (historicalEarlyOutput c idx before).regs 48 ≤ 1 at gatesEarly
  have bh := historicalPostEarlyHead_machine_bounds c idx 0
    (historicalEarlyOutput c idx before) hearlyZero
    gatesEarly.1 gatesEarly.2.1 gatesEarly.2.2
    (by exact (by decide : 8 < M))
  change 0 ≤ (historicalMainOutput c idx before).regs rViol ∧
    (historicalMainOutput c idx before).regs rViol ≤ 8 ∧
    (historicalMainOutput c idx before).regs 33 ≤ 1 ∧
    (historicalMainOutput c idx before).regs 34 ≤ 1 ∧
    (historicalMainOutput c idx before).regs 48 ≤ 1 at bh
  refine ⟨bh.2.2.2.2, ?_, ?_, ?_⟩
  · rw [historicalMiddleOutput_frame33]
    exact bh.2.2.1
  · rw [historicalMiddleOutput_frame34]
    exact bh.2.2.2.1
  · rw [historicalMiddleOutput_frame48]
    exact bh.2.2.2.2

set_option maxHeartbeats 1000000 in
theorem historicalMiddle_zero_gates_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    HistoricalMiddleZeroGates c idx before := by
  have cuts := historicalFlag9_main_zero_of_body_zero c idx before (by
    exact hearlyZero) hbodyZero
  change _ ∧ (historicalMainOutput c idx before).regs rViol = 0 at cuts
  have gates := historicalMiddle_gates_of_early_zero c idx before hearlyZero
  have lateZero : (historicalLateOutput c idx before).regs rViol = 0 :=
    historicalLateOutput_zero_of_body_zero c idx before hbodyZero
  have mb := historicalMiddleOutput_machine_bounds c idx 0 before cuts.2
    gates.main48 (by
      have hM : 3 < M := by decide
      omega)
  have lb := historicalLateOutput_machine_bounds c idx
    ((historicalMiddleOutput c idx before).regs rViol)
    before rfl gates.middle33 gates.middle34 gates.middle48 (by
      have hM : 9 < M := by decide
      omega)
  have middleZero : (historicalMiddleOutput c idx before).regs rViol = 0 := by
    omega
  exact ⟨cuts.2, middleZero, gates.middle33, gates.middle34, gates.middle48,
    lateZero⟩

theorem historicalLate_counterZeros_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero : (historicalEarlyOutput c idx before).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    HistoricalLateCounterZeros c idx (historicalMiddleOutput c idx before) := by
  have mid := historicalMiddle_zero_gates_of_body_zero c idx before
    hearlyZero hbodyZero
  exact historicalLate_counterZeros c idx
    (historicalMiddleOutput c idx before) mid.zero
    mid.gate33 mid.gate34 mid.gate48 mid.lateZero

end LeanCompCert.Ports.DirichletLadderExternalSafety
