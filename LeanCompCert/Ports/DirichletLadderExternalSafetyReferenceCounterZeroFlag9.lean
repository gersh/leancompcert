import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodySource
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMainAfterFlag9

/-! Acceptance-directed zero extraction at the flag-9 cut of the literal body. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

set_option maxHeartbeats 1000000 in
theorem historicalFlag9_main_zero_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero :
      (arun idx (arun idx before (historicalLoad c))
        (historicalEarly c)).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (arun idx
      (arun idx
        (arun idx (arun idx before (historicalLoad c)) (historicalEarly c))
        (historicalDerived c))
      (historicalFlag9 c)).regs rViol = 0 ∧
    (arun idx
      (arun idx
        (arun idx (arun idx before (historicalLoad c)) (historicalEarly c))
        (historicalDerived c))
      (historicalMainFlags c)).regs rViol = 0 := by
  let loaded := arun idx before (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  let derived := arun idx early (historicalDerived c)
  let s9 := arun idx derived (historicalFlag9 c)
  let head := arun idx early (historicalPostEarlyHead c)
  let post := arun idx early (historicalPostEarly c)
  have earlyZero : early.regs rViol = 0 := by exact hearlyZero
  have gates := historicalEarly_gate_bits c idx loaded
  change early.regs 33 ≤ 1 ∧ early.regs 34 ≤ 1 ∧ early.regs 48 ≤ 1 at gates
  have bh := historicalPostEarlyHead_machine_bounds c idx 0 early earlyZero
    gates.1 gates.2.1 gates.2.2 (by exact (by decide : 8 < M))
  change 0 ≤ head.regs rViol ∧ head.regs rViol ≤ 8 ∧
    head.regs 33 ≤ 1 ∧ head.regs 34 ≤ 1 ∧ head.regs 48 ≤ 1 at bh
  have bt := historicalPostEarlyTail_machine_bounds c idx (head.regs rViol)
    head rfl bh.2.2.1 bh.2.2.2.1 bh.2.2.2.2 (by
      have : 17 < M := by decide
      omega)
  have postEq : post = arun idx head (historicalPostEarlyTail c) := by
    simp only [post, head, historicalPostEarly, arun_append]
  rw [← postEq] at bt
  have postZero : post.regs rViol = 0 := by
    have bodyEq : arun idx before c.bodyBlock = post := by
      rw [historicalBody_eq_load_early_post]
      simp only [arun_append, loaded, early, post]
    rw [← bodyEq]
    exact hbodyZero
  have headZero : head.regs rViol = 0 := by omega
  have derivedZero : derived.regs rViol = 0 := by
    dsimp [derived]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalDerived c) (by rfl) early]
    exact earlyZero
  have mainEq : head =
      arun idx s9 (historicalMainAfterFlag9Counter c) := by
    simp only [head, historicalPostEarlyHead, arun_append, derived, s9,
      historicalMainFlags_eq_flag9_counter_tail]
  have gateS9 : s9.regs 48 ≤ 1 := by
    dsimp [s9, derived]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag9 c) (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
        (historicalDerived c) (by rfl)]
    exact gates.2.2
  have bm := historicalMainAfterFlag9Counter_machine_bounds c idx
    (s9.regs rViol) s9 rfl gateS9 (by
      have fs := historicalFlag9_machine_bounds c idx 0 derived derivedZero
        (by exact (by decide : 1 < M))
      change 0 ≤ s9.regs rViol ∧ s9.regs rViol ≤ 1 at fs
      have : 8 < M := by decide
      omega)
  rw [← mainEq, headZero] at bm
  refine ⟨Nat.eq_zero_of_le_zero bm.1, ?_⟩
  simpa only [head, historicalPostEarlyHead, arun_append, derived] using headZero

theorem historicalFlag9_zero_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hearlyZero :
      (arun idx (arun idx before (historicalLoad c))
        (historicalEarly c)).regs rViol = 0)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (arun idx
      (arun idx
        (arun idx (arun idx before (historicalLoad c)) (historicalEarly c))
        (historicalDerived c))
      (historicalFlag9 c)).regs rViol = 0 :=
  (historicalFlag9_main_zero_of_body_zero c idx before hearlyZero hbodyZero).1

end LeanCompCert.Ports.DirichletLadderExternalSafety
