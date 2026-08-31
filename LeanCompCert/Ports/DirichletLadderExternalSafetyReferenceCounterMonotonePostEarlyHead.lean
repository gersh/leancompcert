import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddle

/-! The first, source-identical half of the post-flag-8 counter telescope. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalPostEarlyHead (c : Cfg) : List AInstr :=
  historicalDerived c ++ historicalMainFlags c

set_option maxHeartbeats 1000000 in
theorem historicalPostEarlyHead_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1)
    (h48 : s.regs 48 ≤ 1) (hNoWrap : n + 8 < M) :
    let out := arun idx s (historicalPostEarlyHead c)
    n ≤ out.regs rViol ∧ out.regs rViol ≤ n + 8 ∧
      out.regs 33 ≤ 1 ∧ out.regs 34 ≤ 1 ∧ out.regs 48 ≤ 1 := by
  let s0 := arun idx s (historicalDerived c)
  let out := arun idx s0 (historicalMainFlags c)
  have v0 : s0.regs rViol = n := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalDerived c) (by rfl) s]
    exact hv
  have g33_0 : s0.regs 33 ≤ 1 := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalDerived c) (by rfl) s]
    exact h33
  have g34_0 : s0.regs 34 ≤ 1 := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalDerived c) (by rfl) s]
    exact h34
  have g48_0 : s0.regs 48 ≤ 1 := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalDerived c) (by rfl) s]
    exact h48
  have b : n ≤ out.regs rViol ∧ out.regs rViol ≤ n + 8 := by
    exact historicalMainFlags_machine_bounds c idx n s0 v0 g48_0 hNoWrap
  have g33 : out.regs 33 ≤ 1 := by
    dsimp [out]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalMainFlags c) (by rfl) s0]
    exact g33_0
  have g34 : out.regs 34 ≤ 1 := by
    dsimp [out]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalMainFlags c) (by rfl) s0]
    exact g34_0
  have g48 : out.regs 48 ≤ 1 := by
    dsimp [out]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalMainFlags c) (by rfl) s0]
    exact g48_0
  simpa only [historicalPostEarlyHead, arun_append, s0, out] using
    And.intro b.1 (And.intro b.2 (And.intro g33 (And.intro g34 g48)))

end LeanCompCert.Ports.DirichletLadderExternalSafety
