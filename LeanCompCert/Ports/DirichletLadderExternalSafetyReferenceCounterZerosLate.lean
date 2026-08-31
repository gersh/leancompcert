import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsDigest

/-! Zero counter values at every late-flag source cut. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalLateCounterZeros (c : Cfg) (idx : Nat) (s : AState) : Prop where
  flag24 : (arun idx s (historicalFlag24 c)).regs rViol = 0
  flag25 : (arun idx (arun idx s (historicalFlag24 c))
    (historicalFlag25 c)).regs rViol = 0
  flag21 : (arun idx (arun idx (arun idx s (historicalFlag24 c))
    (historicalFlag25 c)) (historicalFlag21 c)).regs rViol = 0
  flag22 : (arun idx (arun idx (arun idx (arun idx s
    (historicalFlag24 c)) (historicalFlag25 c)) (historicalFlag21 c))
    (historicalFlag22 c)).regs rViol = 0
  flag23 : (arun idx (arun idx (arun idx (arun idx (arun idx s
    (historicalFlag24 c)) (historicalFlag25 c)) (historicalFlag21 c))
    (historicalFlag22 c)) (historicalFlag23 c)).regs rViol = 0
  digest : (arun idx s (historicalLateFlags c)).regs rViol = 0

theorem historicalLate_counterZeros
    (c : Cfg) (idx : Nat) (s : AState)
    (hin : s.regs rViol = 0)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1) (h48 : s.regs 48 ≤ 1)
    (hout : (arun idx s (historicalLateFlags c)).regs rViol = 0) :
    HistoricalLateCounterZeros c idx s := by
  let s1 := arun idx s (historicalFlag24 c)
  let s2 := arun idx s1 (historicalFlag25 c)
  let s3 := arun idx s2 (historicalFlag21 c)
  let s4 := arun idx s3 (historicalFlag22 c)
  let s5 := arun idx s4 (historicalFlag23 c)
  let s6 := arun idx s5
    [digestMulInstr, digestAddInstr, digestCompareInstr, digestBumpInstr]
  have b1 := historicalFlag24_machine_bounds c idx 0 s hin h34
    (by exact one_lt_M)
  change 0 ≤ s1.regs rViol ∧ s1.regs rViol ≤ 1 at b1
  have a1 : s1.regs 135 ≤ 1 := historicalFlag24_addr_gate c idx s
  have g34_1 : s1.regs 34 ≤ 1 := by
    dsimp [s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalFlag24 c) (by rfl) s]
    exact h34
  have b2 := historicalFlag25_machine_bounds c idx (s1.regs rViol) s1 rfl
    g34_1 a1 (by
      have hM : 2 < M := by decide
      omega)
  change s1.regs rViol ≤ s2.regs rViol ∧
    s2.regs rViol ≤ s1.regs rViol + 1 at b2
  have g33_2 : s2.regs 33 ≤ 1 := by
    dsimp [s2, s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalFlag25 c) (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
        (historicalFlag24 c) (by rfl)]
    exact h33
  have b3 := historicalFlag21_machine_bounds c idx (s2.regs rViol) s2 rfl
    g33_2 (by
      have hM : 3 < M := by decide
      omega)
  change s2.regs rViol ≤ s3.regs rViol ∧
    s3.regs rViol ≤ s2.regs rViol + 1 at b3
  have g48_3 : s3.regs 48 ≤ 1 := by
    dsimp [s3, s2, s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag21 c) (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
        (historicalFlag25 c) (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
        (historicalFlag24 c) (by rfl)]
    exact h48
  have b4 := historicalFlag22_machine_bounds c idx (s3.regs rViol) s3 rfl
    g48_3 (by
      have hM : 4 < M := by decide
      omega)
  change s3.regs rViol ≤ s4.regs rViol ∧
    s4.regs rViol ≤ s3.regs rViol + 1 at b4
  have g155_4 : s4.regs 155 ≤ 1 := historicalFlag22_complement_gate c idx s3 g48_3
  have b5 := historicalFlag23_machine_bounds c idx (s4.regs rViol) s4 rfl
    g155_4 (by
      have hM : 5 < M := by decide
      omega)
  change s4.regs rViol ≤ s5.regs rViol ∧
    s5.regs rViol ≤ s4.regs rViol + 1 at b5
  have b6 := historicalDigestBlock_machine_bounds idx (s5.regs rViol) s5 rfl
    (by
      have hM : 6 < M := by decide
      omega)
  change s5.regs rViol ≤ s6.regs rViol ∧
    s6.regs rViol ≤ s5.regs rViol + 1 at b6
  have s6Zero : s6.regs rViol = 0 := by
    have heq : arun idx s (historicalLateFlags c) = s6 := by
      simp only [historicalLateFlags, arun_append, s1, s2, s3, s4, s5, s6]
    rw [heq] at hout
    exact hout
  have z : s1.regs rViol = 0 ∧ s2.regs rViol = 0 ∧
      s3.regs rViol = 0 ∧ s4.regs rViol = 0 ∧
      s5.regs rViol = 0 := by omega
  exact ⟨z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2, hout⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety
