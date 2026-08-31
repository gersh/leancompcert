import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneLate

/-! Quantitative source telescope through flags 24,25,21,22,23 and digest. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalLateFlags (c : Cfg) : List AInstr :=
  historicalFlag24 c ++ historicalFlag25 c ++ historicalFlag21 c ++
  historicalFlag22 c ++ historicalFlag23 c ++
  [digestMulInstr, digestAddInstr, digestCompareInstr, digestBumpInstr]

theorem historicalFlag24_addr_gate (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalFlag24 c)).regs 135 ≤ 1 := by
  simp [historicalFlag24_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol]
  split <;> simp

theorem historicalFlag22_complement_gate (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 48 ≤ 1) :
    (arun idx s (historicalFlag22 c)).regs 155 ≤ 1 := by
  rcases (by omega : s.regs 48 = 0 ∨ s.regs 48 = 1) with h | h
  · simp [historicalFlag22_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, h, rViol, Nat.add_mod_right,
      Nat.mod_eq_of_lt one_lt_M]
  · have hM1 : 1 + (M - 1) = M := by decide
    simp [historicalFlag22_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, h, hM1, rViol]

theorem historicalLateFlags_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (h33 : s.regs 33 ≤ 1) (h34 : s.regs 34 ≤ 1)
    (h48 : s.regs 48 ≤ 1) (hNoWrap : n + 6 < M) :
    n ≤ (arun idx s (historicalLateFlags c)).regs rViol ∧
      (arun idx s (historicalLateFlags c)).regs rViol ≤ n + 6 := by
  let s1 := arun idx s (historicalFlag24 c)
  let s2 := arun idx s1 (historicalFlag25 c)
  let s3 := arun idx s2 (historicalFlag21 c)
  let s4 := arun idx s3 (historicalFlag22 c)
  let s5 := arun idx s4 (historicalFlag23 c)
  let s6 := arun idx s5
    [digestMulInstr, digestAddInstr, digestCompareInstr, digestBumpInstr]
  have b1 := historicalFlag24_machine_bounds c idx n s hv h34 (by omega)
  change n ≤ s1.regs rViol ∧ s1.regs rViol ≤ n + 1 at b1
  have a1 : s1.regs 135 ≤ 1 := by
    exact historicalFlag24_addr_gate c idx s
  have g34_1 : s1.regs 34 ≤ 1 := by
    dsimp [s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalFlag24 c) (by rfl) s]
    exact h34
  have b2 := historicalFlag25_machine_bounds c idx (s1.regs rViol) s1 rfl
    g34_1 a1 (by omega)
  change s1.regs rViol ≤ s2.regs rViol ∧
    s2.regs rViol ≤ s1.regs rViol + 1 at b2
  have g33_2 : s2.regs 33 ≤ 1 := by
    dsimp [s2, s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalFlag25 c) (by rfl) _,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
        (historicalFlag24 c) (by rfl) s]
    exact h33
  have b3 := historicalFlag21_machine_bounds c idx (s2.regs rViol) s2 rfl
    g33_2 (by omega)
  change s2.regs rViol ≤ s3.regs rViol ∧
    s3.regs rViol ≤ s2.regs rViol + 1 at b3
  have g48_3 : s3.regs 48 ≤ 1 := by
    dsimp [s3, s2, s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag21 c) (by rfl) _,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
        (historicalFlag25 c) (by rfl) _,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
        (historicalFlag24 c) (by rfl) s]
    exact h48
  have b4 := historicalFlag22_machine_bounds c idx (s3.regs rViol) s3 rfl
    g48_3 (by omega)
  change s3.regs rViol ≤ s4.regs rViol ∧
    s4.regs rViol ≤ s3.regs rViol + 1 at b4
  have g155_4 : s4.regs 155 ≤ 1 := historicalFlag22_complement_gate c idx s3 g48_3
  have b5 := historicalFlag23_machine_bounds c idx (s4.regs rViol) s4 rfl
    g155_4 (by omega)
  change s4.regs rViol ≤ s5.regs rViol ∧
    s5.regs rViol ≤ s4.regs rViol + 1 at b5
  have b6 := historicalDigestBlock_machine_bounds idx (s5.regs rViol) s5 rfl
    (by omega)
  change s5.regs rViol ≤ s6.regs rViol ∧
    s6.regs rViol ≤ s5.regs rViol + 1 at b6
  have hout : arun idx s (historicalLateFlags c) = s6 := by
    simp only [historicalLateFlags, arun_append, s1, s2, s3, s4, s5, s6]
  rw [hout]
  constructor <;> omega

end LeanCompCert.Ports.DirichletLadderExternalSafety
