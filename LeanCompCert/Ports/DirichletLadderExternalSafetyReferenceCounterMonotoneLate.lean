import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneCoverage

/-! Machine-only monotonicity for historical flags 21--25. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag21Prefix (c : Cfg) := (historicalFlag21 c).take 2
def historicalFlag22Prefix (c : Cfg) := (historicalFlag22 c).take 3
def historicalFlag23Prefix (c : Cfg) := (historicalFlag23 c).take 2
def historicalFlag24Prefix (c : Cfg) := (historicalFlag24 c).take 5
def historicalFlag25Prefix (c : Cfg) := (historicalFlag25 c).take 5

theorem historicalFlag21_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 33 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag21 c)).regs rViol ∧
      (arun idx s (historicalFlag21 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag21 c = historicalFlag21Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 154)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 154 s (historicalFlag21Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hg : s.regs 33 < M := by omega
  simp [historicalFlag21Prefix, historicalFlag21_eq_source,
    bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [Nat.mod_eq_of_lt hg]
  all_goals omega

theorem historicalFlag22_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag22 c)).regs rViol ∧
      (arun idx s (historicalFlag22 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag22 c = historicalFlag22Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 156)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 156 s (historicalFlag22Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hg : s.regs 48 < M := by omega
  have hgmod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hg
  have hM1 : 1 + (M - 1) = M := by decide
  rcases (by omega : s.regs 48 = 0 ∨ s.regs 48 = 1) with hval | hval
  · simp [historicalFlag22Prefix, historicalFlag22_eq_source,
      bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hval, hM1, Nat.add_mod_right,
      Nat.mod_eq_of_lt one_lt_M]
    split <;> simp [Nat.mod_eq_of_lt one_lt_M]
  · simp [historicalFlag22Prefix, historicalFlag22_eq_source,
      bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hval, hM1, Nat.add_mod_right,
      Nat.mod_eq_of_lt one_lt_M]

theorem historicalFlag23_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 155 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag23 c)).regs rViol ∧
      (arun idx s (historicalFlag23 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag23 c = historicalFlag23Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 157)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 157 s (historicalFlag23Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hg : s.regs 155 < M := by omega
  simp [historicalFlag23Prefix, historicalFlag23_eq_source,
    bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [Nat.mod_eq_of_lt hg]
  all_goals omega

theorem historicalFlag24_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 34 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag24 c)).regs rViol ∧
      (arun idx s (historicalFlag24 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag24 c = historicalFlag24Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 136)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 136 s (historicalFlag24Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hg : s.regs 34 < M := by omega
  have hgmod : s.regs 34 % M = s.regs 34 := Nat.mod_eq_of_lt hg
  simp [historicalFlag24Prefix, historicalFlag24_eq_source,
    bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [hgmod]
  all_goals omega

set_option maxRecDepth 10000 in
theorem historicalFlag25_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 34 ≤ 1)
    (haddrGate : s.regs 135 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag25 c)).regs rViol ∧
      (arun idx s (historicalFlag25 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag25 c = historicalFlag25Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 139)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 139 s (historicalFlag25Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hg : s.regs 34 < M := by omega
  have hgmod : s.regs 34 % M = s.regs 34 := Nat.mod_eq_of_lt hg
  have ha : s.regs 135 < M := by omega
  have hamod : s.regs 135 % M = s.regs 135 := Nat.mod_eq_of_lt ha
  rcases (by omega : s.regs 34 = 0 ∨ s.regs 34 = 1) with hval | hval
  · simp [historicalFlag25Prefix, historicalFlag25_eq_source,
      bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hval]
    repeat' first | split | simp [hamod]
    all_goals omega
  · simp [historicalFlag25Prefix, historicalFlag25_eq_source,
      bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hval]
    repeat' first | split | simp [hamod]
    all_goals omega

theorem historicalFlag21_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 33 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag21 c)).regs rViol :=
  (historicalFlag21_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag22_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag22 c)).regs rViol :=
  (historicalFlag22_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag23_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 155 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag23 c)).regs rViol :=
  (historicalFlag23_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag24_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 34 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag24 c)).regs rViol :=
  (historicalFlag24_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag25_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 34 ≤ 1)
    (haddrGate : s.regs 135 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag25 c)).regs rViol :=
  (historicalFlag25_machine_bounds c idx n s hv hgate haddrGate hNoWrap).1

end LeanCompCert.Ports.DirichletLadderExternalSafety
