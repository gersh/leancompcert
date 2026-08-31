import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag9Monotone

/-! A source-scale rule for historical violation blocks.

The rule separates the only two facts needed for monotonicity: the pre
does not write the counter, and the register added by the final instruction
is a bit.  It does not interpret the flag mathematically.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem arun_prefix_add_bit_bounds
    (idx n flag : Nat) (s : AState) (pre : List AInstr)
    (hv : s.regs rViol = n)
    (hframe : LeanCompCert.Verified.ArrayRegFrame.writes rViol pre = false)
    (hbit : (arun idx s pre).regs flag ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (pre ++
      [bo rViol .add (.reg rViol) (.reg flag)])).regs rViol ∧
    (arun idx s (pre ++
      [bo rViol .add (.reg rViol) (.reg flag)])).regs rViol ≤ n + 1 := by
  let p := arun idx s pre
  have hpv : p.regs rViol = n := by
    dsimp [p]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol pre hframe s]
    exact hv
  change p.regs flag ≤ 1 at hbit
  have hsum : n + p.regs flag < M := by
    omega
  rw [arun_append]
  change n ≤ (arun idx p [bo rViol .add (.reg rViol) (.reg flag)]).regs rViol ∧
    (arun idx p [bo rViol .add (.reg rViol) (.reg flag)]).regs rViol ≤ n + 1
  simp [bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hpv, Nat.mod_eq_of_lt hsum]
  omega

theorem arun_prefix_add_bit_mono
    (idx n flag : Nat) (s : AState) (pre : List AInstr)
    (hv : s.regs rViol = n)
    (hframe : LeanCompCert.Verified.ArrayRegFrame.writes rViol pre = false)
    (hbit : (arun idx s pre).regs flag ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (pre ++
      [bo rViol .add (.reg rViol) (.reg flag)])).regs rViol :=
  (arun_prefix_add_bit_bounds idx n flag s pre hv hframe hbit hNoWrap).1

@[simp] theorem gate_complement_true (gate : Nat) :
    gate * (1 + (M - 1)) % M = 0 := by
  have hM1 : 1 + (M - 1) = M := by decide
  rw [hM1]
  exact Nat.mul_mod_left gate M

@[simp] theorem gate_complement_false (gate : Nat) :
    gate * (1 + M) % M = gate % M := by
  rw [Nat.mul_add]
  simpa using Nat.add_mul_mod_self_right gate gate M

def historicalFlag10Prefix (c : Cfg) := (historicalFlag10 c).take 2
def historicalFlag11Prefix (c : Cfg) := (historicalFlag11 c).take 2
def historicalFlag12Prefix (c : Cfg) := (historicalFlag12 c).take 9
def historicalFlag13Prefix (c : Cfg) := (historicalFlag13 c).take 7
def historicalFlag14Prefix (c : Cfg) := (historicalFlag14 c).take 8
def historicalFlag15Prefix (c : Cfg) := (historicalFlag15 c).take 3
def historicalParityPrefix (c : Cfg) := (historicalParity c).take 5

theorem historicalFlag10_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag10 c)).regs rViol ∧
      (arun idx s (historicalFlag10 c)).regs rViol ≤ n + 1 := by
  have hgateWord : s.regs 48 < M := by omega
  rw [show historicalFlag10 c = historicalFlag10Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 102)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 102 s (historicalFlag10Prefix c)
      hv (by rfl) ?_ hNoWrap
  simp [historicalFlag10Prefix, historicalFlag10_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, Nat.mod_eq_of_lt hgateWord]
  split <;> simp
  simpa only [Nat.mod_eq_of_lt hgateWord] using hgate

theorem historicalFlag10_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag10 c)).regs rViol :=
  (historicalFlag10_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag11_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag11 c)).regs rViol ∧
      (arun idx s (historicalFlag11 c)).regs rViol ≤ n + 1 := by
  have hgateWord : s.regs 48 < M := by omega
  rw [show historicalFlag11 c = historicalFlag11Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 103)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 103 s (historicalFlag11Prefix c)
      hv (by rfl) ?_ hNoWrap
  simp [historicalFlag11Prefix, historicalFlag11_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, Nat.mod_eq_of_lt hgateWord]
  split <;> simp
  simpa only [Nat.mod_eq_of_lt hgateWord] using hgate

theorem historicalFlag11_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag11 c)).regs rViol :=
  (historicalFlag11_machine_bounds c idx n s hv hgate hNoWrap).1

set_option maxRecDepth 10000 in
theorem historicalFlag12_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag12 c)).regs rViol ∧
      (arun idx s (historicalFlag12 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag12 c = historicalFlag12Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 110)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 110 s (historicalFlag12Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  have hM1 : 1 + (M - 1) = M := by decide
  simp [historicalFlag12Prefix, historicalFlag12_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hM1, gate_complement_true, gate_complement_false,
    Nat.add_mod_right,
    Nat.mod_eq_of_lt hgateWord]
  repeat' first | split | simp [hgateMod]
  all_goals omega

set_option maxRecDepth 10000 in
theorem historicalFlag13_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag13 c)).regs rViol ∧
      (arun idx s (historicalFlag13 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag13 c = historicalFlag13Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 116)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 116 s (historicalFlag13Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  have hM1 : 1 + (M - 1) = M := by decide
  simp [historicalFlag13Prefix, historicalFlag13_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hM1, gate_complement_true, gate_complement_false,
    Nat.add_mod_right,
    Nat.mod_eq_of_lt hgateWord]
  repeat' first | split | simp [hgateMod]
  all_goals omega

set_option maxRecDepth 10000 in
theorem historicalFlag14_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag14 c)).regs rViol ∧
      (arun idx s (historicalFlag14 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag14 c = historicalFlag14Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 123)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 123 s (historicalFlag14Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  have hM1 : 1 + (M - 1) = M := by decide
  simp [historicalFlag14Prefix, historicalFlag14_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hM1, gate_complement_true, gate_complement_false,
    Nat.add_mod_right,
    Nat.mod_eq_of_lt hgateWord]
  repeat' first | split | simp [hgateMod]
  all_goals omega

theorem historicalFlag15_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag15 c)).regs rViol ∧
      (arun idx s (historicalFlag15 c)).regs rViol ≤ n + 1 := by
  rw [show historicalFlag15 c = historicalFlag15Prefix c ++
      [bo rViol .add (.reg rViol) (.reg 162)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 162 s (historicalFlag15Prefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  simp [historicalFlag15Prefix, historicalFlag15_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  split <;> simp
  simpa only [Nat.mod_eq_of_lt hgateWord] using hgate

set_option maxRecDepth 10000 in
theorem historicalParity_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalParity c)).regs rViol ∧
      (arun idx s (historicalParity c)).regs rViol ≤ n + 1 := by
  rw [show historicalParity c = historicalParityPrefix c ++
      [bo rViol .add (.reg rViol) (.reg 127)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 127 s (historicalParityPrefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  simp [historicalParityPrefix, historicalParity_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [hgateMod]
  all_goals simpa only [Nat.mod_eq_of_lt hgateWord] using hgate

theorem historicalFlag12_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag12 c)).regs rViol :=
  (historicalFlag12_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag13_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag13 c)).regs rViol :=
  (historicalFlag13_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag14_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag14 c)).regs rViol :=
  (historicalFlag14_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalFlag15_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag15 c)).regs rViol :=
  (historicalFlag15_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalParity_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalParity c)).regs rViol :=
  (historicalParity_machine_bounds c idx n s hv hgate hNoWrap).1

end LeanCompCert.Ports.DirichletLadderExternalSafety
