import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotone

/-! Machine-only monotonicity for the height/coverage/digest counter cuts. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightFlagPrefix (c : Cfg) := (historicalHeightFlag c).take 1

theorem historicalHeightFlag_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalHeightFlag c)).regs rViol ∧
      (arun idx s (historicalHeightFlag c)).regs rViol ≤ n + 1 := by
  rw [show historicalHeightFlag c = historicalHeightFlagPrefix c ++
      [bo rViol .add (.reg rViol) (.reg 153)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 153 s (historicalHeightFlagPrefix c)
      hv (by rfl) ?_ hNoWrap
  simp [historicalHeightFlagPrefix, historicalHeightFlag_eq_source,
    bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  split <;> simp

def historicalCoveragePrefix (c : Cfg) :=
  historicalCoverageSucc c ++ historicalCoverageFive c ++
  historicalCoverageQ c ++ historicalCoverageCmp c ++
  historicalCoverageGate c

def historicalCoverageBlock (c : Cfg) :=
  historicalCoveragePrefix c ++ historicalCoverageBump c

theorem historicalCoverageBlock_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalCoverageBlock c)).regs rViol ∧
      (arun idx s (historicalCoverageBlock c)).regs rViol ≤ n + 1 := by
  rw [show historicalCoverageBlock c = historicalCoveragePrefix c ++
      [bo rViol .add (.reg rViol) (.reg 131)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 131 s (historicalCoveragePrefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  simp [historicalCoveragePrefix, historicalCoverageSucc_eq,
    historicalCoverageFive_eq, historicalCoverageQ_eq,
    historicalCoverageCmp_eq, historicalCoverageGate_eq,
    bo, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [hgateMod]
  all_goals omega

def historicalOvershootPrefix (c : Cfg) :=
  historicalOvershootFive c ++ historicalOvershootQ c ++
  historicalOvershootCmp c ++ historicalOvershootGate c

def historicalOvershootBlock (c : Cfg) :=
  historicalOvershootPrefix c ++ historicalOvershootBump c

theorem historicalOvershootBlock_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalOvershootBlock c)).regs rViol ∧
      (arun idx s (historicalOvershootBlock c)).regs rViol ≤ n + 1 := by
  rw [show historicalOvershootBlock c = historicalOvershootPrefix c ++
      [bo rViol .add (.reg rViol) (.reg 133)] by rfl]
  apply arun_prefix_add_bit_bounds idx n 133 s (historicalOvershootPrefix c)
      hv (by rfl) ?_ hNoWrap
  have hgateWord : s.regs 48 < M := by omega
  have hgateMod : s.regs 48 % M = s.regs 48 := Nat.mod_eq_of_lt hgateWord
  simp [historicalOvershootPrefix, historicalOvershootFive_eq,
    historicalOvershootQ_eq, historicalOvershootCmp_eq,
    historicalOvershootGate_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg]
  repeat' first | split | simp [hgateMod]
  all_goals omega

def historicalDigestPrefix : List AInstr :=
  [digestMulInstr, digestAddInstr, digestCompareInstr]

theorem historicalDigestBlock_machine_bounds
    (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s [digestMulInstr, digestAddInstr,
      digestCompareInstr, digestBumpInstr]).regs rViol ∧
    (arun idx s [digestMulInstr, digestAddInstr,
      digestCompareInstr, digestBumpInstr]).regs rViol ≤ n + 1 := by
  let prev := s.regs rPrevDig
  let bits := s.regs 26
  let dig := s.regs 158
  rw [historicalDigestBlock_result idx n prev bits dig s hv
    (by rfl) (by rfl) (by rfl) hNoWrap]
  constructor
  · cases dig != (prev * digMul + bits) % M <;> simp [bump]
  · exact bump_le_succ _ _

theorem historicalHeightFlag_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalHeightFlag c)).regs rViol :=
  (historicalHeightFlag_machine_bounds c idx n s hv hNoWrap).1

theorem historicalCoverageBlock_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalCoverageBlock c)).regs rViol :=
  (historicalCoverageBlock_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalOvershootBlock_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalOvershootBlock c)).regs rViol :=
  (historicalOvershootBlock_machine_bounds c idx n s hv hgate hNoWrap).1

theorem historicalDigestBlock_machine_mono
    (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s [digestMulInstr, digestAddInstr,
      digestCompareInstr, digestBumpInstr]).regs rViol :=
  (historicalDigestBlock_machine_bounds idx n s hv hNoWrap).1

end LeanCompCert.Ports.DirichletLadderExternalSafety
