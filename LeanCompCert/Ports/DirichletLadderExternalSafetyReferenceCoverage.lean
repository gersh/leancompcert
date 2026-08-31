import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightFlag

/-! One-instruction state cuts for height coverage/reference flags 19 and 20. -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalCoverageSucc (c : Cfg) := (c.bodyBlock.drop 197).take 1
def historicalCoverageFive (c : Cfg) := (c.bodyBlock.drop 198).take 1
def historicalCoverageQ (c : Cfg) := (c.bodyBlock.drop 199).take 1
def historicalCoverageCmp (c : Cfg) := (c.bodyBlock.drop 200).take 1
def historicalCoverageGate (c : Cfg) := (c.bodyBlock.drop 201).take 1
def historicalCoverageBump (c : Cfg) := (c.bodyBlock.drop 202).take 1

@[simp] theorem historicalCoverageSucc_eq (c : Cfg) : historicalCoverageSucc c =
    [bo 129 .add (.reg 22) (.lit 1)] := by rfl
@[simp] theorem historicalCoverageFive_eq (c : Cfg) : historicalCoverageFive c =
    [bo 130 .mul (.reg 129) (.lit 5)] := by rfl
@[simp] theorem historicalCoverageQ_eq (c : Cfg) : historicalCoverageQ c =
    [bo 130 .mul (.reg 130) (.reg 128)] := by rfl
@[simp] theorem historicalCoverageCmp_eq (c : Cfg) : historicalCoverageCmp c =
    [bo 131 .lt (.reg 130) (.reg 152)] := by rfl
@[simp] theorem historicalCoverageGate_eq (c : Cfg) : historicalCoverageGate c =
    [bo 131 .mul (.reg 48) (.reg 131)] := by rfl
@[simp] theorem historicalCoverageBump_eq (c : Cfg) : historicalCoverageBump c =
    [bo rViol .add (.reg rViol) (.reg 131)] := by rfl

theorem historicalCoverageSucc_result (c : Cfg) (idx blk : Nat) (s : AState)
    (h : s.regs 22 = blk) (hw : blk + 1 < M) :
    (arun idx s (historicalCoverageSucc c)).regs 129 = blk + 1 := by
  simp [historicalCoverageSucc_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, h, Nat.mod_eq_of_lt hw]

theorem historicalCoverageFive_result (c : Cfg) (idx blockCount : Nat) (s : AState)
    (h : s.regs 129 = blockCount) (hw : blockCount * 5 < M) :
    (arun idx s (historicalCoverageFive c)).regs 130 = blockCount * 5 := by
  simp [historicalCoverageFive_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, h, Nat.mod_eq_of_lt hw]

theorem historicalCoverageQ_result (c : Cfg) (idx fiveCount q : Nat) (s : AState)
    (hc : s.regs 130 = fiveCount) (hq : s.regs 128 = q)
    (hw : fiveCount * q < M) :
    (arun idx s (historicalCoverageQ c)).regs 130 = fiveCount * q := by
  simp [historicalCoverageQ_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hc, hq, Nat.mod_eq_of_lt hw]

theorem historicalCoverageCmp_result (c : Cfg) (idx cover tq : Nat) (s : AState)
    (hc : s.regs 130 = cover) (ht : s.regs 152 = tq) :
    (arun idx s (historicalCoverageCmp c)).regs 131 = if cover < tq then 1 else 0 := by
  simp [historicalCoverageCmp_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hc, ht]

theorem historicalCoverageGate_result (c : Cfg) (idx flag : Nat)
    (isLastB : Bool) (s : AState)
    (hf : s.regs 131 = flag) (hg : s.regs 48 = if isLastB then 1 else 0)
    (hflag : flag ≤ 1) :
    (arun idx s (historicalCoverageGate c)).regs 131 =
      (if isLastB then 1 else 0) * flag := by
  have hw : (if isLastB then 1 else 0) * flag < M := by
    cases isLastB <;> simp [M] <;> omega
  simp [historicalCoverageGate_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hf, hg, Nat.mod_eq_of_lt hw]

theorem historicalCoverageBump_result (c : Cfg) (idx n flag : Nat) (s : AState)
    (hv : s.regs rViol = n) (hf : s.regs 131 = flag)
    (hflag : flag ≤ 1) (hw : n + 1 < M) :
    (arun idx s (historicalCoverageBump c)).regs rViol =
      if flag = 1 then n + 1 else n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
  · simp [historicalCoverageBump_eq, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hf, Nat.mod_eq_of_lt hn, rViol]
  · simp [historicalCoverageBump_eq, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hf, Nat.mod_eq_of_lt hw, rViol]

def historicalOvershootFive (c : Cfg) := (c.bodyBlock.drop 203).take 1
def historicalOvershootQ (c : Cfg) := (c.bodyBlock.drop 204).take 1
def historicalOvershootCmp (c : Cfg) := (c.bodyBlock.drop 205).take 1
def historicalOvershootGate (c : Cfg) := (c.bodyBlock.drop 206).take 1
def historicalOvershootBump (c : Cfg) := (c.bodyBlock.drop 207).take 1

@[simp] theorem historicalOvershootFive_eq (c : Cfg) : historicalOvershootFive c =
    [bo 132 .mul (.reg 22) (.lit 5)] := by rfl
@[simp] theorem historicalOvershootQ_eq (c : Cfg) : historicalOvershootQ c =
    [bo 132 .mul (.reg 132) (.reg 128)] := by rfl
@[simp] theorem historicalOvershootCmp_eq (c : Cfg) : historicalOvershootCmp c =
    [bo 133 .ge (.reg 132) (.reg 152)] := by rfl
@[simp] theorem historicalOvershootGate_eq (c : Cfg) : historicalOvershootGate c =
    [bo 133 .mul (.reg 48) (.reg 133)] := by rfl
@[simp] theorem historicalOvershootBump_eq (c : Cfg) : historicalOvershootBump c =
    [bo rViol .add (.reg rViol) (.reg 133)] := by rfl

theorem historicalOvershootFive_result (c : Cfg) (idx blk : Nat) (s : AState)
    (h : s.regs 22 = blk) (hw : blk * 5 < M) :
    (arun idx s (historicalOvershootFive c)).regs 132 = blk * 5 := by
  simp [historicalOvershootFive_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, h, Nat.mod_eq_of_lt hw]

theorem historicalOvershootQ_result (c : Cfg) (idx fiveBlk q : Nat) (s : AState)
    (hb : s.regs 132 = fiveBlk) (hq : s.regs 128 = q)
    (hw : fiveBlk * q < M) :
    (arun idx s (historicalOvershootQ c)).regs 132 = fiveBlk * q := by
  simp [historicalOvershootQ_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hb, hq, Nat.mod_eq_of_lt hw]

theorem historicalOvershootCmp_result (c : Cfg) (idx over tq : Nat) (s : AState)
    (ho : s.regs 132 = over) (ht : s.regs 152 = tq) :
    (arun idx s (historicalOvershootCmp c)).regs 133 = if tq ≤ over then 1 else 0 := by
  simp [historicalOvershootCmp_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ho, ht]

theorem historicalOvershootGate_result (c : Cfg) (idx flag : Nat)
    (isLastB : Bool) (s : AState)
    (hf : s.regs 133 = flag) (hg : s.regs 48 = if isLastB then 1 else 0)
    (hflag : flag ≤ 1) :
    (arun idx s (historicalOvershootGate c)).regs 133 =
      (if isLastB then 1 else 0) * flag := by
  have hw : (if isLastB then 1 else 0) * flag < M := by
    cases isLastB <;> simp [M] <;> omega
  simp [historicalOvershootGate_eq, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hf, hg, Nat.mod_eq_of_lt hw]

theorem historicalOvershootBump_result (c : Cfg) (idx n flag : Nat) (s : AState)
    (hv : s.regs rViol = n) (hf : s.regs 133 = flag)
    (hflag : flag ≤ 1) (hw : n + 1 < M) :
    (arun idx s (historicalOvershootBump c)).regs rViol =
      if flag = 1 then n + 1 else n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
  · simp [historicalOvershootBump_eq, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hf, Nat.mod_eq_of_lt hn, rViol]
  · simp [historicalOvershootBump_eq, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hf, Nat.mod_eq_of_lt hw, rViol]

end LeanCompCert.Ports.DirichletLadderExternalSafety
