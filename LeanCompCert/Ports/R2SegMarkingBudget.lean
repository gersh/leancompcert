import LeanCompCert.Ports.R2SegMarkingAdvanceOffset

/-! # Mark-budget guard for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markBudgetInstrs (c : R2Cfg) : List Instr :=
  let T := c.markSteps
  let K := c.tableLen
  [ .binop 154 .eq (.reg rR) (.lit (T - 1))
  , .binop 155 .ne (.reg rPi) (.lit K)
  , .binop 156 .mul (.reg 154) (.reg 155)
  , .binop rViol .add (.reg rViol) (.reg 156)
  , .binop rVMark .add (.reg rVMark) (.reg 156) ]

def markBudgetBody (c : R2Cfg) : List AInstr := lift (markBudgetInstrs c)

theorem markBudgetBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 96).take (markBudgetBody c).length =
      markBudgetBody c := by
  rfl

def neBitR2 (a b : Nat) : Nat := if a ≠ b then 1 else 0

def R2Cfg.budgetFailure (c : R2Cfg) (round pi : Nat) : Nat :=
  eqBitR2 round (c.markSteps - 1) * neBitR2 pi c.tableLen

/-- A short marking budget is recorded exactly on its final iteration; a
normal iteration leaves both counters unchanged. -/
theorem markBudgetBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.budgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (markBudgetBody c)
    out.regs 154 = eqBitR2 (s.regs rR) (c.markSteps - 1) ∧
      out.regs 155 = neBitR2 (s.regs rPi) c.tableLen ∧
      out.regs 156 = failure ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.regs rPi = s.regs rPi ∧
      out.arr = s.arr := by
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hT
  have hTm1Mod : (c.markSteps - 1) % M = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have h1M : (1 : Nat) < M := by decide
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt h1M
  simp only [markBudgetBody, arun_lift]
  by_cases hr : s.regs rR = c.markSteps - 1
  · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm353 : s.regs 353 < M := by simpa [rVMark] using hm
      simp [markBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.budgetFailure, eqBitR2, neBitR2,
        hr5, hp2, hTm1Mod, hKMod, Nat.mod_eq_of_lt hv190,
        Nat.mod_eq_of_lt hm353, rR, rPi, rViol, rVMark]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol + 1 < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hviol
      have hm : s.regs rVMark + 1 < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hvmark
      have hv190 : s.regs 190 + 1 < M := by simpa [rViol] using hv
      have hm353 : s.regs 353 + 1 < M := by simpa [rVMark] using hm
      simp [markBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.budgetFailure, eqBitR2, neBitR2,
        hr5, hp2, hTm1Mod, hKMod, Nat.mod_eq_of_lt hv190,
        Nat.mod_eq_of_lt hm353, honeMod, rR, rPi, rViol, rVMark]
  · have hr5 : s.regs 5 ≠ c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm353 : s.regs 353 < M := by simpa [rVMark] using hm
      simp [markBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.budgetFailure, eqBitR2, neBitR2,
        hr5, hp2, hTm1Mod, hKMod, Nat.mod_eq_of_lt hv190,
        Nat.mod_eq_of_lt hm353, rR, rPi, rViol, rVMark]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm353 : s.regs 353 < M := by simpa [rVMark] using hm
      simp [markBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.budgetFailure, eqBitR2, neBitR2,
        hr5, hp2, hTm1Mod, hKMod, Nat.mod_eq_of_lt hv190,
        Nat.mod_eq_of_lt hm353, rR, rPi, rViol, rVMark]

#print axioms markBudgetBody_run

end LeanCompCert.Ports.R2SegSieve
