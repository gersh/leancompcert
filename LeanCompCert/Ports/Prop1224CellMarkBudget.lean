import LeanCompCert.Ports.Prop1224CellMarkAdvanceCursor

/-! # Exact mark-budget guard for Proposition 12.2.4 -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def p1224MarkBudgetInstrs (c : CellCfg) : List Instr :=
  [ .binop 78 .eq (.reg rR) (.lit (c.markSteps - 1))
  , .binop 79 .ne (.reg rPi) (.lit c.tableLen)
  , .binop 80 .mul (.reg 78) (.reg 79)
  , .binop rViol .add (.reg rViol) (.reg 80)
  , .binop rVMark .add (.reg rVMark) (.reg 80) ]

def p1224MarkBudgetBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkBudgetInstrs c)

theorem p1224MarkBudgetBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 81).take (p1224MarkBudgetBody c).length =
      p1224MarkBudgetBody c := by
  rfl

def p1224NeBit (a b : Nat) : Nat := if a ≠ b then 1 else 0

def CellCfg.p1224BudgetFailure (c : CellCfg) (round pi : Nat) : Nat :=
  p1224EqBit round (c.markSteps - 1) * p1224NeBit pi c.tableLen

/-- The local failure signal is exact independently of the two accumulating
counters.  This projection is intentionally weaker than
`p1224MarkBudgetBody_run`: an accepting guarded execution can first prove the
signal is zero and only then discharge the counter no-wrap premises, avoiding
any circular arithmetic assumption. -/
theorem p1224MarkBudgetBody_signal_run (c : CellCfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M) :
    (arun k s (p1224MarkBudgetBody c)).regs 80 =
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) := by
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hT
  have hTm1Mod : (c.markSteps - 1) % M = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have honeMod : (1 : Nat) % M = 1 := by decide
  simp only [p1224MarkBudgetBody, arun_lift]
  by_cases hr : s.regs rR = c.markSteps - 1
  · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod,
        rR, rPi, rViol, rVMark]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod, honeMod,
        rR, rPi, rViol, rVMark]
  · have hr5 : s.regs 5 ≠ c.markSteps - 1 := by simpa [rR] using hr
    simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
      p1224EqBit, p1224NeBit, hr5, hTm1Mod, hKMod,
      rR, rPi, rViol, rVMark]

/-- A short marking budget is recorded exactly on its final iteration. -/
theorem p1224MarkBudgetBody_run (c : CellCfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hviol : s.regs rViol +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.p1224BudgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (p1224MarkBudgetBody c)
    out.regs 78 = p1224EqBit (s.regs rR) (c.markSteps - 1) ∧
      out.regs 79 = p1224NeBit (s.regs rPi) c.tableLen ∧
      out.regs 80 = failure ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.regs rPi = s.regs rPi ∧
      out.arr = s.arr := by
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hT
  have hTm1Mod : (c.markSteps - 1) % M = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have honeMod : (1 : Nat) % M = 1 := by decide
  simp only [p1224MarkBudgetBody, arun_lift]
  by_cases hr : s.regs rR = c.markSteps - 1
  · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm251 : s.regs 251 < M := by simpa [rVMark] using hm
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod,
        Nat.mod_eq_of_lt hv190, Nat.mod_eq_of_lt hm251,
        rR, rPi, rViol, rVMark]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol + 1 < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hviol
      have hm : s.regs rVMark + 1 < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hvmark
      have hv190 : s.regs 190 + 1 < M := by simpa [rViol] using hv
      have hm251 : s.regs 251 + 1 < M := by simpa [rVMark] using hm
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod,
        Nat.mod_eq_of_lt hv190, Nat.mod_eq_of_lt hm251, honeMod,
        rR, rPi, rViol, rVMark]
  · have hr5 : s.regs 5 ≠ c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm251 : s.regs 251 < M := by simpa [rVMark] using hm
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod,
        Nat.mod_eq_of_lt hv190, Nat.mod_eq_of_lt hm251,
        rR, rPi, rViol, rVMark]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv : s.regs rViol < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hviol
      have hm : s.regs rVMark < M := by
        simpa [CellCfg.p1224BudgetFailure, p1224EqBit, p1224NeBit,
          hr, hp] using hvmark
      have hv190 : s.regs 190 < M := by simpa [rViol] using hv
      have hm251 : s.regs 251 < M := by simpa [rVMark] using hm
      simp [p1224MarkBudgetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, CellCfg.p1224BudgetFailure,
        p1224EqBit, p1224NeBit, hr5, hp2, hTm1Mod, hKMod,
        Nat.mod_eq_of_lt hv190, Nat.mod_eq_of_lt hm251,
        rR, rPi, rViol, rVMark]

#print axioms p1224MarkBudgetBody_run
#print axioms p1224MarkBudgetBody_signal_run

end LeanCompCert.Ports.Prop1224Cell
