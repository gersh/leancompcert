import LeanCompCert.Ports.R2SegMarkingAdvanceFlags

/-! # Prime-table selection and load for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markAdvancePiInstrs (c : R2Cfg) : List Instr :=
  let K := c.tableLen
  [ .binop 53 .add (.reg rPi) (.reg 153)
  , .binop 54 .gt (.reg 53) (.lit K)
  , .binop 55 .sub (.lit 1) (.reg 54)
  , .binop 56 .mul (.reg 55) (.reg 53)
  , .binop 57 .mul (.reg 54) (.lit K)
  , .binop rPi .add (.reg 56) (.reg 57) ]

def markAdvancePiBody (c : R2Cfg) : List AInstr :=
  lift (markAdvancePiInstrs c)

theorem markAdvancePiBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 58).take (markAdvancePiBody c).length =
      markAdvancePiBody c := by
  rfl

def clampPi (K candidate : Nat) : Nat :=
  if candidate > K then K else candidate

/-- The selected table cursor advances by the step bit and clamps to the
sentinel row. -/
theorem markAdvancePiBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hsum : s.regs rPi + s.regs 153 < M)
    (hK : c.tableLen < M) :
    let candidate := s.regs rPi + s.regs 153
    let out := arun k s (markAdvancePiBody c)
    out.regs 53 = candidate ∧
      out.regs 54 = (if candidate > c.tableLen then 1 else 0) ∧
      out.regs 55 = (if candidate > c.tableLen then 0 else 1) ∧
      out.regs 56 = (if candidate > c.tableLen then 0 else candidate) ∧
      out.regs 57 = (if candidate > c.tableLen then c.tableLen else 0) ∧
      out.regs rPi = clampPi c.tableLen candidate ∧
      out.regs 153 = s.regs 153 ∧ out.arr = s.arr := by
  have hsum' : s.regs 2 + s.regs 153 < M := by
    simpa [rPi] using hsum
  have hsumMod :
      (s.regs 2 + s.regs 153) % M = s.regs 2 + s.regs 153 :=
    Nat.mod_eq_of_lt hsum'
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have h1M : (1 : Nat) < M := by decide
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt h1M
  have hsub : 1 + (M - 1) = M := by omega
  simp only [markAdvancePiBody, arun_lift]
  by_cases hover : s.regs rPi + s.regs 153 > c.tableLen
  · have hover' : s.regs 2 + s.regs 153 > c.tableLen := by
      simpa [rPi] using hover
    simp [markAdvancePiInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, clampPi, hover', hsumMod, hKMod,
      honeMod, hsub, rPi]
  · have hover' : ¬s.regs 2 + s.regs 153 > c.tableLen := by
      simpa [rPi] using hover
    simp [markAdvancePiInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, clampPi, hover', hsumMod, hKMod,
      honeMod, rPi]

def markAdvanceLoadBody (c : R2Cfg) : List AInstr :=
  [ .scalar (.binop 58 .add (.reg rPi) (.lit c.tableBase))
  , .load 59 58 ]

theorem markAdvanceLoadBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 64).take (markAdvanceLoadBody c).length =
      markAdvanceLoadBody c := by
  rfl

/-- The clamped cursor addresses and loads its exact prime or sentinel row. -/
theorem markAdvanceLoadBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (haddr : s.regs rPi + c.tableBase < M) :
    let address := s.regs rPi + c.tableBase
    let out := arun k s (markAdvanceLoadBody c)
    out.regs 58 = address ∧ out.regs 59 = s.arr address ∧
      out.regs rPi = s.regs rPi ∧ out.arr = s.arr := by
  have haddr' : s.regs 2 + c.tableBase < M := by
    simpa [rPi] using haddr
  have hbase : c.tableBase < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) haddr'
  simp [markAdvanceLoadBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt haddr', Nat.mod_eq_of_lt hbase, rPi]

#print axioms markAdvancePiBody_run
#print axioms markAdvanceLoadBody_run

end LeanCompCert.Ports.R2SegSieve
