import LeanCompCert.Ports.R2SegMarkingHit

/-! # Marking-phase selector for the `R₂*` production loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markPhaseInstrs (c : R2Cfg) : List Instr :=
  let L := c.segLen
  let T := c.markSteps
  [ .binop 8 .lt (.reg rR) (.lit T)
  , .binop 14 .lt (.reg rR) (.lit (T + L))
  , .binop 9 .sub (.reg 14) (.reg 8)
  , .binop 15 .sub (.lit 1) (.reg 14) ]

def markPhaseBody (c : R2Cfg) : List AInstr := lift (markPhaseInstrs c)

theorem markPhaseBody_eq_slice (c : R2Cfg) :
    (c.markBody.take (markPhaseBody c).length) = markPhaseBody c := by
  rfl

/-- Inside the mark budget, the production phase selector enables marking
and disables the accumulation and logarithm phases. -/
theorem markPhaseBody_active_run (c : R2Cfg) (k : Nat) (s : AState)
    (r : Nat) (hr : s.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M) :
    let out := arun k s (markPhaseBody c)
    out.regs 8 = 1 ∧ out.regs 14 = 1 ∧ out.regs 9 = 0 ∧
      out.regs 15 = 0 ∧ out.arr = s.arr := by
  have hTM : c.markSteps < M := by omega
  have hrTL : r < c.markSteps + c.segLen := by omega
  have h1M : (1 : Nat) < M := by decide
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hr5 : s.regs 5 = r := by simpa [rR] using hr
  simp only [markPhaseBody, arun_lift]
  simp [markPhaseInstrs, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, hr5, hrT, hrTL, hzero, rR,
    Nat.mod_eq_of_lt hTM, Nat.mod_eq_of_lt hperiod,
    Nat.mod_eq_of_lt h1M]

#print axioms markPhaseBody_active_run

end LeanCompCert.Ports.R2SegSieve
