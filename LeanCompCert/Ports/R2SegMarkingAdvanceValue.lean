import LeanCompCert.Ports.R2SegMarkingAdvanceDecode

/-! # Cursor-value mux for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markAdvanceValueInstrs : List Instr :=
  [ .binop 64 .sub (.lit 1) (.reg 52)
  , .binop 65 .add (.reg rJ) (.reg rQ)
  , .binop 66 .mul (.reg 152) (.reg 150)
  , .binop 67 .mul (.reg 153) (.reg 60)
  , .binop 68 .mul (.reg 64) (.reg rQ)
  , .binop 69 .add (.reg 66) (.reg 67)
  , .binop rQ .add (.reg 69) (.reg 68)
  , .binop 70 .sub (.lit 1) (.reg 153)
  , .binop 71 .mul (.reg 153) (.reg 60)
  , .binop 72 .mul (.reg 70) (.reg rBp)
  , .binop rBp .add (.reg 71) (.reg 72)
  , .binop 73 .mul (.reg 153) (.reg 62)
  , .binop 74 .mul (.reg 70) (.reg rWt)
  , .binop rWt .add (.reg 73) (.reg 74)
  , .binop 63 .mul (.reg 64) (.reg rFs)
  , .binop rFs .add (.reg 153) (.reg 63) ]

def markAdvanceValueBody : List AInstr := lift markAdvanceValueInstrs

theorem markAdvanceValueBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 69).take markAdvanceValueBody.length =
      markAdvanceValueBody := by
  rfl

def nextPowerValue (active bump step oldPower nextPower nextPrime : Nat) : Nat :=
  bump * nextPower + step * nextPrime + (1 - active) * oldPower

def nextBaseValue (step oldBase nextPrime : Nat) : Nat :=
  step * nextPrime + (1 - step) * oldBase

def nextWeightValue (step oldWeight nextWeight : Nat) : Nat :=
  step * nextWeight + (1 - step) * oldWeight

def nextFirstValue (active step oldFirst : Nat) : Nat :=
  step + (1 - active) * oldFirst

/-- Select exactly one cursor transition: retain the current entry, bump its
power, or install the decoded next table row. -/
theorem markAdvanceValueBody_run (k : Nat) (s : AState)
    (hactive : s.regs 52 ≤ 1) (hbump : s.regs 152 ≤ 1)
    (hstep : s.regs 153 ≤ 1)
    (hmodes : s.regs 152 + s.regs 153 = s.regs 52)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hqOut : nextPowerValue (s.regs 52) (s.regs 152) (s.regs 153)
      (s.regs rQ) (s.regs 150) (s.regs 60) < M)
    (hbpOut : nextBaseValue (s.regs 153) (s.regs rBp)
      (s.regs 60) < M)
    (hwtOut : nextWeightValue (s.regs 153) (s.regs rWt)
      (s.regs 62) < M)
    (hfsOut : nextFirstValue (s.regs 52) (s.regs 153)
      (s.regs rFs) < M) :
    let out := arun k s markAdvanceValueBody
    out.regs 64 = 1 - s.regs 52 ∧
      out.regs 65 = s.regs rJ + s.regs rQ ∧
      out.regs rQ = nextPowerValue (s.regs 52) (s.regs 152)
        (s.regs 153) (s.regs rQ) (s.regs 150) (s.regs 60) ∧
      out.regs rBp = nextBaseValue (s.regs 153) (s.regs rBp)
        (s.regs 60) ∧
      out.regs rWt = nextWeightValue (s.regs 153) (s.regs rWt)
        (s.regs 62) ∧
      out.regs rFs = nextFirstValue (s.regs 52) (s.regs 153)
        (s.regs rFs) ∧ out.arr = s.arr := by
  have hjQ' : s.regs 4 + s.regs 3 < M := by
    simpa [rJ, rQ] using hjQ
  have hjQMod : (s.regs 4 + s.regs 3) % M =
      s.regs 4 + s.regs 3 := Nat.mod_eq_of_lt hjQ'
  have h1M : (1 : Nat) < M := by decide
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt h1M
  have hsub : 1 + (M - 1) = M := by omega
  simp only [markAdvanceValueBody, arun_lift]
  by_cases ha : s.regs 52 = 0
  · have hb : s.regs 152 = 0 := by omega
    have hs : s.regs 153 = 0 := by omega
    have hq : s.regs 3 < M := by
      simpa [nextPowerValue, ha, hb, hs, rQ] using hqOut
    have hbp : s.regs 170 < M := by
      simpa [nextBaseValue, hs, rBp] using hbpOut
    have hwt : s.regs 171 < M := by
      simpa [nextWeightValue, hs, rWt] using hwtOut
    have hfs : s.regs 172 < M := by
      simpa [nextFirstValue, ha, hs, rFs] using hfsOut
    simp [markAdvanceValueInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, nextPowerValue, nextBaseValue,
      nextWeightValue, nextFirstValue, ha, hb, hs, hjQMod,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hbp,
      Nat.mod_eq_of_lt hwt, Nat.mod_eq_of_lt hfs, honeMod,
      rJ, rQ, rBp, rWt, rFs]
  · have ha1 : s.regs 52 = 1 := by omega
    by_cases hb : s.regs 152 = 0
    · have hs : s.regs 153 = 1 := by omega
      have hprime : s.regs 60 < M := by
        simpa [nextPowerValue, ha1, hb, hs, rQ] using hqOut
      have hweight : s.regs 62 < M := by
        simpa [nextWeightValue, hs, rWt] using hwtOut
      simp [markAdvanceValueInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, nextPowerValue, nextBaseValue,
        nextWeightValue, nextFirstValue, ha1, hb, hs, hjQMod,
        Nat.mod_eq_of_lt hprime, Nat.mod_eq_of_lt hweight,
        honeMod, hsub, rJ, rQ, rBp, rWt, rFs]
    · have hb1 : s.regs 152 = 1 := by omega
      have hs : s.regs 153 = 0 := by omega
      have hpower : s.regs 150 < M := by
        simpa [nextPowerValue, ha1, hb1, hs, rQ] using hqOut
      have hbp : s.regs 170 < M := by
        simpa [nextBaseValue, hs, rBp] using hbpOut
      have hwt : s.regs 171 < M := by
        simpa [nextWeightValue, hs, rWt] using hwtOut
      simp [markAdvanceValueInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, nextPowerValue, nextBaseValue,
        nextWeightValue, nextFirstValue, ha1, hb1, hs, hjQMod,
        Nat.mod_eq_of_lt hpower, Nat.mod_eq_of_lt hbp,
        Nat.mod_eq_of_lt hwt, honeMod, hsub,
        rJ, rQ, rBp, rWt, rFs]

#print axioms markAdvanceValueBody_run

end LeanCompCert.Ports.R2SegSieve
