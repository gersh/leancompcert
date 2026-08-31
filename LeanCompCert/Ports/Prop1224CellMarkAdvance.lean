import LeanCompCert.Ports.Prop1224CellMarkArray

/-!
# Literal cursor advance for the Proposition 12.2.4 marker

The 37 cursor instructions after the cell stores are split into bounded
scalar/load stages.  Each theorem is symbolic in the table and state.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def p1224AdvanceActive (inMark pastWindow : Nat) : Nat :=
  inMark * pastWindow

def CellCfg.p1224PowerFits (c : CellCfg) (power prime : Nat) : Nat :=
  if power * prime ≤ c.hi then 1 else 0

def CellCfg.p1224BumpPower (c : CellCfg)
    (inMark pastWindow power prime : Nat) : Nat :=
  p1224AdvanceActive inMark pastWindow * c.p1224PowerFits power prime

def CellCfg.p1224StepPrime (c : CellCfg)
    (inMark pastWindow power prime : Nat) : Nat :=
  p1224AdvanceActive inMark pastWindow -
    c.p1224BumpPower inMark pastWindow power prime

def p1224ClampPi (K candidate : Nat) : Nat :=
  if candidate > K then K else candidate

def p1224NextPowerValue
    (active bump step oldPower nextPower nextPrime : Nat) : Nat :=
  bump * nextPower + step * nextPrime + (1 - active) * oldPower

def p1224NextBaseValue (step oldBase nextPrime : Nat) : Nat :=
  step * nextPrime + (1 - step) * oldBase

def p1224NextFirstValue (active step oldFirst : Nat) : Nat :=
  step + (1 - active) * oldFirst

def p1224NextOffset (active selected fallback : Nat) : Nat :=
  active * selected + (1 - active) * fallback

def p1224EqBit (a b : Nat) : Nat := if a = b then 1 else 0

def p1224MarkAdvanceFlagsInstrs (c : CellCfg) : List Instr :=
  [ .binop 46 .mul (.reg 10) (.reg 27)
  , .binop 47 .udiv (.lit c.hi) (.reg rBp)
  , .binop 48 .le (.reg rQp) (.reg 47)
  , .binop 49 .mul (.reg 46) (.reg 48)
  , .binop 50 .sub (.reg 46) (.reg 49) ]

def p1224MarkAdvanceFlagsBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkAdvanceFlagsInstrs c)

theorem p1224MarkAdvanceFlagsBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 44).take (p1224MarkAdvanceFlagsBody c).length =
      p1224MarkAdvanceFlagsBody c := by
  rfl

theorem p1224MarkAdvanceFlagsBody_run (c : CellCfg) (k : Nat)
    (s : AState) (h10 : s.regs 10 ≤ 1) (h27 : s.regs 27 ≤ 1)
    (hbase : 0 < s.regs rBp) (hhi : c.hi < M) :
    let active := p1224AdvanceActive (s.regs 10) (s.regs 27)
    let bump := c.p1224BumpPower (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let step := c.p1224StepPrime (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let out := arun k s (p1224MarkAdvanceFlagsBody c)
    out.regs 46 = active ∧
      out.regs 47 = c.hi / s.regs rBp ∧
      out.regs 48 = c.p1224PowerFits (s.regs rQp) (s.regs rBp) ∧
      out.regs 49 = bump ∧ out.regs 50 = step ∧
      out.regs rQp = s.regs rQp ∧ out.regs rBp = s.regs rBp ∧
      out.arr = s.arr := by
  have hbase' : s.regs 170 ≠ 0 := by
    simpa [rBp] using Nat.ne_of_gt hbase
  have hhiMod : c.hi % M = c.hi := Nat.mod_eq_of_lt hhi
  have hdivM : c.hi / s.regs 170 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hdivMod : (c.hi / s.regs 170) % M = c.hi / s.regs 170 :=
    Nat.mod_eq_of_lt hdivM
  have honeMod : (1 : Nat) % M = 1 := by decide
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hfit' : s.regs 3 ≤ c.hi / s.regs 170 ↔
      s.regs 3 * s.regs 170 ≤ c.hi := by
    simpa [rBp] using (Nat.le_div_iff_mul_le hbase)
  simp only [p1224MarkAdvanceFlagsBody, arun_lift]
  by_cases ha : s.regs 10 = 0
  · by_cases hp : s.regs 27 = 0
    · simp [p1224MarkAdvanceFlagsInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, p1224AdvanceActive,
        CellCfg.p1224PowerFits, CellCfg.p1224BumpPower,
        CellCfg.p1224StepPrime, ha, hp, hbase', hhiMod, hdivMod, hfit',
        rQp, rBp]
    · have hp1 : s.regs 27 = 1 := by omega
      simp [p1224MarkAdvanceFlagsInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, p1224AdvanceActive,
        CellCfg.p1224PowerFits, CellCfg.p1224BumpPower,
        CellCfg.p1224StepPrime, ha, hp1, hbase', hhiMod, hdivMod, hfit',
        rQp, rBp]
  · have ha1 : s.regs 10 = 1 := by omega
    by_cases hp : s.regs 27 = 0
    · simp [p1224MarkAdvanceFlagsInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, p1224AdvanceActive,
        CellCfg.p1224PowerFits, CellCfg.p1224BumpPower,
        CellCfg.p1224StepPrime, ha1, hp, hbase', hhiMod, hdivMod, hfit',
        rQp, rBp]
    · have hp1 : s.regs 27 = 1 := by omega
      by_cases hf : s.regs rQp * s.regs rBp ≤ c.hi
      · have hf' : s.regs 3 * s.regs 170 ≤ c.hi := by
          simpa [rQp, rBp] using hf
        have hqfit : s.regs 3 ≤ c.hi / s.regs 170 := hfit'.2 hf'
        simp [p1224MarkAdvanceFlagsInstrs, srun, RegState.set, sdest,
          sval, denoteOperand, denoteOp, p1224AdvanceActive,
          CellCfg.p1224PowerFits, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, ha1, hp1, hf', hbase', hhiMod,
          hdivMod, hqfit, honeMod, hzero, rQp, rBp]
      · have hf' : ¬ s.regs 3 * s.regs 170 ≤ c.hi := by
          simpa [rQp, rBp] using hf
        have hqfit : ¬s.regs 3 ≤ c.hi / s.regs 170 :=
          fun h => hf' (hfit'.1 h)
        simp [p1224MarkAdvanceFlagsInstrs, srun, RegState.set, sdest,
          sval, denoteOperand, denoteOp, p1224AdvanceActive,
          CellCfg.p1224PowerFits, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, ha1, hp1, hf', hbase', hhiMod,
          hdivMod, hqfit, honeMod, rQp, rBp]

def p1224MarkAdvancePiInstrs (c : CellCfg) : List Instr :=
  [ .binop 51 .add (.reg rPi) (.reg 50)
  , .binop 52 .gt (.reg 51) (.lit c.tableLen)
  , .binop 53 .sub (.lit 1) (.reg 52)
  , .binop 54 .mul (.reg 53) (.reg 51)
  , .binop 55 .mul (.reg 52) (.lit c.tableLen)
  , .binop rPi .add (.reg 54) (.reg 55) ]

def p1224MarkAdvancePiBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkAdvancePiInstrs c)

theorem p1224MarkAdvancePiBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 49).take (p1224MarkAdvancePiBody c).length =
      p1224MarkAdvancePiBody c := by
  rfl

theorem p1224MarkAdvancePiBody_run (c : CellCfg) (k : Nat)
    (s : AState) (hsum : s.regs rPi + s.regs 50 < M)
    (hK : c.tableLen < M) :
    let candidate := s.regs rPi + s.regs 50
    let out := arun k s (p1224MarkAdvancePiBody c)
    out.regs 51 = candidate ∧
      out.regs 52 = (if candidate > c.tableLen then 1 else 0) ∧
      out.regs 53 = (if candidate > c.tableLen then 0 else 1) ∧
      out.regs 54 = (if candidate > c.tableLen then 0 else candidate) ∧
      out.regs 55 = (if candidate > c.tableLen then c.tableLen else 0) ∧
      out.regs rPi = p1224ClampPi c.tableLen candidate ∧
      out.regs 50 = s.regs 50 ∧ out.arr = s.arr := by
  have hsum' : s.regs 2 + s.regs 50 < M := by
    simpa [rPi] using hsum
  have hsumMod : (s.regs 2 + s.regs 50) % M =
      s.regs 2 + s.regs 50 := Nat.mod_eq_of_lt hsum'
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have honeMod : (1 : Nat) % M = 1 := by decide
  have hsub : 1 + (M - 1) = M := by omega
  simp only [p1224MarkAdvancePiBody, arun_lift]
  by_cases hover : s.regs rPi + s.regs 50 > c.tableLen
  · have hover' : s.regs 2 + s.regs 50 > c.tableLen := by
      simpa [rPi] using hover
    simp [p1224MarkAdvancePiInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, p1224ClampPi, hover', hsumMod, hKMod,
      honeMod, hsub, rPi]
  · have hover' : ¬ s.regs 2 + s.regs 50 > c.tableLen := by
      simpa [rPi] using hover
    simp [p1224MarkAdvancePiInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, p1224ClampPi, hover', hsumMod, hKMod,
      honeMod, rPi]

def p1224MarkAdvanceLoadBody (c : CellCfg) : List AInstr :=
  [ .scalar (.binop 56 .add (.reg rPi) (.lit c.tableBase))
  , .load 57 56 ]

theorem p1224MarkAdvanceLoadBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 55).take (p1224MarkAdvanceLoadBody c).length =
      p1224MarkAdvanceLoadBody c := by
  rfl

theorem p1224MarkAdvanceLoadBody_run (c : CellCfg) (k : Nat)
    (s : AState) (haddr : s.regs rPi + c.tableBase < M) :
    let address := s.regs rPi + c.tableBase
    let out := arun k s (p1224MarkAdvanceLoadBody c)
    out.regs 56 = address ∧ out.regs 57 = s.arr address ∧
      out.regs rPi = s.regs rPi ∧ out.arr = s.arr := by
  have haddr' : s.regs 2 + c.tableBase < M := by
    simpa [rPi] using haddr
  have hbase : c.tableBase < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) haddr'
  simp [p1224MarkAdvanceLoadBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt haddr', Nat.mod_eq_of_lt hbase, rPi]

def p1224MarkAdvanceValueInstrs : List Instr :=
  [ .binop 58 .sub (.lit 1) (.reg 46)
  , .binop 59 .add (.reg rJ) (.reg rQp)
  , .binop 60 .mul (.reg rQp) (.reg rBp)
  , .binop 61 .mul (.reg 49) (.reg 60)
  , .binop 62 .mul (.reg 50) (.reg 57)
  , .binop 63 .add (.reg 61) (.reg 62)
  , .binop 64 .mul (.reg 58) (.reg rQp)
  , .binop rQp .add (.reg 63) (.reg 64)
  , .binop 65 .sub (.reg 57) (.reg rBp)
  , .binop 66 .mul (.reg 50) (.reg 65)
  , .binop rBp .add (.reg rBp) (.reg 66)
  , .binop 67 .mul (.reg 58) (.reg rFs)
  , .binop rFs .add (.reg 50) (.reg 67) ]

def p1224MarkAdvanceValueBody : List AInstr :=
  lift p1224MarkAdvanceValueInstrs

theorem p1224MarkAdvanceValueBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 57).take p1224MarkAdvanceValueBody.length =
      p1224MarkAdvanceValueBody := by
  rfl

theorem p1224AdvanceModeFacts (c : CellCfg)
    (inMark pastWindow power prime : Nat)
    (hinMark : inMark ≤ 1) (hpastWindow : pastWindow ≤ 1) :
    p1224AdvanceActive inMark pastWindow ≤ 1 ∧
      c.p1224BumpPower inMark pastWindow power prime ≤ 1 ∧
      c.p1224StepPrime inMark pastWindow power prime ≤ 1 ∧
      c.p1224BumpPower inMark pastWindow power prime +
        c.p1224StepPrime inMark pastWindow power prime =
          p1224AdvanceActive inMark pastWindow := by
  by_cases hi : inMark = 0
  · simp [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, hi]
  · have hi1 : inMark = 1 := by omega
    by_cases hp : pastWindow = 0
    · simp [p1224AdvanceActive, CellCfg.p1224BumpPower,
        CellCfg.p1224StepPrime, hi1, hp]
    · have hp1 : pastWindow = 1 := by omega
      by_cases hf : power * prime ≤ c.hi
      · simp [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, CellCfg.p1224PowerFits, hi1, hp1, hf]
      · simp [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, CellCfg.p1224PowerFits, hi1, hp1, hf]

theorem p1224MarkAdvanceValueBody_run (k : Nat) (s : AState)
    (hactive : s.regs 46 ≤ 1) (hbump : s.regs 49 ≤ 1)
    (hstep : s.regs 50 ≤ 1)
    (hmodes : s.regs 49 + s.regs 50 = s.regs 46)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hbpWord : s.regs rBp < M)
    (hqOut : p1224NextPowerValue (s.regs 46) (s.regs 49)
      (s.regs 50) (s.regs rQp)
        (s.regs rQp * s.regs rBp) (s.regs 57) < M)
    (hbpOut : p1224NextBaseValue (s.regs 50) (s.regs rBp)
      (s.regs 57) < M)
    (hfsOut : p1224NextFirstValue (s.regs 46) (s.regs 50)
      (s.regs rFs) < M) :
    let out := arun k s p1224MarkAdvanceValueBody
    out.regs 58 = 1 - s.regs 46 ∧
      out.regs 59 = s.regs rJ + s.regs rQp ∧
      out.regs rQp = p1224NextPowerValue (s.regs 46) (s.regs 49)
        (s.regs 50) (s.regs rQp)
          (s.regs rQp * s.regs rBp) (s.regs 57) ∧
      out.regs rBp = p1224NextBaseValue (s.regs 50) (s.regs rBp)
        (s.regs 57) ∧
      out.regs rFs = p1224NextFirstValue (s.regs 46) (s.regs 50)
        (s.regs rFs) ∧ out.arr = s.arr := by
  have hjQ' : s.regs 4 + s.regs 3 < M := by
    simpa [rJ, rQp] using hjQ
  have hjQMod : (s.regs 4 + s.regs 3) % M =
      s.regs 4 + s.regs 3 := Nat.mod_eq_of_lt hjQ'
  have honeMod : (1 : Nat) % M = 1 := by decide
  have hsub : 1 + (M - 1) = M := by omega
  simp only [p1224MarkAdvanceValueBody, arun_lift]
  by_cases ha : s.regs 46 = 0
  · have hb : s.regs 49 = 0 := by omega
    have hs : s.regs 50 = 0 := by omega
    have hq : s.regs 3 < M := by
      simpa [p1224NextPowerValue, ha, hb, hs, rQp] using hqOut
    have hbp : s.regs 170 < M := by
      simpa [p1224NextBaseValue, hs, rBp] using hbpOut
    have hfs : s.regs 172 < M := by
      simpa [p1224NextFirstValue, ha, hs, rFs] using hfsOut
    simp [p1224MarkAdvanceValueInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, p1224NextPowerValue, p1224NextBaseValue,
      p1224NextFirstValue, ha, hb, hs, hjQMod,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hbp,
      Nat.mod_eq_of_lt hfs, honeMod, rJ, rQp, rBp, rFs]
  · have ha1 : s.regs 46 = 1 := by omega
    by_cases hb : s.regs 49 = 0
    · have hs : s.regs 50 = 1 := by omega
      have hprime : s.regs 57 < M := by
        simpa [p1224NextPowerValue, ha1, hb, hs, rQp] using hqOut
      have hbaseSub :
          (s.regs rBp + (s.regs 57 + (M - s.regs rBp))) % M =
            s.regs 57 := by
        have heq :
            s.regs rBp + (s.regs 57 + (M - s.regs rBp)) =
              M + s.regs 57 := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hprime]
      have hbaseSub' :
          (s.regs 170 + (s.regs 57 + (M - s.regs 170))) % M =
            s.regs 57 := by simpa [rBp] using hbaseSub
      simp [p1224MarkAdvanceValueInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, p1224NextPowerValue,
        p1224NextBaseValue, p1224NextFirstValue, ha1, hb, hs, hjQMod,
        Nat.mod_eq_of_lt hprime, hbaseSub', honeMod, hsub, rJ, rQp,
        rBp, rFs]
    · have hb1 : s.regs 49 = 1 := by omega
      have hs : s.regs 50 = 0 := by omega
      have hpower : s.regs rQp * s.regs rBp < M := by
        simpa [p1224NextPowerValue, ha1, hb1, hs, rQp] using hqOut
      have hpower' : s.regs 3 * s.regs 170 < M := by
        simpa [rQp, rBp] using hpower
      have hbp : s.regs 170 < M := by simpa [rBp] using hbpWord
      simp [p1224MarkAdvanceValueInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, p1224NextPowerValue,
        p1224NextBaseValue, p1224NextFirstValue, ha1, hb1, hs, hjQMod,
        Nat.mod_eq_of_lt hpower', Nat.mod_eq_of_lt hbp, honeMod, hsub,
        rJ, rQp, rBp, rFs]

def p1224MarkAdvanceOffsetInstrs (c : CellCfg) : List Instr :=
  [ .binop 68 .urem (.reg rW) (.reg rQp)
  , .binop 69 .sub (.reg rQp) (.reg 68)
  , .binop 70 .urem (.reg 69) (.reg rQp)
  , .binop 71 .eq (.reg rPi) (.lit c.tableLen)
  , .binop 72 .sub (.lit 1) (.reg 71)
  , .binop 73 .mul (.reg 71) (.lit (c.segLen + 1))
  , .binop 74 .mul (.reg 72) (.reg 70)
  , .binop 75 .add (.reg 73) (.reg 74)
  , .binop 76 .mul (.reg 46) (.reg 75)
  , .binop 77 .mul (.reg 58) (.reg 59)
  , .binop rJ .add (.reg 76) (.reg 77) ]

def p1224MarkAdvanceOffsetBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkAdvanceOffsetInstrs c)

theorem p1224MarkAdvanceOffsetBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 70).take (p1224MarkAdvanceOffsetBody c).length =
      p1224MarkAdvanceOffsetBody c := by
  rfl

theorem p1224MarkAdvanceOffsetBody_run (c : CellCfg) (k : Nat)
    (s : AState) (hactive : s.regs 46 ≤ 1)
    (hnot : s.regs 58 = 1 - s.regs 46)
    (hq0 : s.regs rQp ≠ 0) (hq : s.regs rQp < M)
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M)
    (hfallback : s.regs 59 < M) :
    let selected := c.p1224SelectedOffset (s.regs rPi)
      (s.regs rW) (s.regs rQp)
    let value := p1224NextOffset (s.regs 46) selected (s.regs 59)
    let out := arun k s (p1224MarkAdvanceOffsetBody c)
    out.regs 68 = s.regs rW % s.regs rQp ∧
      out.regs 70 = p1224StartOffset (s.regs rW) (s.regs rQp) ∧
      out.regs 71 = p1224EqBit (s.regs rPi) c.tableLen ∧
      out.regs 75 = selected ∧ out.regs rJ = value ∧
      out.regs rPi = s.regs rPi ∧ out.regs rQp = s.regs rQp ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  have hq3 : s.regs 3 ≠ 0 := by simpa [rQp] using hq0
  have hq3M : s.regs 3 < M := by simpa [rQp] using hq
  have hrem : s.regs 6 % s.regs 3 < s.regs 3 :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hq3)
  have hremM : s.regs 6 % s.regs 3 < M := Nat.lt_trans hrem hq3M
  have hremMod : (s.regs 6 % s.regs 3) % M =
      s.regs 6 % s.regs 3 := Nat.mod_eq_of_lt hremM
  have hsubM : s.regs 3 - s.regs 6 % s.regs 3 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq3M
  have hsubWord :
      (s.regs 3 + (M - s.regs 6 % s.regs 3)) % M =
        s.regs 3 - s.regs 6 % s.regs 3 := by
    have hrew : s.regs 3 + (M - s.regs 6 % s.regs 3) =
        M + (s.regs 3 - s.regs 6 % s.regs 3) := by omega
    rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt hsubM]
  have hoff : (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 < M :=
    Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hq3)) hq3M
  have hoffMod :
      ((s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3) % M =
        (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 :=
    Nat.mod_eq_of_lt hoff
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have hL1Mod : (c.segLen + 1) % M = c.segLen + 1 :=
    Nat.mod_eq_of_lt hL1
  have hfMod : s.regs 59 % M = s.regs 59 :=
    Nat.mod_eq_of_lt hfallback
  have honeMod : (1 : Nat) % M = 1 := by decide
  have hsubOne : 1 + (M - 1) = M := by omega
  simp only [p1224MarkAdvanceOffsetBody, arun_lift]
  by_cases ha : s.regs 46 = 0
  · have h58 : s.regs 58 = 1 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp' : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkAdvanceOffsetInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, CellCfg.p1224SelectedOffset,
        p1224StartOffset, p1224NextOffset, p1224EqBit, ha, h58, hp',
        hq3, hremMod, hsubWord, hoffMod, hKMod, hL1Mod, hfMod,
        honeMod, hsubOne, rPi, rQp, rW, rJ]
    · have hp' : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkAdvanceOffsetInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, CellCfg.p1224SelectedOffset,
        p1224StartOffset, p1224NextOffset, p1224EqBit, ha, h58, hp',
        hq3, hremMod, hsubWord, hoffMod, hKMod, hfMod, honeMod,
        rPi, rQp, rW, rJ]
  · have ha1 : s.regs 46 = 1 := by omega
    have h58 : s.regs 58 = 0 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp' : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkAdvanceOffsetInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, CellCfg.p1224SelectedOffset,
        p1224StartOffset, p1224NextOffset, p1224EqBit, ha1, h58, hp',
        hq3, hremMod, hsubWord, hoffMod, hKMod, hL1Mod, honeMod,
        hsubOne, rPi, rQp, rW, rJ]
    · have hp' : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [p1224MarkAdvanceOffsetInstrs, srun, RegState.set, sdest,
        sval, denoteOperand, denoteOp, CellCfg.p1224SelectedOffset,
        p1224StartOffset, p1224NextOffset, p1224EqBit, ha1, h58, hp',
        hq3, hremMod, hsubWord, hoffMod, hKMod, honeMod,
        rPi, rQp, rW, rJ]

#print axioms p1224MarkAdvanceFlagsBody_run
#print axioms p1224MarkAdvancePiBody_run
#print axioms p1224MarkAdvanceLoadBody_run
#print axioms p1224AdvanceModeFacts
#print axioms p1224MarkAdvanceValueBody_run
#print axioms p1224MarkAdvanceOffsetBody_run

end LeanCompCert.Ports.Prop1224Cell
