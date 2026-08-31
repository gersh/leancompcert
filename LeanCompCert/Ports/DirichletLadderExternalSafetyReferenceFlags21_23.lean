import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCoverage

/-! Historical reference flags 21--23: conjugate constancy and absent
off-closing-block Turing fields. -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalFlag21 (c : Cfg) := (c.bodyBlock.drop 220).take 3
def historicalFlag22 (c : Cfg) := (c.bodyBlock.drop 223).take 4
def historicalFlag23 (c : Cfg) := (c.bodyBlock.drop 227).take 3

theorem historicalFlag21_eq_source (c : Cfg) : historicalFlag21 c =
    [ bo 154 .ne (.reg 32) (.reg rPrevConj)
    , bo 154 .mul (.reg 33) (.reg 154)
    , bo rViol .add (.reg rViol) (.reg 154) ] := by rfl

theorem historicalFlag22_eq_source (c : Cfg) : historicalFlag22 c =
    [ bo 155 .sub (.lit 1) (.reg 48)
    , bo 156 .ne (.reg 29) (.lit 0)
    , bo 156 .mul (.reg 155) (.reg 156)
    , bo rViol .add (.reg rViol) (.reg 156) ] := by rfl

theorem historicalFlag23_eq_source (c : Cfg) : historicalFlag23 c =
    [ bo 157 .ne (.reg 30) (.lit 0)
    , bo 157 .mul (.reg 155) (.reg 157)
    , bo rViol .add (.reg rViol) (.reg 157) ] := by rfl

theorem historicalFlag21_result
    (c : Cfg) (idx n cj prevConj : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n) (hcj : s.regs 32 = cj)
    (hp : s.regs rPrevConj = prevConj)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hw : n + 1 < M) :
    (arun idx s (historicalFlag21 c)).regs rViol =
      bump (same && cj != prevConj) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hp11 : s.regs 11 = prevConj := by simpa [rPrevConj] using hp
  cases same <;>
    simp [historicalFlag21_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hcj, hp11, hsame, bump, rViol, rPrevConj,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]
  all_goals by_cases h : cj = prevConj <;>
    simp_all [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]

theorem historicalFlag22_result
    (c : Cfg) (idx n uElem : Nat) (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hu : s.regs 29 = uElem)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hw : n + 1 < M) :
    let out := arun idx s (historicalFlag22 c)
    out.regs rViol = bump (!isLastB && uElem != 0) n ∧
      out.regs 155 = if !isLastB then 1 else 0 := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  cases isLastB <;>
    simp [historicalFlag22_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hu, hgate, bump, hsub1, rViol,
      Nat.mod_eq_of_lt one_lt_M, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hw]
  all_goals by_cases h : uElem = 0 <;>
    simp_all [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]

theorem historicalFlag23_result
    (c : Cfg) (idx n henc : Nat) (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hh : s.regs 30 = henc)
    (hnotgate : s.regs 155 = if !isLastB then 1 else 0)
    (hw : n + 1 < M) :
    (arun idx s (historicalFlag23 c)).regs rViol =
      bump (!isLastB && henc != 0) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  cases isLastB <;>
    simp [historicalFlag23_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hh, hnotgate, bump, rViol,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]
  all_goals by_cases h : henc = 0 <;>
    simp_all [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hw]

end LeanCompCert.Ports.DirichletLadderExternalSafety
