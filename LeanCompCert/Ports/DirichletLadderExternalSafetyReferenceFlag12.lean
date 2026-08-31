import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlags10_11

/-! Historical staircase non-negativity flag (instructions 145--154). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag12 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 145).take 10

theorem historicalFlag12_eq_source (c : Cfg) :
    historicalFlag12 c =
      [ bo 104 .mul (.reg rTrI0) (.lit 127)
      , bo 105 .mul (.reg 77) (.lit 63)
      , bo 106 .mul (.reg 98) (.lit 64)
      , bo 107 .add (.reg 104) (.reg 105)
      , bo 107 .add (.reg 107) (.reg 106)
      , bo 108 .add (.reg rSj0) (.reg 95)
      , bo 109 .ge (.reg 107) (.reg 108)
      , bo 110 .sub (.lit 1) (.reg 109)
      , bo 110 .mul (.reg 48) (.reg 110)
      , bo rViol .add (.reg rViol) (.reg 110) ] := by rfl

theorem historicalFlag12_result
    (c : Cfg) (idx n trI0 sj0 trI sj cross : Nat)
    (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (htrI0 : s.regs rTrI0 = trI0)
    (hsj0 : s.regs rSj0 = sj0) (htrI : s.regs 77 = trI)
    (hsj : s.regs 95 = sj) (hcross : s.regs 98 = cross)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (htrI0b : trI0 ≤ 64) (hsj0b : sj0 ≤ 2240)
    (htrIb : trI ≤ 64) (hsjb : sj ≤ 2240) (hcrossb : cross ≤ 1)
    (hNoWrap : n + 1 < M) :
    let stair := 127 * trI0 + 63 * trI + 64 * cross
    let stairSub := sj0 + sj
    let stairOk := stairSub ≤ stair
    let out := arun idx s (historicalFlag12 c)
    out.regs rViol = bump (isLastB && !stairOk) n ∧
      out.regs 107 = stair ∧ out.regs 108 = stairSub ∧
      out.regs 109 = if stairOk then 1 else 0 := by
  have hn : n < M := by omega
  have h104 : trI0 * 127 < M := by simp only [M]; omega
  have h105 : trI * 63 < M := by simp only [M]; omega
  have h106 : cross * 64 < M := by simp only [M]; omega
  have h107a : trI0 * 127 + trI * 63 < M := by simp only [M]; omega
  have h107 : trI0 * 127 + trI * 63 + cross * 64 < M := by
    simp only [M]; omega
  have h108 : sj0 + sj < M := by simp only [M]; omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have ht0 : s.regs 6 = trI0 := by simpa [rTrI0] using htrI0
  have hs0 : s.regs 7 = sj0 := by simpa [rSj0] using hsj0
  have hmul : trI0 * 127 + trI * 63 + cross * 64 =
      127 * trI0 + 63 * trI + 64 * cross := by
    simp [Nat.mul_comm]
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp [historicalFlag12_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, ht0, hs0, htrI, hsj, hcross, hgate,
    Nat.mod_eq_of_lt h104, Nat.mod_eq_of_lt h105,
    Nat.mod_eq_of_lt h106, Nat.mod_eq_of_lt h107a,
    Nat.mod_eq_of_lt h107, Nat.mod_eq_of_lt h108,
    Nat.mod_eq_of_lt one_lt_M, rViol, rTrI0, rSj0]
  rw [hmul]
  by_cases hok : sj0 + sj ≤ 127 * trI0 + 63 * trI + 64 * cross
  · have hge : decide (sj0 + sj ≤ 127 * trI0 + 63 * trI + 64 * cross) = true :=
      decide_eq_true hok
    cases isLastB <;>
      simp [hge, hok, bump, hsub1, Nat.add_mod_right,
        Nat.mod_eq_of_lt hn]
  · have hge : decide (sj0 + sj ≤ 127 * trI0 + 63 * trI + 64 * cross) = false :=
      decide_eq_false hok
    cases isLastB
    · simp [hge, hok, bump, Nat.mod_eq_of_lt hn]
    · simp [hge, hok, bump]
      rw [show n + (1 + M) = (n + 1) + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety
