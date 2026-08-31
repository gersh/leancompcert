import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag12

/-! Historical staircase scaling and U-underflow flag (155--162). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag13 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 155).take 8

theorem historicalFlag13_eq_source (c : Cfg) :
    historicalFlag13 c =
      [ bo 111 .mul (.reg 109) (.reg 107)
      , bo 112 .mul (.reg 109) (.reg 108)
      , bo 113 .sub (.reg 111) (.reg 112)
      , bo 114 .mul (.reg 113) (.lit 81920)
      , bo 115 .ge (.reg 29) (.reg 114)
      , bo 116 .sub (.lit 1) (.reg 115)
      , bo 116 .mul (.reg 48) (.reg 116)
      , bo rViol .add (.reg rViol) (.reg 116) ] := by rfl

theorem modular_sub_eq (a b : Nat) (hb : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hbM : b ≤ M := by omega
  rw [show a + (M - b) = (a - b) + M by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem historicalFlag13_result
    (c : Cfg) (idx n stair stairSub uElem : Nat)
    (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hstair : s.regs 107 = stair)
    (hsub : s.regs 108 = stairSub)
    (hoknum : s.regs 109 = if stairSub ≤ stair then 1 else 0)
    (huElem : s.regs 29 = uElem)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hstairBound : stair ≤ 12224) (hsubBound : stairSub ≤ 4480)
    (huWord : uElem < M) (hNoWrap : n + 1 < M) :
    let stairOk := stairSub ≤ stair
    let weight := if stairOk then stair - stairSub else 0
    let scaled := weight * 81920
    let uOk := scaled ≤ uElem
    let out := arun idx s (historicalFlag13 c)
    out.regs rViol = bump (isLastB && !uOk) n ∧
      out.regs 113 = weight ∧ out.regs 114 = scaled ∧
      out.regs 115 = if uOk then 1 else 0 := by
  have hn : n < M := by omega
  have hsWord : stair < M := by simp only [M]; omega
  have hssWord : stairSub < M := by simp only [M]; omega
  have hscaledAny : (stair - stairSub) * 81920 < M := by
    simp only [M]; omega
  have hlit : 81920 < M := by decide
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp [historicalFlag13_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, hstair, hsub, hoknum, huElem, hgate,
    Nat.mod_eq_of_lt one_lt_M, Nat.mod_eq_of_lt hsWord,
    Nat.mod_eq_of_lt hssWord, Nat.mod_eq_of_lt hlit, rViol]
  by_cases hsok : stairSub ≤ stair
  · have hsubExact := modular_sub_eq stair stairSub hsok hsWord
    have hsum : stair + (M - stairSub) = (stair - stairSub) + M := by
      omega
    have hscaledExact :
        (stair + (M - stairSub)) * 81920 % M =
          (stair - stairSub) * 81920 := by
      rw [hsum, Nat.add_mul]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hscaledAny]
    simp only [if_pos hsok, Nat.one_mul]
    rw [Nat.mod_eq_of_lt hssWord]
    rw [hsubExact, hscaledExact]
    by_cases huok : (stair - stairSub) * 81920 ≤ uElem
    · cases isLastB <;>
        simp [hsok, huok, bump, hsub1, Nat.add_mod_right,
          Nat.mod_eq_of_lt hn]
    · cases isLastB
      · simp [hsok, huok, bump, Nat.mod_eq_of_lt hn]
      · simp [hsok, huok, bump]
        rw [show n + (1 + M) = (n + 1) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hNoWrap]
  · have hzero : (0 + (M - 0)) % M = 0 := by simp [M]
    simp only [if_neg hsok, Nat.zero_mul, Nat.zero_mod]
    rw [hzero]
    by_cases huok : 0 ≤ uElem
    · cases isLastB <;>
        simp [hsok, huok, bump, hsub1, Nat.add_mod_right,
          Nat.mod_eq_of_lt hn]
    · omega

end LeanCompCert.Ports.DirichletLadderExternalSafety
