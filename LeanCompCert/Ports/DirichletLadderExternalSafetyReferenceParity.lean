import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag15

/-! Historical terminal parity flag (176--181), reference flag 17. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalParity (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 176).take 6

theorem historicalParity_eq_source (c : Cfg) :
    historicalParity c =
      [ bo 124 .eq (.reg rFirstBit) (.reg 97)
      , bo 125 .band (.reg 25) (.lit 1)
      , bo 126 .sub (.lit 1) (.reg 125)
      , bo 127 .ne (.reg 124) (.reg 126)
      , bo 127 .mul (.reg 48) (.reg 127)
      , bo rViol .add (.reg rViol) (.reg 127) ] := by rfl

theorem historicalParity_result
    (c : Cfg) (idx n firstBit lastBit upper : Nat)
    (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hfirst : s.regs rFirstBit = firstBit)
    (hlast : s.regs 97 = lastBit) (hupper : s.regs 25 = upper)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hfirstb : firstBit ≤ 1) (hlastb : lastBit ≤ 1)
    (hupperWord : upper < M) (hNoWrap : n + 1 < M) :
    (arun idx s (historicalParity c)).regs rViol =
      bump (isLastB && ((firstBit == lastBit) != (upper % 2 == 0))) n := by
  have hn : n < M := by omega
  have hpar : upper % 2 ≤ 1 := by
    have := Nat.mod_lt upper (by decide : 0 < 2)
    omega
  have hparWord : upper % 2 < M := by simp only [M]; omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hf0 : s.regs 5 = firstBit := by simpa [rFirstBit] using hfirst
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  have hOneMod : 1 % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hMne : M ≠ 1 := by simp [M]
  simp [historicalParity_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, hf0, hlast, hupper, hgate,
    Nat.mod_eq_of_lt one_lt_M, Nat.mod_eq_of_lt hupperWord,
    and_one_eq_mod_two, Nat.mod_eq_of_lt hparWord, rViol, rFirstBit]
  have hfirstCases : firstBit = 0 ∨ firstBit = 1 := by omega
  have hlastCases : lastBit = 0 ∨ lastBit = 1 := by omega
  have hparCases : upper % 2 = 0 ∨ upper % 2 = 1 := by omega
  rcases hfirstCases with rfl | rfl <;>
    rcases hlastCases with rfl | rfl <;>
    rcases hparCases with hp | hp <;>
    cases isLastB <;>
    simp [hp, bump, hsub1, hOneMod, hMne, Nat.add_mod_right,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety
