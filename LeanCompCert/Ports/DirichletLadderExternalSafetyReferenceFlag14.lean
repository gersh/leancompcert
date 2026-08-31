import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag13

/-! Historical upper side of the terminal U-window (163--171). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag14 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 163).take 9

theorem historicalFlag14_eq_source (c : Cfg) :
    historicalFlag14 c =
      [ bo 117 .mul (.reg 115) (.reg 29)
      , bo 118 .mul (.reg 115) (.reg 114)
      , bo 119 .sub (.reg 117) (.reg 118)
      , bo 120 .add (.reg 25) (.lit 1)
      , bo 121 .mul (.reg 120) (.reg 30)
      , bo 122 .lt (.reg 119) (.reg 121)
      , bo 123 .sub (.lit 1) (.reg 122)
      , bo 123 .mul (.reg 48) (.reg 123)
      , bo rViol .add (.reg rViol) (.reg 123) ] := by rfl

theorem historicalFlag14_result
    (c : Cfg) (idx n scaled uElem upper henc : Nat)
    (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hscaled : s.regs 114 = scaled)
    (huoknum : s.regs 115 = if scaled ≤ uElem then 1 else 0)
    (huElem : s.regs 29 = uElem) (hupper : s.regs 25 = upper)
    (hhenc : s.regs 30 = henc)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hscaledWord : scaled < M) (huWord : uElem < M)
    (hupperSucc : upper + 1 < M)
    (hproduct : (upper + 1) * henc < M)
    (hNoWrap : n + 1 < M) :
    let uOk := scaled ≤ uElem
    let uEnc := if uOk then uElem - scaled else 0
    let upperProduct := (upper + 1) * henc
    let out := arun idx s (historicalFlag14 c)
    out.regs rViol = bump (isLastB && !(uEnc < upperProduct)) n ∧
      out.regs 119 = uEnc ∧ out.regs 121 = upperProduct := by
  have hn : n < M := by omega
  have hencWord : henc < M := by
    by_cases hz : henc = 0
    · simp [hz, M]
    · have hp : henc ≤ (upper + 1) * henc := by
        have : 1 ≤ upper + 1 := by omega
        exact Nat.le_mul_of_pos_left henc (by omega)
      omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp [historicalFlag14_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, hscaled, huoknum, huElem, hupper, hhenc, hgate,
    Nat.mod_eq_of_lt one_lt_M, Nat.mod_eq_of_lt hscaledWord,
    Nat.mod_eq_of_lt huWord, Nat.mod_eq_of_lt hupperSucc,
    Nat.mod_eq_of_lt hproduct, rViol]
  by_cases huok : scaled ≤ uElem
  · have hsubExact := modular_sub_eq uElem scaled huok huWord
    simp only [if_pos huok, Nat.one_mul]
    rw [Nat.mod_eq_of_lt hscaledWord, hsubExact]
    by_cases hup : uElem - scaled < (upper + 1) * henc
    · cases isLastB <;>
        simp [huok, hup, bump, hsub1, Nat.add_mod_right,
          Nat.mod_eq_of_lt hn]
    · cases isLastB
      · simp [huok, hup, bump, Nat.mod_eq_of_lt hn]
      · simp [huok, hup, bump]
        rw [show n + (1 + M) = (n + 1) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hNoWrap]
  · simp only [if_neg huok, Nat.zero_mul, Nat.zero_mod]
    have hzero : (0 + (M - 0)) % M = 0 := by simp [M]
    rw [hzero]
    by_cases hup : 0 < (upper + 1) * henc
    · cases isLastB <;>
        simp [huok, hup, bump, hsub1, Nat.add_mod_right,
          Nat.mod_eq_of_lt hn]
    · cases isLastB
      · simp [huok, hup, bump, Nat.mod_eq_of_lt hn]
      · simp [huok, hup, bump]
        rw [show n + (1 + M) = (n + 1) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety
