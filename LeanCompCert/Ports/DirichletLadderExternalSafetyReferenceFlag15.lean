import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag14

/-! Historical lower side of the terminal U-window (172--175). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag15 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 172).take 4

theorem historicalFlag15_eq_source (c : Cfg) :
    historicalFlag15 c =
      [ bo 161 .mul (.reg 25) (.reg 30)
      , bo 162 .lt (.reg 119) (.reg 161)
      , bo 162 .mul (.reg 48) (.reg 162)
      , bo rViol .add (.reg rViol) (.reg 162) ] := by rfl

theorem historicalFlag15_result
    (c : Cfg) (idx n uEnc upper henc : Nat)
    (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (huEnc : s.regs 119 = uEnc)
    (hupper : s.regs 25 = upper) (hhenc : s.regs 30 = henc)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hproduct : upper * henc < M) (hNoWrap : n + 1 < M) :
    (arun idx s (historicalFlag15 c)).regs rViol =
      bump (isLastB && uEnc < upper * henc) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  simp [historicalFlag15_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, huEnc, hupper, hhenc, hgate,
    Nat.mod_eq_of_lt hproduct, rViol]
  by_cases hlo : uEnc < upper * henc
  · cases isLastB
    · simp [hlo, bump, Nat.mod_eq_of_lt hn]
    · simp [hlo, bump]
      rw [show n + 1 = n + 1 by rfl, Nat.mod_eq_of_lt hNoWrap]
  · cases isLastB <;> simp [hlo, bump, Nat.mod_eq_of_lt hn]

end LeanCompCert.Ports.DirichletLadderExternalSafety
