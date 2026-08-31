import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightOdd

/-! Complement the q-parity bit (185). -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightComplement (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 185).take 1

theorem historicalHeightComplement_eq_source (c : Cfg) :
    historicalHeightComplement c = [bo 146 .sub (.lit 1) (.reg 144)] := by rfl

theorem historicalHeightComplement_result
    (c : Cfg) (idx parity : Nat) (s : AState)
    (hp : s.regs 144 = parity) (hparity : parity ≤ 1) :
    (arun idx s (historicalHeightComplement c)).regs 146 = 1 - parity := by
  have hcases : parity = 0 ∨ parity = 1 := by omega
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp [historicalHeightComplement_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hp, Nat.mod_eq_of_lt one_lt_M]
  rcases hcases with rfl | rfl
  · simp [M]
  · simp [hsub1]

end LeanCompCert.Ports.DirichletLadderExternalSafety
