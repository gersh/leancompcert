import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightSelectAlt

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightSelectComplement (c : Cfg) : List AInstr := (c.bodyBlock.drop 192).take 1
theorem historicalHeightSelectComplement_eq_source (c : Cfg) :
    historicalHeightSelectComplement c = [bo 151 .sub (.lit 1) (.reg 149)] := by rfl
theorem historicalHeightSelectComplement_result
    (c : Cfg) (idx bit : Nat) (s : AState)
    (hb : s.regs 149 = bit) (hbit : bit ≤ 1) :
    (arun idx s (historicalHeightSelectComplement c)).regs 151 = 1 - bit := by
  have hcases : bit = 0 ∨ bit = 1 := by omega
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp [historicalHeightSelectComplement_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hb, Nat.mod_eq_of_lt one_lt_M]
  rcases hcases with rfl | rfl <;> simp [hsub1, M]
end LeanCompCert.Ports.DirichletLadderExternalSafety
