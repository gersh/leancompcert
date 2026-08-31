import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightEvenMul

/-! Sum the two parity-dependent height components (187). -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightCQSum (c : Cfg) : List AInstr := (c.bodyBlock.drop 187).take 1

theorem historicalHeightCQSum_eq_source (c : Cfg) :
    historicalHeightCQSum c = [bo 147 .add (.reg 145) (.reg 146)] := by rfl

theorem historicalHeightCQSum_result
    (c : Cfg) (idx oddPart evenPart : Nat) (s : AState)
    (ho : s.regs 145 = oddPart) (he : s.regs 146 = evenPart)
    (hsum : oddPart + evenPart < M) :
    (arun idx s (historicalHeightCQSum c)).regs 147 = oddPart + evenPart := by
  simp [historicalHeightCQSum_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ho, he, Nat.mod_eq_of_lt hsum]

end LeanCompCert.Ports.DirichletLadderExternalSafety
