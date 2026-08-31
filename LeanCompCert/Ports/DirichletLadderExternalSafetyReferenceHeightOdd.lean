import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightQ

/-! Odd height-constant component (184). -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightOdd (c : Cfg) : List AInstr := (c.bodyBlock.drop 184).take 1

theorem historicalHeightOdd_eq_source (c : Cfg) :
    historicalHeightOdd c = [bo 145 .mul (.reg 144) (.lit c.hOdd)] := by rfl

theorem historicalHeightOdd_sourceCfg_result
    (records termDigest idx parity : Nat) (s : AState)
    (hp : s.regs 144 = parity) (hparity : parity ≤ 1) :
    (arun idx s (historicalHeightOdd (sourceCfg records termDigest))).regs 145 =
      parity * 37500000 := by
  have hword : parity * 37500000 < M := by simp only [M]; omega
  simp [historicalHeightOdd_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hp, sourceCfg, Nat.mod_eq_of_lt hword]

end LeanCompCert.Ports.DirichletLadderExternalSafety
