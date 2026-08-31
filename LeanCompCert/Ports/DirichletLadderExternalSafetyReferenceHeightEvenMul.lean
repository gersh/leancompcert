import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightComplement

/-! Scale the complemented q-parity bit by the even constant (186). -/

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightEvenMul (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 186).take 1

theorem historicalHeightEvenMul_eq_source (c : Cfg) :
    historicalHeightEvenMul c = [bo 146 .mul (.reg 146) (.lit c.hEven)] := by rfl

theorem historicalHeightEvenMul_sourceCfg_result
    (records termDigest idx complement : Nat) (s : AState)
    (hc : s.regs 146 = complement) (hcomplement : complement ≤ 1) :
    (arun idx s (historicalHeightEvenMul (sourceCfg records termDigest))).regs 146 =
      complement * 75000000 := by
  have hword : complement * 75000000 < M := by simp only [M]; omega
  simp [historicalHeightEvenMul_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hc, sourceCfg, Nat.mod_eq_of_lt hword]

end LeanCompCert.Ports.DirichletLadderExternalSafety
