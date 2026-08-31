import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightSelectComplement

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightSelectFloor (c : Cfg) : List AInstr := (c.bodyBlock.drop 193).take 1
theorem historicalHeightSelectFloor_eq_source (c : Cfg) :
    historicalHeightSelectFloor c = [bo 151 .mul (.reg 151) (.lit c.hFloor)] := by rfl
theorem historicalHeightSelectFloor_sourceCfg_result
    (records termDigest idx bit : Nat) (s : AState)
    (hb : s.regs 151 = bit) (hbit : bit ≤ 1) :
    (arun idx s (historicalHeightSelectFloor (sourceCfg records termDigest))).regs 151 =
      bit * 100000000 := by
  have hw : bit * 100000000 < M := by simp only [M]; omega
  simp [historicalHeightSelectFloor_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hb, sourceCfg, Nat.mod_eq_of_lt hw]
end LeanCompCert.Ports.DirichletLadderExternalSafety
