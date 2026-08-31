import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightAlt

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightSelectBit (c : Cfg) : List AInstr := (c.bodyBlock.drop 190).take 1
theorem historicalHeightSelectBit_eq_source (c : Cfg) :
    historicalHeightSelectBit c = [bo 149 .ge (.reg 148) (.lit c.hFloor)] := by rfl
theorem historicalHeightSelectBit_sourceCfg_result
    (records termDigest idx alt : Nat) (s : AState) (halt : s.regs 148 = alt) :
    (arun idx s (historicalHeightSelectBit (sourceCfg records termDigest))).regs 149 =
      if 100000000 ≤ alt then 1 else 0 := by
  simp [historicalHeightSelectBit_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, halt, sourceCfg, Nat.mod_eq_of_lt (by decide : 100000000 < M)]
end LeanCompCert.Ports.DirichletLadderExternalSafety
