import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightSelectFloor

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightSelectSum (c : Cfg) : List AInstr := (c.bodyBlock.drop 194).take 1
theorem historicalHeightSelectSum_eq_source (c : Cfg) :
    historicalHeightSelectSum c = [bo 152 .add (.reg 150) (.reg 151)] := by rfl
theorem historicalHeightSelectSum_result
    (c : Cfg) (idx selectedAlt selectedFloor : Nat) (s : AState)
    (ha : s.regs 150 = selectedAlt) (hf : s.regs 151 = selectedFloor)
    (hsum : selectedAlt + selectedFloor < M) :
    (arun idx s (historicalHeightSelectSum c)).regs 152 = selectedAlt + selectedFloor := by
  simp [historicalHeightSelectSum_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ha, hf, Nat.mod_eq_of_lt hsum]
end LeanCompCert.Ports.DirichletLadderExternalSafety
