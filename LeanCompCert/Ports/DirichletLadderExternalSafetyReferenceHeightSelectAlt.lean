import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightSelectBit

set_option autoImplicit false
namespace LeanCompCert.Ports.DirichletLadderExternalSafety
open LeanCompCert LeanCompCert.Verified.Reflect LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge LeanCompCert.Ports.DirichletLadder

def historicalHeightSelectAlt (c : Cfg) : List AInstr := (c.bodyBlock.drop 191).take 1
theorem historicalHeightSelectAlt_eq_source (c : Cfg) :
    historicalHeightSelectAlt c = [bo 150 .mul (.reg 149) (.reg 148)] := by rfl
theorem historicalHeightSelectAlt_result
    (c : Cfg) (idx bit alt : Nat) (s : AState)
    (hb : s.regs 149 = bit) (ha : s.regs 148 = alt)
    (hbit : bit ≤ 1) (halt : alt < M) :
    (arun idx s (historicalHeightSelectAlt c)).regs 150 = bit * alt := by
  have hw : bit * alt < M := by
    rcases (by omega : bit = 0 ∨ bit = 1) with rfl | rfl
    · simp [M]
    · simpa using halt
  simp [historicalHeightSelectAlt_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hb, ha, Nat.mod_eq_of_lt hw]
end LeanCompCert.Ports.DirichletLadderExternalSafety
