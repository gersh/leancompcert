import LeanCompCert.Ports.R2SegMarkingAdvanceLoad

/-! # Loaded prime-table word decoder for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markAdvanceDecodeInstrs : List Instr :=
  [ .binop 60 .band (.reg 59) (.lit maskVal)
  , .binop 61 .lshr (.reg 59) (.lit valBits)
  , .binop 62 .band (.reg 61) (.lit maskWt) ]

def markAdvanceDecodeBody : List AInstr := lift markAdvanceDecodeInstrs

theorem markAdvanceDecodeBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 66).take markAdvanceDecodeBody.length =
      markAdvanceDecodeBody := by
  rfl

/-- Decode the selected row into its base-prime and logarithmic-weight
fields.  The loaded word guard is the ordinary register invariant. -/
theorem markAdvanceDecodeBody_run (k : Nat) (s : AState)
    (hword : s.regs 59 < M) :
    let out := arun k s markAdvanceDecodeBody
    out.regs 60 = (s.regs 59 &&& maskVal) ∧
      out.regs 61 = s.regs 59 >>> valBits ∧
      out.regs 62 = ((s.regs 59 >>> valBits) &&& maskWt) ∧
      out.regs 59 = s.regs 59 ∧ out.arr = s.arr := by
  have hvalMod : maskVal % M = maskVal := by decide
  have hwtMod : maskWt % M = maskWt := by decide
  have hbitsMod : valBits % M = valBits := by decide
  have hval : maskVal < M := by decide
  have hwt : maskWt < M := by decide
  have hbandVal : (s.regs 59 &&& maskVal) % M =
      s.regs 59 &&& maskVal :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hval)
  have hshift : (s.regs 59 >>> valBits) % M =
      s.regs 59 >>> valBits :=
    Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hword)
  have hbandWt : ((s.regs 59 >>> valBits) &&& maskWt) % M =
      (s.regs 59 >>> valBits) &&& maskWt :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hwt)
  simp only [markAdvanceDecodeBody, arun_lift]
  simp [markAdvanceDecodeInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hvalMod, hwtMod, hbitsMod, hbandVal,
    hshift, hbandWt]

#print axioms markAdvanceDecodeBody_run

end LeanCompCert.Ports.R2SegSieve
