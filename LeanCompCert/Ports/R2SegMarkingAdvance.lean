import LeanCompCert.Ports.R2SegMarkingBudget

/-! # Complete post-hit suffix of the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock

/-- All 48 production instructions after the final marking-cell store. -/
def markAdvanceBody (c : R2Cfg) : List AInstr :=
  markAdvanceFlagsBody c ++ markAdvancePiBody c ++
    markAdvanceLoadBody c ++ markAdvanceDecodeBody ++
    markAdvanceValueBody ++ markAdvanceOffsetBody c ++ markBudgetBody c

/-- The staged cursor, load, decode, value, offset, and budget blocks are
definitionally the complete production suffix. -/
theorem markAdvanceBody_eq_suffix (c : R2Cfg) :
    c.markBody.drop 53 = markAdvanceBody c := by
  rfl

/-- The complete cursor suffix is store-free. -/
theorem markAdvanceBody_arr_frame (c : R2Cfg) (k : Nat) (s : AState) :
    (arun k s (markAdvanceBody c)).arr = s.arr := by
  simp [markAdvanceBody, arun_append, markAdvanceFlagsBody,
    markAdvancePiBody, markAdvanceLoadBody, markAdvanceDecodeBody,
    markAdvanceValueBody, markAdvanceOffsetBody, markBudgetBody,
    arun_lift_arr, arun, astep, AState.writeReg]

#print axioms markAdvanceBody_eq_suffix
#print axioms markAdvanceBody_arr_frame

end LeanCompCert.Ports.R2SegSieve
