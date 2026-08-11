import LeanCompCert.Ports.R2SegMarkingFullPastCursor

/-! # Exact scheduling seam for one complete `R₂*` body -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- One literal scheduled body is definitionally the proved marking block
followed by the proved classifier/log/tail block. -/
theorem body_run_eq_mark_post (c : R2Cfg) (k : Nat) (s : AState) :
    arun k s c.body =
      arun k (arun k s c.markBody) (markPostBody c) := by
  rw [body_eq_mark_post, arun_append]

/-- Transport any staged postcondition across the exact scheduling seam.
This keeps subsequent finite induction independent of the size of the
postcondition and prevents re-elaboration of the literal instruction list. -/
theorem body_run_postcondition (c : R2Cfg) (k : Nat) (s : AState)
    (P : AState → Prop)
    (h : P (arun k (arun k s c.markBody) (markPostBody c))) :
    P (arun k s c.body) := by
  rw [body_run_eq_mark_post]
  exact h

#print axioms body_run_eq_mark_post
#print axioms body_run_postcondition

end LeanCompCert.Ports.R2SegSieve
