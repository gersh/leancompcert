import LeanCompCert.Ports.ClosedBoolCarrier
import LeanCompCert.Ports.Section413Sweep

/-!
# Verified-code certificate for the Section 4.1.3 fixed window

The carrier's closed Boolean is the transparent source model itself:
`windowOK 999 99999`.  Thus its denotation is zero exactly when both complete
`g₁`/`g₂` table sweeps and both window event scans accept.  The generic
`ClosedBoolCarrier` theorem proves preservation through LeanCompCert's CCIR
and generated-C semantics; the one named atom below records only the physical
CompCert result.
-/

namespace LeanCompCert.Ports.Section413Window99999Certificate

open LeanCompCert.Ports.Section413Sweep

def windowResult : Bool := windowOK 999 99999

def windowCarrier : LeanCompCert.Verified.Reflect.Program :=
  LeanCompCert.Ports.ClosedBoolCarrier.program windowResult

/-- Packaged verified-compiler computation for the complete closed window. -/
def windowComputation : LeanCompCert.Verified.Computation :=
  LeanCompCert.Ports.ClosedBoolCarrier.computation windowResult

/-- Physical CompCert result for the complete closed window carrier.  This
atom mentions only the compiled CCIR result, not `windowOK`. -/
axiom section413Window99999_compcert_run :
  windowComputation.Returns ((0 : Nat) : Int)

theorem windowOK_999_99999 : windowOK 999 99999 = true :=
  (LeanCompCert.Ports.ClosedBoolCarrier.computation_returns_zero_iff windowResult).mp
    section413Window99999_compcert_run

end LeanCompCert.Ports.Section413Window99999Certificate
