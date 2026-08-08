import LeanCompCert.Ports.ArraySegMobiusPlattConfig
import LeanCompCert.Ports.ArraySegMobiusSquared
import LeanCompCert.Verified.ArrayAudit

/-!
# Compiled definedness receipts for the aligned Platt campaign

The array compiler's ordinary correctness theorem intentionally runs from a
proved source denotation to the compiled trace.  Each aligned link therefore
has two physical receipts:

* the paper-faithful squared program returns zero violations; and
* its fail-safe audited transform returns zero source-safety failures.

`source_denotes_zero_of_audit_and_source_returns_zero` composes those receipts
without reversing compiler correctness.  The audited program has an
unconditional source denotation; its zero receipt proves that the original
partial program is defined, after which the original zero receipt identifies
the defined result.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPlattConfig

/-- Canonical accumulator carry after the two pre-domain rows `1` and `2`.
The violation counter is initialized separately to zero by the program. -/
def plattFirstSeed : MobLiveSeed := mobLiveSeed 3 0 40960

/-- Carry emitted by the first aligned link at `n = 7,727,054,615`. -/
def plattTailSeed : MobLiveSeed :=
  mobLiveSeed 7727054616 1711921466838888838 32768

/-- The exact squared link covering `[3, 7,727,054,615]`. -/
def plattFirstComputation : AComputation where
  program := mobiusLiveSquaredProgram plattAlignedFirst mobWideBits
    plattFirstSeed
  wellFormed := mobiusLiveSquaredProgram_wf plattAlignedFirst mobWideBits
    plattFirstSeed
  base := 0
  baseOk := by
    constructor
    · decide
    · decide
  name := "platt-squared-aligned-first"

/-- The exact squared link covering `[7,727,054,616, 7,727,068,586]`. -/
def plattTailComputation : AComputation where
  program := mobiusLiveSquaredProgram plattAlignedTail mobWideBits
    plattTailSeed
  wellFormed := mobiusLiveSquaredProgram_wf plattAlignedTail mobWideBits
    plattTailSeed
  base := 0
  baseOk := by
    constructor
    · decide
    · decide
  name := "platt-squared-aligned-tail"

/-- CompCert execution of the original opening link returned zero
paper-majorant violations. -/
axiom plattFirst_compcert_run :
  plattFirstComputation.Returns ((0 : Nat) : Int)

/-- CompCert execution of the fail-safe opening link returned zero dynamic
division/address guard failures. -/
axiom plattFirstAudit_compcert_run :
  (auditComputation plattFirstComputation).Returns ((0 : Nat) : Int)

/-- CompCert execution of the original tail link returned zero
paper-majorant violations. -/
axiom plattTail_compcert_run :
  plattTailComputation.Returns ((0 : Nat) : Int)

/-- CompCert execution of the fail-safe tail link returned zero dynamic
division/address guard failures. -/
axiom plattTailAudit_compcert_run :
  (auditComputation plattTailComputation).Returns ((0 : Nat) : Int)

/-- The original partial opening program has the exact source result zero. -/
theorem plattFirst_denote : plattFirstComputation.program.denote = some 0 := by
  apply source_denotes_zero_of_audit_and_source_returns_zero
    plattFirstComputation
  · decide
  · decide
  · exact plattFirstAudit_compcert_run
  · exact plattFirst_compcert_run

/-- The original partial tail program has the exact source result zero. -/
theorem plattTail_denote : plattTailComputation.program.denote = some 0 := by
  apply source_denotes_zero_of_audit_and_source_returns_zero
    plattTailComputation
  · decide
  · decide
  · exact plattTailAudit_compcert_run
  · exact plattTail_compcert_run

end LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate
