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
open LeanCompCert.Verified.ArrayFoldBridge
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

/-- The same compiled opening trace, with only its returned local changed,
reproduced the low accumulator carry stored for the tail link. -/
axiom plattFirst_tLo_compcert_run :
  plattFirstComputation.ObservesReg rTLo (by decide)
    ((1711921466838888838 : Nat) : Int)

/-- The matching high-limb observation of the identical compiled trace. -/
axiom plattFirst_tHi_compcert_run :
  plattFirstComputation.ObservesReg rTHi (by decide)
    ((32768 : Nat) : Int)

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

/-- Opaque state-level form of the opening receipt.  Keeping the computation
projections in the statement prevents downstream modules from unfolding the
large literal configuration while this proof is elaborated. -/
theorem plattFirst_total_output_zero :
    let sEntry := arun 0 initialAState plattFirstComputation.program.init
    let sLoop := (List.range plattFirstComputation.program.loopCount).foldl
      (fun s idx => arun idx s plattFirstComputation.program.body) sEntry
    let sFinal := arun 0 sLoop plattFirstComputation.program.epilogue
    sFinal.regs plattFirstComputation.program.output = 0 :=
  source_total_output_zero_of_audit_and_source_returns_zero
    plattFirstComputation (by decide) (by decide)
    plattFirstAudit_compcert_run plattFirst_compcert_run

/-- Opaque state-level form of the tail receipt. -/
theorem plattTail_total_output_zero :
    let sEntry := arun 0 initialAState plattTailComputation.program.init
    let sLoop := (List.range plattTailComputation.program.loopCount).foldl
      (fun s idx => arun idx s plattTailComputation.program.body) sEntry
    let sFinal := arun 0 sLoop plattTailComputation.program.epilogue
    sFinal.regs plattTailComputation.program.output = 0 :=
  source_total_output_zero_of_audit_and_source_returns_zero
    plattTailComputation (by decide) (by decide)
    plattTailAudit_compcert_run plattTail_compcert_run

/-- Exact low accumulator carry in the ordinary opening source state. -/
theorem plattFirst_total_tLo :
    let sEntry := arun 0 initialAState plattFirstComputation.program.init
    let sLoop := (List.range plattFirstComputation.program.loopCount).foldl
      (fun s idx => arun idx s plattFirstComputation.program.body) sEntry
    let sFinal := arun 0 sLoop plattFirstComputation.program.epilogue
    sFinal.regs rTLo = 1711921466838888838 :=
  source_total_reg_eq_of_audit_and_observesReg plattFirstComputation
    rTLo (by decide) 1711921466838888838 (by decide) (by decide)
    plattFirstAudit_compcert_run plattFirst_tLo_compcert_run

/-- Exact high accumulator carry in the ordinary opening source state. -/
theorem plattFirst_total_tHi :
    let sEntry := arun 0 initialAState plattFirstComputation.program.init
    let sLoop := (List.range plattFirstComputation.program.loopCount).foldl
      (fun s idx => arun idx s plattFirstComputation.program.body) sEntry
    let sFinal := arun 0 sLoop plattFirstComputation.program.epilogue
    sFinal.regs rTHi = 32768 :=
  source_total_reg_eq_of_audit_and_observesReg plattFirstComputation
    rTHi (by decide) 32768 (by decide) (by decide)
    plattFirstAudit_compcert_run plattFirst_tHi_compcert_run

/-! Projection equations used by the separate trace-composition module.  They
are deliberately small opaque rewrite boundaries: downstream proofs should
rewrite these fields instead of simplifying the entire computation record. -/

theorem plattFirst_program : plattFirstComputation.program =
    mobiusLiveSquaredProgram plattAlignedFirst mobWideBits plattFirstSeed :=
  rfl

theorem plattTail_program : plattTailComputation.program =
    mobiusLiveSquaredProgram plattAlignedTail mobWideBits plattTailSeed :=
  rfl

theorem plattFirst_init : plattFirstComputation.program.init =
    plattAlignedFirst.coreInit ++ mobiusLiveInit plattFirstSeed := rfl

theorem plattFirst_body : plattFirstComputation.program.body =
    plattAlignedFirst.coreBody ++ mobiusLiveSquaredResidue mobWideBits := rfl

theorem plattFirst_loopCount : plattFirstComputation.program.loopCount =
    plattAlignedFirst.period *
      (plattAlignedFirst.rootCount + plattAlignedFirst.segCount) := rfl

theorem plattFirst_epilogue : plattFirstComputation.program.epilogue =
    mobiusLiveEpilogue plattAlignedFirst := rfl

theorem plattFirst_output : plattFirstComputation.program.output =
    outputReg := rfl

theorem plattTail_init : plattTailComputation.program.init =
    plattAlignedTail.coreInit ++ mobiusLiveInit plattTailSeed := rfl

theorem plattTail_body : plattTailComputation.program.body =
    plattAlignedTail.coreBody ++ mobiusLiveSquaredResidue mobWideBits := rfl

theorem plattTail_loopCount : plattTailComputation.program.loopCount =
    plattAlignedTail.period *
      (plattAlignedTail.rootCount + plattAlignedTail.segCount) := rfl

theorem plattTail_epilogue : plattTailComputation.program.epilogue =
    mobiusLiveEpilogue plattAlignedTail := rfl

theorem plattTail_output : plattTailComputation.program.output = outputReg :=
  rfl

end LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate
