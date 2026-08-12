import LeanCompCert.Ports.CDEMAbelProductionCertificate
import LeanCompCert.Verified.ArrayAudit
import LeanCompCert.Verified.ArrayFinalRelation

/-!
# Fail-safe source-definedness certificate for the production CDEM Abel scan

The ordinary array compiler theorem is deliberately one-way: a compiled run
does not by itself establish that every source division and array access was
defined.  `auditComputation productionComputation` is the mechanically
transformed program which latches any zero divisor or out-of-bounds access in
a fresh result register while preserving the original computation.

The theorem below consumes that separate physical computation as an explicit
premise.  Once the production receipt has actually completed, the premise can
be named as a run admission and the literal five-billion-cell source program
will denote zero.  This does not yet identify the result cells with the paper
sums; that is the next, state-observation bridge.
-/

namespace LeanCompCert.Ports.CDEMAbelProductionAuditCertificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.CDEMAbelProductionCertificate

/-- The retained twelve-cell observation includes the original output local,
so it also supplies the ordinary `Returns 0` receipt required by the honest
array run rule. -/
theorem cdemAbelProduction_returns_zero :
    productionComputation.Returns ((0 : Nat) : Int) := by
  have h := cdemAbelProduction_compcert_run
  unfold productionObservation productionExpectedObservation at h
  cases hm : LeanCompCert.Verified.MemFragment.evalMCCSequence
      (productionComputation.program.initialMCC productionComputation.base)
      productionComputation.program.compile with
  | none => simp [hm] at h
  | some m =>
      cases hr : m.env ⟨productionComputation.program.output + 1⟩ with
      | none => simp [hm, hr] at h
      | some result =>
          cases hc : (List.range 12).mapM fun slot =>
              m.mem (LeanCompCert.Verified.ArrayState.cellAddr
                productionComputation.base
                (productionCfg.resultBase + slot)) with
          | none => simp [hm, hr, hc] at h
          | some cells =>
              simp [hm, hr, hc] at h
              rw [h.1] at hr
              simp [AComputation.Returns, AComputation.sourceResult, hm, hr]

/-- Once the independently emitted audit artifact has returned zero, every
partial operation in the literal production source is defined and its
aggregate guard counter denotes zero.  The physical run premise remains
explicit until its production receipt has actually completed. -/
theorem cdemAbelProduction_denote_of_audit
    (hAudit :
      (auditComputation productionComputation).Returns ((0 : Nat) : Int)) :
    productionComputation.program.denote = some 0 := by
  apply source_denotes_zero_of_audit_and_source_returns_zero
    productionComputation
  · decide
  · decide
  · exact hAudit
  · exact cdemAbelProduction_returns_zero

#print axioms cdemAbelProduction_denote_of_audit

end LeanCompCert.Ports.CDEMAbelProductionAuditCertificate
