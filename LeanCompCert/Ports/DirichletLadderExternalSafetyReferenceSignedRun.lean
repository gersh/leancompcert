import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptanceDirectedFinal
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceZeroDecode

/-! Reusable two-compiled-signature endpoint for the external Dirichlet
ladder.  This module only connects signed run predicates to the symbolic
reference theorem; it generates and executes no receipt. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.DirichletLadder

/-- Two successful compiled runs over the identical memory-backed external
array close the finite independent reference checker.  All source-scale and
fixed-width conditions remain explicit; analytic interpretation of the table
is a separate theorem obligation. -/
theorem refViolations_eq_zero_of_rolled_audits_and_results_sourceCfg
    (records termDigest : Nat) (words : List Nat)
    (base : Int)
    (hBaseLadder : BaseOk (sourceCfg records termDigest).program.arrayLen base)
    (hBaseSafety : BaseOk
      (program (sourceCfg records termDigest)).arrayLen base)
    (mem : Mem)
    (ladderCells : ∀ k,
      k < (sourceCfg records termDigest).program.arrayLen →
      mem (cellAddr base k) = some (((wordsArray words k : Nat) : Int)))
    (safetyCells : ∀ k,
      k < (program (sourceCfg records termDigest)).arrayLen →
      mem (cellAddr base k) = some (((wordsArray words k : Nat) : Int)))
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hterm : termDigest < M)
    (ladderLen : (sourceCfg records termDigest).program.arrayLen < M)
    (safetyLen : (program (sourceCfg records termDigest)).arrayLen < M)
    (ladderAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        (sourceCfg records termDigest).program base mem)
    (ladderResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        (sourceCfg records termDigest).program base mem 0)
    (safetyAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        (program (sourceCfg records termDigest)) base mem)
    (safetyResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        (program (sourceCfg records termDigest)) base mem 0) :
    refViolations (sourceCfg records termDigest) words = 0 := by
  have haccept := hardenedMachineAccepts_of_rolled_audits_and_results
    (sourceCfg records termDigest) (wordsArray words) base hBaseLadder
    hBaseSafety mem ladderCells safetyCells (by simpa [wordsArray] using hwords)
    ladderLen safetyLen ladderAudit ladderResult safetyAudit safetyResult
  exact refViolations_eq_zero_of_hardenedMachineAccepts_sourceCfg records
    termDigest words hwords hstatic hbudget hterm haccept

/-- The signed pair also exposes every literal integer record condition and
the terminal last/digest checks in a source-shaped structure. -/
theorem decodedReferenceTranscript_of_rolled_audits_and_results_sourceCfg
    (records termDigest : Nat) (words : List Nat)
    (base : Int)
    (hBaseLadder : BaseOk (sourceCfg records termDigest).program.arrayLen base)
    (hBaseSafety : BaseOk
      (program (sourceCfg records termDigest)).arrayLen base)
    (mem : Mem)
    (ladderCells : ∀ k,
      k < (sourceCfg records termDigest).program.arrayLen →
      mem (cellAddr base k) = some (((wordsArray words k : Nat) : Int)))
    (safetyCells : ∀ k,
      k < (program (sourceCfg records termDigest)).arrayLen →
      mem (cellAddr base k) = some (((wordsArray words k : Nat) : Int)))
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hterm : termDigest < M)
    (ladderLen : (sourceCfg records termDigest).program.arrayLen < M)
    (safetyLen : (program (sourceCfg records termDigest)).arrayLen < M)
    (ladderAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        (sourceCfg records termDigest).program base mem)
    (ladderResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        (sourceCfg records termDigest).program base mem 0)
    (safetyAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        (program (sourceCfg records termDigest)) base mem)
    (safetyResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        (program (sourceCfg records termDigest)) base mem 0) :
    DecodedReferenceTranscript (sourceCfg records termDigest) words := by
  apply decodedReferenceTranscript_of_refViolations_zero
  exact refViolations_eq_zero_of_rolled_audits_and_results_sourceCfg records
    termDigest words base hBaseLadder hBaseSafety mem ladderCells safetyCells
    hwords hstatic hbudget hterm ladderLen safetyLen ladderAudit ladderResult
    safetyAudit safetyResult

end LeanCompCert.Ports.DirichletLadderExternalSafety
