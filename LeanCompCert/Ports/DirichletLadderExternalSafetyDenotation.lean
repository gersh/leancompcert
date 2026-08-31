import LeanCompCert.Ports.DirichletLadderExternalSafetyConsequences

/-!
# Compiled-run denotation for the external ladder safety audit

This is the reusable signature route for the hardened, sticky audit.  It has
the same caller-owned array and rolled CompCert interface as the historical
ladder checker.  No certificate is generated or executed here.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.DirichletLadder

def symbolicEntry (c : Cfg) (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) (program c).init

def symbolicLoop (c : Cfg) (arr : Nat → Nat) : AState :=
  (List.range c.records).foldl
    (fun state index => arun index state (program c).body)
    (symbolicEntry c arr)

def symbolicFinal (c : Cfg) (arr : Nat → Nat) : AState :=
  arun 0 (symbolicLoop c arr) (program c).epilogue

def MachineAccepts (c : Cfg) (arr : Nat → Nat) : Prop :=
  (symbolicFinal c arr).regs rBad = 0

/-- The production machine claim is deliberately a pair: the historical
ladder result and the independent sticky fixed-width audit must both accept
the same external array. -/
def HardenedMachineAccepts (c : Cfg) (arr : Nat → Nat) : Prop :=
  LeanCompCert.Ports.DirichletLadderExternalDenotation.MachineAccepts c arr ∧
    MachineAccepts c arr

theorem runFromArray_eq_symbolicFinal
    (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hRun : (program c).runFromArray arr = some out) :
    out = symbolicFinal c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some (program c) arr out hRun
  simpa [program, symbolicEntry, symbolicLoop, symbolicFinal] using h

/-- A fail-safe source audit and the signed rolled-zero result establish the
exact sticky safety-machine proposition for the represented external array. -/
theorem machineAccepts_of_rolled_audit_and_result
    (c : Cfg) (arr : Nat → Nat)
    (base : Int) (hBase : BaseOk (program c).arrayLen base)
    (mem : Mem)
    (cells : ∀ k, k < (program c).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (words : ∀ k, arr k < M)
    (arrayLen_lt : (program c).arrayLen < M)
    (audit : LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
      (program c) base mem)
    (result : LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
      (program c) base mem 0) :
    MachineAccepts c arr := by
  have arrayLen_pos : 0 < (program c).arrayLen := by
    simp [program, Cfg.arrayLen]
  obtain ⟨out, hRun⟩ :=
    source_runFromArray_of_audit_rolled_zero
      (program c) (program_wf c) base hBase arr mem cells words
      arrayLen_pos arrayLen_lt audit
  have hzero : out.regs (program c).output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      (program c) (program_wf c) base hBase arr mem cells
      (fun k _hk => words k) out hRun 0 result
  rw [runFromArray_eq_symbolicFinal c arr out hRun] at hzero
  simpa [MachineAccepts, program] using hzero

/-- Reusable two-signature endpoint.  Both compiled programs are tied to the
same `arr`, `mem`, and base; a receipt cannot silently audit one stream and
claim the ladder result for another. -/
theorem hardenedMachineAccepts_of_rolled_audits_and_results
    (c : Cfg) (arr : Nat → Nat)
    (base : Int)
    (hBaseLadder : BaseOk c.program.arrayLen base)
    (hBaseSafety : BaseOk (program c).arrayLen base)
    (mem : Mem)
    (ladderCells : ∀ k, k < c.program.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (safetyCells : ∀ k, k < (program c).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (words : ∀ k, arr k < M)
    (ladderLen : c.program.arrayLen < M)
    (safetyLen : (program c).arrayLen < M)
    (ladderAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        c.program base mem)
    (ladderResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        c.program base mem 0)
    (safetyAudit :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.AuditRolledZero
        (program c) base mem)
    (safetyResult :
      LeanCompCert.Ports.DirichletLadderExternalDenotation.RolledResult
        (program c) base mem 0) :
    HardenedMachineAccepts c arr := by
  constructor
  · exact
      LeanCompCert.Ports.DirichletLadderExternalDenotation.machineAccepts_of_rolled_audit_and_result
        c arr base hBaseLadder mem ladderCells words ladderLen ladderAudit
        ladderResult
  · exact machineAccepts_of_rolled_audit_and_result c arr base hBaseSafety mem
      safetyCells words safetyLen safetyAudit safetyResult

end LeanCompCert.Ports.DirichletLadderExternalSafety
