import LeanCompCert.Ports.DirichletLadder
import LeanCompCert.Verified.ArrayAuditFromArray
import LeanCompCert.Verified.ArrayRolledPipeline

/-!
# External-array denotation for the Dirichlet ladder

`DirichletLadder.ladderProgram_compiled` is a forward theorem: it starts from
an already-known closed source denotation.  Production does not use a closed
zero-filled array, however; the record stream is supplied by the caller.

This module gives the production-shaped converse seam.  A fail-safe audit of
the partial array program first proves that the ordinary source run exists.
The independently rolled ordinary execution is then identified, by compiler
correctness and determinism, with the exact symbolic `arun` fold below.  No
record loop is evaluated by Lean, and no receipt or external execution fact is
declared here.

The result deliberately stops at `MachineAccepts`.  Relating that exact
machine fold to the source-level Turing/Dirichlet predicates is a separate
denotation theorem; keeping the boundary explicit prevents a successful
integer transcript from being mistaken for the analytic GRH conclusion.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalDenotation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.DirichletLadder

/-- The exact source state after the table initializer. -/
def symbolicEntry (c : Cfg) (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) c.initBlock

/-- The exact source state after every externally supplied record. -/
def symbolicLoop (c : Cfg) (arr : Nat → Nat) : AState :=
  (List.range c.records).foldl
    (fun state index => arun index state c.bodyBlock)
    (symbolicEntry c arr)

/-- The exact complete source state, including terminal closure and digest
checks.  This is a symbolic fold, not an evaluated production computation. -/
def symbolicFinal (c : Cfg) (arr : Nat → Nat) : AState :=
  arun 0 (symbolicLoop c arr) c.epilogueBlock

/-- Exact integer-machine acceptance of one caller-owned ladder stream. -/
def MachineAccepts (c : Cfg) (arr : Nat → Nat) : Prop :=
  (symbolicFinal c arr).regs rViol = 0

/-- The generic configured ladder is well formed, not only the historical
`sourceCfg` specialization. -/
theorem cfgProgram_wf (c : Cfg) : c.program.WF :=
  ⟨by show rViol < regCount; decide,
    initBlock_wf c, bodyBlock_wf c, epilogueBlock_wf c⟩

/-- Any successful caller-owned source run is definitionally the exact
symbolic state above.  The theorem is uniform in `c.records`. -/
theorem runFromArray_eq_symbolicFinal
    (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hRun : c.program.runFromArray arr = some out) :
    out = symbolicFinal c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some c.program arr out hRun
  simpa [Cfg.program, symbolicEntry, symbolicLoop, symbolicFinal] using h

/-- Rolled output proposition used by a physical execution provider. -/
def RolledResult (p : AProgram) (base : Int) (mem : Mem)
    (value : Int) : Prop :=
  Option.bind
    (evalMCCSequence
      (p.counterAugment.initialMCCWithMem base mem)
      p.rolledCompile)
    (fun out : MCCState => out.env ⟨p.output + 1⟩) = some value

/-- Fail-safe audit proposition for exactly the same represented input. -/
def AuditRolledZero (p : AProgram) (base : Int) (mem : Mem) : Prop :=
  RolledResult (auditProgram p) base mem 0

/-- A fail-safe audit plus the ordinary rolled zero result proves the exact
symbolic integer-machine acceptance proposition.

Both traces start from `mem`; the premises cannot silently use unrelated
source arrays because `cells` fixes that memory to the single `arr` appearing
in the conclusion. -/
theorem machineAccepts_of_rolled_audit_and_result
    (c : Cfg) (arr : Nat → Nat)
    (base : Int) (hBase : BaseOk c.program.arrayLen base)
    (mem : Mem)
    (cells : ∀ k, k < c.program.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (words : ∀ k, arr k < M)
    (arrayLen_lt : c.program.arrayLen < M)
    (audit : AuditRolledZero c.program base mem)
    (result : RolledResult c.program base mem 0) :
    MachineAccepts c arr := by
  have arrayLen_pos : 0 < c.program.arrayLen := by
    simp [Cfg.program, Cfg.arrayLen]
  obtain ⟨out, hRun⟩ :=
    source_runFromArray_of_audit_rolled_zero
      c.program (cfgProgram_wf c) base hBase arr mem cells words
      arrayLen_pos arrayLen_lt audit
  have hzero : out.regs c.program.output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      c.program (cfgProgram_wf c) base hBase arr mem cells
      (fun k _hk => words k) out hRun 0 result
  rw [runFromArray_eq_symbolicFinal c arr out hRun] at hzero
  simpa [MachineAccepts, Cfg.program] using hzero

#print axioms cfgProgram_wf
#print axioms runFromArray_eq_symbolicFinal
#print axioms machineAccepts_of_rolled_audit_and_result

end LeanCompCert.Ports.DirichletLadderExternalDenotation
