import LeanCompCert.Ports.TGEvenGoldbachTwoMask

/-!
# Physical acceptance for the two-mask Goldbach checker

This module turns the two fail-closed rolled signatures for the exact source
program into the source theorem.  The mask propositions are mathematical
denotations of the two input windows; later producer modules discharge them
from retained segmented-sieve executions.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.TGEvenGoldbachTwoMask

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment

abbrev RolledResult := TGEvenGoldbach.RolledResult
abbrev AuditRolledZero := TGEvenGoldbach.AuditRolledZero

/-- A fail-safe audit establishes source definedness, and the ordinary rolled
signature identifies that source output as zero.  The conclusion is exactly
the represented binary-Goldbach interval, not a reimplementation of it. -/
theorem covers_of_rolled_receipts
    (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr)
    (hsmall : PrimeMaskCorrect arr c.smallBase c.smallLo c.smallLen)
    (hlarge : PrimeMaskCorrect arr 0 c.largeLo c.largeLen)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (harr : ∀ k, arr k < M)
    (hAudit : AuditRolledZero (program c) base mem)
    (hAccept : RolledResult (program c) base mem 0) : Covers c := by
  have hlen : 0 < c.arrayLen := by
    rcases hready with ⟨_, hSmallPos, _, hLayoutSmall, _, _, _, _, _, _⟩
    simp only [Cfg.arrayLen]
    omega
  have hlenM : c.arrayLen < M := hready.2.2.2.2.2.2.2.2.1
  obtain ⟨out, hRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (program c) (program_wf c) base hBase arr mem hCells harr hlen hlenM
      hAudit
  have hzero : out.regs (program c).output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      (program c) (program_wf c) base hBase arr mem hCells
      (fun k _ => harr k) out hRun 0 hAccept
  exact covers_of_compiled_run c arr out hready hsmall hlarge hRun (by
    simpa [program, rViol] using hzero)

/-- Manifest-facing signature package.  It stores the physical input and the
two signed computations, while keeping both mask denotations explicit. -/
structure RolledReceipt (c : Cfg) (arr : Nat → Nat) where
  ready : Ready c arr
  smallMask : PrimeMaskCorrect arr c.smallBase c.smallLo c.smallLen
  largeMask : PrimeMaskCorrect arr 0 c.largeLo c.largeLen
  base : Int
  baseOk : BaseOk c.arrayLen base
  mem : Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((arr k : Nat) : Int))
  words : ∀ k, arr k < M
  audit : AuditRolledZero (program c) base mem
  run : RolledResult (program c) base mem 0

theorem RolledReceipt.covers {c : Cfg} {arr : Nat → Nat}
    (r : RolledReceipt c arr) : Covers c :=
  covers_of_rolled_receipts c arr r.ready r.smallMask r.largeMask r.base
    r.baseOk r.mem r.cells r.words r.audit r.run

#print axioms covers_of_rolled_receipts
#print axioms RolledReceipt.covers

end LeanCompCert.Ports.TGEvenGoldbachTwoMask
