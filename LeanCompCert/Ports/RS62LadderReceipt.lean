import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Verified.ArrayRolledPipeline

/-!
# Rolled CompCert receipts for RS62 ladder segments

`RS62LadderEncoding` proves, symbolically, that the guarded array program
denotes one source `loopE` segment.  This file supplies the other half of the
production boundary: a retained result of the rolled CompCert trace determines
that source segment's two outputs.  No candidate range is evaluated in Lean.

The receipt is deliberately about the generated CCIR memory semantics rather
than an emission-time Boolean.  A hosted executable run supplies the two
equalities, while compiler simulation and determinism identify them with the
already-proved source denotation.
-/

namespace LeanCompCert.Ports.RS62LadderReceipt

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.RS62
open LeanCompCert.Ports.RS62Ladder

/-- The zero array used by a standalone ladder program.  Its array length is
zero, but spelling it out lets the generic caller-owned-memory theorem apply
without a special trusted bridge. -/
def zeroArray : Nat → Nat := fun _ => 0

private theorem mbind_some {α β : Type} (a : α) (g : α → Option β) :
    ((some a : Option α) >>= g) = g a := rfl

/-- A successful standalone denotation exposes the complete final source
state, not merely its selected output register. -/
theorem runFromZero_of_denote (p : AProgram) (value : Nat)
    (h : p.denote = some value) :
    ∃ out, p.runFromArray zeroArray = some out ∧
      out.regs p.output = value := by
  have hInitial : initialAStateWithArray zeroArray = initialAState := rfl
  unfold AProgram.denote at h
  rw [← hInitial] at h
  cases hInit : denoteAInstrs p.arrayLen 0
      (initialAStateWithArray zeroArray) p.init with
  | none => simp [hInit] at h
  | some entry =>
      rw [hInit] at h
      rw [mbind_some] at h
      cases hLoop : (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
      | none => simp [hLoop] at h
      | some loopOut =>
          rw [hLoop] at h
          rw [mbind_some] at h
          cases hEpi : denoteAInstrs p.arrayLen 0 loopOut p.epilogue with
          | none => simp [hEpi] at h
          | some out =>
              rw [hEpi] at h
              rw [mbind_some] at h
              injection h with h
              refine ⟨out, ?_, h⟩
              simp [AProgram.runFromArray, hInit, hLoop, hEpi]

/-- Exact rolled-CCIR output receipt for one selected ladder accumulator. -/
def RolledOutputReceipt (p : AProgram) (value : Nat) : Prop :=
  Option.bind
      (evalMCCSequence (p.counterAugment.initialMCC 0) p.rolledCompile)
      (fun m : MCCState => m.env ⟨p.output + 1⟩) =
    some ((value : Nat) : Int)

/-- A rolled physical result equals the already-proved standalone source
denotation.  The proof executes neither the source fold nor the CCIR trace. -/
theorem value_eq_of_rolled_receipt (p : AProgram) (hp : p.WF)
    (hBase : BaseOk p.arrayLen 0) (sourceValue receiptValue : Nat)
    (hDenote : p.denote = some sourceValue)
    (hReceipt : RolledOutputReceipt p receiptValue) :
    sourceValue = receiptValue := by
  obtain ⟨out, hRun, hOut⟩ := runFromZero_of_denote p sourceValue hDenote
  have hCells : ∀ k, k < p.arrayLen →
      initialMem p.arrayLen 0 (cellAddr 0 k) =
        some (((zeroArray k : Nat) : Int)) := by
    intro k hk
    change initialMem p.arrayLen 0 (cellAddr 0 k) = some 0
    exact initialMem_cell p.arrayLen 0 hk
  have hCellsLt : ∀ k, k < p.arrayLen → zeroArray k < M := by
    intro _ _
    simp [zeroArray, M]
  have hPhysical : out.regs p.output = receiptValue :=
    AProgram.output_eq_of_rolledCompile_fromArray p hp 0 hBase zeroArray
      (initialMem p.arrayLen 0) hCells hCellsLt out hRun receiptValue
      (by
        have hStart :
            p.counterAugment.initialMCCWithMem 0 (initialMem p.arrayLen 0) =
              p.counterAugment.initialMCC 0 := by rfl
        rw [hStart]
        exact hReceipt)
  exact hOut.symm.trans hPhysical

/-- The two retained rolled results for one guarded RS62 segment. -/
def SegmentReceipt (n0 f B SL SU lower upper : Nat) : Prop :=
  RolledOutputReceipt (ladderProgram n0 f B SL SU rSL) lower ∧
    RolledOutputReceipt (ladderProgram n0 f B SL SU rSU) upper

/-- The array footprint of every scalar-lifted ladder program is empty, so
base zero is valid independently of the segment size. -/
theorem ladderProgram_baseOk (n0 f B SL SU out : Nat) :
    BaseOk (ladderProgram n0 f B SL SU out).arrayLen 0 := by
  simp [ladderProgram, AProgram.ofProgram, BaseOk, M]

/-- A pair of rolled CompCert results proves the exact guarded source segment,
provided by the symbolic encoding theorem. -/
theorem loopE_scanPrime_of_segmentReceipt
    (n0 f B SL SU lower upper : Nat)
    (hEncoding : LadderEncoding
      RS62LadderEncoding.scanPrime n0 f B SL SU)
    (hReceipt : SegmentReceipt n0 f B SL SU lower upper) :
    loopE RS62LadderEncoding.scanPrime f n0 SL SU = (lower, upper) := by
  have hWFLo := ladderProgram_wf n0 f B SL SU rSL (by decide)
  have hWFHi := ladderProgram_wf n0 f B SL SU rSU (by decide)
  have hLo := value_eq_of_rolled_receipt
    (ladderProgram n0 f B SL SU rSL) hWFLo
    (ladderProgram_baseOk n0 f B SL SU rSL)
    (loopE RS62LadderEncoding.scanPrime f n0 SL SU).1 lower
    hEncoding.1 hReceipt.1
  have hHi := value_eq_of_rolled_receipt
    (ladderProgram n0 f B SL SU rSU) hWFHi
    (ladderProgram_baseOk n0 f B SL SU rSU)
    (loopE RS62LadderEncoding.scanPrime f n0 SL SU).2 upper
    hEncoding.2 hReceipt.2
  apply Prod.ext
  · exact hLo
  · exact hHi

#print axioms runFromZero_of_denote
#print axioms value_eq_of_rolled_receipt
#print axioms loopE_scanPrime_of_segmentReceipt

end LeanCompCert.Ports.RS62LadderReceipt
