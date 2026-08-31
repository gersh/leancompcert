import LeanCompCert.Ports.TGEvenGoldbachPrimeRowsSound
import LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded

/-!
# Causal prime-row production with a multi-window padded root phase

This is the source-scale variant of `RolledSegmentedPipeline`.  It retains the
same physical mark -> normalize -> pack memory chain, but obtains the prime
mask from the general padded root schedule rather than the one-window special
case.  Every theorem is symbolic in all fuels and array lengths.
-/

namespace LeanCompCert.Ports.TGEvenGoldbachPrimeRowsPaddedSound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.TGEvenGoldbachPrimeRows

set_option maxRecDepth 40000

/-- Transfer the general padded-root mask theorem from the zero scratch array
to a caller-owned allocation containing external witness planes. -/
theorem maskCorrect_of_padded_segmented_source_runs
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (hSchedule : PaddedProductionCoreSchedule c.sieve bootBound bootFuel
      laterFuel valid 0 delta)
    (hBase : ArraySegMobiusIndexedFull.mainBase c.sieve bootFuel laterFuel
      delta = c.sieve.lo)
    (hBudget :
      ((RS62SegmentedPrimeMaskPadded.paddedRootTable c.sieve bootBound
        bootFuel laterFuel valid).map
          fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps)
    (hIdxM : c.sieve.rootSpan + c.sieve.markSteps < M)
    (hLoSegM : c.sieve.lo + c.sieve.segLen < M)
    (hAboveRoot : c.sieve.rootCap < c.sieve.lo)
    (hCovered : c.sieve.lo + c.sieve.segLen - 1 ≤
      c.sieve.rootCap * c.sieve.rootCap)
    (initial : Nat → Nat) (marked normalized : AState)
    (hZeroPrefix : ∀ j, j < c.sieve.arrayLen → initial j = 0)
    (hMark : (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
      some marked)
    (hNormalize :
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
        marked.arr = some normalized) :
    RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
      normalized.arr c.sieve.lo c.sieve.segLen := by
  have hScratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  obtain ⟨canonicalMarked, hCanonicalMark, hMarkedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.program c.sieve) initial (fun _ => 0) marked
      (fun j hj => by simpa using hZeroPrefix j hj) hMark
  have hNormalizeInput : ∀ j,
      j < (RS62SegmentedPrimeMask.normalizeProgram
        c.sieve.segLen).arrayLen →
        marked.arr j = canonicalMarked.arr j := by
    intro j hj
    apply hMarkedAgree.2 j
    simpa [RS62SegmentedPrimeMask.program] using
      (Nat.lt_of_lt_of_le hj hScratch)
  obtain ⟨canonicalNormalized, hCanonicalNormalize, hNormalizedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
      marked.arr canonicalMarked.arr normalized hNormalizeInput hNormalize
  have hCanonicalMask :=
    RS62SegmentedPrimeMaskPadded.normalizedRun_maskCorrect c.sieve bootBound
      bootFuel laterFuel valid delta hSchedule hBase hBudget hIdxM hLoSegM
      hAboveRoot hCovered canonicalMarked canonicalNormalized hCanonicalMark
      hCanonicalNormalize
  intro k hk
  rw [hNormalizedAgree.2 k (by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using hk)]
  exact hCanonicalMask k hk

/-- Physical stage composition factored independently of the chosen root
schedule.  `maskBridge` is a proved source theorem, not a mask premise. -/
theorem primeRowsCorrect_and_cells_of_rolled_stages
    (c : Cfg)
    (hSegPos : 0 < c.sieve.segLen)
    (hLoSegM : c.sieve.lo + c.sieve.segLen < M)
    (hArrayM : c.arrayLen < M)
    (initial : Nat → Nat)
    (hZeroPrefix : ∀ j, j < c.sieve.arrayLen → initial j = 0)
    (hInitialWords : ∀ j, initial j < M)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((initial k : Nat) : Int)))
    (hMarkAudit : TGEvenGoldbach.AuditRolledZero
      (RS62SegmentedPrimeMask.program c.sieve) base mem)
    (markedM : MCCState)
    (hMarkEval : evalMCCSequence
      (AProgram.initialMCCWithMem
        (AProgram.counterAugment (AProgram.padArray
          (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) base mem)
      (AProgram.rolledCompile (AProgram.padArray
        (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) = some markedM)
    (hNormalizeAudit : TGEvenGoldbach.AuditRolledZero
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) base
        markedM.mem)
    (normalizedM : MCCState)
    (hNormalizeEval : evalMCCSequence
      (AProgram.initialMCCWithMem
        (AProgram.counterAugment (AProgram.padArray
          (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
          c.arrayLen)) base markedM.mem)
      (AProgram.rolledCompile (AProgram.padArray
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen)) =
          some normalizedM)
    (hPackAudit : TGEvenGoldbach.AuditRolledZero
      (TGEvenGoldbachPrimeRows.program c) base normalizedM.mem)
    (packedM : MCCState)
    (hPackEval : evalMCCSequence
      ((TGEvenGoldbachPrimeRows.program c).counterAugment.initialMCCWithMem
        base normalizedM.mem)
      (TGEvenGoldbachPrimeRows.program c).rolledCompile = some packedM)
    (hPackZero : packedM.env
      ⟨(TGEvenGoldbachPrimeRows.program c).output + 1⟩ = some (0 : Int))
    (maskBridge : ∀ marked normalized,
      (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
          some marked →
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
          marked.arr = some normalized →
      RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
        normalized.arr c.sieve.lo c.sieve.segLen) :
    ∃ marked normalized packed,
      (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
          some marked ∧
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
            marked.arr = some normalized ∧
        (TGEvenGoldbachPrimeRows.program c).runFromArray normalized.arr =
            some packed ∧
        TGEvenGoldbach.PrimeRowsCorrect c.goldbach
          (outputArray c packed.arr) ∧
        (∀ k, k < c.goldbach.arrayLen →
          packedM.mem (cellAddr (scannerBase c base) k) =
            some ((((outputArray c packed.arr k) : Nat) : Int))) := by
  have hScratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  have hMarkPrefix :
      (RS62SegmentedPrimeMask.program c.sieve).arrayLen ≤ c.arrayLen := by
    simp only [RS62SegmentedPrimeMask.program, Cfg.arrayLen, Cfg.outputBase]
    omega
  have hMarkLen : 0 <
      (RS62SegmentedPrimeMask.program c.sieve).arrayLen := by
    simp only [RS62SegmentedPrimeMask.program]
    exact Nat.lt_of_lt_of_le hSegPos hScratch
  obtain ⟨marked, hMark, hMarkedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.program c.sieve)
      (RS62SegmentedPrimeMask.program_wf c.sieve) c.arrayLen hMarkPrefix
      hMarkLen hArrayM initial hInitialWords base hBase mem hCells hMarkAudit
      markedM hMarkEval
  have hMarkedWords : ∀ j, marked.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.program c.sieve) initial hInitialWords marked
      hMark).2
  have hNormalizePrefix :
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).arrayLen ≤
        c.arrayLen := by
    simp only [RS62SegmentedPrimeMask.normalizeProgram, Cfg.arrayLen,
      Cfg.outputBase]
    omega
  have hNormalizeLen : 0 <
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).arrayLen := by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using hSegPos
  obtain ⟨normalized, hNormalize, hNormalizedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
      (RS62SegmentedPrimeMask.normalizeProgram_wf c.sieve.segLen) c.arrayLen
      hNormalizePrefix hNormalizeLen hArrayM marked.arr hMarkedWords base
      hBase markedM.mem hMarkedCells hNormalizeAudit normalizedM
      hNormalizeEval
  have hNormalizedWords : ∀ j, normalized.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) marked.arr
      hMarkedWords normalized hNormalize).2
  have hMask := maskBridge marked normalized hMark hNormalize
  have hReady : Ready c normalized.arr :=
    ⟨hSegPos, hLoSegM, hArrayM, fun j _ => hNormalizedWords j⟩
  obtain ⟨packed, hPack, hPrimeRows, hPackedCells⟩ :=
    primeRowsCorrect_and_cells_of_rolled_state c normalized.arr hReady hMask
      base hBase normalizedM.mem hNormalizedCells hNormalizedWords hPackAudit
      packedM hPackEval hPackZero
  exact ⟨marked, normalized, packed, hMark, hNormalize, hPack, hPrimeRows,
    hPackedCells⟩

/-- Manifest-facing multi-root producer package.  It contains no mathematical
prime mask and no `PrimeRowsCorrect` field. -/
structure RolledPaddedSegmentedPipeline (c : Cfg) where
  bootBound : Nat
  bootFuel : Nat
  laterFuel : Nat
  valid : Nat
  delta : Nat
  schedule : PaddedProductionCoreSchedule c.sieve bootBound bootFuel
    laterFuel valid 0 delta
  base_eq : ArraySegMobiusIndexedFull.mainBase c.sieve bootFuel laterFuel
    delta = c.sieve.lo
  budget :
    ((RS62SegmentedPrimeMaskPadded.paddedRootTable c.sieve bootBound bootFuel
      laterFuel valid).map
        fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps
  idx_word : c.sieve.rootSpan + c.sieve.markSteps < M
  upper_word : c.sieve.lo + c.sieve.segLen < M
  above_root : c.sieve.rootCap < c.sieve.lo
  covered : c.sieve.lo + c.sieve.segLen - 1 ≤
    c.sieve.rootCap * c.sieve.rootCap
  segment_pos : 0 < c.sieve.segLen
  array_word : c.arrayLen < M
  initial : Nat → Nat
  zero_prefix : ∀ j, j < c.sieve.arrayLen → initial j = 0
  initial_words : ∀ j, initial j < M
  base : Int
  base_ok : BaseOk c.arrayLen base
  mem : Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((initial k : Nat) : Int))
  mark_audit : TGEvenGoldbach.AuditRolledZero
    (RS62SegmentedPrimeMask.program c.sieve) base mem
  marked : MCCState
  mark_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) base mem)
    (AProgram.rolledCompile (AProgram.padArray
      (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) = some marked
  normalize_audit : TGEvenGoldbach.AuditRolledZero
    (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) base marked.mem
  normalized : MCCState
  normalize_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen))
      base marked.mem)
    (AProgram.rolledCompile (AProgram.padArray
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen)) =
        some normalized
  pack_audit : TGEvenGoldbach.AuditRolledZero
    (TGEvenGoldbachPrimeRows.program c) base normalized.mem
  packed : MCCState
  pack_eval : evalMCCSequence
    ((TGEvenGoldbachPrimeRows.program c).counterAugment.initialMCCWithMem
      base normalized.mem)
    (TGEvenGoldbachPrimeRows.program c).rolledCompile = some packed
  pack_zero : packed.env
    ⟨(TGEvenGoldbachPrimeRows.program c).output + 1⟩ = some (0 : Int)

/-- Exact denotation of the multi-root physical package. -/
theorem RolledPaddedSegmentedPipeline.sound {c : Cfg}
    (r : RolledPaddedSegmentedPipeline c) :
    ∃ marked normalized packed,
      (RS62SegmentedPrimeMask.program c.sieve).runFromArray r.initial =
          some marked ∧
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
            marked.arr = some normalized ∧
        (TGEvenGoldbachPrimeRows.program c).runFromArray normalized.arr =
            some packed ∧
        TGEvenGoldbach.PrimeRowsCorrect c.goldbach
          (outputArray c packed.arr) ∧
        (∀ k, k < c.goldbach.arrayLen →
          r.packed.mem (cellAddr (scannerBase c r.base) k) =
            some ((((outputArray c packed.arr k) : Nat) : Int))) := by
  apply primeRowsCorrect_and_cells_of_rolled_stages c r.segment_pos
    r.upper_word r.array_word r.initial r.zero_prefix r.initial_words r.base
    r.base_ok r.mem r.cells r.mark_audit r.marked r.mark_eval
    r.normalize_audit r.normalized r.normalize_eval r.pack_audit r.packed
    r.pack_eval r.pack_zero
  intro marked normalized hMark hNormalize
  exact maskCorrect_of_padded_segmented_source_runs c r.bootBound r.bootFuel
    r.laterFuel r.valid r.delta r.schedule r.base_eq r.budget r.idx_word
    r.upper_word r.above_root r.covered r.initial marked normalized
    r.zero_prefix hMark hNormalize

#print axioms maskCorrect_of_padded_segmented_source_runs
#print axioms primeRowsCorrect_and_cells_of_rolled_stages
#print axioms RolledPaddedSegmentedPipeline.sound

end LeanCompCert.Ports.TGEvenGoldbachPrimeRowsPaddedSound
