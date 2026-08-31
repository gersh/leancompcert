import LeanCompCert.Ports.TGEvenGoldbachTwoMaskSound
import LeanCompCert.Ports.TGEvenGoldbachPrimeRowsSound
import LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded

/-!
# Causal multi-root producer for the two-mask Goldbach checker

The large complementary-prime window is produced by the checked segmented
sieve.  Its ordinary padded execution retains a caller-owned suffix containing
the fixed small-prime mask and the two witness planes.  The checker then starts
from the normalizer's exact final physical memory.  Consequently the only
dynamic assumptions are signature-shaped compiled runs; neither large-mask
primality nor binary Goldbach is a premise.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.TGEvenGoldbachTwoMaskSegmentedSound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.TGEvenGoldbachPrimeRows

set_option maxRecDepth 40000

/-- Transfer the general padded-root theorem from its canonical zero scratch
array to an arbitrary caller allocation.  Only the sieve prefix is observed;
the witness suffix remains external data. -/
theorem maskCorrect_of_padded_segmented_source_runs
    (sieve : ArraySegSieve.Cfg)
    (bootBound bootFuel laterFuel valid delta : Nat)
    (hSchedule : PaddedProductionCoreSchedule sieve bootBound bootFuel
      laterFuel valid 0 delta)
    (hBase : ArraySegMobiusIndexedFull.mainBase sieve bootFuel laterFuel
      delta = sieve.lo)
    (hBudget :
      ((LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded.paddedRootTable sieve bootBound bootFuel laterFuel valid).map
        fun p => sieve.segLen / p + 2).sum ≤ sieve.markSteps)
    (hIdxM : sieve.rootSpan + sieve.markSteps < M)
    (hLoSegM : sieve.lo + sieve.segLen < M)
    (hAboveRoot : sieve.rootCap < sieve.lo)
    (hCovered : sieve.lo + sieve.segLen - 1 ≤
      sieve.rootCap * sieve.rootCap)
    (initial : Nat → Nat) (marked normalized : AState)
    (hZeroPrefix : ∀ j, j < sieve.arrayLen → initial j = 0)
    (hMark : (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve).runFromArray initial = some marked)
    (hNormalize : (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).runFromArray
      marked.arr = some normalized) :
    LeanCompCert.Ports.RS62PrimeMaskLadder.MaskCorrect LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool normalized.arr sieve.lo
      sieve.segLen := by
  have hScratch : sieve.segLen ≤ sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  obtain ⟨canonicalMarked, hCanonicalMark, hMarkedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve) initial (fun _ => 0) marked
      (fun j hj => by simpa using hZeroPrefix j hj) hMark
  have hNormalizeInput : ∀ j,
      j < (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen →
        marked.arr j = canonicalMarked.arr j := by
    intro j hj
    apply hMarkedAgree.2 j
    simpa [LeanCompCert.Ports.RS62SegmentedPrimeMask.program] using Nat.lt_of_lt_of_le hj hScratch
  obtain ⟨canonicalNormalized, hCanonicalNormalize, hNormalizedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) marked.arr canonicalMarked.arr
      normalized hNormalizeInput hNormalize
  have hCanonicalMask :=
    LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded.normalizedRun_maskCorrect sieve bootBound bootFuel laterFuel
      valid delta hSchedule hBase hBudget hIdxM hLoSegM hAboveRoot hCovered
      canonicalMarked canonicalNormalized hCanonicalMark hCanonicalNormalize
  intro k hk
  rw [hNormalizedAgree.2 k (by
    simpa [LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram] using hk)]
  exact hCanonicalMask k hk

/-- Convert the normalized RS62 Boolean contract to the exact `IsPrime`
window contract read by the two-mask checker. -/
theorem largePrimeMaskCorrect_of_maskCorrect
    (c : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Cfg) (sieve : ArraySegSieve.Cfg) (arr : Nat → Nat)
    (hLo : c.largeLo = sieve.lo) (hLen : c.largeLen = sieve.segLen)
    (h : LeanCompCert.Ports.RS62PrimeMaskLadder.MaskCorrect LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool arr sieve.lo
      sieve.segLen) :
    LeanCompCert.Ports.TGEvenGoldbachTwoMask.PrimeMaskCorrect arr 0 c.largeLo c.largeLen := by
  intro i hi
  have hi' : i < sieve.segLen := by simpa [hLen] using hi
  have hm := h i hi'
  simp only [Nat.zero_add, hLo]
  rw [hm]
  by_cases hp : IsPrime (sieve.lo + i) <;>
    simp [LeanCompCert.Ports.RS62SegmentedPrimeMask.isPrimeBool, hp]

/-- A complete, causal, physical package for one source-scale shard.  The
small mask is static input data.  The large mask is deliberately absent: it is
derived from the retained mark/normalize runs below. -/
structure RolledPaddedSegmentedPipeline
    (sieve : ArraySegSieve.Cfg) (c : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Cfg) where
  bootBound : Nat
  bootFuel : Nat
  laterFuel : Nat
  valid : Nat
  delta : Nat
  schedule : PaddedProductionCoreSchedule sieve bootBound bootFuel laterFuel
    valid 0 delta
  base_eq : ArraySegMobiusIndexedFull.mainBase sieve bootFuel laterFuel delta =
    sieve.lo
  budget :
    ((LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded.paddedRootTable sieve bootBound bootFuel laterFuel valid).map
      fun p => sieve.segLen / p + 2).sum ≤ sieve.markSteps
  idx_word : sieve.rootSpan + sieve.markSteps < M
  upper_word : sieve.lo + sieve.segLen < M
  above_root : sieve.rootCap < sieve.lo
  covered : sieve.lo + sieve.segLen - 1 ≤ sieve.rootCap * sieve.rootCap
  segment_pos : 0 < sieve.segLen
  large_lo : c.largeLo = sieve.lo
  large_len : c.largeLen = sieve.segLen
  suffix_after_sieve : sieve.arrayLen ≤ c.smallBase
  initial : Nat → Nat
  ready : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Ready c initial
  zero_prefix : ∀ j, j < sieve.arrayLen → initial j = 0
  small_mask : LeanCompCert.Ports.TGEvenGoldbachTwoMask.PrimeMaskCorrect initial c.smallBase c.smallLo
    c.smallLen
  initial_words : ∀ j, initial j < M
  base : Int
  base_ok : BaseOk c.arrayLen base
  mem : Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((initial k : Nat) : Int))
  mark_audit : LeanCompCert.Ports.TGEvenGoldbachTwoMask.AuditRolledZero (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve) base mem
  marked : MCCState
  mark_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve) c.arrayLen))
      base mem)
    ((LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve).padArray c.arrayLen).rolledCompile = some marked
  normalize_audit : LeanCompCert.Ports.TGEvenGoldbachTwoMask.AuditRolledZero
    (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) base marked.mem
  normalized : MCCState
  normalize_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram
          sieve.segLen) c.arrayLen)) base marked.mem)
    ((LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).padArray c.arrayLen).rolledCompile =
      some normalized
  checker_audit : LeanCompCert.Ports.TGEvenGoldbachTwoMask.AuditRolledZero (LeanCompCert.Ports.TGEvenGoldbachTwoMask.program c) base
    normalized.mem
  checker_run : LeanCompCert.Ports.TGEvenGoldbachTwoMask.RolledResult (LeanCompCert.Ports.TGEvenGoldbachTwoMask.program c) base normalized.mem 0

/-- Exact signature-to-source theorem for the complete multi-root/two-mask
shard.  It never enumerates either the sieve interval or the Goldbach rows. -/
theorem RolledPaddedSegmentedPipeline.sound
    {sieve : ArraySegSieve.Cfg} {c : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Cfg}
    (r : RolledPaddedSegmentedPipeline sieve c) : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Covers c := by
  have hMarkPrefix : (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve).arrayLen ≤ c.arrayLen := by
    have hLayout := r.ready.2.2.2.1
    have hSuffix := r.suffix_after_sieve
    simp only [LeanCompCert.Ports.RS62SegmentedPrimeMask.program, LeanCompCert.Ports.TGEvenGoldbachTwoMask.Cfg.arrayLen]
    omega
  have hMarkLen : 0 < (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve).arrayLen := by
    have hScratch : sieve.segLen ≤ sieve.arrayLen := by
      simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
      omega
    simp only [LeanCompCert.Ports.RS62SegmentedPrimeMask.program]
    exact Nat.lt_of_lt_of_le r.segment_pos hScratch
  have hArrayM : c.arrayLen < M := r.ready.2.2.2.2.2.2.2.2.1
  obtain ⟨marked, hMark, hMarkedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve) (LeanCompCert.Ports.RS62SegmentedPrimeMask.program_wf sieve) c.arrayLen hMarkPrefix
      hMarkLen hArrayM r.initial r.initial_words r.base r.base_ok r.mem
      r.cells r.mark_audit r.marked r.mark_eval
  have hMarkedWords : ∀ j, marked.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve) r.initial r.initial_words marked hMark).2
  have hNormalizePrefix :
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen ≤ c.arrayLen := by
    have hScratch : sieve.segLen ≤ sieve.arrayLen := by
      simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
      omega
    have hSuffix := r.suffix_after_sieve
    have hLayout := r.ready.2.2.2.1
    simp only [LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram, LeanCompCert.Ports.TGEvenGoldbachTwoMask.Cfg.arrayLen]
    omega
  have hNormalizeLen :
      0 < (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen := by
    simpa [LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram] using r.segment_pos
  obtain ⟨normalized, hNormalize, hNormalizedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen)
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram_wf sieve.segLen) c.arrayLen hNormalizePrefix
      hNormalizeLen hArrayM marked.arr hMarkedWords r.base r.base_ok
      r.marked.mem hMarkedCells r.normalize_audit r.normalized
      r.normalize_eval
  have hNormalizedWords : ∀ j, normalized.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) marked.arr hMarkedWords
      normalized hNormalize).2
  have hMask := maskCorrect_of_padded_segmented_source_runs sieve r.bootBound
    r.bootFuel r.laterFuel r.valid r.delta r.schedule r.base_eq r.budget
    r.idx_word r.upper_word r.above_root r.covered r.initial marked normalized
    r.zero_prefix hMark hNormalize
  have hLarge : LeanCompCert.Ports.TGEvenGoldbachTwoMask.PrimeMaskCorrect normalized.arr 0 c.largeLo
      c.largeLen :=
    largePrimeMaskCorrect_of_maskCorrect c sieve normalized.arr r.large_lo
      r.large_len hMask
  have hScratch : sieve.segLen ≤ sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  have hSmall : LeanCompCert.Ports.TGEvenGoldbachTwoMask.PrimeMaskCorrect normalized.arr c.smallBase c.smallLo
      c.smallLen := by
    intro i hi
    have hAddr : sieve.arrayLen ≤ c.smallBase + i := by
      have hSuffix := r.suffix_after_sieve
      omega
    have hMarkFrame := (LeanCompCert.Ports.RS62SegmentedPrimeMask.program sieve).runFromArray_frame_ge r.initial
      marked hMark (c.smallBase + i) hAddr
    have hNormalizeFrame :=
      (LeanCompCert.Ports.RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).runFromArray_frame_ge marked.arr
        normalized hNormalize (c.smallBase + i)
        (Nat.le_trans hScratch hAddr)
    rw [hNormalizeFrame, hMarkFrame]
    exact r.small_mask i hi
  have hReady : LeanCompCert.Ports.TGEvenGoldbachTwoMask.Ready c normalized.arr := by
    rcases r.ready with
      ⟨hLargePos, hSmallPos, hLayoutLarge, hLayoutSmall, hLargeM, hSmallM,
        hSumM, hEvenM, hFullM, _⟩
    exact ⟨hLargePos, hSmallPos, hLayoutLarge, hLayoutSmall, hLargeM, hSmallM,
      hSumM, hEvenM, hFullM, fun i _ => hNormalizedWords i⟩
  exact LeanCompCert.Ports.TGEvenGoldbachTwoMask.covers_of_rolled_receipts c normalized.arr hReady hSmall
    hLarge r.base r.base_ok r.normalized.mem hNormalizedCells hNormalizedWords
    r.checker_audit r.checker_run

#print axioms maskCorrect_of_padded_segmented_source_runs
#print axioms largePrimeMaskCorrect_of_maskCorrect
#print axioms RolledPaddedSegmentedPipeline.sound

end LeanCompCert.Ports.TGEvenGoldbachTwoMaskSegmentedSound
