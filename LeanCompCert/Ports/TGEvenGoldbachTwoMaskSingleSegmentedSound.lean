import LeanCompCert.Ports.TGEvenGoldbachTwoMaskSegmentedSound

/-!
# Causal one-root producer for the two-mask Goldbach checker

For low source-scale shards the complementary-prime segment is wider than
its square-root bound.  Those shards intentionally do not inhabit the
multi-root `PaddedProductionCoreSchedule`.  This module supplies the exact
one-root counterpart, retaining the caller-owned small mask and witness
planes across mark, normalization, and checking.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

namespace LeanCompCert.Ports.TGEvenGoldbachTwoMaskSingleSegmentedSound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.TGEvenGoldbachPrimeRows

/-- Transfer the proved one-root sieve denotation from its canonical zero
scratch array to a larger caller allocation. -/
theorem maskCorrect_of_single_segmented_source_runs
    (sieve : ArraySegSieve.Cfg) (bootBound valid delta : Nat)
    (hSchedule : SingleMixedPaddedRootSchedule sieve bootBound valid delta)
    (hBase : (1 + ((sieve.segLen + delta) % M)) % M = sieve.lo)
    (hLen : (rootScanMixed sieve.bootPrimes bootBound 1 valid).length =
      sieve.tableLen)
    (hBudget : ((rootScanMixed sieve.bootPrimes bootBound 1 valid).map
      fun p => sieve.segLen / p + 2).sum ≤ sieve.markSteps)
    (hIdxM : sieve.rootSpan + sieve.markSteps < M)
    (hRootSqM : sieve.rootCap * sieve.rootCap < M)
    (hSegRootM : sieve.segLen + sieve.rootCap < M)
    (hLoSegM : sieve.lo + sieve.segLen < M)
    (hAboveRoot : sieve.rootCap < sieve.lo)
    (hCovered : sieve.lo + sieve.segLen - 1 ≤
      sieve.rootCap * sieve.rootCap)
    (initial : Nat → Nat) (marked normalized : AState)
    (hZeroPrefix : ∀ j, j < sieve.arrayLen → initial j = 0)
    (hMark : (RS62SegmentedPrimeMask.program sieve).runFromArray initial =
      some marked)
    (hNormalize : (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).runFromArray
      marked.arr = some normalized) :
    RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
      normalized.arr sieve.lo sieve.segLen := by
  have hScratch : sieve.segLen ≤ sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  obtain ⟨canonicalMarked, hCanonicalMark, hMarkedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.program sieve) initial (fun _ => 0) marked
      (fun j hj => by simpa using hZeroPrefix j hj) hMark
  have hNormalizeInput : ∀ j,
      j < (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen →
        marked.arr j = canonicalMarked.arr j := by
    intro j hj
    apply hMarkedAgree.2 j
    simpa [RS62SegmentedPrimeMask.program] using
      Nat.lt_of_lt_of_le hj hScratch
  obtain ⟨canonicalNormalized, hCanonicalNormalize, hNormalizedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) marked.arr
      canonicalMarked.arr normalized hNormalizeInput hNormalize
  have hCanonicalMask := RS62SegmentedPrimeMask.normalizedRun_maskCorrect
    sieve bootBound valid delta hSchedule hBase hLen hBudget hIdxM hRootSqM
    hSegRootM hLoSegM hAboveRoot hCovered canonicalMarked canonicalNormalized
    hCanonicalMark hCanonicalNormalize
  intro k hk
  rw [hNormalizedAgree.2 k (by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using hk)]
  exact hCanonicalMask k hk

/-- Complete physical package for a source shard whose root table is built
inside one padded mixed window. -/
structure RolledSingleSegmentedPipeline
    (sieve : ArraySegSieve.Cfg) (c : TGEvenGoldbachTwoMask.Cfg) where
  bootBound : Nat
  valid : Nat
  delta : Nat
  schedule : SingleMixedPaddedRootSchedule sieve bootBound valid delta
  base_eq : (1 + ((sieve.segLen + delta) % M)) % M = sieve.lo
  table_len :
    (rootScanMixed sieve.bootPrimes bootBound 1 valid).length = sieve.tableLen
  budget : ((rootScanMixed sieve.bootPrimes bootBound 1 valid).map
    fun p => sieve.segLen / p + 2).sum ≤ sieve.markSteps
  idx_word : sieve.rootSpan + sieve.markSteps < M
  root_sq_word : sieve.rootCap * sieve.rootCap < M
  seg_root_word : sieve.segLen + sieve.rootCap < M
  upper_word : sieve.lo + sieve.segLen < M
  above_root : sieve.rootCap < sieve.lo
  covered : sieve.lo + sieve.segLen - 1 ≤ sieve.rootCap * sieve.rootCap
  segment_pos : 0 < sieve.segLen
  large_lo : c.largeLo = sieve.lo
  large_len : c.largeLen = sieve.segLen
  suffix_after_sieve : sieve.arrayLen ≤ c.smallBase
  initial : Nat → Nat
  ready : TGEvenGoldbachTwoMask.Ready c initial
  zero_prefix : ∀ j, j < sieve.arrayLen → initial j = 0
  small_mask : TGEvenGoldbachTwoMask.PrimeMaskCorrect initial c.smallBase
    c.smallLo c.smallLen
  initial_words : ∀ j, initial j < M
  base : Int
  base_ok : BaseOk c.arrayLen base
  mem : Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((initial k : Nat) : Int))
  mark_audit : TGEvenGoldbachTwoMask.AuditRolledZero
    (RS62SegmentedPrimeMask.program sieve) base mem
  marked : MCCState
  mark_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.program sieve) c.arrayLen)) base mem)
    ((RS62SegmentedPrimeMask.program sieve).padArray c.arrayLen).rolledCompile =
      some marked
  normalize_audit : TGEvenGoldbachTwoMask.AuditRolledZero
    (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) base marked.mem
  normalized : MCCState
  normalize_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) c.arrayLen))
      base marked.mem)
    ((RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).padArray
      c.arrayLen).rolledCompile = some normalized
  checker_audit : TGEvenGoldbachTwoMask.AuditRolledZero
    (TGEvenGoldbachTwoMask.program c) base normalized.mem
  checker_run : TGEvenGoldbachTwoMask.RolledResult
    (TGEvenGoldbachTwoMask.program c) base normalized.mem 0

/-- Exact signature-to-source theorem for the one-root/two-mask shard. -/
theorem RolledSingleSegmentedPipeline.sound
    {sieve : ArraySegSieve.Cfg} {c : TGEvenGoldbachTwoMask.Cfg}
    (r : RolledSingleSegmentedPipeline sieve c) :
    TGEvenGoldbachTwoMask.Covers c := by
  have hMarkPrefix :
      (RS62SegmentedPrimeMask.program sieve).arrayLen ≤ c.arrayLen := by
    have hLayout := r.ready.2.2.2.1
    have hSuffix := r.suffix_after_sieve
    simp only [RS62SegmentedPrimeMask.program,
      TGEvenGoldbachTwoMask.Cfg.arrayLen]
    omega
  have hMarkLen :
      0 < (RS62SegmentedPrimeMask.program sieve).arrayLen := by
    have hScratch : sieve.segLen ≤ sieve.arrayLen := by
      simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
      omega
    simp only [RS62SegmentedPrimeMask.program]
    exact Nat.lt_of_lt_of_le r.segment_pos hScratch
  have hArrayM : c.arrayLen < M := r.ready.2.2.2.2.2.2.2.2.1
  obtain ⟨marked, hMark, hMarkedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.program sieve)
      (RS62SegmentedPrimeMask.program_wf sieve) c.arrayLen hMarkPrefix
      hMarkLen hArrayM r.initial r.initial_words r.base r.base_ok r.mem
      r.cells r.mark_audit r.marked r.mark_eval
  have hMarkedWords : ∀ j, marked.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.program sieve) r.initial r.initial_words
      marked hMark).2
  have hNormalizePrefix :
      (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen ≤
        c.arrayLen := by
    have hScratch : sieve.segLen ≤ sieve.arrayLen := by
      simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
      omega
    have hSuffix := r.suffix_after_sieve
    have hLayout := r.ready.2.2.2.1
    simp only [RS62SegmentedPrimeMask.normalizeProgram,
      TGEvenGoldbachTwoMask.Cfg.arrayLen]
    omega
  have hNormalizeLen :
      0 < (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).arrayLen := by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using r.segment_pos
  obtain ⟨normalized, hNormalize, hNormalizedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen)
      (RS62SegmentedPrimeMask.normalizeProgram_wf sieve.segLen) c.arrayLen
      hNormalizePrefix hNormalizeLen hArrayM marked.arr hMarkedWords r.base
      r.base_ok r.marked.mem hMarkedCells r.normalize_audit r.normalized
      r.normalize_eval
  have hNormalizedWords : ∀ j, normalized.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen) marked.arr
      hMarkedWords normalized hNormalize).2
  have hMask := maskCorrect_of_single_segmented_source_runs sieve r.bootBound
    r.valid r.delta r.schedule r.base_eq r.table_len r.budget r.idx_word
    r.root_sq_word r.seg_root_word r.upper_word r.above_root r.covered
    r.initial marked normalized r.zero_prefix hMark hNormalize
  have hLarge : TGEvenGoldbachTwoMask.PrimeMaskCorrect normalized.arr 0
      c.largeLo c.largeLen :=
    TGEvenGoldbachTwoMaskSegmentedSound.largePrimeMaskCorrect_of_maskCorrect
      c sieve normalized.arr r.large_lo r.large_len hMask
  have hScratch : sieve.segLen ≤ sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  have hSmall : TGEvenGoldbachTwoMask.PrimeMaskCorrect normalized.arr
      c.smallBase c.smallLo c.smallLen := by
    intro i hi
    have hAddr : sieve.arrayLen ≤ c.smallBase + i := by
      have hSuffix := r.suffix_after_sieve
      omega
    have hMarkFrame := (RS62SegmentedPrimeMask.program sieve).runFromArray_frame_ge
      r.initial marked hMark (c.smallBase + i) hAddr
    have hNormalizeFrame :=
      (RS62SegmentedPrimeMask.normalizeProgram sieve.segLen).runFromArray_frame_ge
        marked.arr normalized hNormalize (c.smallBase + i)
        (Nat.le_trans hScratch hAddr)
    rw [hNormalizeFrame, hMarkFrame]
    exact r.small_mask i hi
  have hReady : TGEvenGoldbachTwoMask.Ready c normalized.arr := by
    rcases r.ready with
      ⟨hLargePos, hSmallPos, hLayoutLarge, hLayoutSmall, hLargeM, hSmallM,
        hSumM, hEvenM, hFullM, _⟩
    exact ⟨hLargePos, hSmallPos, hLayoutLarge, hLayoutSmall, hLargeM,
      hSmallM, hSumM, hEvenM, hFullM, fun i _ => hNormalizedWords i⟩
  exact TGEvenGoldbachTwoMask.covers_of_rolled_receipts c normalized.arr
    hReady hSmall hLarge r.base r.base_ok r.normalized.mem hNormalizedCells
    hNormalizedWords r.checker_audit r.checker_run

#print axioms maskCorrect_of_single_segmented_source_runs
#print axioms RolledSingleSegmentedPipeline.sound

end LeanCompCert.Ports.TGEvenGoldbachTwoMaskSingleSegmentedSound
