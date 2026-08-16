import LeanCompCert.Ports.R2RuntimePackTableSemantics
import LeanCompCert.Ports.R2RuntimeTableReceipt
import LeanCompCert.Verified.ArrayRolledPipeline
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Physical receipt for the compiled R2 runtime table setup

The production driver constructs its prime/log table in compiled code before
the long sparse sweep.  This module gives the already-benchmarked three-stage
setup one constant-size trust proposition and reads that proposition back to
the symbolic source table.  The root mark and pack folds remain opaque: Lean
uses compiler simulation and determinism, never production evaluation.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment

/-- The exact shared-memory trace exercised by `R2RuntimeTableEmit`. -/
def RootSetupReceipt : Prop :=
  ∃ mMark mPack mReceipt : MCCState,
    evalMCCSequence
        ((r2RootMarkProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 (initialMem runtimeProductionCfg.arrayLen 0))
        (r2RootMarkProgram runtimeProductionCfg).rolledCompile = some mMark ∧
    mMark.env ⟨(r2RootMarkProgram runtimeProductionCfg).output + 1⟩ =
      some (0 : Int) ∧
    evalMCCSequence
        ((r2RootPackProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mMark.mem)
        (r2RootPackProgram runtimeProductionCfg).rolledCompile = some mPack ∧
    mPack.env ⟨(r2RootPackProgram runtimeProductionCfg).output + 1⟩ =
      some (runtimePrimeCount : Int) ∧
    evalMCCSequence
        ((rootReceiptProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mPack.mem)
        (rootReceiptProgram runtimeProductionCfg).rolledCompile =
      some mReceipt ∧
    mReceipt.env ⟨(rootReceiptProgram runtimeProductionCfg).output + 1⟩ =
      some (0 : Int)

/-- CompCert 3.17 returned a clean root marker, exactly `13,415` packed
entries, and the accepting endpoint/sentinel/checksum receipt.  The retained
positive and checksum-corruption control are recorded in
`bench/results/manifests/r2star_runtime_table.json`. -/
axiom runtimeRootSetup_compcert_run : RootSetupReceipt

private theorem productionBaseOk : BaseOk runtimeProductionCfg.arrayLen 0 := by
  constructor <;> decide

/-- The physical setup receipt identifies a successful symbolic mark/pack
pipeline and proves the compact table property consumed by the main sweep.
No root-sized fold is reduced in this proof. -/
theorem runtimeRootSetup_source_table (h : RootSetupReceipt) :
    ∃ marked packed : AState,
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
          some marked ∧
      (r2RootPackProgram runtimeProductionCfg).runFromArray marked.arr =
          some packed ∧
      packed.regs rpWrite = runtimePrimeCount ∧
      RootReceiptOK packed.arr := by
  rcases h with
    ⟨mMark, mPack, mReceipt, hMarkEval, _hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero⟩
  let marked := rootMarkedState runtimeProductionCfg (fun _ => 0)
  have hMarkRun :
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
        some marked := by
    simpa only [marked] using rootMarkProduction_runFromArray (fun _ => 0)
  obtain ⟨markedAug, hMarkAug, hMarkAgree⟩ :=
    (r2RootMarkProgram runtimeProductionCfg).counterAugment_runFromArray_of_runFromArray
        (r2RootMarkProgram_wf runtimeProductionCfg) (fun _ => 0) marked hMarkRun
  obtain ⟨mMark', hMarkEval', hMarkRel⟩ :=
    (r2RootMarkProgram runtimeProductionCfg).evalCC_rolledCompile_fromArray
      (r2RootMarkProgram_wf runtimeProductionCfg) 0 productionBaseOk
      (fun _ => 0) (initialMem runtimeProductionCfg.arrayLen 0)
      (fun k hk => initialMem_cell runtimeProductionCfg.arrayLen 0 hk)
      (fun _ _ => M_pos) markedAug hMarkAug
  have hmMark : mMark' = mMark := by
    rw [hMarkEval] at hMarkEval'
    exact (Option.some.inj hMarkEval').symm
  subst mMark'
  obtain ⟨packed, hPackRun⟩ := rootPackProduction_runFromArray marked.arr
  have hMarkCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mMark.mem (cellAddr 0 k) = some (((marked.arr k : Nat) : Int)) := by
    intro k hk
    rw [hMarkAgree.2]
    exact hMarkRel.hcells k hk
  have hMarkCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen →
      marked.arr k < M := by
    intro k hk
    rw [hMarkAgree.2]
    exact hMarkRel.hcellsLt k hk
  obtain ⟨packedAug, hPackAug, hPackAgree⟩ :=
    (r2RootPackProgram runtimeProductionCfg).counterAugment_runFromArray_of_runFromArray
        (r2RootPackProgram_wf runtimeProductionCfg) marked.arr packed hPackRun
  obtain ⟨mPack', hPackEval', hPackRel⟩ :=
    (r2RootPackProgram runtimeProductionCfg).evalCC_rolledCompile_fromArray
      (r2RootPackProgram_wf runtimeProductionCfg) 0 productionBaseOk
      marked.arr mMark.mem hMarkCells hMarkCellsLt packedAug hPackAug
  have hmPack : mPack' = mPack := by
    rw [hPackEval] at hPackEval'
    exact (Option.some.inj hPackEval').symm
  subst mPack'
  have hPackReceipt : Option.bind
      (evalMCCSequence
        ((r2RootPackProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mMark.mem)
        (r2RootPackProgram runtimeProductionCfg).rolledCompile)
      (fun m : MCCState =>
        m.env ⟨(r2RootPackProgram runtimeProductionCfg).output + 1⟩) =
        some (runtimePrimeCount : Int) := by
    rw [hPackEval]
    exact hPackCount
  have hCount : packed.regs rpWrite = runtimePrimeCount := by
    simpa only [r2RootPackProgram] using
      AProgram.output_eq_of_rolledCompile_fromArray
        (r2RootPackProgram runtimeProductionCfg)
        (r2RootPackProgram_wf runtimeProductionCfg) 0 productionBaseOk
        marked.arr mMark.mem hMarkCells hMarkCellsLt packed hPackRun
        runtimePrimeCount hPackReceipt
  have hPackedCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mPack.mem (cellAddr 0 k) = some (((packed.arr k : Nat) : Int)) := by
    intro k hk
    rw [hPackAgree.2]
    exact hPackRel.hcells k hk
  have hPackedCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen →
      packed.arr k < M := by
    intro k hk
    rw [hPackAgree.2]
    exact hPackRel.hcellsLt k hk
  let receiptOut := rootReceiptFinalState packed.arr
  have hReceiptRun :
      (rootReceiptProgram runtimeProductionCfg).runFromArray packed.arr =
        some receiptOut := by
    simpa only [receiptOut] using rootReceiptProduction_runFromArray packed.arr
  have hReceiptMachine : Option.bind
      (evalMCCSequence
        ((rootReceiptProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mPack.mem)
        (rootReceiptProgram runtimeProductionCfg).rolledCompile)
      (fun m : MCCState =>
        m.env ⟨(rootReceiptProgram runtimeProductionCfg).output + 1⟩) =
        some (0 : Int) := by
    rw [hReceiptEval]
    exact hReceiptZero
  have hReceiptOut : receiptOut.regs rrFail = 0 := by
    simpa only [rootReceiptProgram] using
      AProgram.output_eq_of_rolledCompile_fromArray
        (rootReceiptProgram runtimeProductionCfg)
        (rootReceiptProgram_wf runtimeProductionCfg) 0 productionBaseOk
        packed.arr mPack.mem hPackedCells hPackedCellsLt receiptOut hReceiptRun
        0 hReceiptMachine
  exact ⟨marked, packed, hMarkRun, hPackRun, hCount,
    rootReceiptFinalState_zero_sound packed.arr hReceiptOut⟩

/-- The physical setup receipt reaches the source-facing prime table, not
merely a checksum.  It proves the exact production prime count and gives the
prime plus verified fixed-log payload stored at every resident table index.
All large marker/packer folds remain opaque; determinism identifies their
symbolic outputs with the physically observed execution. -/
theorem runtimeRootSetup_source_prime_table (h : RootSetupReceipt) :
    runtimePrimeCount = rootTrialPrimeCount (runtimeRoot - 1) ∧
      ∀ i, i < runtimePrimeCount →
        ∃ q, q < runtimeRoot - 1 ∧
          LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
          rootTrialPrimeCount q = i ∧
          (rootPackedState runtimeProductionCfg
            (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
              (runtimeProductionCfg.tableBase + i) =
            packEntry (q + 2)
              (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  rcases runtimeRootSetup_source_table h with
    ⟨marked, packed, hMarkRun, hPackRun, hCount, _hReceipt⟩
  have hMarkedExact := rootMarkProduction_runFromArray (fun _ => 0)
  rw [hMarkRun] at hMarkedExact
  have hMarked : marked =
      rootMarkedState runtimeProductionCfg (fun _ => 0) :=
    Option.some.inj hMarkedExact
  subst marked
  have hPackedExact := rootPackProduction_runFromArray_exact
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
  rw [hPackRun] at hPackedExact
  have hPacked : packed = rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr :=
    Option.some.inj hPackedExact
  subst packed
  have hCountExact := rootProductionPackedState_write_count
  refine ⟨hCount.symm.trans hCountExact, ?_⟩
  intro i hi
  apply rootProductionPackedState_entry_of_index i
  rw [hCount]
  exact hi

/-- In addition to the source table property, the final compiled receipt
memory represents the exact symbolic packed array.  This is the handoff used
by a following audited consumer; it is proved by compiler simulation and
determinism of each retained physical stage, not by reading the table in
Lean. -/
theorem runtimeRootSetup_source_memory (h : RootSetupReceipt) :
    ∃ marked packed : AState, ∃ mMark mPack mReceipt : MCCState,
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
          some marked ∧
      (r2RootPackProgram runtimeProductionCfg).runFromArray marked.arr =
          some packed ∧
      packed.regs rpWrite = runtimePrimeCount ∧
      RootReceiptOK packed.arr ∧
      (∀ k, packed.arr k < M) ∧
      evalMCCSequence
          ((r2RootMarkProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
            0 (initialMem runtimeProductionCfg.arrayLen 0))
          (r2RootMarkProgram runtimeProductionCfg).rolledCompile =
        some mMark ∧
      evalMCCSequence
          ((r2RootPackProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
            0 mMark.mem)
          (r2RootPackProgram runtimeProductionCfg).rolledCompile =
        some mPack ∧
      evalMCCSequence
          ((rootReceiptProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
            0 mPack.mem)
          (rootReceiptProgram runtimeProductionCfg).rolledCompile =
        some mReceipt ∧
      (∀ k, k < runtimeProductionCfg.arrayLen →
        mReceipt.mem (cellAddr 0 k) = some (((packed.arr k : Nat) : Int))) := by
  rcases h with
    ⟨mMark, mPack, mReceipt, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero⟩
  have hSource := runtimeRootSetup_source_table
    ⟨mMark, mPack, mReceipt, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero⟩
  rcases hSource with
    ⟨marked, packed, hMarkRun, hPackRun, hCount, hReceiptOK⟩
  obtain ⟨markedAug, hMarkAug, hMarkAgree⟩ :=
    (r2RootMarkProgram runtimeProductionCfg).counterAugment_runFromArray_of_runFromArray
      (r2RootMarkProgram_wf runtimeProductionCfg) (fun _ => 0) marked hMarkRun
  obtain ⟨mMark', hMarkEval', hMarkRel⟩ :=
    (r2RootMarkProgram runtimeProductionCfg).evalCC_rolledCompile_fromArray
      (r2RootMarkProgram_wf runtimeProductionCfg) 0 productionBaseOk
      (fun _ => 0) (initialMem runtimeProductionCfg.arrayLen 0)
      (fun k hk => initialMem_cell runtimeProductionCfg.arrayLen 0 hk)
      (fun _ _ => M_pos) markedAug hMarkAug
  have hmMark : mMark' = mMark := by
    rw [hMarkEval] at hMarkEval'
    exact (Option.some.inj hMarkEval').symm
  subst mMark'
  have hMarkCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mMark.mem (cellAddr 0 k) = some (((marked.arr k : Nat) : Int)) := by
    intro k hk
    rw [hMarkAgree.2]
    exact hMarkRel.hcells k hk
  have hMarkCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen →
      marked.arr k < M := by
    intro k hk
    rw [hMarkAgree.2]
    exact hMarkRel.hcellsLt k hk
  obtain ⟨packedAug, hPackAug, hPackAgree⟩ :=
    (r2RootPackProgram runtimeProductionCfg).counterAugment_runFromArray_of_runFromArray
      (r2RootPackProgram_wf runtimeProductionCfg) marked.arr packed hPackRun
  obtain ⟨mPack', hPackEval', hPackRel⟩ :=
    (r2RootPackProgram runtimeProductionCfg).evalCC_rolledCompile_fromArray
      (r2RootPackProgram_wf runtimeProductionCfg) 0 productionBaseOk
      marked.arr mMark.mem hMarkCells hMarkCellsLt packedAug hPackAug
  have hmPack : mPack' = mPack := by
    rw [hPackEval] at hPackEval'
    exact (Option.some.inj hPackEval').symm
  subst mPack'
  have hPackCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mPack.mem (cellAddr 0 k) = some (((packed.arr k : Nat) : Int)) := by
    intro k hk
    rw [hPackAgree.2]
    exact hPackRel.hcells k hk
  have hPackCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen →
      packed.arr k < M := by
    intro k hk
    rw [hPackAgree.2]
    exact hPackRel.hcellsLt k hk
  let receiptOut := rootReceiptFinalState packed.arr
  have hReceiptRun :
      (rootReceiptProgram runtimeProductionCfg).runFromArray packed.arr =
        some receiptOut := by
    simpa only [receiptOut] using rootReceiptProduction_runFromArray packed.arr
  obtain ⟨receiptAug, hReceiptAug, hReceiptAgree⟩ :=
    (rootReceiptProgram runtimeProductionCfg).counterAugment_runFromArray_of_runFromArray
      (rootReceiptProgram_wf runtimeProductionCfg) packed.arr receiptOut
      hReceiptRun
  obtain ⟨mReceipt', hReceiptEval', hReceiptRel⟩ :=
    (rootReceiptProgram runtimeProductionCfg).evalCC_rolledCompile_fromArray
      (rootReceiptProgram_wf runtimeProductionCfg) 0 productionBaseOk
      packed.arr mPack.mem hPackCells hPackCellsLt receiptAug hReceiptAug
  have hmReceipt : mReceipt' = mReceipt := by
    rw [hReceiptEval] at hReceiptEval'
    exact (Option.some.inj hReceiptEval').symm
  subst mReceipt'
  have hReceiptArr : receiptOut.arr = packed.arr := by
    have hspec := rootReceiptMachineFold_spec packed.arr
      (runtimePrimeCount + 1) (by omega)
    change (rootReceiptFinalState packed.arr).arr = packed.arr
    rw [rootReceiptFinalState, rootReceiptEpilogue_arr]
    exact hspec.2
  have hMarkedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (r2RootMarkProgram runtimeProductionCfg) (fun _ => 0)
      (fun _ => M_pos) marked hMarkRun
  have hPackedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (r2RootPackProgram runtimeProductionCfg) marked.arr hMarkedWord.2 packed
      hPackRun
  refine ⟨marked, packed, mMark, mPack, mReceipt, hMarkRun, hPackRun, hCount,
    hReceiptOK, hPackedWord.2, hMarkEval, hPackEval, hReceiptEval, ?_⟩
  intro k hk
  rw [← hReceiptArr, hReceiptAgree.2]
  exact hReceiptRel.hcells k hk

/-- The retained CompCert run specializes the generic physical-to-symbolic
bridge without asking Lean to replay the production setup folds. -/
theorem runtimeRootSetup_verified_table :
    ∃ marked packed : AState,
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
          some marked ∧
      (r2RootPackProgram runtimeProductionCfg).runFromArray marked.arr =
          some packed ∧
      packed.regs rpWrite = runtimePrimeCount ∧
      RootReceiptOK packed.arr :=
  runtimeRootSetup_source_table runtimeRootSetup_compcert_run

/-- Every cell of the exact symbolic production table is a machine word.
This is obtained from the retained setup execution and determinism, without
normalizing either of the production root folds. -/
theorem runtimeRootSetup_verified_packed_words :
    ∀ k, (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr k < M := by
  rcases runtimeRootSetup_source_memory runtimeRootSetup_compcert_run with
    ⟨marked, packed, _, _, _, hMarkRun, hPackRun, _, _, hPackedWords, _⟩
  have hMarkedExact := rootMarkProduction_runFromArray (fun _ => 0)
  rw [hMarkRun] at hMarkedExact
  have hMarked : marked =
      rootMarkedState runtimeProductionCfg (fun _ => 0) :=
    Option.some.inj hMarkedExact
  have hPackRunExact :
      (r2RootPackProgram runtimeProductionCfg).runFromArray
          (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr =
        some packed := by
    rw [← hMarked]
    exact hPackRun
  have hPackedExact := rootPackProduction_runFromArray_exact
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
  rw [hPackRunExact] at hPackedExact
  have hPacked : packed = rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr :=
    Option.some.inj hPackedExact
  intro k
  rw [← hPacked]
  exact hPackedWords k

/-- Closed specialization of the source-facing prime-table theorem to the
retained CompCert setup receipt. -/
theorem runtimeRootSetup_verified_prime_table :
    runtimePrimeCount = rootTrialPrimeCount (runtimeRoot - 1) ∧
      ∀ i, i < runtimePrimeCount →
        ∃ q, q < runtimeRoot - 1 ∧
          LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
          rootTrialPrimeCount q = i ∧
          (rootPackedState runtimeProductionCfg
            (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
              (runtimeProductionCfg.tableBase + i) =
            packEntry (q + 2)
          (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 :=
  runtimeRootSetup_source_prime_table runtimeRootSetup_compcert_run

/-- Fully decoded cursor handoff for the main production sweep.  Each
resident cursor names a genuine prime, and the actual loaded word decodes to
that prime and its verified fixed-log weight. -/
theorem runtimeRootSetup_verified_prime_cursor (i : Nat)
    (hi : i < runtimePrimeCount) :
    ∃ q, q < runtimeRoot - 1 ∧
      LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
      rootTrialPrimeCount q = i ∧
      let word := (rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
          (runtimeProductionCfg.tableBase + i)
      word = packEntry (q + 2)
          (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 ∧
        word &&& maskVal = q + 2 ∧
        ((word >>> valBits) &&& maskWt) =
          LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2) := by
  obtain ⟨q, hq, hprime, hrank, hentry⟩ :=
    runtimeRootSetup_verified_prime_table.2 i hi
  refine ⟨q, hq, hprime, hrank, hentry, ?_, ?_⟩
  · rw [hentry]
    apply packEntry_value_decode
    simp only [runtimeRoot, valBits] at hq ⊢
    omega
  · have hword := runtimeRootSetup_verified_packed_words
      (runtimeProductionCfg.tableBase + i)
    rw [hentry] at hword ⊢
    apply packEntry_weight_decode
    · simp only [runtimeRoot, valBits] at hq ⊢
      omega
    · exact hword

/-- Total lookup contract for the clamped main-sweep cursor: every index
through `tableLen` is either a decoded prime row or the exact inert terminal
sentinel. -/
theorem runtimeRootSetup_verified_cursor_word (i : Nat)
    (hi : i ≤ runtimePrimeCount) :
    (i = runtimePrimeCount ∧
      (rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
          (runtimeProductionCfg.tableBase + i) = packEntry 1 0 0) ∨
    (i < runtimePrimeCount ∧
      ∃ q, q < runtimeRoot - 1 ∧
        LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
        rootTrialPrimeCount q = i ∧
        let word := (rootPackedState runtimeProductionCfg
          (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
            (runtimeProductionCfg.tableBase + i)
        word = packEntry (q + 2)
            (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 ∧
          word &&& maskVal = q + 2 ∧
          ((word >>> valBits) &&& maskWt) =
            LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) := by
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact Or.inr ⟨hlt, runtimeRootSetup_verified_prime_cursor i hlt⟩
  · refine Or.inl ⟨heq, ?_⟩
    rw [heq, runtimeRootSetup_verified_prime_table.1]
    exact rootProductionPackedState_sentinel

#print axioms runtimeRootSetup_source_table
#print axioms runtimeRootSetup_source_prime_table
#print axioms runtimeRootSetup_source_memory
#print axioms runtimeRootSetup_verified_table
#print axioms runtimeRootSetup_verified_packed_words
#print axioms runtimeRootSetup_verified_prime_table
#print axioms runtimeRootSetup_verified_prime_cursor
#print axioms runtimeRootSetup_verified_cursor_word

end LeanCompCert.Ports.R2SegSieve
