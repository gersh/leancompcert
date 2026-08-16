import LeanCompCert.Ports.R2ProductAuditTelescope
import LeanCompCert.Ports.R2RuntimeSetupReceipt

/-!
# Physical receipt for the compiled R₂ exact-product audit

The setup stages build and verify the packed prime table.  The final stage is
the combined partial-operation and exact-product audit.  This file turns a
physical CompCert trace into a source run and then telescopes its zero latch to
every production multiplication; Lean never evaluates the production fold.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ProductAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment

/-- Exact shared-memory trace emitted by the `product-audit` mode of
`bench/R2RuntimeProductionEmit.lean`. -/
def RuntimeProductionProductAuditReceipt : Prop :=
  ∃ mMark mPack mReceipt mAudit : MCCState,
    evalMCCSequence
        ((r2RootMarkProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 (initialMem runtimeProductionCfg.arrayLen 0))
        (r2RootMarkProgram runtimeProductionCfg).rolledCompile = some mMark ∧
    mMark.env ⟨(r2RootMarkProgram runtimeProductionCfg).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((r2RootPackProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mMark.mem)
        (r2RootPackProgram runtimeProductionCfg).rolledCompile = some mPack ∧
    mPack.env ⟨(r2RootPackProgram runtimeProductionCfg).output + 1⟩ =
      some (runtimePrimeCount : Int) ∧
    evalMCCSequence
        ((rootReceiptProgram runtimeProductionCfg).counterAugment.initialMCCWithMem
          0 mPack.mem)
        (rootReceiptProgram runtimeProductionCfg).rolledCompile = some mReceipt ∧
    mReceipt.env ⟨(rootReceiptProgram runtimeProductionCfg).output + 1⟩ = some 0 ∧
    evalMCCSequence
        (runtimeProductAuditProgram.counterAugment.initialMCCWithMem
          0 mReceipt.mem)
        runtimeProductAuditProgram.rolledCompile = some mAudit ∧
    mAudit.env ⟨runtimeProductAuditProgram.output + 1⟩ = some 0

private theorem productionProductAuditBaseOk :
    BaseOk runtimeProductAuditProgram.arrayLen 0 := by
  rw [runtimeProductAuditProgram_arrayLen]
  constructor <;> decide

/-- Compiler simulation and audit soundness turn the retained physical trace
into a zero-latch run of the product-instrumented source. -/
theorem runtimeProductionProductAudit_source_run
    (h : RuntimeProductionProductAuditReceipt) :
    ∃ marked packed out : AState,
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
          some marked ∧
      (r2RootPackProgram runtimeProductionCfg).runFromArray marked.arr =
          some packed ∧
      packed.regs rpWrite = runtimePrimeCount ∧
      RootReceiptOK packed.arr ∧
      (∀ i, packed.arr i < LeanCompCert.Verified.Reflect.M) ∧
      runtimeProductSourceProgram.runFromArray packed.arr = some out ∧
      out.regs auditReg = 0 := by
  rcases h with
    ⟨mMark, mPack, mReceipt, mAudit, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero,
      hAuditEval, hAuditZero⟩
  have hSetup : RootSetupReceipt :=
    ⟨mMark, mPack, mReceipt, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero⟩
  rcases runtimeRootSetup_source_memory hSetup with
    ⟨marked, packed, mMark', mPack', mReceipt', hMarkRun, hPackRun, hCount,
      hReceiptOK, hPackedWord, hMarkEval', hPackEval', hReceiptEval', hCells⟩
  have hmMark : mMark' = mMark := by
    rw [hMarkEval] at hMarkEval'
    exact (Option.some.inj hMarkEval').symm
  subst mMark'
  have hmPack : mPack' = mPack := by
    rw [hPackEval] at hPackEval'
    exact (Option.some.inj hPackEval').symm
  subst mPack'
  have hmReceipt : mReceipt' = mReceipt := by
    rw [hReceiptEval] at hReceiptEval'
    exact (Option.some.inj hReceiptEval').symm
  subst mReceipt'
  have hAuditRun := runtimeProductAudit_runFromArray packed.arr hPackedWord
  have hCells' : ∀ k, k < runtimeProductAuditProgram.arrayLen →
      mReceipt.mem (cellAddr 0 k) =
        some (((packed.arr k : Nat) : Int)) := by
    intro k hk
    rw [runtimeProductAuditProgram_arrayLen] at hk
    exact hCells k hk
  have hCellsLt : ∀ k, k < runtimeProductAuditProgram.arrayLen →
      packed.arr k < LeanCompCert.Verified.Reflect.M := by
    intro k _
    exact hPackedWord k
  have hAuditReceipt : Option.bind
      (evalMCCSequence
        (runtimeProductAuditProgram.counterAugment.initialMCCWithMem
          0 mReceipt.mem)
        runtimeProductAuditProgram.rolledCompile)
      (fun m : MCCState =>
        m.env ⟨runtimeProductAuditProgram.output + 1⟩) = some (0 : Int) := by
    rw [hAuditEval]
    exact hAuditZero
  have hCombinedZero := AProgram.output_eq_of_rolledCompile_fromArray
    runtimeProductAuditProgram runtimeProductAuditProgram_wf 0
    productionProductAuditBaseOk packed.arr mReceipt.mem hCells' hCellsLt
    (combinedFinal packed.arr) hAuditRun 0 hAuditReceipt
  rw [runtimeProductAuditProgram_output] at hCombinedZero
  rcases runtimeProductAudit_zero_sound_fromArray packed.arr hPackedWord
    hCombinedZero with ⟨out, hSourceRun, hProductZero⟩
  exact ⟨marked, packed, out, hMarkRun, hPackRun, hCount, hReceiptOK,
    hPackedWord, hSourceRun, hProductZero⟩

/-- The physical trace certifies every exact natural-number product used by
the production marking loop. -/
theorem runtimeProductionProductAudit_every_product_fits
    (h : RuntimeProductionProductAuditReceipt) :
    ∃ packed : AState,
      RootReceiptOK packed.arr ∧
      ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
        (runtimeOriginalBeforeMul packed.arr j).regs 35 *
          (runtimeOriginalBeforeMul packed.arr j).regs rBp <
            LeanCompCert.Verified.Reflect.M := by
  rcases runtimeProductionProductAudit_source_run h with
    ⟨_, packed, out, _, _, _, hReceipt, hPackedWord, hRun, hzero⟩
  refine ⟨packed, hReceipt, ?_⟩
  exact runtime_every_original_product_fits_of_source_run packed.arr
    hPackedWord out hRun hzero

/-- Determinism identifies the setup array with the canonical production
table, yielding the exact original-sweep states used by the marking proofs. -/
theorem runtimeProductionProductAudit_canonical_products_fit
    (h : RuntimeProductionProductAuditReceipt) :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      (runtimeOriginalBeforeMul
          (rootPackedState runtimeProductionCfg
            (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr j).regs 35 *
        (runtimeOriginalBeforeMul
          (rootPackedState runtimeProductionCfg
            (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr j).regs rBp <
          LeanCompCert.Verified.Reflect.M := by
  rcases runtimeProductionProductAudit_source_run h with
    ⟨marked, packed, out, hMarkRun, hPackRun, _, _, hPackedWord,
      hRun, hzero⟩
  have hMarkedExact := rootMarkProduction_runFromArray (fun _ => 0)
  rw [hMarkRun] at hMarkedExact
  have hMarked : marked =
      rootMarkedState runtimeProductionCfg (fun _ => 0) :=
    Option.some.inj hMarkedExact
  have hPackRun' :
      (r2RootPackProgram runtimeProductionCfg).runFromArray
          (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr =
        some packed := by
    rw [← hMarked]
    exact hPackRun
  have hPackedExact := rootPackProduction_runFromArray_exact
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
  rw [hPackRun'] at hPackedExact
  have hPacked : packed = rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr :=
    Option.some.inj hPackedExact
  subst packed
  exact runtime_every_original_product_fits_of_source_run
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
    hPackedWord out hRun hzero

#print axioms runtimeProductionProductAudit_source_run
#print axioms runtimeProductionProductAudit_every_product_fits
#print axioms runtimeProductionProductAudit_canonical_products_fit

end LeanCompCert.Ports.R2SegSieve.R2ProductAudit
