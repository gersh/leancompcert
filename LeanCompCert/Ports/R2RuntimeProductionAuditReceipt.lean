import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Ports.R2RuntimeSetupReceipt
import LeanCompCert.Ports.R2RuntimeProductionReceipt
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Fail-safe physical receipt for the compiled R2 production sweep

The production root marker, table packer, and table receipt checker build a
caller-owned array.  The fourth stage is the mechanically audited version of
the 221,163,768,000-step sparse sweep.  A zero audit result proves that every
partial source operation used by the original sweep was defined; Lean checks
that implication symbolically and never evaluates the production fold.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment

/-- Exact shared-memory trace emitted by the `audit` mode of
`bench/R2RuntimeProductionEmit.lean`. -/
def RuntimeProductionAuditReceipt : Prop :=
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
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
            (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).counterAugment.initialMCCWithMem
          0 mReceipt.mem)
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).rolledCompile =
      some mAudit ∧
    mAudit.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).output + 1⟩ =
      some 0

/-- Retained CompCert 3.17 execution of the fail-safe production audit.

The generated executable performed the root marking and table setup before
running the mechanically instrumented 221,163,768,000-step sweep.  Its exact
benchmark and hashes are recorded beside the positive production run in
`bench/results/manifests/r2star_runtime_production_emitter.json`. -/
axiom runtimeProductionAudit_compcert_run : RuntimeProductionAuditReceipt

private theorem productionAuditBaseOk :
    BaseOk runtimeProductionCfg.arrayLen 0 := by
  constructor <;> decide

/-- A retained zero audit receipt establishes an actual source execution of
the original sparse sweep.  The long fold is executed only by compiled code;
this theorem uses compiler simulation, determinism, and generic audit
soundness. -/
theorem runtimeProductionAudit_source_run
    (h : RuntimeProductionAuditReceipt) :
    ∃ marked packed out : AState,
      (r2RootMarkProgram runtimeProductionCfg).runFromArray (fun _ => 0) =
          some marked ∧
      (r2RootPackProgram runtimeProductionCfg).runFromArray marked.arr =
          some packed ∧
      packed.regs rpWrite = runtimePrimeCount ∧
      RootReceiptOK packed.arr ∧
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).runFromArray
          packed.arr = some out := by
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
  have hAuditReceipt : Option.bind
      (evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).counterAugment.initialMCCWithMem
            0 mReceipt.mem)
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).rolledCompile)
      (fun m : MCCState => m.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)).output + 1⟩) =
        some (0 : Int) := by
    rw [hAuditEval]
    exact hAuditZero
  obtain ⟨out, hSweepRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed)
      (r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed)
      0 productionAuditBaseOk packed.arr mReceipt.mem hCells hPackedWord
      (by decide) (by decide) hAuditReceipt
  exact ⟨marked, packed, out, hMarkRun, hPackRun, hCount, hReceiptOK,
    hSweepRun⟩

/-- Source-visible terminal words retained by the positive production run. -/
def RuntimeProductionSourceObservation (out : AState) : Prop :=
  out.regs outputReg = 0 ∧
  out.arr (runtimeProductionCfg.resultBase + 0) = 282485211074226 ∧
  out.arr (runtimeProductionCfg.resultBase + 1) = 1781404027878 ∧
  out.arr (runtimeProductionCfg.resultBase + 2) = 21000144997 ∧
  out.arr (runtimeProductionCfg.resultBase + 3) = 4802318405 ∧
  out.arr (runtimeProductionCfg.resultBase + 4) = 144914 ∧
  out.arr (runtimeProductionCfg.resultBase + 5) = 21000357225 ∧
  out.arr (runtimeProductionCfg.resultBase + 6) = 34 ∧
  out.arr (runtimeProductionCfg.resultBase + 7) = 34359738368 ∧
  out.arr (runtimeProductionCfg.resultBase + 8) = 398757432 ∧
  out.arr (runtimeProductionCfg.resultBase + 9) = 111525658352741 ∧
  ∀ slot, 10 ≤ slot → slot < 20 →
    out.arr (runtimeProductionCfg.resultBase + slot) = 0

/-- The fail-safe audit supplies source definedness; the retained positive run
then identifies the source output and all terminal result cells.  Both
executables use the same deterministic compiled setup, so no production fold
is replayed in Lean. -/
theorem runtimeProduction_source_observation
    (hAudit : RuntimeProductionAuditReceipt)
    (hProduction : RuntimeProductionReceipt) :
    ∃ packed out : AState,
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).runFromArray
          packed.arr = some out ∧
      packed = rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr ∧
      RootReceiptOK packed.arr ∧
      RuntimeProductionSourceObservation out := by
  rcases hProduction with
    ⟨mMark, mPack, mReceipt, mSweep, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero,
      hSweepEval, hSweepZero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      hTail⟩
  have hSetup : RootSetupReceipt :=
    ⟨mMark, mPack, mReceipt, hMarkEval, hMarkZero,
      hPackEval, hPackCount, hReceiptEval, hReceiptZero⟩
  rcases runtimeRootSetup_source_memory hSetup with
    ⟨marked, packed, mMark', mPack', mReceipt', hMarkRun, hPackRun, _hCount,
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
  rcases runtimeProductionAudit_source_run hAudit with
    ⟨markedA, packedA, out, hMarkRunA, hPackRunA, _hCountA,
      _hReceiptA, hSweepRunA⟩
  have hMarked : markedA = marked := by
    rw [hMarkRun] at hMarkRunA
    exact (Option.some.inj hMarkRunA).symm
  subst markedA
  have hPacked : packedA = packed := by
    rw [hPackRun] at hPackRunA
    exact (Option.some.inj hPackRunA).symm
  subst packedA
  have hMarkedExact := rootMarkProduction_runFromArray (fun _ => 0)
  rw [hMarkRun] at hMarkedExact
  have hMarkedSymbolic : marked =
      rootMarkedState runtimeProductionCfg (fun _ => 0) :=
    Option.some.inj hMarkedExact
  have hPackRunSymbolic :
      (r2RootPackProgram runtimeProductionCfg).runFromArray
          (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr =
        some packed := by
    rw [← hMarkedSymbolic]
    exact hPackRun
  have hPackedExact := rootPackProduction_runFromArray_exact
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
  rw [hPackRunSymbolic] at hPackedExact
  have hPackedSymbolic : packed =
      rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr :=
    Option.some.inj hPackedExact
  let sweep := r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed
  obtain ⟨outAug, hOutAug, hAgree⟩ :=
    sweep.counterAugment_runFromArray_of_runFromArray
      (r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed)
      packed.arr out hSweepRunA
  obtain ⟨mSweep', hSweepEval', hRel⟩ :=
    sweep.evalCC_rolledCompile_fromArray
      (r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed)
      0 productionAuditBaseOk packed.arr mReceipt.mem hCells
      (fun k _ => hPackedWord k)
      outAug hOutAug
  have hmSweep : mSweep' = mSweep := by
    change evalMCCSequence
        (sweep.counterAugment.initialMCCWithMem 0 mReceipt.mem)
        sweep.rolledCompile = some mSweep at hSweepEval
    rw [hSweepEval] at hSweepEval'
    exact (Option.some.inj hSweepEval').symm
  subst mSweep'
  have hOut : out.regs outputReg = 0 := by
    have hOutReg := hRel.hregs.1 outputReg (by decide)
    change mSweep.env ⟨outputReg + 1⟩ = some (outAug.regs outputReg : Int)
      at hOutReg
    have hSweepZero' : mSweep.env ⟨outputReg + 1⟩ = some 0 := by
      simpa only [r2RuntimeProgram] using hSweepZero
    rw [hSweepZero'] at hOutReg
    have hAugZero : outAug.regs outputReg = 0 := by
      exact_mod_cast Option.some.inj hOutReg.symm
    exact (hAgree.1 outputReg (by decide)).trans hAugZero
  have sourceCell (slot value : Nat) (hslot : slot < 20)
      (hm : mSweep.mem
        (cellAddr 0 (runtimeProductionCfg.resultBase + slot)) =
          some (value : Int)) :
      out.arr (runtimeProductionCfg.resultBase + slot) = value := by
    have hk : runtimeProductionCfg.resultBase + slot < sweep.arrayLen := by
      simp only [sweep, r2RuntimeProgram, R2Cfg.arrayLen]
      omega
    have hr := hRel.hcells (runtimeProductionCfg.resultBase + slot) hk
    rw [hm] at hr
    have hAug : outAug.arr (runtimeProductionCfg.resultBase + slot) = value := by
      exact_mod_cast (Option.some.inj hr).symm
    rw [hAgree.2]
    exact hAug
  refine ⟨packed, out, hSweepRunA, hPackedSymbolic, hReceiptOK, hOut,
    sourceCell 0 282485211074226 (by decide) h0,
    sourceCell 1 1781404027878 (by decide) h1,
    sourceCell 2 21000144997 (by decide) h2,
    sourceCell 3 4802318405 (by decide) h3,
    sourceCell 4 144914 (by decide) h4,
    sourceCell 5 21000357225 (by decide) h5,
    sourceCell 6 34 (by decide) h6,
    sourceCell 7 34359738368 (by decide) h7,
    sourceCell 8 398757432 (by decide) h8,
    sourceCell 9 111525658352741 (by decide) h9, ?_⟩
  intro slot hslotLo hslotHi
  exact sourceCell slot 0 hslotHi (hTail slot hslotLo hslotHi)

/-- The two retained compiled executions provide a source-level run and its
exact terminal observation.  This is a logical projection through the proved
compiler simulation; Lean does not replay either production sweep. -/
theorem runtimeProduction_verified_source_observation :
    ∃ packed out : AState,
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).runFromArray
          packed.arr = some out ∧
      packed = rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr ∧
      RootReceiptOK packed.arr ∧
      RuntimeProductionSourceObservation out :=
  runtimeProduction_source_observation runtimeProductionAudit_compcert_run
    runtimeProduction_compcert_run

#print axioms runtimeProductionAudit_source_run
#print axioms runtimeProduction_source_observation
#print axioms runtimeProduction_verified_source_observation

end LeanCompCert.Ports.R2SegSieve
