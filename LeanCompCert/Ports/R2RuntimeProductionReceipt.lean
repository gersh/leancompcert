import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Ports.R2RuntimeSetupReceipt

/-!
# Physical receipt for the complete compiled R2 production run

This leaf records the exact shared-memory trace exercised by
`bench/R2RuntimeProductionEmit.lean`.  All four folds execute in the
CompCert-produced binary.  The proposition deliberately exposes the final
result cells needed by the later source-level telescope; it contains no
emission-time Boolean and asks Lean to evaluate no production fold.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment

/-- Exact physical trace and final observation of the production executable.
The root marker, table packer, receipt checker, and 221,163,768,000-step sparse
sweep share one array, in the same order as the retained hosted driver. -/
def RuntimeProductionReceipt : Prop :=
  ∃ mMark mPack mReceipt mSweep : MCCState,
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
        ((r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).counterAugment.initialMCCWithMem
          0 mReceipt.mem)
        (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).rolledCompile =
      some mSweep ∧
    mSweep.env
        ⟨(r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).output + 1⟩ =
      some 0 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 0)) =
      some 282485211074226 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 1)) =
      some 1781404027878 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 2)) =
      some 21000144997 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 3)) =
      some 4802318405 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 4)) =
      some 144914 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 5)) =
      some 21000357225 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 6)) =
      some 34 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 7)) =
      some 34359738368 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 8)) =
      some 398757432 ∧
    mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 9)) =
      some 111525658352741 ∧
    ∀ slot, 10 ≤ slot → slot < 20 →
      mSweep.mem (cellAddr 0 (runtimeProductionCfg.resultBase + slot)) = some 0

/-- Retained CompCert 3.17 execution of the complete runtime pipeline. -/
axiom runtimeProduction_compcert_run : RuntimeProductionReceipt

/-- The physical observation directly exposes the zero violation result and
the exact terminal `prev` word.  This is a constant-time logical projection,
not a replay of the compiled sweep. -/
theorem runtimeProduction_zero_and_endpoint
    (h : RuntimeProductionReceipt) :
    ∃ m : MCCState,
      m.env
          ⟨(r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).output + 1⟩ =
        some 0 ∧
      m.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 2)) =
        some 21000144997 := by
  rcases h with
    ⟨_, _, _, m, _, _, _, _, _, _, _, hz, _, _, hprev, _⟩
  exact ⟨m, hz, hprev⟩

theorem runtimeProduction_verified_zero_and_endpoint :
    ∃ m : MCCState,
      m.env
          ⟨(r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).output + 1⟩ =
        some 0 ∧
      m.mem (cellAddr 0 (runtimeProductionCfg.resultBase + 2)) =
        some 21000144997 :=
  runtimeProduction_zero_and_endpoint runtimeProduction_compcert_run

#print axioms runtimeProduction_zero_and_endpoint
#print axioms runtimeProduction_verified_zero_and_endpoint

end LeanCompCert.Ports.R2SegSieve
