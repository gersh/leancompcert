import LeanCompCert.Ports.R2RuntimePackTableSemantics

/-!
# Empty live planes after the compiled root-table setup

The root marker temporarily uses the beginning of the runtime array and the
root packer subsequently clears every candidate cell.  This file proves that
the entire live-sieve region is zero when the packed table is handed to the
main sweep.  Both large loops are treated by symbolic induction; no
production-sized fold is evaluated by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

set_option maxRecDepth 4096

/-- Outside the bounded candidate interval, the root marker leaves a
zero-initialized array cell equal to zero. -/
theorem rootMarkFoldPrefix_outside_zero (c : R2Cfg) (k x : Nat)
    (hArray : c.arrayLen < M) (hRoot : runtimeRoot < c.arrayLen)
    (hk : k ≤ (r2RootMarkProgram c).loopCount)
    (hx : x < 2 ∨ runtimeRoot < x) :
    (rootMarkFoldPrefix c (fun _ => 0) k).arr x = 0 := by
  induction k with
  | zero => simp [rootMarkFoldPrefix, initialAStateWithArray]
  | succ k ih =>
      have hklt : k < (r2RootMarkProgram c).loopCount := by
        omega
      have hkpre : k ≤ (r2RootMarkProgram c).loopCount := by
        omega
      let prev := rootMarkFoldPrefix c (fun _ => 0) k
      have hprev : prev.arr x = 0 := ih hkpre
      have hstep := (rootMarkBody_spec c k prev hArray hRoot hklt).2 x
      have hn := (rootMark_index_bounds (by
        simpa [r2RootMarkProgram, rootMarkWidth, runtimeDivCap] using hklt)).2.1
      have hxne : x ≠ rootMarkN k := by
        rcases hx with hxlo | hxhi
        · have hn2 : 2 ≤ rootMarkN k := by simp [rootMarkN]
          omega
        · omega
      have hfold :
          rootMarkFoldPrefix c (fun _ => 0) (k + 1) =
            arun k prev (rootMarkBody c) := by
        simp [rootMarkFoldPrefix, prev, List.range_succ, List.foldl_append]
      rw [hfold, hstep]
      by_cases hhit : rootMarkHit k = 1
      · simp [hhit, hxne, hprev]
      · have hhit0 : rootMarkHit k = 0 := by
          have hcases : rootMarkHit k = 0 ∨ rootMarkHit k = 1 := by
            unfold rootMarkHit
            split <;> simp
          rcases hcases with hz | ho
          · exact hz
          · exact False.elim (hhit ho)
        simp [hhit0, hprev]

/-- The marker epilogue changes only a register, so the outside-cell theorem
also holds for the named compiled marker result. -/
theorem rootMarkedState_arr (c : R2Cfg) (arr : Nat → Nat) (x : Nat) :
    (rootMarkedState c arr).arr x = (rootMarkFold c arr).arr x := by
  change (arun 0 (rootMarkFold c arr)
    (r2RootMarkProgram c).epilogue).arr x = _
  exact congrFun
    (LeanCompCert.Verified.ArrayScalarBlock.arun_scalarOnly_arr 0
      (r2RootMarkProgram c).epilogue (rootMarkFold c arr) (by
        simp [r2RootMarkProgram,
          LeanCompCert.Verified.ArrayScalarBlock.ScalarOnly])) x

theorem rootMarkedState_outside_zero_core (c : R2Cfg) (x : Nat)
    (hArray : c.arrayLen < M) (hRoot : runtimeRoot < c.arrayLen)
    (hx : x < 2 ∨ runtimeRoot < x) :
    (rootMarkedState c (fun _ => 0)).arr x = 0 := by
  rw [rootMarkedState_arr, rootMarkFold_eq_prefix]
  exact rootMarkFoldPrefix_outside_zero c
    (r2RootMarkProgram c).loopCount x hArray hRoot (Nat.le_refl _) hx

theorem rootMarkedState_outside_zero (x : Nat)
    (hx : x < 2 ∨ runtimeRoot < x) :
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x = 0 := by
  exact rootMarkedState_outside_zero_core runtimeProductionCfg x
    (by decide) (by decide) hx

/-- A packer round frames cells below the table that lie outside the bounded
candidate interval. -/
theorem rootPackModelStep_outside_table_frame (c : R2Cfg) (index x : Nat)
    (m : RootPackModel)
    (hi : index < (r2RootPackProgram c).loopCount)
    (hx : x < 2 ∨ runtimeRoot < x)
    (hsink : c.tableBase < c.streamSink)
    (htable : x < c.tableBase) :
    (rootPackModelStep c index m).arr x = m.arr x := by
  have hn := (rootPack_index_bounds (by
    simpa [r2RootPackProgram] using hi)).2.1
  have hxCandidate : x ≠ rootPackN index := by
    rcases hx with hxlo | hxhi
    · have hn2 : 2 ≤ rootPackN index := by simp [rootPackN]
      omega
    · omega
  have hxSink : x ≠ c.streamSink := by omega
  have hxTable : x ≠ m.write + c.tableBase := by omega
  by_cases hfinish : rootPackFinish index = 1
  · have hclear : rootPackClearTargetSpec c index =
        rootPackN index := by simp [rootPackClearTargetSpec, hfinish]
    by_cases hhit : rootPackHit index m = 1
    · have hstore : rootPackStoreTargetSpec c index m =
          m.write + c.tableBase := by
        simp [rootPackStoreTargetSpec, hhit]
      simp [rootPackModelStep, hclear, hstore, hxCandidate, hxTable]
    · have hstore : rootPackStoreTargetSpec c index m = c.streamSink := by
        simp [rootPackStoreTargetSpec, hhit]
      simp [rootPackModelStep, hclear, hstore, hxCandidate, hxSink]
  · have hclear : rootPackClearTargetSpec c index = c.streamSink := by
      simp [rootPackClearTargetSpec, hfinish]
    have hfinish0 : rootPackFinish index = 0 := by
      have hcases : rootPackFinish index = 0 ∨ rootPackFinish index = 1 := by
        unfold rootPackFinish
        split <;> simp
      rcases hcases with hz | ho
      · exact hz
      · exact False.elim (hfinish ho)
    have hhit : rootPackHit index m = 0 := by
      simp [rootPackHit, hfinish0]
    have hstore : rootPackStoreTargetSpec c index m = c.streamSink := by
      simp [rootPackStoreTargetSpec, hhit]
    simp [rootPackModelStep, hclear, hstore, hxSink]

/-- Symbolic iteration of the preceding frame theorem. -/
theorem rootPackModelFold_outside_table_frame (c : R2Cfg)
    (arr : Nat → Nat) (k x : Nat)
    (hk : k ≤ (r2RootPackProgram c).loopCount)
    (hx : x < 2 ∨ runtimeRoot < x)
    (hsink : c.tableBase < c.streamSink)
    (htable : x < c.tableBase) :
    (rootPackModelFold c (rootPackInitialModel arr) k).arr x =
      arr x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rootPackModelFold_succ]
      rw [rootPackModelStep_outside_table_frame c k x _ (by omega) hx
        hsink htable]
      exact ih (by omega)

/-- The machine loop has the same outside-cell frame as its source model. -/
theorem rootPackLoopState_outside_table_frame_core (c : R2Cfg)
    (arr : Nat → Nat) (x : Nat)
    (hx : x < 2 ∨ runtimeRoot < x)
    (hsink : c.tableBase < c.streamSink)
    (htable : x < c.tableBase)
    (hsafe : ∀ i, i < (r2RootPackProgram c).loopCount →
      RootPackStepSafe c i
        (rootPackModelFold c (rootPackInitialModel arr) i)) :
    (rootPackLoopState c arr).arr x = arr x := by
  have hobs := rootPackFold_observe c
    (rootPackStartedState arr)
    (r2RootPackProgram c).loopCount
    (fun i hi => by
      rw [rootPackStartedState, rootPackInit_observe]
      exact hsafe i hi)
  have hstart : rootPackObserve (rootPackStartedState arr) =
      rootPackInitialModel arr := rootPackInit_observe arr
  have hmodel := rootPackModelFold_outside_table_frame c arr
    (r2RootPackProgram c).loopCount x (Nat.le_refl _) hx hsink htable
  have hstartFold :
      rootPackModelFold c (rootPackObserve (rootPackStartedState arr))
          (r2RootPackProgram c).loopCount =
        rootPackModelFold c (rootPackInitialModel arr)
          (r2RootPackProgram c).loopCount := by
    rw [hstart]
  have hobs' : rootPackObserve
      (rootPackLoopState c arr) =
      rootPackModelFold c (rootPackInitialModel arr)
        (r2RootPackProgram c).loopCount := by
    rw [rootPackLoopState]
    exact hobs.trans hstartFold
  calc
    (rootPackLoopState c arr).arr x =
        (rootPackObserve (rootPackLoopState c arr)).arr x := by
          rw [rootPackObserve_arr]
    _ = (rootPackModelFold c (rootPackInitialModel arr)
          (r2RootPackProgram c).loopCount).arr x :=
      congrArg (fun m => m.arr x) hobs'
    _ = arr x := hmodel

theorem rootPackLoopState_outside_table_frame (arr : Nat → Nat) (x : Nat)
    (hx : x < 2 ∨ runtimeRoot < x)
    (htable : x < runtimeProductionCfg.tableBase) :
    (rootPackLoopState runtimeProductionCfg arr).arr x = arr x := by
  exact rootPackLoopState_outside_table_frame_core runtimeProductionCfg arr x hx
    (by decide) htable (rootPackProductionModelFold_safe arr)

/-- The complete compiled root setup leaves all five live runtime planes
empty.  The table begins immediately after these cells. -/
theorem rootProductionPackedState_live_zero (x : Nat)
    (hx : x < runtimeProductionCfg.tableBase) :
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x = 0 := by
  have hcount :
      (rootPackLoopState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).regs rpWrite =
      rootPackCount
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
        (runtimeRoot - 1) :=
    rootPackLoopState_write_count _
  have hwrite :
      (rootPackLoopState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).regs rpWrite +
          runtimeProductionCfg.tableBase < M := by
    rw [hcount]
    have hc := rootPackCount_le
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
      (runtimeRoot - 1)
    have hlayout : runtimeRoot + runtimeProductionCfg.tableBase < M := by decide
    omega
  have hne : x ≠
      (rootPackLoopState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).regs rpWrite +
          runtimeProductionCfg.tableBase := by omega
  have hpacked := congrArg (fun s => s.arr x)
    (rootPackedState_eq_loop_epilogue runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr)
  have hepilogue := rootPackEpilogue_arr_of_ne
    (rootPackLoopState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr)
    x hwrite hne
  have htoLoop :
      (rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x =
      (rootPackLoopState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x :=
    hpacked.trans hepilogue
  calc
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x =
      (rootPackLoopState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x := htoLoop
    _ = 0 := by
      by_cases hmiddle : 2 ≤ x ∧ x ≤ runtimeRoot
      · have hinv := rootPackLoopState_tableInvariant
          (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
        have hzero := hinv.processedZero x hmiddle.1 (by
          rw [rootPackProduction_final_candidate]
          omega)
        calc
          (rootPackLoopState runtimeProductionCfg
              (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x =
              (rootPackObserve (rootPackLoopState runtimeProductionCfg
                (rootMarkedState runtimeProductionCfg
                  (fun _ => 0)).arr)).arr x := by
            rw [rootPackObserve_arr]
          _ = 0 := hzero
      · have houtside : x < 2 ∨ runtimeRoot < x := by omega
        calc
          (rootPackLoopState runtimeProductionCfg
              (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x =
              (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x :=
            rootPackLoopState_outside_table_frame _ x houtside hx
          _ = 0 := rootMarkedState_outside_zero x houtside

#print axioms rootMarkFoldPrefix_outside_zero
#print axioms rootMarkedState_outside_zero
#print axioms rootPackModelFold_outside_table_frame
#print axioms rootPackLoopState_outside_table_frame
#print axioms rootProductionPackedState_live_zero

end LeanCompCert.Ports.R2SegSieve
