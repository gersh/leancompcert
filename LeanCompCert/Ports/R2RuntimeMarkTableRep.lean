import LeanCompCert.Ports.R2RuntimeMarkCursorBounds
import LeanCompCert.Ports.R2SegMarkingWindowModel
import LeanCompCert.Ports.R2RuntimePackLiveZero
import LeanCompCert.Ports.R2SegMarkingInit
import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Ports.R2SegMarkingWindowLiteral

/-! # Physical representation of the retained production marking table -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- Every actual packed row loaded by the sweep is a machine word. -/
theorem runtimeProduction_table_words_lt (i : Nat)
    (_hi : i ≤ runtimeProductionCfg.tableLen) :
    runtimeProductionTableWord i < M := by
  exact runtimeRootSetup_verified_packed_words
    (runtimeProductionCfg.tableBase + i)

/-- The caller-owned root-setup array represents the same abstract packed
table used by the pure cursor model. -/
theorem runtimeProductionPacked_table_rep :
    R2MarkTableRep runtimeProductionCfg runtimeProductionTableWord
      (rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr) := by
  intro i _hi
  simp [runtimeProductionTableWord, Nat.add_comm]

/-- Exact caller-owned array handed from the compiled setup to the sweep. -/
def runtimeSweepPackedState : AState :=
  rootPackedState runtimeProductionCfg
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr

/-- Exact source entry after the compact register-only seed block. -/
def runtimeSweepEntry : AState :=
  arun 0 (initialAStateWithArray runtimeSweepPackedState.arr)
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init

/-- State after the first marking prelude has installed row zero. -/
def runtimeSweepFirstPrelude : AState :=
  arun 0 runtimeSweepEntry (markPreludeBody runtimeProductionCfg)

def runtimeFirstWindow : R2MarkWindow :=
  { cursor := runtimeWindowInitialCursor runtimeProductionCfg.lo
    cells := fun _ => emptyMarkCell }

/-- Register seeding cannot modify the caller-owned table or live planes. -/
theorem runtimeSeedRegs_arr (k : Nat) (s : AState)
    (l : List (Nat × Nat)) :
    (arun k s (LeanCompCert.Ports.PsiSegSieve.seedRegs l)).arr = s.arr := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [LeanCompCert.Ports.PsiSegSieve.seedRegs, List.map_cons, arun]
      exact ih _

theorem runtimeSweepEntry_arr : runtimeSweepEntry.arr = runtimeSweepPackedState.arr := by
  exact runtimeSeedRegs_arr 0 _ _

theorem runtimeSweepEntry_table_rep :
    R2MarkTableRep runtimeProductionCfg runtimeProductionTableWord
      runtimeSweepEntry := by
  intro i hi
  rw [runtimeSweepEntry_arr]
  exact runtimeProductionPacked_table_rep i hi

/-- Before the first reset, the caller-owned live planes already represent
the empty logical window.  This is deliberately a structural theorem about
the retained setup array, rather than an evaluation of the production
marking schedule. -/
theorem runtimeSweepEntry_cells_rep :
    runtimeFirstWindow.CellsRep runtimeProductionCfg runtimeSweepEntry := by
  intro i hi
  unfold planeWordsAt
  rw [runtimeSweepEntry_arr]
  have h0 := rootProductionPackedState_live_zero i (by
    simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
    omega)
  have h1 := rootProductionPackedState_live_zero
    (i + runtimeProductionCfg.segLen) (by
      simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
      omega)
  have h2 := rootProductionPackedState_live_zero
    (i + 2 * runtimeProductionCfg.segLen) (by
      simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
      omega)
  change runtimeSweepPackedState.arr i = 0 at h0
  change runtimeSweepPackedState.arr
    (i + runtimeProductionCfg.segLen) = 0 at h1
  change runtimeSweepPackedState.arr
    (i + 2 * runtimeProductionCfg.segLen) = 0 at h2
  simp [runtimeFirstWindow, emptyMarkCell, MarkCell.encode, packWeights,
    h0, h1, h2]

theorem runtimeSweepEntry_failure_regs :
    runtimeSweepEntry.regs rViol = 0 ∧
      runtimeSweepEntry.regs rVMark = 0 := by
  constructor <;> rfl

/-- The first literal reset prelude represents the pure empty window with the
same verified table.  No production schedule is evaluated in this theorem. -/
theorem runtimeSweepFirstPrelude_rep :
    (runtimeFirstWindow.Rep runtimeProductionCfg runtimeSweepFirstPrelude) ∧
      R2MarkTableRep runtimeProductionCfg runtimeProductionTableWord
        runtimeSweepFirstPrelude := by
  have hpos := seedList_mark_position_run runtimeProductionCfg
    runtimeProductionSeed
    (initialAStateWithArray runtimeSweepPackedState.arr) rfl (by decide)
  change runtimeSweepEntry.regs rR = 0 ∧
    runtimeSweepEntry.regs rW = runtimeProductionCfg.lo at hpos
  have hp := markPreludeBody_start_run runtimeProductionCfg 0 runtimeSweepEntry
    runtimeProductionCfg.lo hpos.1 hpos.2 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  dsimp only at hp
  rcases hp with
    ⟨_h8, _h14, _h9, _h15, hpi, hq, hbp, hwt, hfs, hj,
      _hr, _hw, harr⟩
  change runtimeSweepFirstPrelude.regs rPi = 0 at hpi
  change runtimeSweepFirstPrelude.regs rQ = runtimeProductionCfg.q0 at hq
  change runtimeSweepFirstPrelude.regs rBp = runtimeProductionCfg.q0 at hbp
  change runtimeSweepFirstPrelude.regs rWt = runtimeProductionCfg.w0 at hwt
  change runtimeSweepFirstPrelude.regs rFs = 1 at hfs
  change runtimeSweepFirstPrelude.regs rJ =
    resetOffset runtimeProductionCfg.q0 runtimeProductionCfg.lo at hj
  change runtimeSweepFirstPrelude.arr = runtimeSweepEntry.arr at harr
  constructor
  · constructor
    · apply R2MarkCursor.ext
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hpi
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hq
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hbp
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hwt
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hfs
      · simpa [R2MarkCursor.ofState, runtimeFirstWindow,
          runtimeWindowInitialCursor] using hj
    · intro i hi
      unfold planeWordsAt
      rw [harr, runtimeSweepEntry_arr]
      have h0 := rootProductionPackedState_live_zero i (by
        simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
        omega)
      have h1 := rootProductionPackedState_live_zero
        (i + runtimeProductionCfg.segLen) (by
          simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
          omega)
      have h2 := rootProductionPackedState_live_zero
        (i + 2 * runtimeProductionCfg.segLen) (by
          simp only [runtimeProductionCfg, R2Cfg.tableBase] at hi ⊢
          omega)
      change runtimeSweepPackedState.arr i = 0 at h0
      change runtimeSweepPackedState.arr
        (i + runtimeProductionCfg.segLen) = 0 at h1
      change runtimeSweepPackedState.arr
        (i + 2 * runtimeProductionCfg.segLen) = 0 at h2
      simp [runtimeFirstWindow, emptyMarkCell, MarkCell.encode, packWeights,
        h0, h1, h2]
  · intro i hi
    rw [harr]
    exact runtimeSweepEntry_table_rep i hi

#print axioms runtimeProduction_table_words_lt
#print axioms runtimeProductionPacked_table_rep
#print axioms runtimeSeedRegs_arr
#print axioms runtimeSweepEntry_arr
#print axioms runtimeSweepEntry_table_rep
#print axioms runtimeSweepEntry_cells_rep
#print axioms runtimeSweepEntry_failure_regs
#print axioms runtimeSweepFirstPrelude_rep

end LeanCompCert.Ports.R2SegSieve
