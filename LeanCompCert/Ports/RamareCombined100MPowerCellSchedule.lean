import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleStep

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Simultaneous invariant for every symbolic prefix of the emitted
production marking loop.  Specializing `fuel` to the production budget does
not reduce the millions of body iterations. -/
theorem productionMarkStateInv_run
    (k w i fuel : Nat) (initial : PowerCellState) (s : AState)
    (hi : i < productionCursorCfg.segLen) (hwM : w < M)
    (hfuel : fuel ≤ productionCursorCfg.markSteps)
    (hinitial : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable initial.cursor)
    (h0 : ProductionMarkStateInv w i 0 initial s)
    (hmark : ∀ round, round < fuel →
      let pure := powerCellRun productionCursorCfg round w i
        productionPowerTable initial
      pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
        PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell) :
    ProductionMarkStateInv w i fuel initial
      (emittedBodyRun k productionCursorCfg fuel s) := by
  induction fuel with
  | zero => simpa using h0
  | succ fuel ih =>
      have hprev := ih (by omega)
        (fun round hround => hmark round (by omega))
      have hnext := hprev.step k hi (by omega) hwM hinitial
        (hmark fuel (Nat.lt_succ_self fuel))
      simpa using hnext

/-- Closed production specialization: the compact phase-chain/source proof
discharges every per-round cell-update premise, including fixed-budget slack
after the sentinel. -/
theorem productionMarkStateInv_run_closed
    (k w i fuel : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen) (hwM : w < M)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hfuel : fuel ≤ productionCursorCfg.markSteps)
    (h0 : ProductionMarkStateInv w i 0
      (productionInitialPowerCell w) s) :
    ProductionMarkStateInv w i fuel (productionInitialPowerCell w)
      (emittedBodyRun k productionCursorCfg fuel s) := by
  exact productionMarkStateInv_run k w i fuel
    (productionInitialPowerCell w) s hi hwM hfuel
    (productionInitialPowerCell_cursor_bounds w) h0
    (fun round _hround =>
      productionPowerCellRun_markPre w i round hi hnpos hnglobal)

/-- A zero compiled marking-failure result proves that the final pure cursor
reached the prime-table sentinel.  The proof uses only the last emitted
round's exact failure bit; it does not normalize the production loop. -/
theorem ProductionMarkStateInv.cursor_exhausted_of_vmark_zero
    {w i : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i productionCursorCfg.markSteps initial s)
    (hzero : s.regs rVMark = 0) :
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps w i
      productionPowerTable initial).cursor.pi =
        productionCursorCfg.tableLen := by
  let pi := (powerCellRun productionCursorCfg
    productionCursorCfg.markSteps w i productionPowerTable initial).cursor.pi
  have hfailure := h.last_failure_le productionCursorCfg_markSteps_pos
  change productionCursorCfg.budgetFailure
    (productionCursorCfg.markSteps - 1) pi ≤ s.regs rVMark at hfailure
  by_cases heq : pi = productionCursorCfg.tableLen
  · simpa only [pi] using heq
  · have hone : productionCursorCfg.budgetFailure
        (productionCursorCfg.markSteps - 1) pi = 1 := by
      simp [Cfg.budgetFailure, eqBit, neBit, heq]
    rw [hone, hzero] at hfailure
    omega

/-- Closed production phase enumeration has the same selected-cell result as
the exact production table-row fold for every live window cell. -/
theorem productionPowerSchedule_cell_eq_cursorRows
    (w i : Nat) (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi) :
    let first := productionPowerPhases.headD ⟨0, 1, 1⟩
    let st : PowerScheduleState :=
      ⟨⟨first.pi, first.pow, first.base, startOffset w first.pow⟩,
        emptyPlaneCell⟩
    (powerScheduleRun
        (powerPhaseChainFuel productionCursorCfg.segLen w
          productionPowerPhases)
        productionCursorCfg.segLen w productionCursorCfg.hi
        productionCursorCfg.tableLen i productionPowerTable st).cell =
      cursorRowsFold productionCursorCfg.segLen w i
        (factorRows productionCursorCfg.table) emptyPlaneCell := by
  have hnonempty : productionPowerPhases ≠ [] := productionPowerPhases_nonempty
  cases hphases : productionPowerPhases with
  | nil => exact (hnonempty hphases).elim
  | cons phase phases =>
    let st : PowerScheduleState :=
      ⟨⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩,
        emptyPlaneCell⟩
    have hrun := powerScheduleRun_phase_chain_cell
      productionCursorCfg.segLen w productionCursorCfg.hi
      productionCursorCfg.tableLen i productionPowerTable st
      productionPowerPhases productionPowerPhaseChain
      ⟨phase, phases, hphases, rfl⟩
    have hpos : ∀ p ∈ productionCursorCfg.table, 0 < p := by
      intro p hp
      have hp2 : 2 ≤ p := by
        apply trialPrimesBelow_two_le _ p
        simpa [productionCursorCfg, Cfg.ofChain] using hp
      omega
    have hfold := cursorPhasesFold_tablePowerPhases
      productionCursorCfg.segLen w i productionCursorCfg.hi
      productionCursorCfg.table emptyPlaneCell hpos hi hnpos hnglobal
    simpa [hphases, st] using hrun.trans hfold

/-- Reaching the sentinel at any symbolic production fuel is enough to
identify the selected cell with the complete source table-row fold. -/
theorem productionPowerCellRun_cell_eq_cursorRows_of_exhausted
    (fuel w i : Nat) (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hpi : (powerCellRun productionCursorCfg fuel w i productionPowerTable
      (productionInitialPowerCell w)).cursor.pi =
        productionCursorCfg.tableLen) :
    (powerCellRun productionCursorCfg fuel w i productionPowerTable
      (productionInitialPowerCell w)).cell =
        cursorRowsFold productionCursorCfg.segLen w i
          (factorRows productionCursorCfg.table) emptyPlaneCell := by
  have hcomplete := productionPowerCellRun_eq_phase_of_cursor_exhausted
    fuel w i hpi
  rw [hcomplete]
  have hbridge := powerCellRun_cell_eq_powerScheduleRun productionCursorCfg
    (powerPhaseChainFuel productionCursorCfg.segLen w productionPowerPhases)
    w i productionPowerTable (productionInitialPowerCell w)
  rw [hbridge]
  simpa [productionInitialPowerCell] using
    productionPowerSchedule_cell_eq_cursorRows w i hi hnpos hnglobal

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
