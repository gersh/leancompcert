import LeanCompCert.Ports.RamareCombined100MPowerCellSchedulePrefixBoundsA

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Selected-cell initial state of the closed production cursor. -/
def productionInitialPowerCell (w : Nat) : PowerCellState :=
  let first := productionPowerPhases.headD ⟨0, 1, 1⟩
  ⟨⟨first.pi, first.pow, first.base, startOffset w first.pow⟩,
    emptyPlaneCell⟩

theorem productionInitialPowerCell_cursor_bounds (w : Nat) :
    PowerCursorBounds productionCursorCfg.segLen productionCursorCfg.hi
      productionCursorCfg.tableLen productionPowerTable
      (productionInitialPowerCell w).cursor := by
  cases hphases : productionPowerPhases with
  | nil => exact (productionPowerPhases_nonempty hphases).elim
  | cons phase phases =>
      have hphase : phase ∈ productionPowerPhases := by
        rw [hphases]
        simp
      simpa [productionInitialPowerCell, hphases] using
        productionPowerPhase_cursor_bounds w phase hphase

theorem productionInitialPowerCell_base_le_10000 (w : Nat) :
    (productionInitialPowerCell w).cursor.base ≤ 10000 := by
  cases hphases : productionPowerPhases with
  | nil => exact (productionPowerPhases_nonempty hphases).elim
  | cons phase phases =>
      have hphase : phase ∈ productionPowerPhases := by
        rw [hphases]
        simp
      simpa [productionInitialPowerCell, hphases] using
        productionPowerPhases_base_le_10000 phase hphase

/-- The production initial cursor cannot already carry the sentinel table
index, so sentinel-shape uniqueness holds vacuously at round zero. -/
theorem productionInitialPowerCell_terminal_shape (w : Nat) :
    (productionInitialPowerCell w).cursor.pi = productionCursorCfg.tableLen →
      (productionInitialPowerCell w).cursor =
        { pi := productionCursorCfg.tableLen, pow := 1, base := 1,
          j := productionCursorCfg.segLen + 1 } := by
  cases hphases : productionPowerPhases with
  | nil => exact (productionPowerPhases_nonempty hphases).elim
  | cons phase phases =>
      intro hpi
      have hphase : phase ∈ productionPowerPhases := by
        rw [hphases]
        simp
      have hlt := tablePowerPhases_pi_lt hphase
      change phase.pi < productionCursorCfg.tableLen at hlt
      have hhead : (productionInitialPowerCell w).cursor.pi = phase.pi := by
        simp [productionInitialPowerCell, hphases]
      have hpi' : phase.pi = productionCursorCfg.tableLen := hhead.symm.trans hpi
      omega

/-- The selected cell at the exact compact-chain endpoint has the closed
source production bounds. -/
theorem productionPowerCellRun_phase_bounds
    (w i : Nat) (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi) :
    PlaneCellProductionBounds
      (powerCellRun productionCursorCfg
        (powerPhaseChainFuel productionCursorCfg.segLen w
          productionPowerPhases)
        w i productionPowerTable (productionInitialPowerCell w)).cell := by
  cases hphases : productionPowerPhases with
  | nil => exact (productionPowerPhases_nonempty hphases).elim
  | cons phase phases =>
      let st : PowerScheduleState :=
        ⟨⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩,
          emptyPlaneCell⟩
      have hrun := powerScheduleRun_phase_chain_cell
        productionCursorCfg.segLen w productionCursorCfg.hi
        productionCursorCfg.tableLen i productionPowerTable st
        productionPowerPhases productionPowerPhaseChain
        ⟨phase, phases, hphases, rfl⟩
      have hbridge := powerCellRun_cell_eq_powerScheduleRun
        productionCursorCfg
        (powerPhaseChainFuel productionCursorCfg.segLen w
          productionPowerPhases)
        w i productionPowerTable (productionInitialPowerCell w)
      have hfinal := productionCursorPhasesFold_bounds w i hi hnpos hnglobal
      have hbounded : PlaneCellProductionBounds
          (powerScheduleRun
            (powerPhaseChainFuel productionCursorCfg.segLen w
              productionPowerPhases)
            productionCursorCfg.segLen w productionCursorCfg.hi
            productionCursorCfg.tableLen i productionPowerTable st).cell := by
        rw [hrun]
        simpa [st] using hfinal
      rw [← hphases]
      rw [hbridge]
      simpa [productionInitialPowerCell, hphases, st] using hbounded

/-- The exact compact-chain endpoint is the explicit fixed-point sentinel. -/
theorem productionPowerCellRun_phase_terminal
    (w i : Nat) :
    (powerCellRun productionCursorCfg
      (powerPhaseChainFuel productionCursorCfg.segLen w
        productionPowerPhases)
      w i productionPowerTable (productionInitialPowerCell w)).cursor =
        { pi := productionCursorCfg.tableLen, pow := 1, base := 1,
          j := productionCursorCfg.segLen + 1 } := by
  cases hphases : productionPowerPhases with
  | nil => exact (productionPowerPhases_nonempty hphases).elim
  | cons phase phases =>
      let st : PowerScheduleState :=
        ⟨⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩,
          emptyPlaneCell⟩
      let fuel := powerPhaseChainFuel productionCursorCfg.segLen w
        productionPowerPhases
      have htrace := tracedPowerScheduleRun_phase_chain
        productionCursorCfg.segLen w productionCursorCfg.hi
        productionCursorCfg.tableLen i productionPowerTable st
        productionPowerPhases productionPowerPhaseChain
        ⟨phase, phases, hphases, rfl⟩
      have hstate := tracedPowerScheduleRun_state fuel
        productionCursorCfg.segLen w productionCursorCfg.hi
        productionCursorCfg.tableLen i productionPowerTable st
      have hsched :
          (powerScheduleRun fuel productionCursorCfg.segLen w
            productionCursorCfg.hi productionCursorCfg.tableLen i
            productionPowerTable st).cursor =
            { pi := productionCursorCfg.tableLen,
              pow := productionPowerTable productionCursorCfg.tableLen,
              base := productionPowerTable productionCursorCfg.tableLen,
              j := productionCursorCfg.segLen + 1 } := by
        rw [← hstate]
        exact htrace.2
      rw [← hphases]
      rw [powerCellRun_cursor_eq_powerScheduleRun]
      simpa [productionInitialPowerCell, hphases, st, fuel,
        productionPowerTable_sentinel] using hsched

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
