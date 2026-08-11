import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleBase

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Production specialization of the generic advance-premise constructor.
The caller supplies only the live whole-state facts: cursor agreement,
initialized table memory, round position, and the two counter invariants. -/
theorem productionAdvanceWordPre_of_cursorBounds
    (s : AState) (cur : PowerCursor)
    (hcur : machinePowerCursor s = cur)
    (hphase : s.regs 10 = 1)
    (hpast : s.regs 25 =
      if cur.j < productionCursorCfg.segLen then 0 else 1)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable cur)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hround : s.regs rR < productionCursorCfg.markSteps)
    (hviol : s.regs rViol ≤ s.regs rR)
    (hvmark : s.regs rVMark ≤ s.regs rR) :
    AdvanceWordPre productionCursorCfg s productionPowerTable := by
  rcases productionCursorStaticWordBounds with
    ⟨hhiPos, hhiWord, hhiSq, hK1, haddr, hjpow⟩
  have hseg : productionCursorCfg.segLen + 1 < M := by
    change 999900 + 1 < M
    decide
  exact AdvanceWordPre.of_cursorBounds productionCursorCfg s
    productionPowerTable cur hcur hphase hpast hbounds htable hhiPos
    hhiWord hhiSq hK1 haddr hjpow hseg
    productionCursorCfg_markSteps_lt_word hround hviol hvmark

/-- The complete compact production phase fold is bounded directly from the
source cell's divisor invariant and the symbolic coprimality proof for the
trial-prime table. -/
theorem productionCursorPhasesFold_bounds
    (w i : Nat) (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi) :
    PlaneCellProductionBounds
      (cursorPhasesFold productionCursorCfg.segLen w i
        productionPowerPhases emptyPlaneCell) := by
  have hpos : ∀ p ∈ productionCursorCfg.table, 0 < p := by
    intro p hp
    have hp2 : 2 ≤ p := by
      apply trialPrimesBelow_two_le _ p
      simpa [productionCursorCfg, Cfg.ofChain] using hp
    omega
  have hfold := cursorPhasesFold_tablePowerPhases
    productionCursorCfg.segLen w i productionCursorCfg.hi
    productionCursorCfg.table emptyPlaneCell hpos hi hnpos hnglobal
  have hrel := ofChain_cursorRows_refines
    10001 999900 100 100000000 w i hi
  have hcell := ofChain_markCell_productionBounds
    10001 999900 100 100000000 (w + i) hnpos (by
      simpa [productionCursorCfg, Cfg.hi, Cfg.ofChain] using hnglobal)
  have hbounds := hrel.productionBounds hcell
  rw [productionPowerPhases]
  rw [hfold]
  simpa [productionCursorCfg, Cfg.ofChain] using hbounds

/-- Once the final selected production cell is source-bounded, every compact
phase-prefix cell is source-bounded as well. -/
theorem productionPowerPhases_prefix_bounds
    (w i : Nat) (pre suf : List PowerPhase)
    (hphases : productionPowerPhases = pre ++ suf)
    (hfinal : PlaneCellProductionBounds
      (cursorPhasesFold productionCursorCfg.segLen w i
        productionPowerPhases emptyPlaneCell)) :
    PlaneCellProductionBounds
      (cursorPhasesFold productionCursorCfg.segLen w i pre emptyPlaneCell) := by
  have hbase : ∀ phase ∈ pre ++ suf, 1 ≤ phase.base := by
    intro phase hphase
    have hphase' : phase ∈ productionPowerPhases := by
      rw [hphases]
      exact hphase
    have := productionPowerPhases_base_two_le phase hphase'
    omega
  rw [hphases] at hfinal
  exact PlaneCellProductionBounds.cursorPhasesFold_prefix
    productionCursorCfg.segLen w i pre suf emptyPlaneCell
    hbase hfinal

/-- Fully discharged prefix form: every phase-prefix cell in every live
production window satisfies the compact machine word invariant. -/
theorem productionPowerPhases_prefix_bounds_closed
    (w i : Nat) (pre suf : List PowerPhase)
    (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hphases : productionPowerPhases = pre ++ suf) :
    PlaneCellProductionBounds
      (cursorPhasesFold productionCursorCfg.segLen w i pre emptyPlaneCell) :=
  productionPowerPhases_prefix_bounds w i pre suf hphases
    (productionCursorPhasesFold_bounds w i hi hnpos hnglobal)

/-- The exact cell-update premise at the start of every closed production
phase.  A selected cell is hit at most once inside one positive progression,
so this is the per-round premise needed by `Cfg.body_mark_powerCell_run`. -/
theorem productionPowerPhases_prefix_markPre
    (w i : Nat) (pre suf : List PowerPhase) (phase : PowerPhase)
    (hi : i < productionCursorCfg.segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hphases : productionPowerPhases = pre ++ phase :: suf) :
    PlaneCellMarkPre phase.pow phase.base
      (cursorPhasesFold productionCursorCfg.segLen w i pre emptyPlaneCell) := by
  have hphase : phase ∈ productionPowerPhases := by
    rw [hphases]
    simp
  exact planeCellMarkPre_of_production phase.pow phase.base
    (cursorPhasesFold productionCursorCfg.segLen w i pre emptyPlaneCell)
    (productionPowerPhases_prefix_bounds_closed w i pre (phase :: suf)
      hi hnpos hnglobal hphases)
    (productionPowerPhases_base_two_le phase hphase)
    (productionPowerPhases_base_le_10000 phase hphase)

/-- Production bounds can be read backwards across one selected-cell cursor
round whenever its base is positive. -/
theorem PlaneCellProductionBounds.of_powerCellStep
    (c : Cfg) (w i : Nat) (table : Nat → Nat) (st : PowerCellState)
    (hbase : 1 ≤ st.cursor.base)
    (hnext : PlaneCellProductionBounds
      (powerCellStep c w i table st).cell) :
    PlaneCellProductionBounds st.cell := by
  by_cases hmark : st.cursor.j < c.segLen ∧ st.cursor.j = i
  · rcases hmark with ⟨hj, hji⟩
    subst i
    simp only [powerCellStep, hj, true_and, if_true] at hnext
    exact PlaneCellProductionBounds.of_markPower hbase hnext
  · simpa [powerCellStep, hmark] using hnext

/-- A bounded final selected cell bounds the initial cell of every finite
symbolic selected-cell run. -/
theorem PlaneCellProductionBounds.of_powerCellRun
    (c : Cfg) (fuel w i : Nat) (table : Nat → Nat)
    (st : PowerCellState)
    (hcursor : PowerCursorBounds c.segLen c.hi c.tableLen table st.cursor)
    (hhi : 0 < c.hi)
    (hfinal : PlaneCellProductionBounds
      (powerCellRun c fuel w i table st).cell) :
    PlaneCellProductionBounds st.cell := by
  induction fuel with
  | zero => simpa using hfinal
  | succ fuel ih =>
      have hbounds := powerCellRun_cursor_bounds c fuel w i table st
        hcursor hhi
      have hprev := PlaneCellProductionBounds.of_powerCellStep c w i table
        (powerCellRun c fuel w i table st) hbounds.base_pos hfinal
      exact ih hprev

/-- Consequently, a bounded complete run bounds the selected cell at any
symbolic prefix. -/
theorem PlaneCellProductionBounds.powerCellRun_prefix
    (c : Cfg) (a b w i : Nat) (table : Nat → Nat)
    (st : PowerCellState)
    (hcursor : PowerCursorBounds c.segLen c.hi c.tableLen table st.cursor)
    (hhi : 0 < c.hi)
    (hfinal : PlaneCellProductionBounds
      (powerCellRun c (a + b) w i table st).cell) :
    PlaneCellProductionBounds (powerCellRun c a w i table st).cell := by
  rw [powerCellRun_add] at hfinal
  exact PlaneCellProductionBounds.of_powerCellRun c b w i table
    (powerCellRun c a w i table st)
    (powerCellRun_cursor_bounds c a w i table st hcursor hhi) hhi hfinal


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
