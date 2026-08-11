import LeanCompCert.Ports.RamareCombined100MProductionPhases

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

def cursorPhasesFold (segLen w i : Nat) (phases : List PowerPhase)
    (x : PlaneCell) : PlaneCell :=
  phases.foldl
    (fun q phase => cursorPowerFold segLen w i phase.pow phase.base q) x

/-- A bounded final cell bounds the cell at the start of every positive-base
phase list.  The proof runs backwards over the compact phase descriptors,
not over the millions of cursor rounds they denote. -/
theorem PlaneCellProductionBounds.of_cursorPhasesFold
    (segLen w i : Nat) (phases : List PowerPhase) (x : PlaneCell)
    (hbase : ∀ phase ∈ phases, 1 ≤ phase.base)
    (hfinal : PlaneCellProductionBounds
      (cursorPhasesFold segLen w i phases x)) :
    PlaneCellProductionBounds x := by
  induction phases generalizing x with
  | nil => simpa [cursorPhasesFold] using hfinal
  | cons phase phases ih =>
      simp only [cursorPhasesFold, List.foldl_cons] at hfinal
      have htail := ih
        (cursorPowerFold segLen w i phase.pow phase.base x)
        (fun q hq => hbase q (by simp [hq])) hfinal
      exact PlaneCellProductionBounds.of_cursorPowerFold
        segLen w i phase.pow phase.base x
        (hbase phase (by simp)) htail

/-- Every phase-prefix state is bounded whenever the closed full phase fold is
bounded.  This is the form consumed by the emitted-loop induction. -/
theorem PlaneCellProductionBounds.cursorPhasesFold_prefix
    (segLen w i : Nat) (pre suf : List PowerPhase) (x : PlaneCell)
    (hbase : ∀ phase ∈ pre ++ suf, 1 ≤ phase.base)
    (hfinal : PlaneCellProductionBounds
      (cursorPhasesFold segLen w i (pre ++ suf) x)) :
    PlaneCellProductionBounds (cursorPhasesFold segLen w i pre x) := by
  have hsuffix : PlaneCellProductionBounds
      (cursorPhasesFold segLen w i suf
        (cursorPhasesFold segLen w i pre x)) := by
    simpa [cursorPhasesFold, List.foldl_append] using hfinal
  exact PlaneCellProductionBounds.of_cursorPhasesFold
    segLen w i suf (cursorPhasesFold segLen w i pre x)
    (fun phase hphase => hbase phase (by simp [hphase])) hsuffix

theorem powerEventCellFold_powerPhaseEvents
    (segLen w i : Nat) (phase : PowerPhase) (x : PlaneCell) :
    powerEventCellFold i (powerPhaseEvents segLen w phase) x =
      cursorPowerFold segLen w i phase.pow phase.base x := by
  unfold powerPhaseEvents cursorPowerFold powerCursorEvents cursorLiveEvents
    powerEventCellFold planeEventCellFold
  generalize (List.range
    (liveCount segLen (startOffset w phase.pow) phase.pow)) = events
  induction events generalizing x with
  | nil => rfl
  | cons event events ih => simp [ih]

/-- Flattening phase event lists and then applying them is the same as
folding the corresponding cursor blocks phase by phase. -/
theorem powerEventCellFold_powerPhaseChainEvents
    (segLen w i : Nat) (phases : List PowerPhase) (x : PlaneCell) :
    powerEventCellFold i (powerPhaseChainEvents segLen w phases) x =
      cursorPhasesFold segLen w i phases x := by
  induction phases generalizing x with
  | nil => rfl
  | cons phase phases ih =>
      simp only [powerPhaseChainEvents, powerEventCellFold,
        List.foldl_append, cursorPhasesFold, List.foldl_cons]
      rw [show (powerPhaseEvents segLen w phase).foldl
            (fun q event =>
              if event.1 = i then q.markPower event.2.1 event.2.2 else q) x =
          cursorPowerFold segLen w i phase.pow phase.base x by
        exact powerEventCellFold_powerPhaseEvents segLen w i phase x]
      exact ih _

/-- A valid finite phase chain has exactly the selected-cell effect of its
phase descriptor fold. -/
theorem powerScheduleRun_phase_chain_cell
    (segLen w hi limit i : Nat) (table : Nat → Nat)
    (st : PowerScheduleState) (phases : List PowerPhase)
    (hchain : PowerPhaseChain hi limit table phases)
    (hcursor :
      ∃ phase rest, phases = phase :: rest ∧
        st.cursor =
          ⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩) :
    (powerScheduleRun (powerPhaseChainFuel segLen w phases)
        segLen w hi limit i table st).cell =
      cursorPhasesFold segLen w i phases st.cell := by
  let traced := tracedPowerScheduleRun
    (powerPhaseChainFuel segLen w phases)
    segLen w hi limit i table st
  have htrace := tracedPowerScheduleRun_phase_chain
    segLen w hi limit i table st phases hchain hcursor
  dsimp only at htrace
  calc
    (powerScheduleRun (powerPhaseChainFuel segLen w phases)
        segLen w hi limit i table st).cell = traced.state.cell := by
      exact congrArg PowerScheduleState.cell
        (tracedPowerScheduleRun_state
          (powerPhaseChainFuel segLen w phases)
          segLen w hi limit i table st).symm
    _ = powerEventCellFold i traced.events st.cell := by
      exact tracedPowerScheduleRun_cell
        (powerPhaseChainFuel segLen w phases)
        segLen w hi limit i table st
    _ = powerEventCellFold i
        (powerPhaseChainEvents segLen w phases) st.cell := by rw [htrace.1]
    _ = cursorPhasesFold segLen w i phases st.cell :=
      powerEventCellFold_powerPhaseChainEvents segLen w i phases st.cell

/-- Omitting powers already above the global endpoint does not change a
selected cell representing a positive integer at or below that endpoint. -/
theorem cursorPowerListFold_filter_le
    (segLen w i p global : Nat) (js : List Nat) (x : PlaneCell)
    (hp : 0 < p) (hi : i < segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ global) :
    cursorPowerListFold segLen w i p
        (js.filter fun j => decide (p ^ j ≤ global)) x =
      cursorPowerListFold segLen w i p js x := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
      by_cases hpower : p ^ j ≤ global
      · simp only [List.filter_cons, decide_eq_true_eq, hpower, if_true,
          cursorPowerListFold, List.foldl_cons]
        exact ih _
      · have hnotdvd : ¬p ^ j ∣ w + i := by
          intro hdvd
          have hle : p ^ j ≤ w + i := Nat.le_of_dvd hnpos hdvd
          exact hpower (Nat.le_trans hle hnglobal)
        simp only [List.filter_cons, decide_eq_true_eq, hpower, if_false,
          cursorPowerListFold, List.foldl_cons]
        rw [cursorPowerFold_eq segLen w i (p ^ j) p x
          (Nat.pow_pos hp) hi, if_neg hnotdvd]
        exact ih x

theorem cursorPhasesFold_boundedPowerPhases
    (segLen w i global pi p : Nat) (x : PlaneCell)
    (hp : 0 < p) (hi : i < segLen)
    (hnpos : 0 < w + i) (hnglobal : w + i ≤ global) :
    cursorPhasesFold segLen w i (boundedPowerPhases global pi p) x =
      cursorPrimePowerFold segLen w i p x := by
  unfold cursorPhasesFold boundedPowerPhases cursorPrimePowerFold
  rw [List.foldl_map]
  exact cursorPowerListFold_filter_le segLen w i p global
    (List.range' 1 32) x hp hi hnpos hnglobal

/-- Flattened table phases have exactly the row-wise cursor semantics; phase
indices affect only table navigation and not the selected-cell update. -/
theorem cursorPhasesFold_flatMap_bounded
    (segLen w i global : Nat) (rows : List (Nat × Nat)) (x : PlaneCell)
    (hpos : ∀ row ∈ rows, 0 < row.1)
    (hi : i < segLen) (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ global) :
    cursorPhasesFold segLen w i
        (rows.flatMap fun row => boundedPowerPhases global row.2 row.1) x =
      (rows.map Prod.fst).foldl
        (fun q p => cursorPrimePowerFold segLen w i p q) x := by
  induction rows generalizing x with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatMap_cons, cursorPhasesFold, List.foldl_append,
        List.map_cons, List.foldl_cons]
      rw [show (boundedPowerPhases global row.2 row.1).foldl
            (fun q phase =>
              cursorPowerFold segLen w i phase.pow phase.base q) x =
          cursorPrimePowerFold segLen w i row.1 x by
        exact cursorPhasesFold_boundedPowerPhases segLen w i global
          row.2 row.1 x (hpos row (by simp)) hi hnpos hnglobal]
      exact ih _ (fun q hq => hpos q (by simp [hq]))

theorem cursorPhasesFold_tablePowerPhases
    (segLen w i global : Nat) (ps : List Nat) (x : PlaneCell)
    (hpos : ∀ p ∈ ps, 0 < p)
    (hi : i < segLen) (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ global) :
    cursorPhasesFold segLen w i (tablePowerPhases global ps) x =
      cursorRowsFold segLen w i (factorRows ps) x := by
  rw [tablePowerPhases]
  have hrows := cursorPhasesFold_flatMap_bounded segLen w i global
    ps.zipIdx x
    (fun row hrow => hpos row.1 (by
      have : row.1 ∈ ps.zipIdx.map Prod.fst := List.mem_map.2 ⟨row, hrow, rfl⟩
      simpa [List.zipIdx_map_fst] using this))
    hi hnpos hnglobal
  rw [List.zipIdx_map_fst] at hrows
  simpa [cursorRowsFold, factorRows, List.foldl_map, factorRow] using hrows

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
