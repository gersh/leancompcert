import LeanCompCert.Ports.RamareCombined100MProductionPhases

/-!
# Finite selected-cell semantics of the Ramaré production phase schedule

This module connects the compact phase-chain witness to the already-proved
row-wise prime-power fold.  It deliberately reasons over a few thousand phase
descriptors, never over the millions of emitted marking rounds.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Selected-cell fold of a finite list of power-phase descriptors. -/
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

/-- Phase flattening does not invent bases: every descriptor base came from
the finite input table. -/
theorem tablePowerPhases_base_mem
    {global : Nat} {ps : List Nat} {phase : PowerPhase}
    (hphase : phase ∈ tablePowerPhases global ps) : phase.base ∈ ps := by
  rw [tablePowerPhases, List.mem_flatMap] at hphase
  obtain ⟨row, hrow, hbounded⟩ := hphase
  have hrowBase : row.1 ∈ ps := by
    have hmapped : row.1 ∈ ps.zipIdx.map Prod.fst :=
      List.mem_map.mpr ⟨row, hrow, rfl⟩
    simpa [List.zipIdx_map_fst] using hmapped
  unfold boundedPowerPhases at hbounded
  simp only [List.mem_map] at hbounded
  obtain ⟨j, hj, hphaseEq⟩ := hbounded
  subst phase
  exact hrowBase

/-- A flattened phase retains the in-range index of its source table row. -/
theorem tablePowerPhases_pi_lt
    {global : Nat} {ps : List Nat} {phase : PowerPhase}
    (hphase : phase ∈ tablePowerPhases global ps) : phase.pi < ps.length := by
  rw [tablePowerPhases, List.mem_flatMap] at hphase
  obtain ⟨row, hrow, hbounded⟩ := hphase
  have hidx := List.mem_zipIdx hrow
  unfold boundedPowerPhases at hbounded
  simp only [List.mem_map] at hbounded
  obtain ⟨j, hj, hphaseEq⟩ := hbounded
  subst phase
  simpa using hidx.2.1

/-- Every flattened phase power passed the defining global-endpoint filter. -/
theorem tablePowerPhases_pow_le
    {global : Nat} {ps : List Nat} {phase : PowerPhase}
    (hphase : phase ∈ tablePowerPhases global ps) : phase.pow ≤ global := by
  rw [tablePowerPhases, List.mem_flatMap] at hphase
  obtain ⟨row, _hrow, hbounded⟩ := hphase
  unfold boundedPowerPhases at hbounded
  simp only [List.mem_map] at hbounded
  obtain ⟨j, hj, hphaseEq⟩ := hbounded
  subst phase
  exact of_decide_eq_true (List.mem_filter.mp hj).2

/-- Positive table bases make every flattened power positive. -/
theorem tablePowerPhases_pow_pos
    {global : Nat} {ps : List Nat} {phase : PowerPhase}
    (hpos : ∀ p ∈ ps, 0 < p)
    (hphase : phase ∈ tablePowerPhases global ps) : 0 < phase.pow := by
  rw [tablePowerPhases, List.mem_flatMap] at hphase
  obtain ⟨row, hrow, hbounded⟩ := hphase
  have hrowBase : row.1 ∈ ps := by
    have hmapped : row.1 ∈ ps.zipIdx.map Prod.fst :=
      List.mem_map.mpr ⟨row, hrow, rfl⟩
    simpa [List.zipIdx_map_fst] using hmapped
  unfold boundedPowerPhases at hbounded
  simp only [List.mem_map] at hbounded
  obtain ⟨j, _hj, hphaseEq⟩ := hbounded
  subst phase
  exact Nat.pow_pos (hpos row.1 hrowBase)

/-- Every production phase has a genuine positive prime-table base. -/
theorem productionPowerPhases_base_two_le
    (phase : PowerPhase) (hphase : phase ∈ productionPowerPhases) :
    2 ≤ phase.base := by
  apply trialPrimesBelow_two_le _ phase.base
  have hmem := tablePowerPhases_base_mem hphase
  simpa [productionPowerPhases, productionCursorCfg, Cfg.ofChain] using hmem

theorem productionPowerPhases_base_le_10000
    (phase : PowerPhase) (hphase : phase ∈ productionPowerPhases) :
    phase.base ≤ 10000 := by
  have hmem := tablePowerPhases_base_mem hphase
  change phase.base ∈
    trialPrimesBelow (Nat.sqrt 100000000 + 1) at hmem
  have hsqrt : Nat.sqrt 100000000 = 10000 := by decide +kernel
  have htable : phase.base ∈ trialPrimesBelow 10001 := by
    simpa [hsqrt] using hmem
  have hrange := (List.mem_filter.mp htable).1
  rw [List.mem_range] at hrange
  omega

/-- Every physical table load, including the explicit sentinel at
`tableLen`, returns a positive value. -/
theorem productionPowerTable_pos (pi : Nat) :
    0 < productionPowerTable pi := by
  by_cases hlt : pi < productionCursorCfg.table.length
  · have hget := List.getElem?_eq_getElem
      (l := productionCursorCfg.table) hlt
    have hmem := List.getElem_mem
      (l := productionCursorCfg.table) hlt
    change productionCursorCfg.table[pi] ∈
      trialPrimesBelow (Nat.sqrt 100000000 + 1) at hmem
    have hp2 : 2 ≤ productionCursorCfg.table[pi] := by
      exact trialPrimesBelow_two_le _ _ hmem
    simp only [productionPowerTable, hget, Option.getD_some]
    omega
  · have hlen : productionCursorCfg.table.length ≤ pi :=
      Nat.le_of_not_gt hlt
    have hget := List.getElem?_eq_none
      (l := productionCursorCfg.table) hlen
    simp [productionPowerTable, hget]

/-- Every physical table load is at most the production square-root bound;
the sentinel value is one. -/
theorem productionPowerTable_le_10000 (pi : Nat) :
    productionPowerTable pi ≤ 10000 := by
  by_cases hlt : pi < productionCursorCfg.table.length
  · have hget := List.getElem?_eq_getElem
      (l := productionCursorCfg.table) hlt
    have hmem := List.getElem_mem
      (l := productionCursorCfg.table) hlt
    change productionCursorCfg.table[pi] ∈
      trialPrimesBelow (Nat.sqrt 100000000 + 1) at hmem
    have hsqrt : Nat.sqrt 100000000 = 10000 := by decide +kernel
    have htable : productionCursorCfg.table[pi] ∈ trialPrimesBelow 10001 := by
      simpa [hsqrt] using hmem
    have hrange := (List.mem_filter.mp htable).1
    rw [List.mem_range] at hrange
    simp only [productionPowerTable, hget, Option.getD_some]
    omega
  · have hlen : productionCursorCfg.table.length ≤ pi :=
      Nat.le_of_not_gt hlt
    have hget := List.getElem?_eq_none
      (l := productionCursorCfg.table) hlen
    simp [productionPowerTable, hget]

/-- Every compact production descriptor supplies a valid initial cursor for
its phase.  This is the bridge from finite phase membership to the generic
round-prefix invariant, and performs no production-fuel reduction. -/
theorem productionPowerPhase_cursor_bounds
    (w : Nat) (phase : PowerPhase) (hphase : phase ∈ productionPowerPhases) :
    PowerCursorBounds productionCursorCfg.segLen productionCursorCfg.hi
      productionCursorCfg.tableLen productionPowerTable
      ⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩ := by
  have hpiLt : phase.pi < productionCursorCfg.table.length := by
    apply tablePowerPhases_pi_lt
    simpa [productionPowerPhases] using hphase
  have hpowPos : 0 < phase.pow := by
    apply tablePowerPhases_pow_pos
      (ps := productionCursorCfg.table)
    · intro p hp
      have hp2 : 2 ≤ p := by
        apply trialPrimesBelow_two_le _ p
        simpa [productionCursorCfg, Cfg.ofChain] using hp
      omega
    · simpa [productionPowerPhases] using hphase
  have hpowLe : phase.pow ≤ productionCursorCfg.hi := by
    apply tablePowerPhases_pow_le
    simpa [productionPowerPhases] using hphase
  have hbaseTwo := productionPowerPhases_base_two_le phase hphase
  have hbase10000 := productionPowerPhases_base_le_10000 phase hphase
  refine ⟨?_, hpowPos, hpowLe, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cfg.tableLen] using Nat.le_of_lt hpiLt
  · change 0 < phase.base
    omega
  · change phase.base ≤ 100000000
    omega
  · have hoff : startOffset w phase.pow < phase.pow :=
      Nat.mod_lt _ hpowPos
    change startOffset w phase.pow ≤ 999900 + 100000000
    have hp : phase.pow ≤ 100000000 := by
      simpa [productionCursorCfg, Cfg.hi, Cfg.ofChain] using hpowLe
    omega
  · intro pi _hpi
    exact productionPowerTable_pos pi
  · intro pi _hpi
    have hp := productionPowerTable_le_10000 pi
    change productionPowerTable pi ≤ 100000000
    omega

/-- Every finite round prefix started at a compact production phase retains
the cursor arithmetic invariant.  Specializing `fuel` to 3,260,306 does not
evaluate that many rounds in the kernel. -/
theorem productionPowerScheduleRun_cursor_bounds
    (fuel w i : Nat) (phase : PowerPhase) (st : PowerScheduleState)
    (hphase : phase ∈ productionPowerPhases)
    (hcursor : st.cursor =
      ⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩) :
    PowerCursorBounds productionCursorCfg.segLen productionCursorCfg.hi
      productionCursorCfg.tableLen productionPowerTable
      (powerScheduleRun fuel productionCursorCfg.segLen w
        productionCursorCfg.hi productionCursorCfg.tableLen i
        productionPowerTable st).cursor := by
  apply powerScheduleRun_cursor_bounds fuel productionCursorCfg.segLen w
    productionCursorCfg.hi productionCursorCfg.tableLen i
    productionPowerTable st
  · rw [hcursor]
    exact productionPowerPhase_cursor_bounds w phase hphase
  · change 0 < 100000000
    omega

theorem productionCursorCfg_tableLen_le_10001 :
    productionCursorCfg.tableLen ≤ 10001 := by
  have hsqrt : Nat.sqrt 100000000 = 10000 := by decide +kernel
  change (trialPrimesBelow (Nat.sqrt 100000000 + 1)).length ≤ 10001
  rw [hsqrt]
  change ((List.range 10001).filter trialPrime).length ≤ 10001
  simpa only [List.length_range] using
    List.length_filter_le trialPrime (List.range 10001)

/-- Closed production-scale word facts that do not require evaluating the
prime table or mark budget. -/
theorem productionCursorStaticWordBounds :
    0 < productionCursorCfg.hi ∧
      productionCursorCfg.hi < M ∧
      productionCursorCfg.hi * productionCursorCfg.hi < M ∧
      productionCursorCfg.tableLen + 1 < M ∧
      productionCursorCfg.tableLen + productionCursorCfg.tableBase < M ∧
      productionCursorCfg.segLen + 2 * productionCursorCfg.hi < M := by
  have hlen := productionCursorCfg_tableLen_le_10001
  have hM : M = 18446744073709551616 := rfl
  constructor
  · change 0 < 100000000
    omega
  constructor
  · change 100000000 < M
    omega
  constructor
  · change 100000000 * 100000000 < M
    omega
  constructor
  · omega
  constructor
  · change productionCursorCfg.tableLen + 14 * 999900 < M
    omega
  · change 999900 + 2 * 100000000 < M
    omega

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

/-- All seven live-plane addresses fit in one word for every live production
cursor offset. -/
theorem productionLivePlaneWordBounds {j : Nat}
    (hj : j < productionCursorCfg.segLen) :
    j < M ∧ j + productionCursorCfg.segLen < M ∧
      j + 2 * productionCursorCfg.segLen < M ∧
      j + 3 * productionCursorCfg.segLen < M ∧
      j + 4 * productionCursorCfg.segLen < M ∧
      j + 5 * productionCursorCfg.segLen < M ∧
      j + 6 * productionCursorCfg.segLen < M := by
  change j < M ∧ j + 999900 < M ∧ j + 2 * 999900 < M ∧
    j + 3 * 999900 < M ∧ j + 4 * 999900 < M ∧
    j + 5 * 999900 < M ∧ j + 6 * 999900 < M
  change j < 999900 at hj
  have hM : 7 * 999900 < M := by decide
  constructor <;> omega

/-- The seven live planes and seven sink planes all fit below the `u64`
modulus, as does the exhausted-cursor sentinel. -/
theorem productionStaticPlaneWordBounds :
    productionCursorCfg.segLen + 1 < M ∧
      7 * productionCursorCfg.segLen < M ∧
      8 * productionCursorCfg.segLen < M ∧
      9 * productionCursorCfg.segLen < M ∧
      10 * productionCursorCfg.segLen < M ∧
      11 * productionCursorCfg.segLen < M ∧
      12 * productionCursorCfg.segLen < M ∧
      13 * productionCursorCfg.segLen < M := by
  change 999900 + 1 < M ∧ 7 * 999900 < M ∧
    8 * 999900 < M ∧ 9 * 999900 < M ∧
    10 * 999900 < M ∧ 11 * 999900 < M ∧
    12 * 999900 < M ∧ 13 * 999900 < M
  decide

/-- The live whole-state invariant automatically supplies the advance
premise after phase selection, cursor reset, and the physical cell prefix. -/
theorem productionAdvanceWordPre_after_mark_prefix
    (k : Nat) (s : AState) (cur : PowerCursor)
    (hround : s.regs rR < productionCursorCfg.markSteps)
    (hcur :
      let phased := arun k s (lift productionCursorCfg.markPhaseBody)
      let reset := arun k phased productionCursorCfg.markResetBody
      machinePowerCursor reset = cur)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable cur)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hviol : s.regs rViol ≤ s.regs rR)
    (hvmark : s.regs rVMark ≤ s.regs rR) :
    let phased := arun k s (lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let marked := arun k reset productionCursorCfg.markCellPrefix
    AdvanceWordPre productionCursorCfg marked productionPowerTable := by
  let c := productionCursorCfg
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let marked := arun k reset c.markCellPrefix
  change machinePowerCursor reset = cur at hcur
  change ∀ pi, pi ≤ c.tableLen →
    s.arr (pi + c.tableBase) = productionPowerTable pi at htable
  have hp := c.markPhaseBody_run k s productionCursorCfg_markSteps_lt_word
  dsimp only at hp
  have hp10 : phased.regs 10 = 1 := by
    rw [hp.1, if_pos hround]
  have hr10 : reset.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  rcases productionStaticPlaneWordBounds with
    ⟨_hseg, h7, h8, h9, h10, h11, h12, h13⟩
  have hlive : reset.regs rJ < c.segLen →
      reset.regs rJ < M ∧ reset.regs rJ + c.segLen < M ∧
      reset.regs rJ + 2 * c.segLen < M ∧
      reset.regs rJ + 3 * c.segLen < M ∧
      reset.regs rJ + 4 * c.segLen < M ∧
      reset.regs rJ + 5 * c.segLen < M ∧
      reset.regs rJ + 6 * c.segLen < M := by
    intro hj
    exact productionLivePlaneWordBounds hj
  have hprefix := c.markCellPrefix_cursor_past k reset hr10 hlive
    h7 h8 h9 h10 h11 h12 h13
  have hmCur : machinePowerCursor marked = cur := by
    exact hprefix.1.trans hcur
  have hrJ : reset.regs rJ = cur.j := congrArg PowerCursor.j hcur
  have hmPast : marked.regs 25 =
      if cur.j < c.segLen then 0 else 1 := by
    simpa [hrJ] using hprefix.2
  have hmPhase : marked.regs 10 = 1 :=
    (arun_frame k 10 c.markCellPrefix (by rfl) reset).trans hr10
  have hresetArr : reset.arr = phased.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markResetBody phased (by rfl)
  have hmTable : ∀ pi, pi ≤ c.tableLen →
      marked.arr (pi + c.tableBase) = productionPowerTable pi := by
    intro pi hpi
    have hmark := c.markCellPrefix_table_frame k reset
      (pi + c.tableBase) hr10 (by change 0 < 999900; omega)
      hlive h7 h8 h9 h10 h11 h12 h13 (by omega)
    exact hmark.trans ((congrFun hresetArr _).trans
      ((congrFun hp.2.2.2 _).trans (htable pi hpi)))
  have frameToMarked (r : Nat)
      (hphaseF : writes r (lift c.markPhaseBody) = false)
      (hresetF : writes r c.markResetBody = false)
      (hprefixF : writes r c.markCellPrefix = false) :
      marked.regs r = s.regs r := by
    exact (arun_frame k r c.markCellPrefix hprefixF reset).trans
      ((arun_frame k r c.markResetBody hresetF phased).trans
        (arun_frame k r (lift c.markPhaseBody) hphaseF s))
  have hmR : marked.regs rR = s.regs rR :=
    frameToMarked rR (by rfl) (by rfl) (by rfl)
  have hmViol : marked.regs rViol = s.regs rViol :=
    frameToMarked rViol (by rfl) (by rfl) (by rfl)
  have hmVMark : marked.regs rVMark = s.regs rVMark :=
    frameToMarked rVMark (by rfl) (by rfl) (by rfl)
  apply productionAdvanceWordPre_of_cursorBounds marked cur hmCur hmPhase
    hmPast hbounds hmTable
  · simpa [hmR] using hround
  · rw [hmViol, hmR]
    exact hviol
  · rw [hmVMark, hmR]
    exact hvmark

/-- The first physical table entry is positive and representable, as follows
from the already-proved indexed production table bounds. -/
theorem productionTableHead_word :
    productionCursorCfg.table.headD 1 ≠ 0 ∧
      productionCursorCfg.table.headD 1 < M := by
  have hpos := productionPowerTable_pos 0
  have hle := productionPowerTable_le_10000 0
  have heq : productionCursorCfg.table.headD 1 = productionPowerTable 0 := by
    cases htable : productionCursorCfg.table with
    | nil => simp [productionPowerTable, List.headD, htable]
    | cons p ps => simp [productionPowerTable, List.headD, htable]
  constructor
  · rw [heq]
    omega
  · rw [heq]
    have hM : 10000 < M := by decide
    omega

/-- Simultaneous machine invariant for one production marking window.  The
reset projection makes round zero and all later nonzero rounds uniform. -/
structure ProductionMarkStateInv
    (w i round : Nat) (initial : PowerCellState) (s : AState) : Prop where
  observable :
    resetPowerCellState productionCursorCfg i s =
      powerCellRun productionCursorCfg round w i productionPowerTable initial
  table : ∀ pi, pi ≤ productionCursorCfg.tableLen →
    s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi
  round_eq : s.regs rR = round
  window_eq : s.regs rW = w
  viol_le : s.regs rViol ≤ round
  vmark_le : s.regs rVMark ≤ round

/-- The emitted phase/reset prefix realizes the reset projection recorded by
the simultaneous invariant. -/
theorem ProductionMarkStateInv.phaseReset_observable
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable
      (powerCellRun productionCursorCfg round w i
        productionPowerTable initial).cursor)
    (k : Nat) :
    let phased := arun k s (lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    machinePowerCellState productionCursorCfg i reset =
      powerCellRun productionCursorCfg round w i
        productionPowerTable initial := by
  let c := productionCursorCfg
  let pure := powerCellRun c round w i productionPowerTable initial
  have hmachineCursor (hn : s.regs rR ≠ 0) :
      machinePowerCursor s = pure.cursor := by
    have heq : machinePowerCellState c i s = pure := by
      rw [← resetPowerCellState_eq_machinePowerCellState c i s hn]
      exact h.observable
    exact congrArg PowerCellState.cursor heq
  rcases productionCursorStaticWordBounds with
    ⟨_hhiPos, hhiWord, _hhiSq, hK1, _haddr, hjpow⟩
  rcases productionTableHead_word with ⟨hp0, hp0M⟩
  have hreset := c.markPhaseResetBody_machinePowerCellState k s i
    productionCursorCfg_markSteps_lt_word hp0 hp0M
    (by
      intro hn
      have heq := congrArg PowerCursor.pi (hmachineCursor hn)
      change s.regs rPi = pure.cursor.pi at heq
      rw [heq]
      have hpi := hbounds.pi_le
      change pure.cursor.pi ≤ productionCursorCfg.tableLen at hpi
      omega)
    (by
      intro hn
      have heq := congrArg PowerCursor.pow (hmachineCursor hn)
      change s.regs rPow = pure.cursor.pow at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.pow_le hhiWord)
    (by
      intro hn
      have heq := congrArg PowerCursor.base (hmachineCursor hn)
      change s.regs rBase = pure.cursor.base at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.base_le hhiWord)
    (by
      intro hn
      have heq := congrArg PowerCursor.j (hmachineCursor hn)
      change s.regs rJ = pure.cursor.j at heq
      rw [heq]
      exact Nat.lt_of_le_of_lt hbounds.j_le (by omega))
  rw [Cfg.markPhaseResetBody, arun_append] at hreset
  simpa [c, pure] using hreset.trans h.observable

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- One actual emitted marking body preserves the simultaneous production
invariant and advances the pure selected-cell run by one step. -/
theorem ProductionMarkStateInv.step
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (k : Nat) (hi : i < productionCursorCfg.segLen)
    (hround : round < productionCursorCfg.markSteps)
    (hwM : w < M)
    (hinitial : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable initial.cursor)
    (hmark :
      let pure := powerCellRun productionCursorCfg round w i
        productionPowerTable initial
      pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
        PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell) :
    ProductionMarkStateInv w i (round + 1) initial
      (arun k s productionCursorCfg.body) := by
  let c := productionCursorCfg
  let pure := powerCellRun c round w i productionPowerTable initial
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let out := arun k s c.body
  have hhiPos : 0 < c.hi := productionCursorStaticWordBounds.1
  have hbounds : PowerCursorBounds c.segLen c.hi c.tableLen
      productionPowerTable pure.cursor := by
    exact powerCellRun_cursor_bounds c round w i productionPowerTable
      initial hinitial hhiPos
  have hresetState : machinePowerCellState c i reset = pure := by
    simpa [c, pure, phased, reset] using h.phaseReset_observable hbounds k
  have hcur : machinePowerCursor reset = pure.cursor :=
    congrArg PowerCellState.cursor hresetState
  have hresetW : reset.regs rW = w := by
    exact (arun_frame k rW c.markResetBody (by rfl) phased).trans
      ((arun_frame k rW (lift c.markPhaseBody) (by rfl) s).trans h.window_eq)
  have hroundS : s.regs rR < c.markSteps := by
    rw [h.round_eq]
    exact hround
  have hviolS : s.regs rViol ≤ s.regs rR := by
    rw [h.round_eq]
    exact h.viol_le
  have hvmarkS : s.regs rVMark ≤ s.regs rR := by
    rw [h.round_eq]
    exact h.vmark_le
  have hadvance := productionAdvanceWordPre_after_mark_prefix k s
    pure.cursor hroundS (by simpa [c, phased, reset] using hcur)
    hbounds h.table hviolS hvmarkS
  rcases productionStaticPlaneWordBounds with
    ⟨_hseg, h7, h8, h9, h10, h11, h12, h13⟩
  have hlive : pure.cursor.j < c.segLen →
      pure.cursor.j < M ∧ pure.cursor.j + c.segLen < M ∧
      pure.cursor.j + 2 * c.segLen < M ∧
      pure.cursor.j + 3 * c.segLen < M ∧
      pure.cursor.j + 4 * c.segLen < M ∧
      pure.cursor.j + 5 * c.segLen < M ∧
      pure.cursor.j + 6 * c.segLen < M := by
    intro hj
    exact productionLivePlaneWordBounds hj
  have hmarkReset : pure.cursor.j < c.segLen → pure.cursor.j = i →
      PlaneCellMarkPre (reset.regs rPow) (reset.regs rBase)
        (c.readPlaneCell (reset.regs rJ) reset) := by
    intro hj hji
    have hpow := congrArg PowerCursor.pow hcur
    have hbase := congrArg PowerCursor.base hcur
    have hjreg := congrArg PowerCursor.j hcur
    change reset.regs rPow = pure.cursor.pow at hpow
    change reset.regs rBase = pure.cursor.base at hbase
    change reset.regs rJ = pure.cursor.j at hjreg
    have hcell := congrArg PowerCellState.cell hresetState
    change c.readPlaneCell i reset = pure.cell at hcell
    rw [hpow, hbase, hjreg, hji, hcell]
    exact hmark hj hji
  have hbody := c.body_mark_powerCell_run k s productionPowerTable i
    hroundS productionCursorCfg_markSteps_lt_word hi pure.cursor
    (by simpa [phased, reset] using hcur) hlive
    h7 h8 h9 h10 h11 h12 h13
    (by simpa [phased, reset] using hmarkReset)
    (by simpa [phased, reset] using hadvance) hbounds.pi_le
  have hbodyState : machinePowerCellState c i out =
      powerCellStep c w i productionPowerTable pure := by
    simpa [out, phased, reset, hresetW, hresetState] using hbody
  have hpos := c.body_mark_position k s hroundS (by
      change 0 < 999900
      omega) productionCursorCfg_period_lt_word (by simpa [h.window_eq] using hwM)
  dsimp only at hpos
  have houtR : out.regs rR = round + 1 := by
    rw [hpos.1, h.round_eq]
  have houtW : out.regs rW = w := hpos.2.trans h.window_eq
  have hcounter := c.body_mark_counter_bounds k s productionPowerTable
    hroundS productionCursorCfg_markSteps_lt_word (by
      change 0 < 999900
      omega) productionCursorCfg_period_lt_word
    (by simpa [h.window_eq] using hwM) hviolS hvmarkS
    (by simpa [phased, reset] using hadvance)
  dsimp only at hcounter
  have houtReset : resetPowerCellState c i out =
      powerCellRun c (round + 1) w i productionPowerTable initial := by
    rw [resetPowerCellState_eq_machinePowerCellState c i out (by
      rw [houtR]
      omega)]
    rw [hbodyState]
    rfl
  dsimp only [c, out] at houtR houtW houtReset
  refine {
    observable := ?_
    table := ?_
    round_eq := houtR
    window_eq := houtW
    viol_le := ?_
    vmark_le := ?_ }
  · exact houtReset
  · intro pi hpi
    have hframe := c.body_mark_table_frame k s
      (pi + c.tableBase) hroundS productionCursorCfg_markSteps_lt_word
      (by change 0 < 999900; omega) pure.cursor
      (by simpa [phased, reset] using hcur) hlive
      h7 h8 h9 h10 h11 h12 h13 (by omega)
    exact hframe.trans (h.table pi hpi)
  · rw [hpos.1, h.round_eq] at hcounter
    exact hcounter.1
  · rw [hpos.1, h.round_eq] at hcounter
    exact hcounter.2

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
  have hnonempty : productionPowerPhases ≠ [] := by decide +kernel
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

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
