import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleGeneric

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

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

theorem productionPowerPhases_nonempty : productionPowerPhases ≠ [] := by
  intro hempty
  have hhead := productionPowerPhases_head
  simp [hempty] at hhead

theorem productionPowerTable_sentinel :
    productionPowerTable productionCursorCfg.tableLen = 1 := by
  simp [productionPowerTable, productionCursorCfg, Cfg.tableLen]

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

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
