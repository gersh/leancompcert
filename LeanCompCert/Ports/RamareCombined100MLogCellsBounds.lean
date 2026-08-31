import LeanCompCert.Ports.RamareCombined100MLambdaPsiBase
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleLength

/-!
# Generic address bounds for the Ramaré log table

This small module keeps list-membership reasoning away from concrete
production log values.  In particular, proving address safety must not force
Lean to elaborate the 10,001-entry production table.
-/

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-- A selected active row occurs at its lower positional address. -/
theorem logLowerCell_mem (c : Cfg) {p : Nat} {cell : LogCell}
    (hget : c.logs[p]? = some cell) (hactive : cell.active = true) :
    (c.logLoBase + p, cell.lo48) ∈ c.logCells := by
  have hzip : (cell, p) ∈ c.logs.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hget
  apply List.mem_append_left
  rw [List.mem_flatMap]
  exact ⟨(cell, p), hzip, by simp [hactive]⟩

/-- A selected active row occurs at its upper positional address. -/
theorem logUpperCell_mem (c : Cfg) {p : Nat} {cell : LogCell}
    (hget : c.logs[p]? = some cell) (hactive : cell.active = true) :
    (c.logHiBase + p, cell.hi48) ∈ c.logCells := by
  have hzip : (cell, p) ∈ c.logs.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hget
  apply List.mem_append_left
  rw [List.mem_flatMap]
  exact ⟨(cell, p), hzip, by simp [hactive]⟩

/-- The lower positional address uniquely determines the selected row value. -/
theorem logLowerCell_value (c : Cfg) {p : Nat} {cell : LogCell}
    (hp : p < c.logLen) (hget : c.logs[p]? = some cell)
    (x : Nat × Nat) (hx : x ∈ c.logCells)
    (haddr : x.1 = c.logLoBase + p) : x.2 = cell.lo48 := by
  unfold Cfg.logCells at hx
  rcases List.mem_append.mp hx with hrow | hsink
  · rw [List.mem_flatMap] at hrow
    obtain ⟨row, hrow, hcell⟩ := hrow
    have hrowGet : c.logs[row.2]? = some row.1 :=
      List.mem_zipIdx_iff_getElem?.mp hrow
    have hidx : row.2 < c.logLen := by
      simpa [Cfg.logLen] using (List.mem_zipIdx hrow).2.1
    by_cases ha : row.1.active
    · simp [ha] at hcell
      rcases hcell with hcell | hcell
      · subst x
        have heq : row.2 = p := by
          simp only at haddr
          omega
        subst p
        have hrowEq : row.1 = cell := Option.some.inj (hrowGet.symm.trans hget)
        rw [hrowEq]
      · subst x
        unfold Cfg.logHiBase at haddr
        omega
    · simp [ha] at hcell
  · simp only [List.mem_singleton] at hsink
    subst x
    unfold Cfg.logSink Cfg.logHiBase at haddr
    omega

/-- The upper positional address uniquely determines the selected row value. -/
theorem logUpperCell_value (c : Cfg) {p : Nat} {cell : LogCell}
    (hp : p < c.logLen) (hget : c.logs[p]? = some cell)
    (x : Nat × Nat) (hx : x ∈ c.logCells)
    (haddr : x.1 = c.logHiBase + p) : x.2 = cell.hi48 := by
  unfold Cfg.logCells at hx
  rcases List.mem_append.mp hx with hrow | hsink
  · rw [List.mem_flatMap] at hrow
    obtain ⟨row, hrow, hcell⟩ := hrow
    have hrowGet : c.logs[row.2]? = some row.1 :=
      List.mem_zipIdx_iff_getElem?.mp hrow
    have hidx : row.2 < c.logLen := by
      simpa [Cfg.logLen] using (List.mem_zipIdx hrow).2.1
    by_cases ha : row.1.active
    · simp [ha] at hcell
      rcases hcell with hcell | hcell
      · subst x
        unfold Cfg.logHiBase at haddr
        omega
      · subst x
        have heq : row.2 = p := by
          simp only at haddr
          omega
        subst p
        have hrowEq : row.1 = cell := Option.some.inj (hrowGet.symm.trans hget)
        rw [hrowEq]
    · simp [ha] at hcell
  · simp only [List.mem_singleton] at hsink
    subst x
    unfold Cfg.logSink at haddr
    omega

/-- The dedicated zero sink is always the final emitted log cell. -/
theorem logSink_mem (c : Cfg) : (c.logSink, 0) ∈ c.logCells := by
  unfold Cfg.logCells
  exact List.mem_append_right _ (by simp)

/-- The dedicated sink address uniquely carries zero. -/
theorem logSink_value (c : Cfg) (x : Nat × Nat) (hx : x ∈ c.logCells)
    (haddr : x.1 = c.logSink) : x.2 = 0 := by
  unfold Cfg.logCells at hx
  rcases List.mem_append.mp hx with hrow | hsink
  · rw [List.mem_flatMap] at hrow
    obtain ⟨row, hrow, hcell⟩ := hrow
    have hidx : row.2 < c.logLen := by
      simpa [Cfg.logLen] using (List.mem_zipIdx hrow).2.1
    by_cases ha : row.1.active
    · simp [ha] at hcell
      rcases hcell with hcell | hcell <;> subst x <;>
        simp only at haddr <;>
        unfold Cfg.logSink Cfg.logHiBase at haddr <;> omega
    · simp [ha] at hcell
  · simpa using congrArg Prod.snd (List.mem_singleton.mp hsink)

/-- Every address emitted by `logCells` lies above the shape-sieve storage
and at or below the dedicated log sink. -/
theorem logCells_address_range (c : Cfg) (x : Nat × Nat)
    (hx : x ∈ c.logCells) :
    c.shape.arrayLen ≤ x.1 ∧ x.1 ≤ c.logSink := by
  unfold Cfg.logCells at hx
  rcases List.mem_append.mp hx with hrow | hsink
  · rw [List.mem_flatMap] at hrow
    obtain ⟨row, hrow, hcell⟩ := hrow
    have hidx : row.2 < c.logs.length := by
      simpa using (List.mem_zipIdx hrow).2.1
    by_cases hactive : row.1.active
    · simp [hactive] at hcell
      rcases hcell with hcell | hcell <;> subst x
      · constructor
        · unfold Cfg.logLoBase
          omega
        · unfold Cfg.logSink Cfg.logHiBase Cfg.logLoBase Cfg.logLen
          omega
      · constructor
        · unfold Cfg.logHiBase Cfg.logLoBase
          omega
        · unfold Cfg.logSink Cfg.logHiBase Cfg.logLoBase Cfg.logLen
          omega
    · simp [hactive] at hcell
  · simp only [List.mem_singleton] at hsink
    subst x
    constructor
    · unfold Cfg.logSink Cfg.logHiBase Cfg.logLoBase
      omega
    · exact Nat.le_refl _

/-- A word-sized complete array makes all emitted log-table addresses
machine-word safe. -/
theorem logCells_address_bounds (c : Cfg) (hM : c.logSink < M)
    (x : Nat × Nat) (hx : x ∈ c.logCells) :
    x.1 < M ∧ c.shape.arrayLen ≤ x.1 := by
  have h := logCells_address_range c x hx
  exact ⟨Nat.lt_of_le_of_lt h.2 hM, h.1⟩

/-- The production shape plus any at-most-10,001-entry log table has a
word-sized sink address.  The proof switches to the certified literal prime
table before exposing `arrayLen`, avoiding reduction of trial division. -/
theorem production_logSink_lt_word (logs : List LogCell)
    (hlogs : logs.length ≤ 10001) :
    ({ shape := productionCursorCfg, logs } : Cfg).logSink < M := by
  rw [productionCursorCfg_eq_certified]
  have htable : certifiedProductionCursorCfg.tableLen ≤ 10001 := by
    rw [← congrArg ShapeSieve.Cfg.tableLen productionCursorCfg_eq_certified]
    exact productionCursorCfg_tableLen_le_10001
  change (14 * 999900 + certifiedProductionCursorCfg.tableLen + 1 + 4) +
    2 + logs.length + logs.length < M
  have hM : M = 18446744073709551616 := rfl
  omega

/-- Closed upper bound for the complete production array layout, proved
without exposing the trial-generated table to downstream elaboration. -/
theorem production_arrayLen_le (logs : List LogCell)
    (hlogs : logs.length ≤ 10001) :
    ({ shape := productionCursorCfg, logs } : Cfg).arrayLen ≤
      (14 * 999900 + 10001 + 1 + 4) + 2 + 10001 + 10001 + 1 + 6 := by
  rw [productionCursorCfg_eq_certified]
  have htable : certifiedProductionCursorCfg.tableLen ≤ 10001 := by
    rw [← congrArg ShapeSieve.Cfg.tableLen productionCursorCfg_eq_certified]
    exact productionCursorCfg_tableLen_le_10001
  change (14 * 999900 + certifiedProductionCursorCfg.tableLen + 1 + 4) +
      2 + logs.length + logs.length + 1 + 6 ≤
    (14 * 999900 + 10001 + 1 + 4) + 2 + 10001 + 10001 + 1 + 6
  omega

end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep
