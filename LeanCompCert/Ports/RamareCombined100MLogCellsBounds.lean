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
