import LeanCompCert.Ports.R2SegMarkingCursorModel
import LeanCompCert.Ports.R2RuntimeSetupReceipt

/-!
# Production bounds for the `R₂*` marking cursor

This module turns the compiled root-table receipt into the small static table
contract used by the symbolic marking cursor.  It does not enumerate the
production table: each lookup is discharged from the prime-table theorem
obtained by compiler simulation and the retained CompCert run.
-/

namespace LeanCompCert.Ports.R2SegSieve

/-- The actual packed table consumed by the production sparse sweep. -/
def runtimeProductionTableWord (i : Nat) : Nat :=
  (rootPackedState runtimeProductionCfg
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
      (runtimeProductionCfg.tableBase + i)

/-- Every clamped production table lookup decodes to a positive power below
the sweep ceiling, with a weight fitting its declared packed lane. -/
theorem runtimeProduction_table_bounds :
    R2MarkTableBounds runtimeProductionCfg runtimeProductionTableWord := by
  refine
    { power_pos := ?_
      power_le := ?_
      weight_lt := ?_ }
  · intro i hi
    have hi' : i ≤ runtimePrimeCount := by
      simpa [runtimeProductionCfg, R2Cfg.tableLen] using hi
    rcases runtimeRootSetup_verified_cursor_word i hi' with
      ⟨rfl, hword⟩ | ⟨_, q, hq, _, _, hword, hvalue, _⟩
    · change 0 < runtimeProductionTableWord runtimePrimeCount &&& maskVal
      have hw : runtimeProductionTableWord runtimePrimeCount =
          packEntry 1 0 0 := by
        simpa only [runtimeProductionTableWord] using hword
      rw [hw]
      decide
    · change 0 < runtimeProductionTableWord i &&& maskVal
      have hv : runtimeProductionTableWord i &&& maskVal = q + 2 := by
        simpa only [runtimeProductionTableWord] using hvalue
      rw [hv]
      omega
  · intro i hi
    have hi' : i ≤ runtimePrimeCount := by
      simpa [runtimeProductionCfg, R2Cfg.tableLen] using hi
    rcases runtimeRootSetup_verified_cursor_word i hi' with
      ⟨rfl, hword⟩ | ⟨_, q, hq, _, _, hword, hvalue, _⟩
    · change runtimeProductionTableWord runtimePrimeCount &&& maskVal ≤
        runtimeProductionCfg.hi
      have hw : runtimeProductionTableWord runtimePrimeCount =
          packEntry 1 0 0 := by
        simpa only [runtimeProductionTableWord] using hword
      rw [hw]
      change packEntry 1 0 0 &&& maskVal ≤ runtimeProductionCfg.hi
      have hone : packEntry 1 0 0 &&& maskVal = 1 := by
        decide
      rw [hone]
      decide
    · change runtimeProductionTableWord i &&& maskVal ≤
        runtimeProductionCfg.hi
      have hv : runtimeProductionTableWord i &&& maskVal = q + 2 := by
        simpa only [runtimeProductionTableWord] using hvalue
      rw [hv]
      simp only [runtimeProductionCfg, R2Cfg.hi, runtimeRoot] at hq ⊢
      omega
  · intro i hi
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by
      simp [maskWt, wtBits])

/-- Cursor state installed by the per-window reset prelude. -/
def runtimeWindowInitialCursor (windowBase : Nat) : R2MarkCursor :=
  { pi := 0
    power := runtimeProductionCfg.q0
    base := runtimeProductionCfg.q0
    weight := runtimeProductionCfg.w0
    first := 1
    offset := resetOffset runtimeProductionCfg.q0 windowBase }

/-- The reset cursor satisfies the symbolic bounds for every window. -/
theorem runtimeWindowInitialCursor_bounds (windowBase : Nat) :
    (runtimeWindowInitialCursor windowBase).Bounds runtimeProductionCfg := by
  have hoff : resetOffset runtimeProductionCfg.q0 windowBase <
      runtimeProductionCfg.q0 := by
    apply Nat.mod_lt
    decide
  refine
    { pi_le := ?_
      power_pos := ?_
      power_le := ?_
      base_pos := ?_
      base_le := ?_
      weight_lt := ?_
      first_le_one := ?_
      offset_le := ?_ }
  · change 0 ≤ 13415; decide
  · change 0 < 2; decide
  · change 2 ≤ 21000144999; decide
  · change 0 < 2; decide
  · change 2 ≤ 21000144999; decide
  · change 11629079 < 2 ^ 28; decide
  · change 1 ≤ 1; decide
  · dsimp [runtimeWindowInitialCursor]
    have hq : runtimeProductionCfg.q0 ≤ runtimeProductionCfg.hi := by decide
    omega

/-- All symbolic cursor prefixes in every production window stay within the
machine-side preconditions, without evaluating the production schedule. -/
theorem runtimeWindowCursorPrefix_bounds (fuel windowBase : Nat) :
    (R2MarkCursor.run fuel runtimeProductionCfg windowBase
      runtimeProductionTableWord (runtimeWindowInitialCursor windowBase)).Bounds
        runtimeProductionCfg :=
  R2MarkCursor.run_bounds fuel (runtimeWindowInitialCursor_bounds windowBase)
    runtimeProduction_table_bounds (by decide)

#print axioms runtimeProduction_table_bounds
#print axioms runtimeWindowInitialCursor_bounds
#print axioms runtimeWindowCursorPrefix_bounds

end LeanCompCert.Ports.R2SegSieve
