import LeanCompCert.Ports.R2RuntimeMarkTableRep
import LeanCompCert.Ports.R2SegMarkingWindowBounds

/-! # Production specialization of symbolic marking-window word bounds -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect

theorem runtimeFirstWindow_cells_inv : runtimeFirstWindow.CellsInv := by
  intro i
  exact emptyMarkCell_inv

theorem runtimeFirstWindow_lsum_zero : runtimeFirstWindow.LsumBound 0 := by
  intro i
  simp [runtimeFirstWindow, emptyMarkCell]

theorem runtimeWindowRun_cells_inv (fuel : Nat) :
    (runtimeFirstWindow.run fuel runtimeProductionCfg runtimeProductionCfg.lo
      runtimeProductionTableWord).CellsInv :=
  R2MarkWindow.CellsInv.run fuel runtimeFirstWindow_cells_inv
    (runtimeWindowInitialCursor_bounds runtimeProductionCfg.lo)
    runtimeProduction_table_bounds (by decide)

theorem runtimeWindowRun_lsum_bound (fuel : Nat) :
    (runtimeFirstWindow.run fuel runtimeProductionCfg runtimeProductionCfg.lo
      runtimeProductionTableWord).LsumBound (fuel * 2 ^ wtBits) := by
  simpa only [Nat.zero_add] using
    R2MarkWindow.LsumBound.run fuel runtimeFirstWindow_lsum_zero
      (runtimeWindowInitialCursor_bounds runtimeProductionCfg.lo)
      runtimeProduction_table_bounds (by decide)

/-- The entire production marking budget leaves more than enough room for
one further fixed-log word. -/
theorem runtimeProduction_lsum_word_room {fuel : Nat}
    (hfuel : fuel < runtimeProductionCfg.markSteps) :
    fuel * 2 ^ wtBits + 2 ^ wtBits < M := by
  rw [show M = 2 ^ 64 by rfl]
  simp only [wtBits]
  change fuel < 3558013 at hfuel
  omega

#print axioms runtimeFirstWindow_cells_inv
#print axioms runtimeFirstWindow_lsum_zero
#print axioms runtimeWindowRun_cells_inv
#print axioms runtimeWindowRun_lsum_bound
#print axioms runtimeProduction_lsum_word_room

end LeanCompCert.Ports.R2SegSieve
