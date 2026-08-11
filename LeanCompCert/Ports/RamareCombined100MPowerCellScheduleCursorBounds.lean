import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleTable

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Every compact production descriptor supplies a valid initial cursor for
its phase.  This is the bridge from finite phase membership to the generic
round-prefix invariant, and performs no production-fuel reduction. -/
theorem productionPowerPhase_cursor_bounds
    (w : Nat) (phase : PowerPhase) (hphase : phase ∈ productionPowerPhases) :
    PowerCursorBounds productionCursorCfg.segLen productionCursorCfg.hi
      productionCursorCfg.tableLen productionPowerTable
      ⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩ := by
  have hphaseCert : phase ∈ certifiedProductionPowerPhases := by
    rw [← productionPowerPhases_eq_certified]
    exact hphase
  have hphaseTable :
      phase ∈ tablePowerPhases 100000000 productionPrimeTable := by
    simpa only [certifiedProductionPowerPhases] using hphaseCert
  have hpiLt : phase.pi < productionPrimeTable.length :=
    tablePowerPhases_pi_lt hphaseTable
  have hpowPos : 0 < phase.pow := by
    apply tablePowerPhases_pow_pos
      (ps := productionPrimeTable)
    · intro p hp
      have hp2 : 2 ≤ p := by
        apply trialPrimesBelow_two_le _ p
        rw [trialPrimesBelow_10001_eq_productionPrimeTable]
        exact hp
      omega
    · exact hphaseTable
  have hpowLe : phase.pow ≤ 100000000 :=
    tablePowerPhases_pow_le hphaseTable
  have hbaseTwo := productionPowerPhases_base_two_le phase hphase
  have hbase10000 := productionPowerPhases_base_le_10000 phase hphase
  refine ⟨?_, hpowPos, hpowLe, ?_, ?_, ?_, ?_, ?_⟩
  · change phase.pi ≤ productionCursorCfg.table.length
    rw [productionCursorCfg_table_eq]
    exact Nat.le_of_lt hpiLt
  · change 0 < phase.base
    omega
  · change phase.base ≤ 100000000
    omega
  · have hoff : startOffset w phase.pow < phase.pow :=
      Nat.mod_lt _ hpowPos
    change startOffset w phase.pow ≤ 999900 + 100000000
    have hp : phase.pow ≤ 100000000 := by
      exact hpowLe
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


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
