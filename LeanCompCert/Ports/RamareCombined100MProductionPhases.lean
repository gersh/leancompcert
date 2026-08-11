import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard00
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard01
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard02
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard03
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard04
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard05
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard06
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard07
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard08
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard09
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard10
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard11
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard12
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard13
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard14
import LeanCompCert.Ports.RamareCombined100MProductionPhaseShard15

/-!
# Exact production phase witness for the Ramaré 100-million cursor

The paper's trial-division table is checked in ten finite numeric blocks.  The
2,632 adjacent phase transitions are then checked in sixteen independent
blocks sized to remain below the repository's 1.5 GiB compilation ceiling.
This aggregate only composes opaque block results; it never repeats either
production-scale computation.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 20000 in
/-- Kernel-checked finite witness that the exact production phase list takes
only the emitted bump/load branches and ends at the explicit sentinel. -/
theorem productionPowerPhaseChain :
    PowerPhaseChain productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable productionPowerPhases := by
  have h15 := productionPowerPhaseShardOK.prepend 2560 72
    productionPowerPhaseShard15 productionPowerPhaseEdgeChecks_drop_2632
  have h14 := productionPowerPhaseShardOK.prepend 2496 64
    productionPowerPhaseShard14 h15
  have h13 := productionPowerPhaseShardOK.prepend 2432 64
    productionPowerPhaseShard13 h14
  have h12 := productionPowerPhaseShardOK.prepend 2304 128
    productionPowerPhaseShard12 h13
  have h11 := productionPowerPhaseShardOK.prepend 2176 128
    productionPowerPhaseShard11 h12
  have h10 := productionPowerPhaseShardOK.prepend 2048 128
    productionPowerPhaseShard10 h11
  have h09 := productionPowerPhaseShardOK.prepend 1920 128
    productionPowerPhaseShard09 h10
  have h08 := productionPowerPhaseShardOK.prepend 1792 128
    productionPowerPhaseShard08 h09
  have h07 := productionPowerPhaseShardOK.prepend 1664 128
    productionPowerPhaseShard07 h08
  have h06 := productionPowerPhaseShardOK.prepend 1536 128
    productionPowerPhaseShard06 h07
  have h05 := productionPowerPhaseShardOK.prepend 1280 256
    productionPowerPhaseShard05 h06
  have h04 := productionPowerPhaseShardOK.prepend 1024 256
    productionPowerPhaseShard04 h05
  have h03 := productionPowerPhaseShardOK.prepend 768 256
    productionPowerPhaseShard03 h04
  have h02 := productionPowerPhaseShardOK.prepend 512 256
    productionPowerPhaseShard02 h03
  have h01 := productionPowerPhaseShardOK.prepend 256 256
    productionPowerPhaseShard01 h02
  have hall := productionPowerPhaseShardOK.prepend 0 256
    productionPowerPhaseShard00 h01
  have hterminal :
      powerPhaseTerminalCheck 100000000 productionPrimeTable.length
        certifiedProductionPowerPhases.getLast? = true := by
    decide +kernel
  have hcert := PowerPhaseChain.of_edge_checks 100000000
    productionPrimeTable.length certifiedProductionPowerTable
    certifiedProductionPowerPhases hall hterminal
  rw [show productionCursorCfg.hi = 100000000 by rfl]
  rw [show productionCursorCfg.tableLen = productionPrimeTable.length by
    simp only [Cfg.tableLen, productionCursorCfg_table_eq]]
  rw [productionPowerTable_eq_certified,
    productionPowerPhases_eq_certified]
  exact hcert

/-- The first flattened power phase is the first prime-table row at its
first power. -/
theorem productionPowerPhases_head :
    productionPowerPhases.headD ⟨0, 1, 1⟩ = ⟨0, 2, 2⟩ := by
  rw [productionPowerPhases_eq_certified]
  decide +kernel

theorem productionTable_head : productionCursorCfg.table.headD 1 = 2 := by
  rw [productionCursorCfg_table_eq]
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
