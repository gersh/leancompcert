import LeanCompCert.Ports.RamareCombined100MProductionPrimeTable

/-!
# Closed production phase data for the Ramaré cursor

The data live below the independently checked phase shards so every shard can
reduce the same closed descriptor without importing the aggregate theorem.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def productionCursorCfg : Cfg :=
  Cfg.ofChain 10001 999900 100 100000000

def productionPowerPhases : List PowerPhase :=
  tablePowerPhases productionCursorCfg.hi productionCursorCfg.table

def productionPowerTable (pi : Nat) : Nat :=
  (productionCursorCfg.table[pi]?).getD 1

theorem productionCursorCfg_table_eq :
    productionCursorCfg.table = productionPrimeTable := by
  change trialPrimesBelow (Nat.sqrt 100000000 + 1) = productionPrimeTable
  rw [show Nat.sqrt 100000000 = 10000 by decide +kernel]
  exact trialPrimesBelow_10001_eq_productionPrimeTable

/-- The complete production descriptor with its expensive generated table
replaced by the independently certified literal table. -/
def certifiedProductionCursorCfg : Cfg :=
  { productionCursorCfg with table := productionPrimeTable }

theorem productionCursorCfg_eq_certified :
    productionCursorCfg = certifiedProductionCursorCfg := by
  unfold certifiedProductionCursorCfg
  rw [← productionCursorCfg_table_eq]

/-- The same descriptor with the expensive trial-division table replaced by
its independently certified literal value. -/
def certifiedProductionPowerPhases : List PowerPhase :=
  tablePowerPhases 100000000 productionPrimeTable

def certifiedProductionPowerTable (pi : Nat) : Nat :=
  (productionPrimeTable[pi]?).getD 1

theorem productionPowerPhases_eq_certified :
    productionPowerPhases = certifiedProductionPowerPhases := by
  simp only [productionPowerPhases, certifiedProductionPowerPhases]
  rw [productionCursorCfg_table_eq]
  rfl

theorem productionPowerTable_eq_certified :
    productionPowerTable = certifiedProductionPowerTable := by
  funext pi
  simp only [productionPowerTable, certifiedProductionPowerTable]
  rw [productionCursorCfg_table_eq]

/-- The production mark counter is word-safe without reducing its
3.26-million-round emit-time budget computation in the kernel. -/
theorem productionCursorCfg_markSteps_lt_word :
    productionCursorCfg.markSteps < LeanCompCert.Verified.Reflect.M := by
  exact Cfg.ofChain_markSteps_lt_word 10001 999900 100 100000000

theorem productionCursorCfg_period_lt_word :
    productionCursorCfg.period < LeanCompCert.Verified.Reflect.M := by
  exact Cfg.ofChain_period_lt_word 10001 999900 100 100000000 (by decide)

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
