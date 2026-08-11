import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard00
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard01
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard02
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard03
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard04
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard05
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard06
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard07
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard08
import LeanCompCert.Ports.RamareCombined100MProductionPrimeTableShard09

/-!
# Exact production prime table

The ten imported blocks independently run the source `trialPrime` predicate.
This module recombines only their list boundaries, so no aggregate kernel
command repeats the 0-through-10,000 divisor sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def productionPrimeTable : List Nat :=
  productionPrimeTableChunk00 ++ productionPrimeTableChunk01 ++
  productionPrimeTableChunk02 ++ productionPrimeTableChunk03 ++
  productionPrimeTableChunk04 ++ productionPrimeTableChunk05 ++
  productionPrimeTableChunk06 ++ productionPrimeTableChunk07 ++
  productionPrimeTableChunk08 ++ productionPrimeTableChunk09

set_option maxRecDepth 20000 in
theorem trialPrimesBelow_10001_eq_productionPrimeTable :
    trialPrimesBelow 10001 = productionPrimeTable := by
  rw [trialPrimesBelow, List.range_eq_range']
  change trialPrimeRange 0 10001 = productionPrimeTable
  rw [show 10001 = 1000 + 9001 by omega,
    trialPrimeRange_split,
    show 9001 = 1000 + 8001 by omega,
    trialPrimeRange_split,
    show 8001 = 1000 + 7001 by omega,
    trialPrimeRange_split,
    show 7001 = 1000 + 6001 by omega,
    trialPrimeRange_split,
    show 6001 = 1000 + 5001 by omega,
    trialPrimeRange_split,
    show 5001 = 1000 + 4001 by omega,
    trialPrimeRange_split,
    show 4001 = 1000 + 3001 by omega,
    trialPrimeRange_split,
    show 3001 = 1000 + 2001 by omega,
    trialPrimeRange_split,
    show 2001 = 1000 + 1001 by omega,
    trialPrimeRange_split]
  rw [productionPrimeTableChunk00_eq, productionPrimeTableChunk01_eq,
    productionPrimeTableChunk02_eq, productionPrimeTableChunk03_eq,
    productionPrimeTableChunk04_eq, productionPrimeTableChunk05_eq,
    productionPrimeTableChunk06_eq, productionPrimeTableChunk07_eq,
    productionPrimeTableChunk08_eq, productionPrimeTableChunk09_eq]
  rfl

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
