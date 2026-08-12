import LeanCompCert.Ports.CDEMAbelMarkTermination
import LeanCompCert.Ports.CDEMAbelProductionCertificate

/-!
Evaluate the compact source-level upper bound for the production CDEM Abel
marking schedule.  The production prime table is passed once and reused for
every divisor, avoiding reconstruction of `muPrimes` inside the hot loop.

Usage:

```
lake env lean --run bench/CDEMAbelMarkBudget.lean
```
-/

open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelScan

def main : IO UInt32 := do
  let primes := Ref.muPrimes productionCfg.kBound
  let compact := compactMarkBudgetRunWith productionCfg primes
  IO.println s!"compact={compact}"
  IO.println s!"markSteps={productionCfg.markSteps}"
  IO.println s!"margin={productionCfg.markSteps - compact}"
  return if compact ≤ productionCfg.markSteps then 0 else 1
