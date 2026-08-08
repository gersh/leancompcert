import LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

/-!
Finite benchmark for the root-selector bootstrap guard handoff used by the
production Platt-strong segmented campaign.  It deliberately evaluates the
transparent reference folds rather than using `native_decide`.

```
lake env lean --run bench/ArraySegRootGuardCheck.lean
```
-/

open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

namespace Bench.ArraySegRootGuardCheck

def targetHi : Nat := 7727068586
def segLen : Nat := 200
def segCount : Nat := (targetHi + segLen - 1) / segLen
def cfg : Cfg := Cfg.ofRange 1 segLen segCount
def bootBound : Nat := max (Nat.sqrt cfg.rootLen) 2
def afterFirst : List Nat :=
  rootScanTable cfg.bootPrimes bootBound cfg.segLen
def afterSecond : List Nat :=
  rootScanFrom afterFirst (1 + cfg.segLen) cfg.segLen

def run : IO Unit := do
  IO.println s!"hi={cfg.hi} segLen={cfg.segLen} rootCount={cfg.rootCount}"
  IO.println s!"bootBound={bootBound} bootCount={cfg.bootPrimes.length}"
  IO.println s!"firstCount={afterFirst.length} extended={
    bootstrapExtendedBool cfg.bootPrimes afterFirst}"
  IO.println s!"secondCount={afterSecond.length} extended={
    bootstrapExtendedBool cfg.bootPrimes afterSecond}"

end Bench.ArraySegRootGuardCheck

open Bench.ArraySegRootGuardCheck in
def main (_args : List String) : IO UInt32 := do
  run
  return 0
