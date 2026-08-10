import LeanCompCert.Ports.CDEMAbelScan
import LeanCompCert.Verified.ArrayComputation

/-!
# Exact compiled observation for the production CDEM Abel scan

The production driver returns the aggregate guard count and prints the twelve
result cells written by `CDEMAbelScan`'s epilogue.  This module gives that one
physical execution one exact Lean proposition.  It does not claim that the
source program is defined or that the cells denote the Abel sums; those are
separate refinement obligations.
-/

namespace LeanCompCert.Ports.CDEMAbelProductionCertificate

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.CDEMAbelScan

/-- The exact configuration emitted for the completed five-billion-index
CompCert run. -/
def productionCfg : Cfg where
  wScale := 1000000000000000000
  kBound := 199330
  segLen := 1000000
  segCount := 5000
  bsSteps := 61
  markSteps := 8845158
  primes :=
    [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59
    , 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127
    , 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193
    , 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269
    , 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349
    , 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431
    , 433, 439, 443 ]

/-- The compiled array computation whose emitted C was run. -/
def productionComputation : AComputation where
  program := abelProgram productionCfg
  wellFormed := abelProgram_wf productionCfg
  base := 0
  baseOk := by
    constructor <;> decide
  name := "cdem-abel-5e9"

/-- Read the returned guard count and the twelve consecutive result cells from
one final compiled state.  This is exactly the observation made by the hosted
production driver. -/
def productionObservation : Option (Int × List Int) := do
  let m ← evalMCCSequence
    (productionComputation.program.initialMCC productionComputation.base)
    productionComputation.program.compile
  let result ← m.env ⟨productionComputation.program.output + 1⟩
  let cells ← (List.range 12).mapM fun slot =>
    m.mem (cellAddr productionComputation.base
      (productionCfg.resultBase + slot))
  pure (result, cells)

/-- The exact return value and cells recorded by the retained production
manifest, named separately so downstream refinement theorems do not copy the
physical observation contract. -/
def productionExpectedObservation : Option (Int × List Int) :=
  some
    (0,
      [ 2037368965713732597, 0
      , 2037044085256098857, 0
      , 10818755014043801788, 2640
      , 1678512305, 112, 111, 70710, 199330, 0 ])

/-- CompCert 3.17 execution returned zero failed guards and the exact twelve
cells recorded in `bench/results/manifests/cdem_abel_5e9.json`. -/
axiom cdemAbelProduction_compcert_run :
  productionObservation = productionExpectedObservation

end LeanCompCert.Ports.CDEMAbelProductionCertificate
