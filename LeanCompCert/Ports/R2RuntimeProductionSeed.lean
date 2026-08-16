import LeanCompCert.Ports.R2RuntimeTable

/-!
# Leaf receipt for the dense R2 production prefix

The sparse runtime sweep starts immediately after the separately compiled
dense head through `144999`.  Keeping its eleven observed words in this leaf
prevents a receipt update from invalidating every symbolic R2 refinement
module importing `R2RuntimeTable`.
-/

namespace LeanCompCert.Ports.R2SegSieve

/-- Exact compiled dense-head receipt through `144999`, used to seed the
runtime-only production suffix.  These compact words are observations from
the separately compiled head campaign; no head fold is evaluated while
emitting or checking the production suffix. -/
def runtimeProductionSeed : R2Seed :=
  { d := 281482090502886
    err := 10983953
    prev := 144999
    terms := 61171
    sq := 380
    sq2 := 145161
    ex := 17
    th := 262144
    ln := 199388523
    thr := 146230987829
    viol := 0 }

end LeanCompCert.Ports.R2SegSieve
