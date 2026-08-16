import LeanCompCert.Ports.R2DenseHead
import LeanCompCert.Ports.R2RuntimeProductionSeed

/-!
# Production configurations for the compiled dense R2 head

The retained dense-head campaign has two compiled shards.  This module gives
their configurations and carry words stable names, so the physical receipts,
the emitter, and the runtime suffix all refer to the same Lean terms.
-/

namespace LeanCompCert.Ports.R2SegSieve

/-- The full-factor-table shard covering the beginning of the paper range. -/
def denseHeadFirstCfg : R2Cfg :=
  { lo := 3
    segLen := 998
    segCount := 1
    sc := defaultS
    markSteps := 3269
    logSteps := 24080
    streamCap := 1126
    table := (LeanCompCert.Ports.ArraySegSieve.primesBelow 1001).map
      (fun p => packEntry p (LeanCompCert.Ports.PsiSegSieve.lnFix defaultS p) 1)
    tableLenOverride := some 168 }

def denseHeadFirstSeed : R2Seed := R2Seed.afterTwo defaultS

/-- Compiled carry after the inclusive range `[3, 1000]`. -/
def denseHeadFirstCarry : R2Seed :=
  { d := 281475517734600
    err := 69492
    prev := 1000
    terms := 701
    sq := 31
    sq2 := 1024
    ex := 9
    th := 1024
    ln := 115892902
    thr := 6933846013
    viol := 0 }

/-- The second dense shard; its lower endpoint exceeds its sieve root. -/
def denseHeadSecondCfg : R2Cfg :=
  { lo := 1001
    segLen := 143999
    segCount := 1
    sc := defaultS
    markSteps := 406929
    logSteps := 3456104
    streamCap := 144127
    table := markTable defaultS 144999
    tableLenOverride := some 75 }

def denseHeadSecondSeed : R2Seed := denseHeadFirstCarry

/-- Compiled carry after the inclusive range `[1001, 144999]`. -/
def denseHeadFinalCarry : R2Seed :=
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

def R2Seed.words (s : R2Seed) : List Nat :=
  [s.d, s.err, s.prev, s.terms, s.sq, s.sq2, s.ex, s.th, s.ln, s.thr,
    s.viol]

/-- The runtime suffix is seeded by exactly the retained dense-head carry. -/
theorem denseHeadFinalCarry_eq_runtimeProductionSeed :
    denseHeadFinalCarry = runtimeProductionSeed := by
  rfl

theorem denseHeadFirst_arrayLen : denseHeadFirstCfg.arrayLen = 7434 := by
  rfl

theorem denseHeadSecond_arrayLen : denseHeadSecondCfg.arrayLen = 1008348 := by
  rfl

end LeanCompCert.Ports.R2SegSieve
