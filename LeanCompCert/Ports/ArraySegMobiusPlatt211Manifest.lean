import LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
import LeanCompCert.Ports.ArraySegSieve

/-!
# Kernel-checked structure of the completed Platt (2.11) manifest

This file checks the cheap but load-bearing part of the retained production
receipt: every window is nonempty and internally consistent, indices and
ranges are gap-free, the next accumulator seed is exactly the preceding
output, the chain begins at one and ends at `10^12`, and the only nonzero
artifact counter is the documented inherited equality at row one (`n = 2`).

It intentionally does not claim that a JSON file proves a CompCert run.  The
physical run admissions and the source-sieve refinement are separate layers.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest

open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData

/-- Literal source configuration reconstructed from one retained row.  Only
the short bootstrap prime prefix is evaluated from `bootBound`; the expensive
full prime-table count and marking budget remain recorded scalar fields to be
checked by their own compiled finite computation. -/
def rowCfg (row : Row) : Cfg where
  lo := row.lo
  segLen := row.segLen
  segCount := row.segCount
  rootCount := row.rootCount
  bootPrimes := bootstrapPrimes.take row.bootCount
  mainCount := row.mainCount
  rootCap := row.rootCap
  markSteps := row.markSteps

/-- The exact historical program whose three result cells were retained.
Its threshold used denominator `hi`; the body and the three extrema stores
are unchanged by the later paper-faithful `hi + 1` correction. -/
def artifactProgram (row : Row) : LeanCompCert.Verified.ArrayState.AProgram :=
  mobiusProgram (rowCfg row) row.seed row.threshold

/-- Arithmetic shape of one independently emitted segmented window. -/
def rowShapeOK (row : Row) : Bool :=
  decide (0 < row.lo ∧ 0 < row.segLen ∧ 0 < row.segCount ∧
    row.hi = row.lo + row.segLen * row.segCount - 1)

/-- The production artifact has one known equality-boundary counter at index
one. Every other retained window returned zero violations. -/
def rowViolationOK (row : Row) : Bool :=
  decide (if row.idx = 1 then row.violations = 1 else row.violations = 0)

def rowOK (row : Row) : Bool := rowShapeOK row && rowViolationOK row

/-- Cheap arithmetic reconstruction of the emit-time configuration.  Exact
prime counts and weighted prime sums are intentionally a separate compiled
certificate rather than a giant kernel reduction of `primeStats`. -/
def cfgShapeOK (row : Row) : Bool :=
  let rootLen := row.rootCount * row.segLen
  decide (
    row.rootCap * row.rootCap ≤ row.hi ∧
    row.hi < (row.rootCap + 1) * (row.rootCap + 1) ∧
    row.rootCount = max 1 ((row.rootCap + row.segLen - 1) / row.segLen) ∧
    ((row.bootBound = 2 ∧ rootLen < 9) ∨
      (2 ≤ row.bootBound ∧ row.bootBound * row.bootBound ≤ rootLen ∧
        rootLen < (row.bootBound + 1) * (row.bootBound + 1))) ∧
    row.mainCount ≤ row.rootCap ∧ 0 < row.markSteps ∧
    8 * (3 * row.segLen + row.mainCount + 18) ≤
      LeanCompCert.Verified.Reflect.M)

def cfgShapesOK : Bool := rows.all cfgShapeOK

/-- Ordered manifest seam: consecutive index, gap-free integer range, and
literal accumulator carry. -/
def linkOK (left right : Row) : Bool :=
  decide (right.idx = left.idx + 1 ∧ right.lo = left.hi + 1 ∧
    right.seed = left.tOut)

def linksOK : Row → List Row → Bool
  | _, [] => true
  | left, right :: tail =>
      rowOK right && linkOK left right && linksOK right tail

/-- Complete structural check for the pinned 1,092-window receipt. -/
def manifestOK : Bool :=
  match rows with
  | [] => false
  | first :: tail =>
      decide (rows.length = 1092) &&
      decide (first.idx = 0 ∧ first.lo = 1 ∧ first.seed = tBias) &&
      rowOK first && cfgShapeOK first &&
      linksOK first tail && tail.all cfgShapeOK &&
      match rows.getLast? with
      | none => false
      | some last => decide (last.idx = 1091 ∧ last.hi = 10 ^ 12)

/-- A reduction-friendly square certificate for one paper-faithful strict
threshold.  The retained artifact used `hi` internally; its separately
generated `strictThreshold` field uses the formal worst-point denominator
`hi + 1`.  Adjacent squares avoid asking the kernel to unfold `Nat.sqrt`'s
well-founded implementation. -/
def StrictThresholdCertificate (row : Row) : Prop :=
  let budget := (row.hi + 1) / 2
  let raw := row.strictThreshold + budget
  let radicand := 2 ^ 125 / (row.hi + 1)
  raw * raw ≤ radicand ∧ radicand < (raw + 1) * (raw + 1) ∧ budget < raw

instance (row : Row) : Decidable (StrictThresholdCertificate row) := by
  unfold StrictThresholdCertificate
  infer_instance

/-- All generated strict thresholds carry exact adjacent-square witnesses. -/
def thresholdsOK : Bool :=
  rows.all fun row => decide (StrictThresholdCertificate row)

/-- Adjacent-square certificate for the literal historical artifact
threshold, whose root denominator was `hi`. -/
def ArtifactThresholdCertificate (row : Row) : Prop :=
  let budget := (row.hi + 1) / 2
  let raw := row.threshold + budget
  let radicand := 2 ^ 125 / row.hi
  raw * raw ≤ radicand ∧ radicand < (raw + 1) * (raw + 1) ∧ budget < raw

instance (row : Row) : Decidable (ArtifactThresholdCertificate row) := by
  unfold ArtifactThresholdCertificate
  infer_instance

def artifactThresholdsOK : Bool :=
  rows.all fun row => decide (ArtifactThresholdCertificate row)

/-- Paper-side extrema test for a retained window.  The first two singleton
windows are explicit because the `n = 1` sample is proved directly in the
real reduction: its exact accumulator is one unit above the rounded-down
strict threshold.  Window one inherits that `n = 1` value as its entry
maximum, so only its newly attained `n = 2` output is relevant.  From window
two onward both carried extrema are below the strict `hi + 1` threshold. -/
def strictSideOK (row : Row) : Bool :=
  if row.idx = 0 then
    decide (row.lo = 1 ∧ row.hi = 1 ∧
      row.tOut = tBias + 2 ^ 62 ∧ row.tMax = row.tOut ∧ row.tMin = tBias)
  else if row.idx = 1 then
    decide (row.lo = 2 ∧ row.hi = 2 ∧
      row.tOut ≤ tBias + row.strictThreshold ∧
      tBias - row.strictThreshold ≤ row.tOut)
  else
    decide (row.tMax ≤ tBias + row.strictThreshold ∧
      tBias - row.strictThreshold ≤ row.tMin)

/-- Every retained observation satisfies its paper-faithful side test. -/
def strictSidesOK : Bool := rows.all strictSideOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of all gap, carry, range, and counter-shape fields
copied from the SHA-pinned production manifest. -/
theorem manifest_ok : manifestOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cfgShapes_ok : cfgShapesOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of all 1,092 exact strict-threshold literals. -/
theorem thresholds_ok : thresholdsOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of the historical threshold literals, kept
separate from the stricter paper-side thresholds. -/
theorem artifactThresholds_ok : artifactThresholdsOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of the strict paper-side extrema comparisons. -/
theorem strictSides_ok : strictSidesOK = true := by decide

/-- The adjacent-square witness uniquely identifies the core natural square
root, hence the literal is definitionally the formal conservative threshold. -/
theorem strictThreshold_eq_platt211Threshold_of_certificate (row : Row)
    (h : StrictThresholdCertificate row) :
    row.strictThreshold = platt211Threshold row.hi := by
  let budget := (row.hi + 1) / 2
  let raw := row.strictThreshold + budget
  let radicand := 2 ^ 125 / (row.hi + 1)
  have hlow : raw * raw ≤ radicand := h.1
  have hhigh : radicand < (raw + 1) * (raw + 1) := h.2.1
  have hbudget : budget < raw := h.2.2
  have hrawLe : raw ≤ Nat.sqrt radicand := by
    have hsq : raw * raw <
        (Nat.sqrt radicand + 1) * (Nat.sqrt radicand + 1) :=
      Nat.lt_of_le_of_lt hlow (Nat.lt_succ_sqrt radicand)
    have := (Nat.mul_self_lt_mul_self_iff.mp hsq)
    omega
  have hsqrtLe : Nat.sqrt radicand ≤ raw := by
    have hsq : Nat.sqrt radicand * Nat.sqrt radicand <
        (raw + 1) * (raw + 1) :=
      Nat.lt_of_le_of_lt (Nat.sqrt_le radicand) hhigh
    have := (Nat.mul_self_lt_mul_self_iff.mp hsq)
    omega
  have hsqrt : Nat.sqrt radicand = raw := Nat.le_antisymm hsqrtLe hrawLe
  unfold platt211Threshold
  change row.strictThreshold =
    (if Nat.sqrt radicand ≤ budget then 0 else Nat.sqrt radicand - budget)
  rw [hsqrt, if_neg (Nat.not_le_of_lt hbudget)]
  dsimp only [raw, budget]
  omega

/-- Every retained row's strict threshold is connected to the formal generator
by ordinary kernel proof, not by trusting a generated literal. -/
theorem row_strictThreshold_eq (row : Row) (hrow : row ∈ rows) :
    row.strictThreshold = platt211Threshold row.hi := by
  have hbool := (List.all_eq_true.mp thresholds_ok) row hrow
  exact strictThreshold_eq_platt211Threshold_of_certificate row
    (of_decide_eq_true hbool)

#print axioms manifest_ok
#print axioms cfgShapes_ok
#print axioms thresholds_ok
#print axioms artifactThresholds_ok
#print axioms strictSides_ok
#print axioms row_strictThreshold_eq

end LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
