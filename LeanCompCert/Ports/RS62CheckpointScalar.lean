import LeanCompCert.Ports.RS62CheckpointManifestData

/-!
# Scalar metadata for the RS62 checkpoint campaign

These are only the 120 rows of literal sizing metadata.  The prime-table,
weighted-prime, and long ladder computations are deliberately absent: those
are supplied by verified compiled programs.  Keeping this closed scalar layer
separate prevents a future proof from accidentally evaluating a production
range in Lean.
-/

namespace LeanCompCert.Ports.RS62CheckpointScalar

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62CheckpointManifestData

/-- Cheap word, address, endpoint, and one-window schedule facts. -/
def RowScalar (row : Row) : Prop :=
  let c := row.cfg
  1000 ≤ row.rootCap ∧ row.rootCap ≤ 18001 ∧
  0 < row.segLen ∧ row.segLen ≤ 3158551 ∧
  100000001 ≤ row.lo ∧ row.lo + row.segLen ≤ 324000001 ∧
  row.mainCount ≤ row.rootCap + c.bootCount ∧
  row.markSteps < 10000000 ∧
  (1 + ((c.segLen + c.wDelta) % M)) % M = c.lo ∧
  c.rootSpan + c.markSteps < M ∧
  c.rootCap * c.rootCap < M ∧
  c.segLen + c.rootCap < M ∧
  c.lo + c.segLen < M ∧
  c.rootCap < c.lo ∧
  c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap ∧
  3 ≤ c.lo ∧ row.SL < M ∧ row.SU < M ∧
  c.lo + c.segLen ≤ 2 ^ 40 ∧
  8 * c.arrayLen ≤ M ∧
  0 < row.rootCap + 1 ∧ row.rootCap + 1 < M ∧
  (1000 + 1) * (row.rootCap + 1) < M ∧
  (1000 + 2) * (1000 + 2) < M ∧
  row.rootCap + 1 ≤ (1000 + 2) * (1000 + 2) ∧
  (row.rootCap + 1) * (row.segLen + 2) < M ∧
  8 * (row.rootCap + 1) ≤ M

/-- Coarse literal bounds plus the only row-correlated inequality.  Keeping
this proposition small avoids reducing the expanded configuration or any
prime table while dispatching the 120 manifest constructors. -/
def RowBounds (row : Row) : Prop :=
  10050 ≤ row.rootCap ∧ row.rootCap ≤ 18001 ∧
  984459 ≤ row.segLen ∧ row.segLen ≤ 3158551 ∧
  100000001 ≤ row.lo ∧ row.lo + row.segLen ≤ 324000001 ∧
  row.mainCount ≤ 2064 ∧ row.markSteps < 10000000 ∧
  row.lo + row.segLen - 1 ≤ row.rootCap * row.rootCap ∧
  row.SL ≤ 404000000000000 ∧ row.SU ≤ 404000000000000

/-- Reusable low-level evidence required by the segmented receipt.  Unlike
`RowScalar`, this structure contains no campaign-specific coarse bounds, so
the same verified pipeline can certify the lower anchor rows. -/
structure RowCore (row : Row) : Prop where
  rootAtLeast1000 : 1000 ≤ row.rootCap
  rootAtLeast1009 : 1009 ≤ row.rootCap
  segmentPositive : 0 < row.segLen
  segmentAtLeastTwo : 2 ≤ row.segLen
  rootBelowSegment : row.rootCap < row.segLen
  rootBootstrapCoverage : 1 + row.rootCap ≤ (1000 + 1) * (1000 + 1)
  baseEq :
    (1 + ((row.cfg.segLen + row.cfg.wDelta) % M)) % M = row.cfg.lo
  indexRoom : row.cfg.rootSpan + row.cfg.markSteps < M
  rootSquareRoom : row.cfg.rootCap * row.cfg.rootCap < M
  segmentRootRoom : row.cfg.segLen + row.cfg.rootCap < M
  endpointWordRoom : row.cfg.lo + row.cfg.segLen < M
  aboveRoot : row.cfg.rootCap < row.cfg.lo
  rootCoverage :
    row.cfg.lo + row.cfg.segLen - 1 ≤ row.cfg.rootCap * row.cfg.rootCap
  startAtLeastThree : 3 ≤ row.cfg.lo
  lowerWord : row.SL < M
  upperWord : row.SU < M
  endpointBound : row.cfg.lo + row.cfg.segLen ≤ 2 ^ 40
  arrayBytesRoom : 8 * row.cfg.arrayLen ≤ M
  mainCountWord : row.mainCount < M
  markStepsWord : row.markSteps < M
  countLengthPositive : 0 < row.rootCap + 1
  countLengthWord : row.rootCap + 1 < M
  countLoopWord : (134 + 1) * (row.rootCap + 1) < M
  countSieveSquareWord : (134 + 2) * (134 + 2) < M
  countSieveCoverage : row.rootCap + 1 ≤ (134 + 2) * (134 + 2)
  bootSquareWord : (1000 + 2) * (1000 + 2) < M
  bootCoverage : row.rootCap + 1 ≤ (1000 + 2) * (1000 + 2)
  weightedProductWord : (row.rootCap + 1) * (row.segLen + 2) < M
  countArrayBytesRoom : 8 * (row.rootCap + 1) ≤ M

/-!
The literal manifest audit is intentionally split by column.  A single
`rows.all` over the full nested conjunction made Lean elaborate one enormous
proof term.  These eleven independent checks each reduce only a short list of
machine-sized literals; no prime table or production fold occurs here.
-/

private def rootCapLowerOK : Bool :=
  rows.all fun row => decide (10050 ≤ row.rootCap)
private def rootCapUpperOK : Bool :=
  rows.all fun row => decide (row.rootCap ≤ 18001)
private def segLenLowerOK : Bool :=
  rows.all fun row => decide (984459 ≤ row.segLen)
private def segLenUpperOK : Bool :=
  rows.all fun row => decide (row.segLen ≤ 3158551)
private def loLowerOK : Bool :=
  rows.all fun row => decide (100000001 ≤ row.lo)
private def endpointUpperOK : Bool :=
  rows.all fun row => decide (row.lo + row.segLen ≤ 324000001)
private def mainCountUpperOK : Bool :=
  rows.all fun row => decide (row.mainCount ≤ 2064)
private def markStepsUpperOK : Bool :=
  rows.all fun row => decide (row.markSteps < 10000000)
private def rootCoverageOK : Bool := rows.all fun row =>
  decide (row.lo + row.segLen - 1 ≤ row.rootCap * row.rootCap)
private def lowerAccumulatorOK : Bool :=
  rows.all fun row => decide (row.SL ≤ 404000000000000)
private def upperAccumulatorOK : Bool :=
  rows.all fun row => decide (row.SU ≤ 404000000000000)

set_option maxRecDepth 10000 in
private theorem rootCapLower_ok : rootCapLowerOK = true := by decide
set_option maxRecDepth 10000 in
private theorem rootCapUpper_ok : rootCapUpperOK = true := by decide
set_option maxRecDepth 10000 in
private theorem segLenLower_ok : segLenLowerOK = true := by decide
set_option maxRecDepth 10000 in
private theorem segLenUpper_ok : segLenUpperOK = true := by decide
set_option maxRecDepth 10000 in
private theorem loLower_ok : loLowerOK = true := by decide
set_option maxRecDepth 10000 in
private theorem endpointUpper_ok : endpointUpperOK = true := by decide
set_option maxRecDepth 10000 in
private theorem mainCountUpper_ok : mainCountUpperOK = true := by decide
set_option maxRecDepth 10000 in
private theorem markStepsUpper_ok : markStepsUpperOK = true := by decide
set_option maxRecDepth 10000 in
private theorem rootCoverage_ok : rootCoverageOK = true := by decide
set_option maxRecDepth 10000 in
private theorem lowerAccumulator_ok : lowerAccumulatorOK = true := by decide
set_option maxRecDepth 10000 in
private theorem upperAccumulator_ok : upperAccumulatorOK = true := by decide

theorem row_bounds (row : Row) (hrow : row ∈ rows) : RowBounds row := by
  have get {p : Row → Prop} [DecidablePred p]
      (h : rows.all (fun x => decide (p x)) = true) : p row :=
    of_decide_eq_true ((List.all_eq_true.mp h) row hrow)
  exact ⟨get rootCapLower_ok, get rootCapUpper_ok,
    get segLenLower_ok, get segLenUpper_ok, get loLower_ok,
    get endpointUpper_ok, get mainCountUpper_ok, get markStepsUpper_ok,
    get rootCoverage_ok, get lowerAccumulator_ok, get upperAccumulator_ok⟩

/-- All remaining word and allocation premises follow symbolically from the
small manifest bounds.  The modular base jump is proved algebraically; no
row-sized computation or prime enumeration is hidden in this theorem. -/
theorem row_scalar (row : Row) (hrow : row ∈ rows) : RowScalar row := by
  rcases row_bounds row hrow with
    ⟨hrootLo, hrootHi, hsegLo, hsegHi, hlo, hend, hcount,
      hmark, hcover, hSL, hSU⟩
  have hMbig : 1000000000000000000 < M := by decide
  have hM : row.lo + row.segLen < M := by omega
  have hsegM : 1 + row.segLen < M := by omega
  have hloSub : 1 + row.segLen ≤ row.lo := by omega
  have hloDeltaM : row.lo - (1 + row.segLen) < M := by omega
  have hwDelta :
      (row.lo + M - (1 + row.segLen) % M) % M =
        row.lo - (1 + row.segLen) := by
    rw [Nat.mod_eq_of_lt hsegM]
    have hsplit : row.lo + M - (1 + row.segLen) =
        M + (row.lo - (1 + row.segLen)) := by omega
    rw [hsplit, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hloDeltaM
  have hbase :
      (1 + ((row.segLen +
        (row.lo + M - (1 + row.segLen) % M) % M) % M)) % M = row.lo := by
    rw [hwDelta]
    have hsum : row.segLen + (row.lo - (1 + row.segLen)) = row.lo - 1 := by
      omega
    have hpredM : row.lo - 1 < M := by omega
    have hloM : row.lo < M := by omega
    rw [hsum, Nat.mod_eq_of_lt hpredM]
    have hsucc : 1 + (row.lo - 1) = row.lo := by omega
    rw [hsucc, Nat.mod_eq_of_lt hloM]
  have hrootSq : row.rootCap * row.rootCap < M := by
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hrootHi hrootHi) (by decide)
  have hcountProduct : (1000 + 1) * (row.rootCap + 1) < M := by
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (by omega : 1000 + 1 ≤ 1001)
        (Nat.add_le_add_right hrootHi 1)) (by decide)
  have hbootSquare : (1000 + 2) * (1000 + 2) < M := by decide
  have hweightedProduct :
      (row.rootCap + 1) * (row.segLen + 2) < M := by
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (Nat.add_le_add_right hrootHi 1)
        (Nat.add_le_add_right hsegHi 2)) (by decide)
  unfold RowScalar
  dsimp [Row.cfg, Cfg.bootCount, Cfg.rootSpan, Cfg.period, Cfg.rootLen,
    Cfg.wDelta, Cfg.arrayLen, Cfg.resultBase, Cfg.tableLen]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by simpa only [Nat.one_mul] using hbase,
    by omega, hrootSq, by omega, by omega,
    by omega, hcover, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, hcountProduct, hbootSquare, by omega,
    hweightedProduct, by omega⟩

theorem row_core (row : Row) (hrow : row ∈ rows) : RowCore row := by
  have hb := row_bounds row hrow
  unfold RowBounds at hb
  rcases hb with ⟨hrootStrong, _hrootBound, _hsegLower, _hsegBound,
    _hloBound, _hendBound, hmainBound, _hmarkBound, _hcoverBound,
    _hSLBound, _hSUBound⟩
  have hs := row_scalar row hrow
  unfold RowScalar at hs
  rcases hs with ⟨hrootLo, hrootHi, hsegPos, _hsegHi, _hlo, _hend,
    _hcountUpper, hmarkSmall, hbase, hindex, hrootSq, hsegRoot,
    hendpointWord, habove, hcoverage, hthree, hSL, hSU, hendpointBound,
    harrayBytes, hcountPos, hcountM, hcountLoop, hbootSquare,
    hbootCover, hweightedFit, hcountBytes⟩
  exact
    { rootAtLeast1000 := hrootLo
      rootAtLeast1009 := by omega
      segmentPositive := hsegPos
      segmentAtLeastTwo := by omega
      rootBelowSegment := by omega
      rootBootstrapCoverage := by omega
      baseEq := hbase
      indexRoom := hindex
      rootSquareRoom := hrootSq
      segmentRootRoom := hsegRoot
      endpointWordRoom := hendpointWord
      aboveRoot := habove
      rootCoverage := hcoverage
      startAtLeastThree := hthree
      lowerWord := hSL
      upperWord := hSU
      endpointBound := hendpointBound
      arrayBytesRoom := harrayBytes
      mainCountWord := Nat.lt_of_le_of_lt hmainBound (by decide)
      markStepsWord := Nat.lt_trans hmarkSmall (by decide)
      countLengthPositive := hcountPos
      countLengthWord := hcountM
      countLoopWord := by
        exact Nat.lt_of_le_of_lt
          (Nat.mul_le_mul_right (row.rootCap + 1)
            (by decide : 134 + 1 ≤ 1000 + 1)) hcountLoop
      countSieveSquareWord := by decide
      countSieveCoverage := by omega
      bootSquareWord := hbootSquare
      bootCoverage := hbootCover
      weightedProductWord := hweightedFit
      countArrayBytesRoom := hcountBytes }

/-!
There is intentionally no closed `rows.all ... by decide` theorem here.
The former endpoint majorant multiplied the full segment length by `2^48`;
it is false for production-sized segments because only prime-mask cells
advance the ladder.  The exact no-wrap property must therefore be checked by
a compiled prefix-overflow program over the normalized mask and then lifted
through a generic proof.
-/

end LeanCompCert.Ports.RS62CheckpointScalar
