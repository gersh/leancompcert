import LeanCompCert.Ports.R2SegMarkingWindowModel

/-!
# Word bounds for the pure `R₂*` marking window

These invariants discharge the packed-weight and accumulated-logarithm word
premises of the literal marking theorem for an arbitrary symbolic schedule.
They do not evaluate a production cursor or materialize a production window.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-- The three packed fields of an invariant cell occupy less than four
`2^56` lanes.  Reuse the already-proved exact decoder instead of expanding
the bit arithmetic again. -/
private theorem MarkCell.Inv.encode_weights_lt_four {x : MarkCell}
    (hx : x.Inv) : x.encode.weights < 4 * 2 ^ 56 := by
  have hdecode := packWeights_count x.count x.w1 x.w2 hx.2.1 hx.2.2
  have hdiv : x.encode.weights / 2 ^ 56 = x.count := by
    simpa only [MarkCell.encode, PlaneWords.count, Nat.shiftRight_eq_div_pow]
      using hdecode
  have hcount : x.count ≤ 3 := hx.1.1
  have hq : x.encode.weights / 2 ^ 56 < 4 := by
    rw [hdiv]
    omega
  exact Nat.lt_mul_of_div_lt hq (Nat.two_pow_pos 56)

/-- One packed weight update occupies less than two `2^56` lanes. -/
private theorem markWeightAdd_lt_two_lanes (d wt : Nat) (hd : d ≤ 3)
    (hwt : wt < 2 ^ wtBits) : markWeightAdd d wt < 2 * 2 ^ 56 := by
  have hp : 2 ^ wtBits < 2 ^ 56 := by
    simp only [wtBits]
    decide
  have hmul : wt * 2 ^ wtBits < 2 ^ 56 := by
    calc
      wt * 2 ^ wtBits < 2 ^ wtBits * 2 ^ wtBits :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos wtBits)).2 hwt
      _ = 2 ^ 56 := by simp [wtBits, ← Nat.pow_add]
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [markWeightAdd, markBit, Nat.shiftLeft_eq] <;> omega

/-- The encoded packed word of an invariant cell has enough room for one
more base-prime weight update. -/
theorem MarkCell.Inv.encode_weights_add_markWeightAdd_lt
    {x : MarkCell} (hx : x.Inv) (wt : Nat) (first : Bool)
    (hwt : wt < 2 ^ wtBits) :
    x.encode.weights + (if first then markWeightAdd x.count wt else 0) < M := by
  have henc := hx.encode_weights_lt_four
  have hadd := markWeightAdd_lt_two_lanes x.count wt hx.1.1 hwt
  have hcap : 6 * 2 ^ 56 < M := by
    simp only [M]
    decide
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Nat.lt_trans henc (Nat.lt_of_lt_of_le (by
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos 56)).2 (by decide : 4 < 6))
      (Nat.le_of_lt hcap))
  · simp only [Bool.true_eq, ↓reduceIte]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add henc hadd) (Nat.le_of_lt hcap)

private theorem MarkCell.markPower_lsum (x : MarkCell) (p wt : Nat)
    (first : Bool) : (x.markPower p wt first).lsum = x.lsum + wt := by
  cases first
  · rfl
  · by_cases h0 : x.count = 0
    · simp [MarkCell.markPower, h0]
    · by_cases h1 : x.count = 1
      · simp [MarkCell.markPower, h0, h1]
      · by_cases h2 : x.count = 2 <;>
          simp [MarkCell.markPower, h0, h1, h2]

/-- Pointwise packed-field invariant for a logical marking window. -/
def R2MarkWindow.CellsInv (w : R2MarkWindow) : Prop :=
  ∀ i, (w.cells i).Inv

/-- Uniform upper bound on the accumulated fixed logarithm in every cell. -/
def R2MarkWindow.LsumBound (w : R2MarkWindow) (bound : Nat) : Prop :=
  ∀ i, (w.cells i).lsum ≤ bound

/-- The source-shaped arithmetic condition for the current resident hit: the
next accumulated small-prime factor still divides into the represented
candidate range.  The later number-theoretic cursor proof establishes this;
the machine seam only needs its immediate inequality consequence. -/
def R2MarkWindow.ResidentProductReady (c : R2Cfg) (windowBase : Nat)
    (w : R2MarkWindow) : Prop :=
  w.cursor.offset < c.segLen →
    ((w.cells w.cursor.offset).prod +
      markBit ((w.cells w.cursor.offset).prod = 0)) * w.cursor.base ≤
        windowBase + w.cursor.offset

theorem R2MarkWindow.CellsInv.step {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {w : R2MarkWindow}
    (hinv : w.CellsInv) (hcursor : w.cursor.Bounds c) :
    (w.step c windowBase tableWord).CellsInv := by
  intro i
  by_cases hresident : w.cursor.offset < c.segLen
  · rw [R2MarkWindow.step_cells_resident hresident]
    by_cases hi : i = w.cursor.offset
    · subst i
      simp only [updateCell, if_pos rfl]
      exact (hinv w.cursor.offset).markPower w.cursor.base w.cursor.weight
        (w.cursor.first = 1) hcursor.weight_lt
    · simp only [updateCell, if_neg hi]
      exact hinv i
  · rw [R2MarkWindow.step_cells_past (Nat.le_of_not_gt hresident)]
    exact hinv i

theorem R2MarkWindow.CellsInv.run (fuel : Nat) {c : R2Cfg}
    {windowBase : Nat} {tableWord : Nat → Nat} {w : R2MarkWindow}
    (hinv : w.CellsInv) (hcursor : w.cursor.Bounds c)
    (htable : R2MarkTableBounds c tableWord) (hhi : 0 < c.hi) :
    (w.run fuel c windowBase tableWord).CellsInv := by
  induction fuel with
  | zero => exact hinv
  | succ fuel ih =>
      apply R2MarkWindow.CellsInv.step ih
      exact w.run_cursor_bounds fuel hcursor htable hhi

theorem R2MarkWindow.LsumBound.step {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {w : R2MarkWindow} {bound : Nat}
    (hbound : w.LsumBound bound) (hcursor : w.cursor.Bounds c) :
    (w.step c windowBase tableWord).LsumBound (bound + 2 ^ wtBits) := by
  intro i
  by_cases hresident : w.cursor.offset < c.segLen
  · rw [R2MarkWindow.step_cells_resident hresident]
    by_cases hi : i = w.cursor.offset
    · subst i
      simp only [updateCell, if_true]
      rw [MarkCell.markPower_lsum]
      have hcell := hbound w.cursor.offset
      have hwt := hcursor.weight_lt
      omega
    · simp only [updateCell, if_neg hi]
      exact Nat.le_trans (hbound i) (Nat.le_add_right bound (2 ^ wtBits))
  · rw [R2MarkWindow.step_cells_past (Nat.le_of_not_gt hresident)]
    exact Nat.le_trans (hbound i) (Nat.le_add_right bound (2 ^ wtBits))

/-- After `fuel` symbolic marking rounds, no cell's log plane can exceed one
full weight lane per round.  This intentionally crude bound is still far
below `2^64` for the production budget. -/
theorem R2MarkWindow.LsumBound.run (fuel : Nat) {c : R2Cfg}
    {windowBase : Nat} {tableWord : Nat → Nat} {w : R2MarkWindow}
    {bound : Nat} (hbound : w.LsumBound bound)
    (hcursor : w.cursor.Bounds c) (htable : R2MarkTableBounds c tableWord)
    (hhi : 0 < c.hi) :
    (w.run fuel c windowBase tableWord).LsumBound
      (bound + fuel * 2 ^ wtBits) := by
  induction fuel with
  | zero => exact hbound
  | succ fuel ih =>
      have hs := R2MarkWindow.LsumBound.step
        (windowBase := windowBase) (tableWord := tableWord) ih
        (w.run_cursor_bounds fuel hcursor htable hhi)
      change R2MarkWindow.LsumBound
        ((w.run fuel c windowBase tableWord).step c windowBase tableWord)
        (bound + (fuel + 1) * 2 ^ wtBits)
      simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
        Nat.add_assoc] using hs

/-- A represented invariant cell automatically supplies the physical packed
weight no-wrap premise required by a resident literal step. -/
theorem R2MarkWindow.Rep.weights_room {c : R2Cfg} {s : AState}
    {w : R2MarkWindow} (hrep : w.Rep c s) (hinv : w.CellsInv)
    (hresident : w.cursor.offset < c.segLen)
    (hcursor : w.cursor.Bounds c) (first : Bool)
    (hfirst : w.cursor.first = if first then 1 else 0) :
    s.arr (w.cursor.offset + 2 * c.segLen) +
      (if first then
        markWeightAdd (w.cells w.cursor.offset).count w.cursor.weight
      else 0) < M := by
  have hloaded := hrep.2 w.cursor.offset hresident
  have hword : s.arr (w.cursor.offset + 2 * c.segLen) =
      (w.cells w.cursor.offset).encode.weights := by
    simpa only [planeWordsAt] using congrArg PlaneWords.weights hloaded
  rw [hword]
  exact (hinv w.cursor.offset).encode_weights_add_markWeightAdd_lt
    w.cursor.weight first hcursor.weight_lt

/-- A represented uniform log-plane bound supplies the literal addition
guard for the next resident weight. -/
theorem R2MarkWindow.Rep.lsum_room {c : R2Cfg} {s : AState}
    {w : R2MarkWindow} {bound : Nat} (hrep : w.Rep c s)
    (hbound : w.LsumBound bound) (hresident : w.cursor.offset < c.segLen)
    (hcursor : w.cursor.Bounds c) (hroom : bound + 2 ^ wtBits < M) :
    s.arr (w.cursor.offset + c.segLen) + w.cursor.weight < M := by
  have hloaded := hrep.2 w.cursor.offset hresident
  have hword : s.arr (w.cursor.offset + c.segLen) =
      (w.cells w.cursor.offset).lsum := by
    simpa only [planeWordsAt, MarkCell.encode] using
      congrArg PlaneWords.lsum hloaded
  rw [hword]
  have hlsum := hbound w.cursor.offset
  have hwt := hcursor.weight_lt
  omega

/-- Product readiness plus the explicit candidate ceiling gives the literal
machine-word multiplication guard. -/
theorem R2MarkWindow.Rep.product_room {c : R2Cfg} {s : AState}
    {w : R2MarkWindow} {windowBase ceiling : Nat} (hrep : w.Rep c s)
    (hready : w.ResidentProductReady c windowBase)
    (hresident : w.cursor.offset < c.segLen)
    (hcandidate : windowBase + w.cursor.offset ≤ ceiling)
    (hceiling : ceiling < M) :
    (s.arr w.cursor.offset + markBit (s.arr w.cursor.offset = 0)) *
      w.cursor.base < M := by
  have hloaded := hrep.2 w.cursor.offset hresident
  have hword : s.arr w.cursor.offset = (w.cells w.cursor.offset).prod := by
    simpa only [planeWordsAt, MarkCell.encode] using
      congrArg PlaneWords.prod hloaded
  rw [hword]
  exact Nat.lt_of_le_of_lt (hready hresident)
    (Nat.lt_of_le_of_lt hcandidate hceiling)

#print axioms MarkCell.Inv.encode_weights_add_markWeightAdd_lt
#print axioms R2MarkWindow.CellsInv.step
#print axioms R2MarkWindow.CellsInv.run
#print axioms R2MarkWindow.LsumBound.step
#print axioms R2MarkWindow.LsumBound.run
#print axioms R2MarkWindow.Rep.weights_room
#print axioms R2MarkWindow.Rep.lsum_room
#print axioms R2MarkWindow.Rep.product_room

end LeanCompCert.Ports.R2SegSieve
