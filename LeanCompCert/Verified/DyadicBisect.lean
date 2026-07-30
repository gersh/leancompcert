import LeanCompCert.Verified.Dyadic
import LeanCompCert.Verified.SqrtEquiv

/-!
# Interval bisection in dyadic fixed point

`Verified/Dyadic.lean` gives the scalar layer: mantissas at a static binary
precision `p`, with `add`/`sub` exact and `mul`/`div` rounded **outward**, every
bound stated cross-multiplied over `Nat`.  This module adds the three things an
interval-bisection certificate needs on top of it, and nothing else:

* **a grid** — the `2^depth` cells of `[a, b]`, with each cell's endpoints
  rounded outward (left endpoint down, right endpoint up), so a cell is always a
  *superset* of the exact cell it stands for, and consecutive cells overlap
  (`Grid.chain`).  Overlap plus monotonicity is a cover (`chain_cover`);
* **a square root** — `sqrtI`, floor of `Nat.sqrt` below and `+1` above, whose
  correctness is the pair of squared inequalities `lo² ≤ m·2^p < hi²`.  That is
  the cross-multiplied form of `lo/2^p ≤ √(m/2^p) ≤ hi/2^p`, and it pins the
  root without ever naming a real number: squaring is monotone on any ordered
  ring, so a consumer's step from here is one `Real.sqrt` monotonicity lemma;
* **a checked square root** — `sqrtOK`, which takes *any* pair of candidate
  mantissas and verifies the same two inequalities.  A guessed root that passes
  the check is as sound as a computed one, which is what lets the emitted
  artifact use a fixed-shape Newton iteration and prove nothing about it.

## Outward, never inward

Every rounding in this file is away from the enclosed value:

| quantity | rounding | why it is outward |
| --- | --- | --- |
| `Grid.loM` | floor | moves the left endpoint left, enlarging the cell |
| `Grid.hiM` | ceiling | moves the right endpoint right, enlarging the cell |
| `sqrtI.lo` | `Nat.sqrt` (floor) | under-estimates the root |
| `sqrtI.hi` | `Nat.sqrt + 1` | over-estimates the root |

`Dyadic.mulLo`/`mulHi` and `divLo`/`divHi` are outward for the same reason, and
that is proved there.  A rounding in the other direction would shrink the
enclosure and could turn a false claim into a passing certificate; none is used,
and each of the four theorems below states the direction explicitly so a
reviewer can check it without reading the definitions.

## Size independence

Nothing here mentions the depth except `allBelow`, whose characterisation
`allBelow_iff` is proved for every `n` at once.  The cover lemma `chain_cover`
is likewise an induction over the number of cells, so instantiating at depth 8
and at depth 24 is the same theorem.
-/

namespace LeanCompCert.Verified.DyadicBisect

open LeanCompCert.Verified.Dyadic

/-! ### Constants -/

/-- The degenerate interval holding the integer `k` exactly. -/
def constD (p k : Nat) : DInt p := ⟨k * 2 ^ p, k * 2 ^ p⟩

theorem constD_wf (p k : Nat) : (constD p k).WF := Nat.le_refl _

/-! ### The cell grid

A grid is the arithmetic progression `(base + step·i) / den`, `i = 0, …, n`.
Cell `i` spans grid points `i` and `i+1`.  Both endpoints are converted to
precision-`p` mantissas with directed rounding.
-/

/-- The endpoints of a uniform grid: point `i` is the rational
`(base + step·i) / den`. -/
structure Grid where
  den : Nat
  base : Nat
  step : Nat

namespace Grid

variable (g : Grid) (p : Nat)

/-- Exact numerator of grid point `i` scaled to precision `p`. -/
def pointN (i : Nat) : Nat := 2 ^ p * (g.base + g.step * i)

/-- Cell `i`'s left mantissa: grid point `i`, rounded **down**. -/
def loM (i : Nat) : Nat := g.pointN p i / g.den

/-- Cell `i`'s right mantissa: grid point `i+1`, rounded **up**. -/
def hiM (i : Nat) : Nat := (g.pointN p (i + 1) + g.den - 1) / g.den

/-- Cell `i` as a dyadic interval. -/
def cell (i : Nat) : DInt p := ⟨g.loM p i, g.hiM p i⟩

variable {g p}

theorem pointN_mono {i j : Nat} (h : i ≤ j) : g.pointN p i ≤ g.pointN p j :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _)

/-- The left endpoint is rounded down: `loM i · den ≤ pointN i`. -/
theorem loM_mul_le (i : Nat) : g.loM p i * g.den ≤ g.pointN p i :=
  floor_mul_le _ _

/-- The right endpoint is rounded up: `pointN (i+1) ≤ hiM i · den`. -/
theorem le_hiM_mul (hd : 0 < g.den) (i : Nat) :
    g.pointN p (i + 1) ≤ g.hiM p i * g.den :=
  le_ceil_mul _ _ hd

/-- `loM` is monotone in the cell index. -/
theorem loM_mono {i j : Nat} (h : i ≤ j) : g.loM p i ≤ g.loM p j :=
  Nat.div_le_div_right (pointN_mono h)

/-- Consecutive cells overlap: the next cell starts at or before this one ends.
Both sides round the *same* exact grid point `i+1`, one down and one up. -/
theorem chain (hd : 0 < g.den) (i : Nat) : g.loM p (i + 1) ≤ g.hiM p i :=
  floor_le_ceil _ _ hd

/-- A cell is nonempty. -/
theorem cell_wf (hd : 0 < g.den) (i : Nat) : (g.cell p i).WF :=
  Nat.le_trans (loM_mono (Nat.le_succ i)) (chain hd i)

end Grid

/-! ### Overlapping chains cover

The purely combinatorial half of "the cells cover `[a, b]`": a monotone chain of
intervals whose successor starts no later than the predecessor ends has no gaps.
Stated over `Nat` mantissas; a consumer working over an ordered field repeats
the same three-line induction with its own order.
-/

theorem chain_cover (lo hi : Nat → Nat)
    (hchain : ∀ i, lo (i + 1) ≤ hi i) :
    ∀ (n m : Nat), lo 0 ≤ m → m ≤ hi n → ∃ i, i ≤ n ∧ lo i ≤ m ∧ m ≤ hi i := by
  intro n
  induction n with
  | zero => intro m h0 h1; exact ⟨0, Nat.le_refl _, h0, h1⟩
  | succ k ih =>
      intro m h0 h1
      by_cases hk : m ≤ hi k
      · obtain ⟨i, hik, hlo, hhi⟩ := ih m h0 hk
        exact ⟨i, Nat.le_succ_of_le hik, hlo, hhi⟩
      · refine ⟨k + 1, Nat.le_refl _, ?_, h1⟩
        exact Nat.le_of_not_le fun hc =>
          hk (Nat.le_trans hc (hchain k))

/-! ### Outward square root

`√(m / 2^p)` has precision-`p` mantissa `μ` with `μ² = m · 2^p`.  So an
enclosure of the root is exactly a pair `lo ≤ μ ≤ hi`, and by monotonicity of
squaring on nonnegatives that is the pair of `Nat` inequalities
`lo² ≤ m·2^p < hi²`.  No real number appears.
-/

/-- The outward square root of an interval: floor below, floor `+ 1` above. -/
def sqrtI {p : Nat} (x : DInt p) : DInt p :=
  ⟨Nat.sqrt (x.lo * 2 ^ p), Nat.sqrt (x.hi * 2 ^ p) + 1⟩

theorem sqrtI_wf {p : Nat} {x : DInt p} (hx : x.WF) : (sqrtI x).WF := by
  have h : Nat.sqrt (x.lo * 2 ^ p) ≤ Nat.sqrt (x.hi * 2 ^ p) :=
    SqrtEquiv.le_sqrt_of_sq_le
      (Nat.le_trans (Nat.sqrt_le _) (Nat.mul_le_mul_right _ hx))
  exact Nat.le_trans h (Nat.le_succ _)

/-- **Lower root is outward**: the returned lower mantissa squares to at most
the scaled radicand, for every mantissa `m` enclosed by `x`. -/
theorem sqrtI_lo_sq_le {p : Nat} {x : DInt p} {m : Nat} (h : x.mem m) :
    (sqrtI x).lo * (sqrtI x).lo ≤ m * 2 ^ p :=
  Nat.le_trans (Nat.sqrt_le _) (Nat.mul_le_mul_right _ h.1)

/-- **Upper root is outward**: the scaled radicand is strictly below the square
of the returned upper mantissa, for every mantissa `m` enclosed by `x`. -/
theorem sqrtI_lt_hi_sq {p : Nat} {x : DInt p} {m : Nat} (h : x.mem m) :
    m * 2 ^ p < (sqrtI x).hi * (sqrtI x).hi :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h.2) (Nat.lt_succ_sqrt _)

/-- The two halves together: the root's mantissa is bracketed. -/
theorem sqrtI_encloses {p : Nat} {x : DInt p} {m : Nat} (h : x.mem m) :
    (sqrtI x).lo * (sqrtI x).lo ≤ m * 2 ^ p ∧
      m * 2 ^ p < (sqrtI x).hi * (sqrtI x).hi :=
  ⟨sqrtI_lo_sq_le h, sqrtI_lt_hi_sq h⟩

/-! ### Checked square root

The emitted artifact cannot afford `Nat.sqrt`'s data-dependent clamp loop, and
does not need it: it may guess the two mantissas by any fixed-shape iteration
and then *verify* the same two inequalities.  Soundness rests on the check
alone, so the iteration needs no proof at all — only the check is trusted, and
the check is one multiply and one comparison per side.
-/

/-- The verification predicate for a guessed root pair `(s, t)` of `x`. -/
def sqrtOK {p : Nat} (x : DInt p) (s t : Nat) : Bool :=
  (s * s ≤ x.lo * 2 ^ p) && (x.hi * 2 ^ p < t * t) && (s ≤ t)

/-- A guessed root that passes `sqrtOK` encloses the true root of every
mantissa in `x`, with exactly the bracket `sqrtI` would have given. -/
theorem sqrtOK_encloses {p : Nat} {x : DInt p} {m s t : Nat}
    (hck : sqrtOK x s t = true) (h : x.mem m) :
    s * s ≤ m * 2 ^ p ∧ m * 2 ^ p < t * t := by
  simp only [sqrtOK, Bool.and_eq_true, decide_eq_true_eq] at hck
  exact ⟨Nat.le_trans hck.1.1 (Nat.mul_le_mul_right _ h.1),
         Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h.2) hck.1.2⟩

/-- A checked root pair is a well-formed interval. -/
theorem sqrtOK_wf {p : Nat} {x : DInt p} {s t : Nat}
    (hck : sqrtOK x s t = true) : (⟨s, t⟩ : DInt p).WF := by
  simp only [sqrtOK, Bool.and_eq_true, decide_eq_true_eq] at hck
  exact hck.2

/-! ### The sweep

A uniform-depth bisection lower-bound certificate is a conjunction over the
`2^depth` leaves, and nothing more: the hull's lower endpoint is the minimum of
the leaves' lower endpoints, so `c ≤ hull.lo` iff `c ≤ leaf.lo` for every leaf.
That is why the whole family is a flat fold and needs no tree at all.
-/

/-- Every index below `n` passes `f`. -/
def allBelow (n : Nat) (f : Nat → Bool) : Bool := (List.range n).all f

theorem allBelow_iff (n : Nat) (f : Nat → Bool) :
    allBelow n f = true ↔ ∀ i, i < n → f i = true := by
  simp [allBelow, List.all_eq_true, List.mem_range]

/-- The fold form, which is what a register program computes: accumulate the
conjunction one leaf at a time. -/
def sweepFold (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i => if f i then acc else 1) 0

theorem sweepFold_eq_zero_iff (n : Nat) (f : Nat → Bool) :
    sweepFold n f = 0 ↔ ∀ i, i < n → f i = true := by
  have key : ∀ (l : List Nat) (a : Nat),
      (l.foldl (fun acc i => if f i then acc else 1) a = 0) ↔
        (a = 0 ∧ ∀ i ∈ l, f i = true) := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x xs ih =>
        intro a
        by_cases hx : f x
        · simp only [List.foldl_cons, hx, if_pos, List.mem_cons]
          rw [ih]
          constructor
          · rintro ⟨ha, hall⟩
            refine ⟨ha, ?_⟩
            rintro i (rfl | hi)
            · exact hx
            · exact hall i hi
          · rintro ⟨ha, hall⟩
            exact ⟨ha, fun i hi => hall i (Or.inr hi)⟩
        · simp only [List.foldl_cons, hx, if_neg, Bool.false_eq_true, not_false_eq_true]
          rw [ih]
          simp only [List.mem_cons]
          constructor
          · rintro ⟨h1, _⟩; exact absurd h1 (by omega)
          · rintro ⟨_, hall⟩
            exact absurd (hall x (Or.inl rfl)) (by simp [hx])
  simp [sweepFold, key, List.mem_range]

end LeanCompCert.Verified.DyadicBisect
