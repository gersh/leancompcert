/-
Dyadic fixed-point interval layer (roadmap M2).

Dyadic numbers are modeled as `Nat` mantissas at a static binary precision
`p`: a mantissa `m` denotes the value `m / 2 ^ p`.  All correctness
statements are phrased over `Nat` in cross-multiplied form — the value
comparison `a / 2 ^ p ≤ b / 2 ^ q` becomes the `Nat` inequality
`a * 2 ^ q ≤ b * 2 ^ p` — so every proof stays inside linear arithmetic
over `Nat` (`omega` plus core division/modulus facts); no `Rat` arithmetic
lemmas are needed, and the statements are exactly the rational enclosures
after clearing denominators.

Scalar operations at precision `p`:
* `addD` — mantissa addition, exact at a common precision;
* `subD` — mantissa subtraction, `Nat`-truncated at zero, exact under the
  documented ordering hypothesis (`subD_exact`);
* `mulLo` / `mulHi` — the `2p`-precision product rounded back to precision
  `p`, downward resp. upward;
* `divLo` / `divHi` — the quotient scaled to precision `p`, rounded
  downward resp. upward.

Machine-checked enclosures (cross-multiplied against exact semantics):
* `mulLo_le` / `mulHi_ge` : `mulLo p a b * 2^p ≤ a*b ≤ mulHi p a b * 2^p`,
  i.e. the exact product of values `(a/2^p) * (b/2^p)` lies in the interval
  `[mulLo/2^p, mulHi/2^p]`;
* `divLo_le` / `divHi_ge` : `divLo p a b * b ≤ a * 2^p ≤ divHi p a b * b`,
  i.e. the exact quotient of values `(a/2^p) / (b/2^p) = a/b` lies in
  `[divLo/2^p, divHi/2^p]`;
* `mulLo_le_mulHi` / `divLo_le_divHi` — the rounded bounds are ordered.

`DInt p` packages a lower and an upper mantissa into an interval with
well-formedness `WF := lo ≤ hi`, and the four interval operations
(`add` exact, `sub` truncated-at-zero, `mul` / `div` outward-rounded)
preserve `WF` (`add_wf`, `sub_wf`, `mul_wf`, `div_wf`) and enclose the
corresponding exact operation on any enclosed mantissas (`add_encloses`,
`sub_encloses` — sound for `Nat`-truncated subtraction unconditionally, and
exact subtraction once the intervals are ordered (`sub_no_truncation`) —
`mul_encloses`, `div_encloses`).

A fixed-round Newton reciprocal is intentionally NOT included here: the
directed division `divLo` / `divHi` above already discharges the roadmap
item ("add/sub/mul/div with directed rounding at a static precision"), and
the repository separately provides a proved wide division routine.
-/

namespace LeanCompCert.Verified.Dyadic

/-! ### Directed-rounding division bounds over `Nat`

The two workhorse facts: floor division under-approximates and the
`(n + d - 1) / d` ceiling over-approximates, both stated multiplicatively so
that all downstream enclosures are `Nat.le_trans` chains. -/

/-- Floor bound: `n / d * d ≤ n` (holds for every `d`, including `0`). -/
theorem floor_mul_le (n d : Nat) : n / d * d ≤ n :=
  Nat.div_mul_le_self n d

/-- Ceiling bound: `n ≤ (n + d - 1) / d * d` for `0 < d`.  From
`Nat.div_add_mod` and `mod < d`, with the division and modulus terms treated
as atoms, the inequality is linear and `omega` closes it. -/
theorem le_ceil_mul (n d : Nat) (hd : 0 < d) : n ≤ (n + d - 1) / d * d := by
  have hdm := Nat.div_add_mod (n + d - 1) d
  have hlt : (n + d - 1) % d < d := Nat.mod_lt _ hd
  rw [Nat.mul_comm]
  omega

/-- The floor rounding never exceeds the ceiling rounding. -/
theorem floor_le_ceil (n d : Nat) (hd : 0 < d) : n / d ≤ (n + d - 1) / d :=
  Nat.div_le_div_right (by omega)

/-! ### Scalar dyadic operations at static precision `p` -/

/-- Mantissa addition; exact at a common precision `p` since
`a/2^p + b/2^p = (a + b)/2^p`. -/
def addD (a b : Nat) : Nat := a + b

/-- Mantissa subtraction, truncated at zero by `Nat` subtraction.  Exact
when `b ≤ a` (see `subD_exact`); otherwise it clamps to `0`, which is still
a valid lower bound for a nonnegative quantity. -/
def subD (a b : Nat) : Nat := a - b

/-- Product mantissa rounded down: the exact product of `a/2^p` and `b/2^p`
is `a*b / 2^(2p)`, so at precision `p` its mantissa is `a*b / 2^p`, floored. -/
def mulLo (p a b : Nat) : Nat := a * b / 2 ^ p

/-- Product mantissa rounded up (ceiling division by `2^p`). -/
def mulHi (p a b : Nat) : Nat := (a * b + 2 ^ p - 1) / 2 ^ p

/-- Quotient mantissa rounded down: the exact quotient of `a/2^p` by `b/2^p`
is `a/b`, whose precision-`p` mantissa is `a * 2^p / b`, floored.
(Meaningful for `b ≠ 0`; at `b = 0` `Nat` division returns `0`.) -/
def divLo (p a b : Nat) : Nat := a * 2 ^ p / b

/-- Quotient mantissa rounded up (ceiling division by `b`). -/
def divHi (p a b : Nat) : Nat := (a * 2 ^ p + b - 1) / b

/-- Addition of mantissas is exact. -/
theorem addD_exact (a b : Nat) : addD a b = a + b := rfl

/-- Subtraction of mantissas is exact under the ordering hypothesis
`b ≤ a` (stated additively to stay inside `Nat`). -/
theorem subD_exact (a b : Nat) (h : b ≤ a) : b + subD a b = a := by
  unfold subD
  omega

/-- Lower enclosure for multiplication, cross-multiplied:
`mulLo p a b * 2^p ≤ a * b`, i.e. `mulLo p a b / 2^p ≤ (a/2^p) * (b/2^p)`
after clearing the denominator `2^(2p)`. -/
theorem mulLo_le (p a b : Nat) : mulLo p a b * 2 ^ p ≤ a * b := by
  unfold mulLo
  exact floor_mul_le (a * b) (2 ^ p)

/-- Upper enclosure for multiplication, cross-multiplied:
`a * b ≤ mulHi p a b * 2^p`, i.e. `(a/2^p) * (b/2^p) ≤ mulHi p a b / 2^p`
after clearing the denominator `2^(2p)`. -/
theorem mulHi_ge (p a b : Nat) : a * b ≤ mulHi p a b * 2 ^ p := by
  unfold mulHi
  exact le_ceil_mul (a * b) (2 ^ p) (Nat.two_pow_pos p)

/-- The rounded product bounds are ordered: `mulLo p a b ≤ mulHi p a b`. -/
theorem mulLo_le_mulHi (p a b : Nat) : mulLo p a b ≤ mulHi p a b := by
  unfold mulLo mulHi
  exact floor_le_ceil (a * b) (2 ^ p) (Nat.two_pow_pos p)

/-- Lower enclosure for division, cross-multiplied:
`divLo p a b * b ≤ a * 2^p`, i.e. `divLo p a b / 2^p ≤ a / b` after
cross-multiplying (no hypothesis on `b` is needed: at `b = 0` the left side
is `0`). -/
theorem divLo_le (p a b : Nat) : divLo p a b * b ≤ a * 2 ^ p := by
  unfold divLo
  exact floor_mul_le (a * 2 ^ p) b

/-- Upper enclosure for division, cross-multiplied:
`a * 2^p ≤ divHi p a b * b` for `b ≠ 0`, i.e. `a / b ≤ divHi p a b / 2^p`
after cross-multiplying. -/
theorem divHi_ge (p a b : Nat) (hb : b ≠ 0) : a * 2 ^ p ≤ divHi p a b * b := by
  unfold divHi
  exact le_ceil_mul (a * 2 ^ p) b (Nat.pos_of_ne_zero hb)

/-- The rounded quotient bounds are ordered: `divLo p a b ≤ divHi p a b`
for `b ≠ 0`. -/
theorem divLo_le_divHi (p a b : Nat) (hb : b ≠ 0) :
    divLo p a b ≤ divHi p a b := by
  unfold divLo divHi
  exact floor_le_ceil (a * 2 ^ p) b (Nat.pos_of_ne_zero hb)

/-! ### The interval layer -/

/-- A dyadic interval at static precision `p`: mantissas `lo` and `hi`
denote the value interval `[lo / 2^p, hi / 2^p]`. -/
structure DInt (p : Nat) where
  lo : Nat
  hi : Nat

namespace DInt

variable {p : Nat}

/-- Well-formedness: the interval is nonempty, `lo ≤ hi`. -/
def WF (x : DInt p) : Prop := x.lo ≤ x.hi

/-- A mantissa `m` (denoting the value `m / 2^p`) lies in the interval. -/
def mem (x : DInt p) (m : Nat) : Prop := x.lo ≤ m ∧ m ≤ x.hi

/-- Interval addition; exact endpoint-wise at a common precision. -/
def add (x y : DInt p) : DInt p := ⟨x.lo + y.lo, x.hi + y.hi⟩

/-- Interval subtraction, `Nat`-truncated at zero:
`[lo₁ - hi₂, hi₁ - lo₂]`.  This is the standard outward interval
subtraction; because both the endpoints and the enclosed values use the
same truncated `Nat` subtraction, it is unconditionally sound for the
truncated difference (`sub_encloses`), and once the intervals are ordered
(`y.hi ≤ x.lo`) the truncated difference coincides with the exact one
(`sub_no_truncation`). -/
def sub (x y : DInt p) : DInt p := ⟨x.lo - y.hi, x.hi - y.lo⟩

/-- Interval multiplication with outward rounding (nonnegative operands, so
the product of lower bounds bounds below and of upper bounds above). -/
def mul (x y : DInt p) : DInt p := ⟨mulLo p x.lo y.lo, mulHi p x.hi y.hi⟩

/-- Interval division with outward rounding: smallest numerator over the
largest denominator below, largest numerator over the smallest denominator
above. -/
def div (x y : DInt p) : DInt p := ⟨divLo p x.lo y.hi, divHi p x.hi y.lo⟩

/-- `add` preserves well-formedness. -/
theorem add_wf {x y : DInt p} (hx : x.WF) (hy : y.WF) : (x.add y).WF :=
  Nat.add_le_add hx hy

/-- `sub` preserves well-formedness (truncation at zero only ever raises
the lower endpoint to `0`). -/
theorem sub_wf {x y : DInt p} (hx : x.WF) (hy : y.WF) : (x.sub y).WF := by
  have h1 : x.lo ≤ x.hi := hx
  have h2 : y.lo ≤ y.hi := hy
  show x.lo - y.hi ≤ x.hi - y.lo
  omega

/-- `mul` preserves well-formedness. -/
theorem mul_wf {x y : DInt p} (hx : x.WF) (hy : y.WF) : (x.mul y).WF := by
  have hx' : x.lo ≤ x.hi := hx
  have hy' : y.lo ≤ y.hi := hy
  show mulLo p x.lo y.lo ≤ mulHi p x.hi y.hi
  have h1 : mulLo p x.lo y.lo ≤ mulLo p x.hi y.hi := by
    unfold mulLo
    exact Nat.div_le_div_right (Nat.mul_le_mul hx' hy')
  exact Nat.le_trans h1 (mulLo_le_mulHi p x.hi y.hi)

/-- `div` preserves well-formedness when the denominator interval is
positive (`y.lo ≠ 0`, hence by `y.WF` also `y.hi ≠ 0`). -/
theorem div_wf {x y : DInt p} (hx : x.WF) (hy : y.WF) (h0 : y.lo ≠ 0) :
    (x.div y).WF := by
  have hx' : x.lo ≤ x.hi := hx
  have hy' : y.lo ≤ y.hi := hy
  have hlo : 0 < y.lo := Nat.pos_of_ne_zero h0
  show divLo p x.lo y.hi ≤ divHi p x.hi y.lo
  have h1 : divLo p x.lo y.hi ≤ divLo p x.hi y.lo := by
    unfold divLo
    have hnum : x.lo * 2 ^ p / y.hi ≤ x.hi * 2 ^ p / y.hi :=
      Nat.div_le_div_right (Nat.mul_le_mul hx' (Nat.le_refl _))
    have hden : x.hi * 2 ^ p / y.hi ≤ x.hi * 2 ^ p / y.lo :=
      Nat.div_le_div_left hy' hlo
    exact Nat.le_trans hnum hden
  exact Nat.le_trans h1 (divLo_le_divHi p x.hi y.lo h0)

/-- Enclosure for `add`: exact endpoint-wise, so membership is preserved on
the nose. -/
theorem add_encloses {x y : DInt p} {a b : Nat}
    (ha : x.mem a) (hb : y.mem b) : (x.add y).mem (a + b) :=
  ⟨Nat.add_le_add ha.1 hb.1, Nat.add_le_add ha.2 hb.2⟩

/-- Enclosure for `sub` with respect to the truncated `Nat` difference:
for any enclosed mantissas `a ∈ x`, `b ∈ y`, the truncated difference
`a - b` lies in `x.sub y`.  (Relative to exact rational subtraction this is
the one-sided guarantee that holds for `Nat` mantissas; see
`sub_no_truncation` for when it is the exact difference.) -/
theorem sub_encloses {x y : DInt p} {a b : Nat}
    (ha : x.mem a) (hb : y.mem b) : (x.sub y).mem (a - b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  show x.lo - y.hi ≤ a - b ∧ a - b ≤ x.hi - y.lo
  exact ⟨by omega, by omega⟩

/-- When the intervals are ordered (`y.hi ≤ x.lo`), no truncation occurs:
the truncated difference of enclosed mantissas is the exact difference
(stated additively, `b + (a - b) = a`). -/
theorem sub_no_truncation {x y : DInt p} {a b : Nat}
    (ha : x.mem a) (hb : y.mem b) (hord : y.hi ≤ x.lo) :
    b + (a - b) = a := by
  obtain ⟨ha1, _⟩ := ha
  obtain ⟨_, hb2⟩ := hb
  omega

/-- Enclosure for `mul`, cross-multiplied: for enclosed mantissas
`a ∈ x`, `b ∈ y`, the exact product value `(a/2^p) * (b/2^p)` lies in
`x.mul y`, i.e. `(x.mul y).lo * 2^p ≤ a*b ≤ (x.mul y).hi * 2^p` after
clearing the denominator `2^(2p)`. -/
theorem mul_encloses {x y : DInt p} {a b : Nat}
    (ha : x.mem a) (hb : y.mem b) :
    (x.mul y).lo * 2 ^ p ≤ a * b ∧ a * b ≤ (x.mul y).hi * 2 ^ p := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  show mulLo p x.lo y.lo * 2 ^ p ≤ a * b ∧ a * b ≤ mulHi p x.hi y.hi * 2 ^ p
  constructor
  · exact Nat.le_trans (mulLo_le p x.lo y.lo) (Nat.mul_le_mul ha1 hb1)
  · exact Nat.le_trans (Nat.mul_le_mul ha2 hb2) (mulHi_ge p x.hi y.hi)

/-- Enclosure for `div`, cross-multiplied: for enclosed mantissas
`a ∈ x`, `b ∈ y` with a positive denominator interval (`y.lo ≠ 0`), the
exact quotient value `(a/2^p) / (b/2^p) = a/b` lies in `x.div y`, i.e.
`(x.div y).lo * b ≤ a * 2^p ≤ (x.div y).hi * b` after cross-multiplying. -/
theorem div_encloses {x y : DInt p} {a b : Nat}
    (ha : x.mem a) (hb : y.mem b) (h0 : y.lo ≠ 0) :
    (x.div y).lo * b ≤ a * 2 ^ p ∧ a * 2 ^ p ≤ (x.div y).hi * b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  show divLo p x.lo y.hi * b ≤ a * 2 ^ p ∧ a * 2 ^ p ≤ divHi p x.hi y.lo * b
  constructor
  · have h1 : divLo p x.lo y.hi * b ≤ divLo p x.lo y.hi * y.hi :=
      Nat.mul_le_mul (Nat.le_refl _) hb2
    have h2 : x.lo * 2 ^ p ≤ a * 2 ^ p := Nat.mul_le_mul ha1 (Nat.le_refl _)
    exact Nat.le_trans h1 (Nat.le_trans (divLo_le p x.lo y.hi) h2)
  · have h1 : a * 2 ^ p ≤ x.hi * 2 ^ p := Nat.mul_le_mul ha2 (Nat.le_refl _)
    have h2 : divHi p x.hi y.lo * y.lo ≤ divHi p x.hi y.lo * b :=
      Nat.mul_le_mul (Nat.le_refl _) hb1
    exact Nat.le_trans h1 (Nat.le_trans (divHi_ge p x.hi y.lo h0) h2)

end DInt

end LeanCompCert.Verified.Dyadic
