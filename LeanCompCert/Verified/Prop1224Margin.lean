import LeanCompCert.Verified.Dyadic
import LeanCompCert.Verified.ExpFixed

/-!
# Helfgott Prop. 12.2.4: the integer margin, and the guards that make it sound

`Ports/Prop1224Row.lean` and `Ports/Prop1224Cell.lean` produce integers.  The
statement they are supposed to certify is about real numbers.  This module is
the seam, and it is written in `Verified/Dyadic.lean`'s idiom: **every claim is
a cross-multiplied `Nat` inequality**, which is exactly the rational enclosure
after clearing denominators, so nothing here needs `Rat` or `ℝ`.

## The claim, and why `c_E` disappears from it

The axiom `finite_check_helfgott_prop_12_2_4_computation_source` says: for `q`
in range and every integer `k` with `ϖ(q) ≤ k` and
`k^{1/3}·κ*(q) < (q/φ(q))·7.284(1+β*)·f₁(q)`,

```
err_{q,k} + ω*·7.284·(20000k)^{−1/3}·f₁(q)  ≤  (φ(q)/q)·κ*(q)
```

with `err_{q,k} = G_q(k) − (φ/q)(log k + c_E + L(q))` and
`κ*(q) = (1−ω*)(log q − L(q)) + 1.36 − c_E`.  Substituting both and cancelling,

```
M(q,k) := (φ(q)/q)·[ log k + (1−ω*)·log q + ω*·L(q) + 1.36 ]
          − G_q(k) − ω*·7.284·(20000k)^{−1/3}·f₁(q)   ≥   0.
```

**`c_E` cancels identically.**  That matters: `c_E = γ + Σ_p log p/(p(p−1))` is
the one constant in the statement that is not a decimal and has no closed form,
and the checked inequality does not contain it.  It survives only in the
*window* — inside `c_Δ = 1.36 − c_E` in `κ*`, and inside
`c₂* = exp(0.1109 + ω*(c_E − 1.312))` in `ϖ` — where it appears in a
**hypothesis**, so a bracket for it costs cells rather than soundness.

## Which direction of each inequality is the dangerous one

There are two independent soundness obligations, and they fail in different
ways.  Writing `A` for the true admissible set of pairs and `A'` for the set
the artifact enumerates:

**(1) Coverage, `A ⊆ A'`.**  The anti-conservative direction is a window that
is too *small*.  A `ϖ` computed too high, or a `λ` computed too low, silently
*skips* cells; the artifact then reports a clean run while the axiom asserts
something about a pair that was never examined.  Nothing downstream can detect
this — the artifact's own violation counter stays zero.  This is the failure
mode to guard, and the guards are `k0_covers` and `lamHi_covers` below: the
floor is rounded **down** and the ceiling **up**, and each guard is a `Nat`
theorem, not a comment.

  *Corollary for `c_E`.*  In the window, `c_E` must be taken at the end of its
  proved bracket that makes the window **larger**: `c_Δ` at its **lower** end
  (from `c_E` **upper**), because `κ*` small means `λ = (B/κ*)³` large.  The
  repo's bracket `1.3325822 ≤ c_E ≤ 1.3339` costs about `16 %` extra cells at
  `q = 1`; the cheap direction would have been to use the true value, and it is
  the wrong one.

**(2) Soundness of each examined cell.**  Here the anti-conservative direction
is a margin computed too *high*.  The integer margin must under-estimate the
real `M(q,k)`: every term entering `M` positively is rounded **down**, every
term entering it negatively **up**.  Concretely `log k`, `log q`, `L(q)`,
`φ/q` down; `G_q(k)` and the `(12.32)` envelope up — and inside the envelope
the direction inverts twice, since `(20000k)^{−1/3}` up needs
`(20000k)^{1/3}` **down** (`cbrtOK`), and `f₁(q)` up needs, through the
reciprocal of its denominator, `p^{1/3}` and `p^{2/3}` **down**.  `marginOK_sound` is the
assembly, and its hypotheses are stated so that a flipped direction does not
typecheck.

`Check.skipped_cell_witness` below exhibits, as a decidable witness, exactly
what a flipped `ϖ` guard costs: an integer `k` inside the true window that a
rounded-up floor would have skipped.

## The scales

| | | |
| --- | ---: | --- |
| `E` | 26 | row scale; every row real is `< 32`, so a product of two `E`-scaled row values is `< 2^62` |
| `C` | 44 | cell scale for `G_q`; `G_q ≤ 21`, and `≤ 2·10⁷` outward-rounded terms overshoot by `< 2·10⁷/2^44 = 1.1·10⁻⁶` against a minimum margin of `0.0233` |
| `P` | 30 | `ExpFixed`'s mantissa precision — the proved `u64` wall (`expIter_fits_64`) |
| `S` | 24 | `LogFixed`/`ExpFixed` exponent scale |
| `T` | 24 | scale of `rpow`'s rational exponent |

## What this module does *not* do

It does not prove that the artifact's `denote` is `M(q,k)`; that is the
oracle's job, exactly as in `Ports/R2SegSieve.lean`.  And it does not name a
real number, so the last step — from these cross-multiplied `Nat` facts to the
`ℝ`-valued `RamareProp1224FiniteComputation` — is a monotonicity argument that
belongs on the `claude_math` side, where `Real.log` and `Real.rpow` exist.  The
content of that step is `Finset.sum_le_sum` and `gcongr`; the content of the
*directions* is here.
-/

namespace LeanCompCert.Verified.Prop1224Margin

open LeanCompCert.Verified

/-! ## Scales -/

/-- Row scale. -/
def E : Nat := 26
/-- Cell scale, at which `G_q` is accumulated and the margin is formed. -/
def C : Nat := 44
/-- `ExpFixed` mantissa precision; `P ≤ 30` is proved by `expIter_fits_64`. -/
def P : Nat := 30
/-- `LogFixed`/`ExpFixed` exponent scale. -/
def S : Nat := 24
/-- Scale of `rpow`'s rational exponent. -/
def T : Nat := 24

/-- Ceiling division, the artifact's only outward-rounding primitive.  Stated
here rather than reused from `Dyadic` because every upward rounding in the row
and cell modules goes through it and the soundness lemma is quoted by name. -/
def cdiv (n d : Nat) : Nat := (n + d - 1) / d

/-- **The ceiling really is one.**  `Dyadic.le_ceil_mul`, renamed. -/
theorem le_cdiv_mul (n d : Nat) (hd : 0 < d) : n ≤ cdiv n d * d :=
  Dyadic.le_ceil_mul n d hd

/-- …and the floor really is one. -/
theorem fdiv_mul_le (n d : Nat) : n / d * d ≤ n := Dyadic.floor_mul_le n d

/-! ## Guard 1 — the window floor `ϖ(q)`

The artifact starts its `k` loop at `k0 = ⌊varpiLo / 2^E⌋`.  `varpiLo` is a
**lower** bound for `2^E·ϖ(q)`, and the floor rounds **down** again: two
outward roundings in the same direction, both of which only add cells.
-/

/-- The first `k` the cell loop examines. -/
def k0 (varpiLo : Nat) : Nat := varpiLo / 2 ^ E

/-- **The floor guard.**  If `varpiLo` is a lower bound for `2^E·ϖ(q)` — the
hypothesis is `varpiLo ≤ 2^E·k`, which is `ϖ(q) ≤ k` weakened by that lower
bound — then `k` is at or above where the loop starts.  So every `k` the axiom
quantifies over is examined.

This is the guard whose *opposite* is silent: a `k0` computed one too high
skips the axiom's worst cell (the margin is minimised at the window floor) and
leaves the violation counter at zero. -/
theorem k0_covers {varpiLo k : Nat} (h : varpiLo ≤ 2 ^ E * k) : k0 varpiLo ≤ k := by
  have h1 : varpiLo / 2 ^ E ≤ 2 ^ E * k / 2 ^ E := Nat.div_le_div_right h
  have h2 : 2 ^ E * k / 2 ^ E = k :=
    Nat.mul_div_cancel_left k (Nat.two_pow_pos E)
  simpa [k0, h2] using h1

/-! ## Guard 2 — the window ceiling `λ(q)`

The paper's `λ(q) = ((q/φ(q))·7.284(1+β*)·f₁(q)/κ*(q))³` is a cube, and the
axiom's hypothesis is the *uncubed* `k^{1/3}·κ*(q) < B(q)`.  Cubing it gives
`k·κ*(q)³ < B(q)³`, which contains **no cube root and no `rpow` at all** — so
the artifact never computes `λ` by exponentiation, and the per-cell cost loses
one `rpow`.

What remains is that the staged integer cube below does not lose the bound.
`B_hi³` and `κ*_lo³` do not fit in a machine word (`κ*_lo` reaches `2^29`, and
its cube `2^87`), so the artifact forms the ratio first, at scale `2^20`, and
cubes that in two rounded steps.  `lamCube_ge` is the statement that both
roundings go outward.
-/

/-- `⌈2^20·B/κ*⌉`, the ratio the cube is taken of. -/
def lamR (bHi kapLo : Nat) : Nat := cdiv (bHi * 2 ^ 20) kapLo

/-- `⌈r³/2^60⌉`, staged as two roundings so that no intermediate exceeds
`2^63`.  **The order of the two shifts is load-bearing**: at the production
extreme `r ≤ 3.0·10⁸` the sequence `>>> 40` then `>>> 20` peaks at
`⌈r²/2^40⌉·r ≤ 2.5·10^13`, while the opposite order peaks at
`⌈r²/2^20⌉·r ≤ 2.6·10^19` — over `2^63`, where the artifact would wrap and
report a window far too small.  `lamCube_fits` pins it. -/
def lamCube (r : Nat) : Nat := cdiv (cdiv (r * r) (2 ^ 40) * r) (2 ^ 20)

/-- The first `k` beyond the window. -/
def lamHi (bHi kapLo : Nat) : Nat := lamCube (lamR bHi kapLo) + 1

/-- **The staged cube rounds outward.**  `r³ ≤ lamCube r · 2^60`. -/
theorem lamCube_ge (r : Nat) : r * r * r ≤ lamCube r * 2 ^ 60 := by
  have h20 : 0 < 2 ^ 20 := Nat.two_pow_pos 20
  have h40 : 0 < 2 ^ 40 := Nat.two_pow_pos 40
  have hA : r * r ≤ cdiv (r * r) (2 ^ 40) * 2 ^ 40 := le_cdiv_mul _ _ h40
  have hB : cdiv (r * r) (2 ^ 40) * r
      ≤ cdiv (cdiv (r * r) (2 ^ 40) * r) (2 ^ 20) * 2 ^ 20 := le_cdiv_mul _ _ h20
  calc r * r * r ≤ cdiv (r * r) (2 ^ 40) * 2 ^ 40 * r :=
        Nat.mul_le_mul_right _ hA
    _ = cdiv (r * r) (2 ^ 40) * r * 2 ^ 40 := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ cdiv (cdiv (r * r) (2 ^ 40) * r) (2 ^ 20) * 2 ^ 20 * 2 ^ 40 :=
        Nat.mul_le_mul_right _ hB
    _ = lamCube r * 2 ^ 60 := by
        simp [lamCube, Nat.mul_assoc]

/-- **The ceiling guard.**  If `k` satisfies the axiom's window hypothesis in
its cubed form `k·κ*³ < B³`, and `kapLo ≤ 2^E·κ*`, `2^E·B ≤ bHi` are the
artifact's enclosures, then `k < lamHi`, i.e. `k` is examined.

The proof is monotone cubing: `k·kapLo³ ≤ k·(2^E κ*)³ < (2^E B)³ ≤ bHi³`, and
then the staged cube.  Stated directly on the integers the artifact holds, so
the hypothesis below is the already-cubed, already-enclosed one; the step from
the axiom's `k^{1/3}·κ* < B` to it is one `gcongr` on the `ℝ` side. -/
theorem lamHi_covers {bHi kapLo k : Nat} (hk : 0 < kapLo)
    (h : k * (kapLo * kapLo * kapLo) < bHi * bHi * bHi) :
    k < lamHi bHi kapLo := by
  have h20 : 0 < 2 ^ 20 := Nat.two_pow_pos 20
  have hr : lamHi bHi kapLo = lamCube (lamR bHi kapLo) + 1 := rfl
  -- `bHi·2^20 ≤ r·κ*_lo`, cubed
  have hR : bHi * 2 ^ 20 ≤ lamR bHi kapLo * kapLo := le_cdiv_mul _ _ hk
  have hR3 : (bHi * bHi * bHi) * 2 ^ 60
      ≤ (lamR bHi kapLo * lamR bHi kapLo * lamR bHi kapLo)
          * (kapLo * kapLo * kapLo) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hR hR) hR
    calc (bHi * bHi * bHi) * 2 ^ 60
        = (bHi * 2 ^ 20) * (bHi * 2 ^ 20) * (bHi * 2 ^ 20) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (lamR bHi kapLo * kapLo) * (lamR bHi kapLo * kapLo)
            * (lamR bHi kapLo * kapLo) := this
      _ = (lamR bHi kapLo * lamR bHi kapLo * lamR bHi kapLo)
            * (kapLo * kapLo * kapLo) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  -- and the staged cube does not lose it
  have hC : (lamR bHi kapLo * lamR bHi kapLo * lamR bHi kapLo)
        * (kapLo * kapLo * kapLo)
      ≤ (lamCube (lamR bHi kapLo) * 2 ^ 60) * (kapLo * kapLo * kapLo) :=
    Nat.mul_le_mul_right _ (lamCube_ge _)
  -- chain: `k·κ³·2^60 < lamCube·2^60·κ³`
  have hkey : (k * (kapLo * kapLo * kapLo)) * 2 ^ 60
      < (lamCube (lamR bHi kapLo) * (kapLo * kapLo * kapLo)) * 2 ^ 60 := by
    have hlt : (k * (kapLo * kapLo * kapLo)) * 2 ^ 60
        < (bHi * bHi * bHi) * 2 ^ 60 :=
      Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl _) (Nat.two_pow_pos 60)
    calc (k * (kapLo * kapLo * kapLo)) * 2 ^ 60
        < (bHi * bHi * bHi) * 2 ^ 60 := hlt
      _ ≤ (lamR bHi kapLo * lamR bHi kapLo * lamR bHi kapLo)
            * (kapLo * kapLo * kapLo) := hR3
      _ ≤ (lamCube (lamR bHi kapLo) * 2 ^ 60) * (kapLo * kapLo * kapLo) := hC
      _ = (lamCube (lamR bHi kapLo) * (kapLo * kapLo * kapLo)) * 2 ^ 60 := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hk3 : 0 < kapLo * kapLo * kapLo :=
    Nat.mul_pos (Nat.mul_pos hk hk) hk
  have h1 : k * (kapLo * kapLo * kapLo)
      < lamCube (lamR bHi kapLo) * (kapLo * kapLo * kapLo) :=
    Nat.lt_of_mul_lt_mul_right hkey
  have h2 : k < lamCube (lamR bHi kapLo) := Nat.lt_of_mul_lt_mul_right
    (by simpa [Nat.mul_comm] using h1)
  rw [hr]; exact Nat.lt_succ_of_lt h2

/-! ## The per-cell margin

`posLo` is the artifact's lower bound for `2^C` times the positive part of
`M(q,k)`; `gHi` and `envHi` are its upper bounds for `2^C·G_q(k)` and for `2^C`
times the `(12.32)` envelope.  The check is one comparison.
-/

/-- The artifact's per-cell test. -/
def marginOK (posLo gHi envHi : Nat) : Bool := decide (gHi + envHi ≤ posLo)

/-- **The assembly.**  The hypotheses are the three enclosures, *each in the
only direction that makes the conclusion follow*: `posLo` below the positive
part, `gHi` and `envHi` above the two negative parts.  Flip any one of them and
this does not typecheck — which is the point, since the flipped version is
exactly the silent failure described at the top of the file. -/
theorem marginOK_sound {posLo gHi envHi pos g env : Nat}
    (hp : posLo ≤ pos) (hg : g ≤ gHi) (hv : env ≤ envHi)
    (h : marginOK posLo gHi envHi = true) : g + env ≤ pos := by
  have h' : gHi + envHi ≤ posLo := of_decide_eq_true h
  omega

/-! ## The `G_q` accumulation

`G_q(k) = Σ_{r ≤ k, (r,q)=1} μ²(r)/φ(r)` is a sum of *rationals*, so unlike
every other term it needs no transcendental enclosure at all — only that each
reciprocal is rounded **up**, and that the accumulator is wide enough that
`k` such roundings stay far below the margin.
-/

/-- One term of `G_q`, at the cell scale: `⌈2^C/φ(r)⌉`. -/
def gqTerm (phir : Nat) : Nat := cdiv (2 ^ C) phir

/-- **Each term is rounded up.**  Cross-multiplied, `1/φ(r) ≤ gqTerm/2^C`. -/
theorem gqTerm_ge (phir : Nat) (h : 0 < phir) : 2 ^ C ≤ gqTerm phir * phir :=
  le_cdiv_mul _ _ h

/-- **The accumulated overshoot is at most one ulp per term.**  With `n` terms
the sum exceeds `2^C·G_q` by less than `n`; at `n ≤ 2·10⁷` and `C = 44` that
is `1.1·10⁻⁶`, against a minimum observed margin of `0.0233`. -/
theorem gqTerm_lt (phir : Nat) (h : 0 < phir) : gqTerm phir * phir < 2 ^ C + phir := by
  have hfl : gqTerm phir * phir ≤ 2 ^ C + phir - 1 :=
    Dyadic.floor_mul_le (2 ^ C + phir - 1) phir
  have hpos : 0 < 2 ^ C := Nat.two_pow_pos C
  omega

/-! ## The envelope, and a cube root with no exponential in it

`ω*·7.284·(20000k)^{−1/3}·f₁(q)`, upper.  The direction inverts: an upper bound
on a reciprocal needs a **lower** bound on what is inverted.

The reciprocal cube root would be one `ExpFixed.rpow` per cell — the single
most expensive thing in the cell loop, and `bench/results/exp_fixed.md` prices
it at `1.34 µs`.  It is not needed.  `k` runs over *consecutive integers*, so
`t = ⌊2^5·(20000k)^{1/3}⌋` can be carried in a register and advanced by the
same certified-comparison discipline the square root uses: the artifact
proposes a `t` and the loop checks `t³ ≤ 2^15·20000k`, which **is** the
statement `t/2^5 ≤ (20000k)^{1/3}` after cubing.  No exponential, no root, and
the check is one multiply chain.

`2^5` is the largest scale that fits: `t ≤ 2^5·7368 = 2.4·10^5` over the whole
range, so `t³ ≤ 1.3·10^16` and `2^15·20000k ≤ 1.3·10^16`, both clear of `2^63`.
The residual coarseness is `1/(2^5·27) = 0.12 %` of the envelope at the very
smallest `k` the window ever admits, against a smallest observed margin of
`0.0233` at `q = 1` where the envelope is `0.004`.
-/

/-- The certifying comparison for the incremental cube root: `t` is admissible
at `k` exactly when this holds. -/
def cbrtOK (t k : Nat) : Bool := decide (t * t * t ≤ 2 ^ 15 * (20000 * k))

/-- **A passing `t` is a lower bound for `2^5·(20000k)^{1/3}`.**  Cubed and
cleared of denominators, that is literally what `cbrtOK` checks — so, exactly
as with `ExpFixed.expOK`, the artifact may produce `t` by any means at all and
only the comparison is trusted. -/
theorem cbrtOK_sound {t k : Nat} (h : cbrtOK t k = true) :
    t * t * t ≤ 2 ^ 15 * (20000 * k) := of_decide_eq_true h

/-- …and it is monotone in `k`, which is why one register survives the sweep:
a `t` certified at `k` is still certified at `k+1`. -/
theorem cbrtOK_mono {t k : Nat} (h : cbrtOK t k = true) : cbrtOK t (k + 1) = true := by
  have h' := cbrtOK_sound h
  have : 2 ^ 15 * (20000 * k) ≤ 2 ^ 15 * (20000 * (k + 1)) := by
    have : 20000 * k ≤ 20000 * (k + 1) := Nat.mul_le_mul_left _ (Nat.le_succ k)
    exact Nat.mul_le_mul_left _ this
  exact decide_eq_true (Nat.le_trans h' this)

/-- `af` is `⌈ω*·7.284·f₁(q)⌉` at scale `2^E`; `t` is the certified cube root
at scale `2^5`.  `af·2^5 ≤ 2.9·10^10`, so nothing here is near `2^63`. -/
def envHi (af t : Nat) : Nat := cdiv (af * 2 ^ 5) t

/-- **The envelope is rounded up.**  Cross-multiplied: `af·2^5 ≤ envHi·t`,
which with `t/2^5 ≤ (20000k)^{1/3}` gives `af/(20000k)^{1/3} ≤ envHi` at scale
`2^E`. -/
theorem envHi_ge (af t : Nat) (h : 0 < t) : af * 2 ^ 5 ≤ envHi af t * t :=
  le_cdiv_mul _ _ h

/-! ## The positive part

`(φ(q)/q)·[log k + (1−ω*)·log q + ω*·L(q) + 1.36]`, lower.  `φ(q)/q` is exact
rational data, so it is floored once; the bracket is a sum of lower bounds; the
product is floored again and then shifted from the row scale to the cell scale,
which is exact.
-/

/-- `⌊2^E·φ(q)/q⌋`. -/
def phiLo (phi q : Nat) : Nat := phi * 2 ^ E / q

/-- **`φ/q` is rounded down.**  Cross-multiplied: `phiLo·q ≤ φ·2^E`. -/
theorem phiLo_le (phi q : Nat) : phiLo phi q * q ≤ phi * 2 ^ E :=
  Dyadic.floor_mul_le _ _

/-- The positive part at the cell scale: floor the product back to the row
scale, then shift.  The shift is exact, so it introduces no rounding. -/
def posLo (pl brk : Nat) : Nat := (pl * brk / 2 ^ E) * 2 ^ (C - E)

/-- **The positive part is rounded down.**  `posLo·2^E ≤ pl·brk·2^(C−E)`. -/
theorem posLo_le (pl brk : Nat) :
    posLo pl brk * 2 ^ E ≤ pl * brk * 2 ^ (C - E) := by
  have h := Dyadic.floor_mul_le (pl * brk) (2 ^ E)
  calc posLo pl brk * 2 ^ E
      = pl * brk / 2 ^ E * 2 ^ E * 2 ^ (C - E) := by
        simp [posLo, Nat.mul_assoc, Nat.mul_comm]
    _ ≤ pl * brk * 2 ^ (C - E) := Nat.mul_le_mul_right _ h

/-! ## What a flipped guard costs, as a witness

At `q = 6` the paper's window floor is `ϖ(6) = 585.8402…`, and the artifact's
`varpiLo` is `39227955487` at scale `2^26`, i.e. `584.5421…`.  The loop starts
at `k0 = 584`.  A `ϖ` rounded the *other* way — `⌈varpiLo/2^E⌉ + 1 = 586` — would
skip `k = 585`, which is the integer the axiom's hypothesis first admits and
where the margin is smallest (`0.1306` there against `0.1308` at `k = 586`).

The witness is decidable and is the whole content of `k0_covers`: the floor
lands at or below `585`, the ceiling-plus-one does not.
-/

namespace Check

/-- The artifact's floor at `q = 6` admits `k = 585`; a floor rounded up by one
does not.  `585 · 2^26 = 39258685440 ≥ varpiLo`, so `585` really is in the
window, and `k0_covers` places it at or above the loop start. -/
example : k0 39227955487 ≤ 585 ∧ ¬ (cdiv 39227955487 (2 ^ E) + 1 ≤ 585) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- …and `585` genuinely satisfies the hypothesis the lower bound expresses. -/
example : (39227955487 : Nat) ≤ 2 ^ E * 585 := by decide

/-- The staged cube is outward at the production extreme `r = 3.0·10⁸`… -/
example : (300000000 : Nat) * 300000000 * 300000000 ≤ lamCube 300000000 * 2 ^ 60 :=
  lamCube_ge 300000000

/-- …and **the chosen shift order is the one that fits**: `>>> 40` first keeps
the intermediate at `2.6·10^13`, while `>>> 20` first reaches `2.6·10^19`,
above `2^63 = 9.2·10^18`.  This is the whole reason the two shifts are in the
order they are in. -/
example : cdiv ((300000000 : Nat) * 300000000) (2 ^ 40) * 300000000 < 2 ^ 63 := by
  decide

example : ¬ (cdiv ((300000000 : Nat) * 300000000) (2 ^ 20) * 300000000 < 2 ^ 63) := by
  decide

end Check

end LeanCompCert.Verified.Prop1224Margin
