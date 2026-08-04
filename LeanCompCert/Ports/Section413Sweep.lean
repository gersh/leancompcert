import LeanCompCert.Ports.MertensCDEM

/-!
# The Helfgott §4.1.3 fixed-point divisor sweep: the reference model

Three `native_decide` atoms in `claude_math` evaluate one shared engine — the
outward-rounded integer-interval sweep that encloses Helfgott's `g_v(X)`
(arXiv:1205.5252v4 §4.1.3) at the common fixed scale `10¹⁸`:

* `section413G2SmallCertificate_native` — `|g₂(X)| ≤ 2.1/X` for
  `33 ≤ X ≤ 10⁶` (one `v = 2` sweep, a per-`X` cell test);
* `section413HeadMainFixedCertificate_native` — the four (4.31) residuals at
  `cap = 10⁴` (a `v = 1` and a `v = 2` sweep, two running aggregates);
* `section413Window431BothFixedCertificate_native` — the two (4.31) windows at
  `cap = 99999` (both sweeps, plus a `K₁/K₂` event scan over the `g_v` table).

The sweep's accumulator is a divisor-indexed table (`A_{v,d}(X) = Σ_{r ≤ X,
d ∣ r} a_v(r)`), so the port targets the **array machine** (`AProgram`); the
scalar fragment cannot carry a `10⁶`-slot state.

This module is the *reference model*: the mathematics the machine is intended
to compute, written in ordinary `Int`/`Nat` arithmetic over `Array`, with no
registers, no truncation and no trace.  It is the interface both halves of the
port proof meet at:

* downstream (`claude_math`, where Mathlib lives) proves this model equals the
  production sweep `section413GvZScan` — divisor pairing equals `Nat.divisors`,
  the shared trial division equals `μ`, and the interleaved read-update pass
  equals the two-phase step;
* upstream (here) the array program's denotation is to be proved equal to this
  model.  Until that simulation theorem lands, a run of the emitted artifact
  is evidence about the C, not about the atoms — the campaign registry entry
  must carry `evaluates_atom_predicate: false`.

Design notes.

* **Divisors by pairing, not by sieve**: divisor `r ≤ √X` is paired with
  `X / r`, exactly `Section413KernelDivisors.section413FastDivisors`
  downstream.  No divisor-list table exists anywhere.
* **`μ` by the shared trial division**: `muCode` from `Ports/MertensCDEM`, so
  the downstream bridge is the already-proved
  `TGNativeCertificates.TrialDivisionMoebius.muPlus_sub_muMinus_eq_moebius`.
* **Interleaved touch**: each divisor slot is read (for the delta term, at its
  pre-step value) and then written, in one pass.  The slots a step touches are
  pairwise distinct, so this equals the production two-phase step; that
  equality is part of the downstream bridge.
* **`Int` division is Euclidean**: for the positive divisors used here `/` on
  `Int` is genuine floor division, matching `section413ZFloorDiv` downstream.
-/

namespace LeanCompCert.Ports.Section413Sweep

open LeanCompCert.Ports.MertensCDEM (muCode)

/-- The common fixed-point scale `10¹⁸`. -/
def SCALE : Nat := 1000000000000000000

/-! ## Cells: closed integer intervals at scale `SCALE`

Mirrors `Section413ZInterval` and the `section413Z*` operations downstream,
field for field and case for case. -/

/-- An outward-rounded interval `[lo/SCALE, hi/SCALE]`. -/
structure Cell where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

instance : Inhabited Cell := ⟨⟨0, 0⟩⟩

def czero : Cell := ⟨0, 0⟩

/-- The constant `1`. -/
def cone : Cell := ⟨(SCALE : Int), (SCALE : Int)⟩

def cadd (I J : Cell) : Cell := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Scalar multiple; a negative scalar swaps the endpoints. -/
def csmul (c : Int) (I : Cell) : Cell :=
  if 0 ≤ c then ⟨c * I.lo, c * I.hi⟩ else ⟨c * I.hi, c * I.lo⟩

/-- Floor division by a positive natural (`Int./` is Euclidean division, which
is floor division for positive divisors). -/
def cfloorDiv (a : Int) (d : Nat) : Int := a / (d : Int)

/-- Ceiling division by a positive natural. -/
def cceilDiv (a : Int) (d : Nat) : Int := -((-a) / (d : Int))

/-- Outward-rounded division of a cell by a natural. -/
def cdivNat (I : Cell) (d : Nat) : Cell :=
  ⟨cfloorDiv I.lo d, cceilDiv I.hi d⟩

/-- Outward-rounded multiplication by the rational `c / d`. -/
def cratSMul (c : Int) (d : Nat) (I : Cell) : Cell :=
  cdivNat (csmul c I) d

def cprodLo (I J : Cell) : Int :=
  min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))

def cprodHi (I J : Cell) : Int :=
  max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))

/-- Outward-rounded interval product, renormalized to scale `SCALE`. -/
def cmul (I J : Cell) : Cell :=
  ⟨cfloorDiv (cprodLo I J) SCALE, cceilDiv (cprodHi I J) SCALE⟩

/-! ## Möbius through the shared trial division -/

/-- `μ(X)` as a signed integer, decoded from `Ports/MertensCDEM.muCode`.
Correct for `X < (R + 2)²`; the downstream bridge is
`TrialDivisionMoebius.muPlus_sub_muMinus_eq_moebius`. -/
def muZ (X R : Nat) : Int :=
  match muCode X R with
  | 1 => 1
  | 2 => -1
  | _ => 0

/-! ## Divisors by `√`-pairing -/

/-- `σ(X)`, accumulated over the divisor pairs `(r, X/r)`, `r ≤ √X`. -/
def sigmaPair (X : Nat) : Nat :=
  (List.range (Nat.sqrt X)).foldl
    (fun acc i =>
      let r := i + 1
      if X % r = 0 then
        acc + r + (if X / r ≠ r then X / r else 0)
      else acc) 0

/-! ## The sweep -/

/-- The per-divisor correction of the signed divisor inversion:
`μ(d) · (2·A_d·w + w²)`. -/
def deltaTerm (mu : Int) (A w : Cell) : Cell :=
  csmul mu (cadd (csmul 2 (cmul A w)) (cmul w w))

/-- Process one divisor slot: read the accumulator at its pre-step value,
add the slot's delta term, then push `w` into the slot. -/
def touch (R : Nat) (w : Cell) (p : Array Cell × Cell) (d : Nat) :
    Array Cell × Cell :=
  let A := p.1[d]!
  (p.1.set! d (cadd A w), cadd p.2 (deltaTerm (muZ d R) A w))

/-- One pass over the divisor pairs of `X`, feeding `touch`. -/
def stepDivisors (R X : Nat) (w : Cell) (st : Array Cell × Cell) :
    Array Cell × Cell :=
  (List.range (Nat.sqrt X)).foldl
    (fun p i =>
      let r := i + 1
      if X % r = 0 then
        let p1 := touch R w p r
        if X / r ≠ r then touch R w p1 (X / r) else p1
      else p) st

/-- The weight cell `a_v(X)` for `v = 2`: `μ(X)/σ(X)` when `X` is odd,
`0` otherwise (`Coprime X 2` is oddness). -/
def weightV2 (R X : Nat) : Cell :=
  if X % 2 = 1 then cratSMul (muZ X R) (sigmaPair X) cone else czero

/-- The weight cell for `v = 1`: `μ(X)/σ(X)`, no parity gate. -/
def weightV1 (R X : Nat) : Cell :=
  cratSMul (muZ X R) (sigmaPair X) cone

/-! ## Atom 2: the finite `g₂` range check (`|g₂(X)| ≤ 2.1/X`) -/

/-- The per-`X` endpoint test, exactly
`section413G2SmallCellCheck` downstream. -/
def g2Check (X : Nat) (I : Cell) : Bool :=
  decide (-21 * (SCALE : Int) ≤ I.lo * ((10 * X : Nat) : Int) ∧
    I.hi * ((10 * X : Nat) : Int) ≤ 21 * (SCALE : Int))

/-- Sweep state for the `g₂` range check. -/
structure G2State where
  acc : Array Cell
  g : Cell
  ok : Bool

/-- One step of the `v = 2` sweep with the inline `g₂` test. -/
def g2Step (R checkLo : Nat) (s : G2State) (X : Nat) : G2State :=
  let w := weightV2 R X
  let ad := stepDivisors R X w (s.acc, czero)
  let g' := cadd s.g ad.2
  { acc := ad.1, g := g',
    ok := s.ok && (if checkLo ≤ X then g2Check X g' else true) }

/-- The complete `v = 2` sweep over `X = 1, …, N`. -/
def g2Run (R checkLo N : Nat) : G2State :=
  (List.range N).foldl (fun s i => g2Step R checkLo s (i + 1))
    ⟨Array.replicate (N + 1) czero, czero, true⟩

/-- **Atom 2's model Boolean.**  At `R = 999`, `checkLo = 33`, `N = 10⁶` this
is intended to equal `section413G2SmallCertificateNative (10 ^ 6)`
downstream. -/
def g2SweepOK (R checkLo N : Nat) : Bool := (g2Run R checkLo N).ok

/-! ## Atom 1: the four (4.31) head-mass / main-term residuals

The same sweep, with the `g_v` cell folded into two running aggregates
instead of an inline test.  The main-term aggregate needs a certified
upper bracket of `log(1 + 1/m)`; it is carried as dyadic numbers at scale
`2⁶⁰` computed by directed rounding from the `atanh` series at
`x = 1/(2m+1)` — the same series, with the same per-`m` term count
`nTerms`, as the downstream exact-rational brackets `loQ`/`hiQ`, so the
downstream comparison is one series against the other, term by term. -/

/-- The dyadic bracket scale `2⁶⁰`. -/
def DYS : Nat := 1152921504606846976

/-- The downstream term-count schedule `nTermsFn`, verbatim. -/
def nTerms (m : Nat) : Nat :=
  if m ≤ 1 then 11
  else if m ≤ 2 then 7
  else if m ≤ 3 then 6
  else if m ≤ 6 then 5
  else if m ≤ 14 then 4
  else if m ≤ 56 then 3
  else if m ≤ 1356 then 2
  else 1

/-- Lower dyadic bracket of `x = 1/(2m+1)` at scale `DYS`. -/
def xLoDy (m : Nat) : Nat := DYS / (2 * m + 1)

/-- Upper dyadic bracket of `x = 1/(2m+1)` at scale `DYS`. -/
def xHiDy (m : Nat) : Nat := (DYS + 2 * m) / (2 * m + 1)

/-- Floor product at scale `DYS`. -/
def dyMulLo (a b : Nat) : Nat := a * b / DYS

/-- Ceiling product at scale `DYS`. -/
def dyMulHi (a b : Nat) : Nat := (a * b + (DYS - 1)) / DYS

/-- Lower dyadic bracket of `loQ m n = 2·Σ_{i<n} x^(2i+1)/(2i+1)`:
`n` series terms, every rounding downward. -/
def atanhLoDy (m n : Nat) : Nat :=
  let x := xLoDy m
  let x2 := dyMulLo x x
  (List.range n).foldl
    (fun st i =>
      let p' := if i = 0 then x else dyMulLo st.2 x2
      (st.1 + 2 * p' / (2 * i + 1), p'))
    ((0 : Nat), (0 : Nat)) |>.1

/-- Upper dyadic bracket of `hiQ m n = loQ m n + 2·x^(2n+1)/(1−x²)`:
`n` series terms upward, plus the tail bounded through
`1/(1−x²) ≤ 1 + 2x²` (valid for `x² ≤ 1/2`). -/
def atanhHiDy (m n : Nat) : Nat :=
  let x := xHiDy m
  let x2 := dyMulHi x x
  let sp := (List.range n).foldl
    (fun st i =>
      let p' := if i = 0 then x else dyMulHi st.2 x2
      (st.1 + (2 * p' + 2 * i) / (2 * i + 1), p'))
    ((0 : Nat), (0 : Nat))
  let ptail := dyMulHi sp.2 x2  -- x^(2n+1), upward
  sp.1 + (2 * ptail * (DYS + 2 * x2) + (DYS - 1)) / DYS

/-- Integer upper bound for the signed main-term contribution
`⌈hi · bracket⌉`: the upper log bracket against a nonnegative `hi`, the
lower one against a negative `hi` — dominating
`section413MainNumTerm` downstream. -/
def mainTermUB (m : Nat) (I : Cell) : Int :=
  if 0 ≤ I.hi then cceilDiv (I.hi * (atanhHiDy m (nTerms m) : Int)) DYS
  else cceilDiv (I.hi * (atanhLoDy m (nTerms m) : Int)) DYS

/-- `max (−lo) hi`, the head-mass numerator of a cell
(`section413ZAbsUB` downstream). -/
def cabsUB (I : Cell) : Int := max (-I.lo) I.hi

/-- Sweep state for the head-mass / main-term aggregates. -/
structure HMState where
  acc : Array Cell
  g : Cell
  headAcc : Int
  mainAcc : Int

/-- One step of the aggregate sweep at candidate `X`. -/
def hmStep (R : Nat) (w : Cell) (s : HMState) (X : Nat) : HMState :=
  let ad := stepDivisors R X w (s.acc, czero)
  let g' := cadd s.g ad.2
  { acc := ad.1, g := g',
    headAcc := s.headAcc + cabsUB g' * ((5 * X * X + 2 * X + 1 : Nat) : Int),
    mainAcc := s.mainAcc + mainTermUB X g' }

/-- The aggregate sweep over `X = 1, …, N` for `v ∈ {1, 2}`. -/
def hmRun (v R N : Nat) : HMState :=
  (List.range N).foldl
    (fun s i =>
      let X := i + 1
      hmStep R (if v = 2 then weightV2 R X else weightV1 R X) s X)
    ⟨Array.replicate (N + 1) czero, czero, 0, 0⟩

/-- **Atom 1's model Boolean, `v = 1` half**: the head-mass and main-term
checks of `section413HeadMainKernelV1`, with the main-term side checked
against the dominating aggregate. -/
def hmV1OK (R N : Nat) : Bool :=
  let s := hmRun 1 R N
  decide (s.headAcc ≤ 37224400 * (SCALE : Int)) &&
    decide (10000000 * s.mainAcc ≤ 2 * 3624829 * (SCALE : Int))

/-- **Atom 1's model Boolean, `v = 2` half.** -/
def hmV2OK (R N : Nat) : Bool :=
  let s := hmRun 2 R N
  decide (s.headAcc ≤ 47734021 * (SCALE : Int)) &&
    decide (10000000 * s.mainAcc ≤ 4 * 3605763 * (SCALE : Int))

/-! ## Atom 3: the two exact (4.31) windows

The same sweep once more, now keeping the whole `g_v` table, followed by
the `K₁/K₂` event scan that reads the table at divisor-derived indices —
mirroring `section413KZScan` downstream operation for operation. -/

def cneg (I : Cell) : Cell := ⟨-I.hi, -I.lo⟩

def csub (I J : Cell) : Cell := cadd I (cneg J)

def cmax (I J : Cell) : Cell := ⟨max I.lo J.lo, max I.hi J.hi⟩

/-- Sweep state that keeps the table. -/
structure TabState where
  acc : Array Cell
  g : Cell
  table : Array Cell

def tabStep (R : Nat) (w : Cell) (s : TabState) (X : Nat) : TabState :=
  let ad := stepDivisors R X w (s.acc, czero)
  let g' := cadd s.g ad.2
  ⟨ad.1, g', s.table.push g'⟩

def tabRun (v R N : Nat) : TabState :=
  (List.range N).foldl
    (fun s i =>
      let X := i + 1
      tabStep R (if v = 2 then weightV2 R X else weightV1 R X) s X)
    ⟨Array.replicate (N + 1) czero, czero, #[czero]⟩

/-- Pairing sum of `f` over the divisors of `n` coprime to `v`. -/
def kDivSum (v n : Nat) (f : Nat → Cell) : Cell :=
  (List.range (Nat.sqrt n)).foldl
    (fun c i =>
      let r := i + 1
      if n % r = 0 then
        let c1 := if Nat.gcd r v = 1 then cadd c (f r) else c
        if n / r ≠ r then
          if Nat.gcd (n / r) v = 1 then cadd c1 (f (n / r)) else c1
        else c1
      else c) czero

def k1First (G : Nat → Cell) (n s : Nat) : Cell :=
  cratSMul (-1) s (csub (G (n / s - 1)) (G (n / s)))

def k1Second (G : Nat → Cell) (q s : Nat) : Cell :=
  cratSMul 1 (2 * s) (csub (G (q / s - 1)) (G (q / s)))

def k2First (G : Nat → Cell) (n s : Nat) : Cell :=
  csmul ((n / s : Nat) : Int) (csub (G (n / s - 1)) (G (n / s)))

def k2Second (G : Nat → Cell) (q s : Nat) : Cell :=
  csmul (-((q / s : Nat) : Int)) (csub (G (q / s - 1)) (G (q / s)))

def k1Delta (G : Nat → Cell) (v n : Nat) : Cell :=
  cadd (kDivSum v n (k1First G n))
    (if n % 2 = 0 then kDivSum v (n / 2) (k1Second G (n / 2)) else czero)

def k2Delta (G : Nat → Cell) (v n : Nat) : Cell :=
  cadd (kDivSum v n (k2First G n))
    (if n % 2 = 0 then kDivSum v (n / 2) (k2Second G (n / 2)) else czero)

def unitCell (k1 k2 : Cell) (n : Nat) : Cell :=
  cadd k1 (cmax (cdivNat k2 n) (cdivNat k2 (n + 1)))

structure KState where
  k1 : Cell
  k2 : Cell
  ok : Bool

def kStep (G : Nat → Cell) (v lo : Nat) (boundNum : Int) (boundDen n : Nat)
    (p : KState) : KState :=
  let d1 := k1Delta G v (n + 1)
  let d2 := k2Delta G v (n + 1)
  let k1' := cadd p.k1 d1
  let k2' := cadd p.k2 d2
  let unit := unitCell k1' k2' (n + 1)
  let checked := decide (n + 1 < lo ∨
    unit.hi * (boundDen : Int) ≤ boundNum * (SCALE : Int))
  ⟨k1', k2', p.ok && checked⟩

def kRun (G : Nat → Cell) (v lo : Nat) (boundNum : Int) (boundDen N : Nat) :
    KState :=
  (List.range N).foldl (fun p n => kStep G v lo boundNum boundDen n p)
    ⟨czero, czero, true⟩

/-- **Atom 3's model Boolean** at `R = 999`, `N = 99999`: intended to imply
`section413Window431BothFixedCertificate` downstream. -/
def windowOK (R N : Nat) : Bool :=
  let T1 := (tabRun 1 R N).table
  let ok1 := (kRun (fun k => T1[k]!) 1 40 36393 100000 N).ok
  let T2 := (tabRun 2 R N).table
  let ok2 := (kRun (fun k => T2[k]!) 2 16 37273 100000 N).ok
  ok1 && ok2

end LeanCompCert.Ports.Section413Sweep
