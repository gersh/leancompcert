import LeanCompCert.Ports.PsiSegSieve

/-!
# The `R₂*` residue: a segmented **factorisation** sieve

`Ports/ArraySegSieve.lean` sieves `[lo, hi]` and leaves, per integer, the one
bit a Möbius residue needs.  `Ports/PsiSegSieve.lean` adds a logarithm and a
fourth loop phase, because `ψ` sums `log p` over prime powers.  `R₂*` needs
neither of those signals: its coefficient is a **Dirichlet convolution**, and
evaluating it at `n` needs `n`'s factorisation, not its primality.

## What the residue is

`r2Coeff(k) = (Λ∗Λ)(k) − Λ(k)·log k + 2γ` (`MathExtras/NumberTheory/Mertens/
RamareEq22.lean` on `claude_math`), and the convolution collapses:

```
(Λ∗Λ)(p^a)     = (a−1)·log²p        Λ(p^a)·log(p^a) = a·log²p
(Λ∗Λ)(p^a q^b) = 2·log p·log q      Λ(·)·log(·)     = 0
(Λ∗Λ)(k)       = 0                  for k with ≥ 3 distinct prime factors
```

so that

```
R₂*(N) = 2γN − Σ_{p^a ≤ N} log²p + 2·Σ_{p^a q^b ≤ N, p≠q} log p·log q .
```

Per integer `k` the residue therefore needs the classification *prime power /
two distinct prime powers / more*, **together with both prime factors** — a
factorisation, which no sieve in this repository produced.

## The sieve: three planes, and `p^j` for every `j`

The mark table is every prime power `q = p^j ≤ hi` with `p ≤ ⌊√hi⌋`, sorted by
`(p, j)`, so a cell divisible by `p^v` is marked exactly `v` times by `p`'s
entries.  Each mark writes three planes:

* `prod` — multiplied by the **base prime** `p`, so after the window it holds
  `Π p^{v_p(n)}` over the small primes.  `prod ≠ n` is exactly "`n` has a
  prime factor `> ⌊√hi⌋`", which for `n ≤ hi` is one prime to the first power;
* `lsum` — incremented by `lnFix p`, so it holds `Σ v_p·lnFix p`, the
  fixed-point logarithm of `prod`;
* `W` — at a `j = 1` mark only: the first two distinct weights and a two-bit
  saturating count of distinct small primes, `w1 | w2<<28 | d<<56`.

The base prime never has to be stored: the table is sorted by `(p, j)` and the
`j = 1` entries carry a flag, so one register tracks it.  Each entry is
therefore **one array cell**, `value | lnFix p <<35 | first <<63`, and the
whole table is `π(√hi)` plus the higher powers — 27 510 cells at
`hi = 2.1·10¹⁰`.

The mark budget goes from `L·Σ 1/p = 2.74·L` to `L·Σ 1/(p−1) = 3.51·L`, 28%
more marking, which is what carrying full multiplicity costs.

## Four modes, and only two of them pay for a logarithm

The accumulation phase reads the three planes and classifies:

| mode | cell | jump | log needed |
| --- | --- | --- | --- |
| 0 | `d = 0`, `prod ≠ n` | `−(log n)²` | yes |
| 1 | `d = 1`, `prod ≠ n` | `+2·log p·log Q` | yes |
| 2 | `d = 1`, `prod = n` | `−(log p)²` | no |
| 3 | `d = 2`, `prod = n` | `+2·log p·log q` | no |

Everything else has three or more distinct primes and contributes nothing.
`Q = n/prod` is the large prime; its logarithm is **not** computed directly —
`log Q = lnFix n − lsum`, one subtraction, which is why the log phase runs on
`n` (increasing along the stream, so `⌊log₂ n⌋` stays incremental) rather than
on `Q` (which jumps around and would need a `clz` the fragment lacks).

Modes 2 and 3 need no squaring loop at all: both weights are already in the
cell.  They still go through the stream, because the running extrema of `R₂*`
are only right if the jumps are applied in increasing `n`; they simply finish
after one round instead of `S`.

## The test points are the jumps, not the integers

Between consecutive jumps `R₂*` increases by `2γ` per integer and the majorant
`1.93·√n·log n` increases too, so on `[prev, cur−1]`

* the maximum of `R₂*` is at `cur−1` and the minimum of the majorant at
  `prev`: **clause 1** is tested once, at `cur−1`, against `thr(prev)`;
* the minimum of `R₂*` is at `prev`, where the majorant binds hardest from
  below: **clause 2** is tested at each test point, right after its jump.

Both bounds then hold at every integer of the cell, and the artifact runs
about `0.3·L` clause tests per window rather than `L`.

## The error is carried, not assumed

`lnFix m = ⌊2^S·ln m⌋` up to `4` ulps **on one side** (`logFix_bracket`'s two,
plus two for the conversion to natural logarithm), and every jump is a
*product* of two such values, so a term is off by at most
`2·4·(log p + log q) ≤ 16·log n` ulps of `2^-S`.  The artifact keeps a running
budget register, incremented by `16·(⌊log₂ n⌋+1)·ln 2 + 2` at every test
point, and adds it to both clause tests, so a passing run bounds the **real**
`R₂*` and not merely its fixed-point image.  At `S = 24` over `2.1·10¹⁰` the
budget reaches `8.4·10⁴` against a margin of `1.65·10⁶`: twenty times inside.

`S = 24` is also forced from above: a jump is a `64×64` product of two `lnFix`
values, so `(2^S·log hi)² < 2⁶⁴` caps `S ≤ 27`, and one word then holds
`2^S·R₂*` with the bias.  No two-limb accumulator is needed here — the `ψ`
residue's, in `Verified/AddWide.lean`, is the case where it was.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`: `r2Program_wf` and
`r2Program_compiled`, so `AProgram.evalCC_compile` applies and the emitted C
computes exactly `denote`.

Not proved, exactly as in `ArraySegSieve` and `PsiSegSieve`: that `denote`
*is* the residue.  That is checked by kernel evaluation against a
**trial-division** reference at a tiny configuration — which shares no code
with the sieve — and by the artifact against `bench/ref_r2.c` at `10⁶`, `10⁷`
and `10⁸`.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (lnFix L2hi L2lo storeLit storeLits seedRegs)

/-! ## Emit-time constants

The fixed-point scale `S` is a parameter carried by the configuration.  The
production value is `24`: a jump is a product of two `lnFix` values, so
`(2^S·log hi)² < 2⁶⁴` caps `S ≤ 27`, and the accumulated enclosure at `S = 24`
is `8.4·10⁴` against a margin of `1.65·10⁶`.
-/

/-- The production fixed-point scale. -/
def defaultS : Nat := 24

/-- `2γ` to thirty places, truncated **down**, over `10³⁰`. -/
def gamma2Num : Nat := 1154431329803065721213024180164
def scaleDen : Nat := 10 ^ 30

/-- `ln 2` to thirty places, rounded **up**, over `10³⁰`. -/
def ln2NumUp : Nat := 693147180559945309417232121459

/-- `⌊2γ·2^S⌋`: the per-integer linear increment.  Rounded down, so the
accumulator runs at most one ulp per integer *below* the true value; clause 1
adds `n` back. -/
def gammaStep (S : Nat) : Nat := gamma2Num * 2 ^ S / scaleDen

/-- `⌈2^S·ln 2⌉`: turns `⌊log₂ n⌋ + 1` into an upper bound for `2^S·log n`,
which is what the per-term error budget is stated against. -/
def ln2Up (S : Nat) : Nat := (ln2NumUp * 2 ^ S + scaleDen - 1) / scaleDen

/-- `⌊1.93·2¹⁶⌋`, the majorant's constant as a dyadic, rounded **down** so
that `(a193·⌊√n⌋·lnLo) >>> 16 ≤ 1.93·2^S·√n·log n` and each test is the
stronger statement. -/
def a193 : Nat := 193 * 2 ^ 16 / 100

/-- The accumulator's bias, `2^(S+24)`.  `|R₂*(n)| ≤ 1.93·√n·log n ≤ 6.7·10⁶`
on the whole range, so `2^S·|R₂*| ≤ 1.1·10¹⁴` and `2⁴⁸` clears it `2.5×` over
while `D` stays one word. -/
def biasOf (S : Nat) : Nat := 2 ^ (S + 24)

/-- Bits of an entry's value field: `p^j ≤ hi < 2³⁵`. -/
def valBits : Nat := 35
/-- Bits of an entry's weight field: `lnFix p < 2²⁸` for `p ≤ 1.4·10⁵`. -/
def wtBits : Nat := 28
def maskVal : Nat := 2 ^ valBits - 1
def maskWt : Nat := 2 ^ wtBits - 1
def maskAux : Nat := 2 ^ 29 - 1

/-- A mark-table entry: the prime power to step by, the weight `lnFix p` of
its base prime, and whether it is the base prime itself. -/
def packEntry (v w f : Nat) : Nat := v + w * 2 ^ valBits + f * 2 ^ 63

/-! ## Emit-time number theory

Everything in this section runs in Lean when the artifact is built.  None of
it is compiled; it only produces the literals the program carries.
-/

/-- Smallest-prime-factor table for `[0, n]`. -/
def spfTable (n : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := Array.range (n + 1)
  let mut d := 2
  while d * d ≤ n do
    if a[d]! == d then
      let mut m := d * d
      while m ≤ n do
        if a[m]! == m then a := a.set! m d
        m := m + d
    d := d + 1
  return a

/-- The distinct prime factors of `n`, in increasing order. -/
def factorsOf (a : Array Nat) (n : Nat) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut m := n
  let mut fuel := 64
  while m > 1 && fuel > 0 do
    let p := a[m]!
    out := out.push p
    while m % p == 0 do
      m := m / p
    fuel := fuel - 1
  return out.toList

/-- `v_p(n)`, by division.  Structurally recursive rather than a `while`, so
that the kernel can unfold it: `classifyList` is evaluated by `decide` in the
sanity checks below, and a `do`-`while` is opaque there. -/
def padicValAux (n p : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => if 1 < p && n % p = 0 then padicValAux (n / p) p fuel + 1 else 0

def padicVal (n p : Nat) : Nat := padicValAux n p 64

/-- The mark table: the primes `p ≤ ⌊√hi⌋` with their weights, one cell each.

The higher powers are **not** in the table.  They cost nothing to generate:
when the multiples of `p^j` run past the window the loop tries `p^{j+1}`
first, and only steps the cursor when that would exceed `hi`.  Eight
instructions, and it is what keeps the init block compilable — at
`hi = 2.1·10¹⁰` the powers are 14 006 of the 27 421 entries, so the emitted C
halves, from 82 277 statements to 40 261.  There is still no root phase: a
root phase can collect prime *values* but not their logarithms. -/
def markTable (S hi : Nat) : List Nat :=
  (primesBelow (Nat.sqrt hi + 1)).map (fun p => packEntry p (lnFix S p) 1)

/-- Mark steps a window of `len` cells needs: one per multiple of each prime
**power** `p^j ≤ hi`, one per power to advance the cursor or bump it, and
slack. -/
def markBudget (root hi len : Nat) : Nat := Id.run do
  let mut acc := 16
  for p in primesBelow (root + 1) do
    let mut q := p
    while q ≤ hi do
      acc := acc + len / q + 2
      q := q * p
  return acc

/-! ### Classification, at emit time

The same four modes the loop decodes, but read off a true factorisation rather
than off the sieve's three planes.  Used for the head fold and for the two
budgets; `Check` below carries a second, independent copy by trial division.
-/

/-- `(mode, u, v)` at `n`, whose distinct prime factors are `ps`.  The jump is
`±(u·v)·2^{mode &&& 1} / 2^S`; `mode = 4` means "no jump". -/
def classifyList (S n root : Nat) : List Nat → Nat × Nat × Nat
  | [p] => if root < p then (0, lnFix S n, lnFix S n) else (2, lnFix S p, lnFix S p)
  | [p, q] =>
      if root < q then (1, lnFix S p, lnFix S n - lnFix S p * padicVal n p)
      else (3, lnFix S p, lnFix S q)
  | _ => (4, 0, 0)

/-- The jump the loop applies, as `(mode, term)`. -/
def jumpOf (S n root : Nat) (ps : List Nat) : Nat × Nat :=
  let c := classifyList S n root ps
  (c.1, if c.1 == 4 then 0 else ((c.2.1 * c.2.2) <<< (c.1 % 2)) >>> S)

/-! ## The head, folded exactly at emit time

`[1, lo−1]` is not swept by the artifact — `lo > ⌊√hi⌋` is what makes an
unmarked cell a prime — so it is folded here, in Lean, with the identical
fixed-point arithmetic, and its clauses are tested at **every** integer rather
than at test points only.  That matters at the bottom of the range, where
`⌊√n⌋` is coarse and the prev-based weakening of clause 1 is not affordable:
at `n = 2` the majorant is `1.93·√2·log 2 = 1.892` while `⌊√2⌋ = 1` gives
`1.338`, below the true `R₂*(2) = 1.828`.
-/

structure R2Seed where
  d : Nat
  err : Nat
  prev : Nat
  terms : Nat
  sq : Nat
  sq2 : Nat
  ex : Nat
  th : Nat
  ln : Nat
  thr : Nat
  viol : Nat
  deriving Repr

/-- Fold `[1, top]` exactly, testing both clauses at every `n ≥ 3`.  `root` is
the small/large split the artifact will use; in the head every prime factor is
named directly, so it only picks the convention for mode `1`. -/
def headFold (S top root : Nat) : R2Seed := Id.run do
  let spf := spfTable top
  let bias := biasOf S
  let g := gammaStep S
  let l2 := ln2Up S
  let mut d := bias
  let mut err := 0
  let mut terms := 0
  let mut prev := 0
  let mut sq := 0
  let mut sq2 := 1
  let mut ex := 0
  let mut th := 2
  let mut ln := 0
  let mut thr := 0
  let mut viol := 0
  for n in [1:top+1] do
    d := d + g
    while n ≥ sq2 do
      sq := sq + 1
      sq2 := (sq + 1) * (sq + 1)
    while n ≥ th do
      ex := ex + 1
      th := 2 * th
    let mt := jumpOf S n root (factorsOf spf n)
    if mt.1 ≠ 4 then
      if mt.1 % 2 == 1 then d := d + mt.2 else d := d - mt.2
      err := err + ((ex + 1) * l2) / 2 ^ (S - 4) + 2
      terms := terms + 1
      prev := n
    ln := lnFix S n
    thr := a193 * sq * ln / 2 ^ 16
    if n ≥ 3 then
      if d + err + n > bias + thr then viol := viol + 1
      if d + thr < bias + err then viol := viol + 1
  return { d := d, err := err, prev := prev, terms := terms, sq := sq, sq2 := sq2,
           ex := ex, th := th, ln := ln, thr := thr, viol := viol }

/-! ## Configuration -/

structure R2Cfg where
  /-- First integer of the main sweep; must exceed `⌊√hi⌋`. -/
  lo : Nat
  /-- Cells per window. -/
  segLen : Nat
  /-- Number of windows. -/
  segCount : Nat
  /-- The fixed-point scale. -/
  sc : Nat
  /-- Mark steps budgeted per window. -/
  markSteps : Nat
  /-- Log-phase iterations budgeted per window: `S` per mode-`0`/`1` test
  point, one per mode-`2`/`3` test point.  Too small is *checked*, not
  silently wrong: a stream still undrained at window turnover counts a
  violation. -/
  logSteps : Nat
  /-- Test points budgeted per window.  A push past this clamps to a sink and
  counts a violation. -/
  streamCap : Nat
  /-- The mark table, packed one entry to a cell. -/
  table : List Nat
  deriving Repr

def R2Cfg.hi (c : R2Cfg) : Nat := c.lo + c.segLen * c.segCount - 1
def R2Cfg.tableLen (c : R2Cfg) : Nat := c.table.length
def R2Cfg.root (c : R2Cfg) : Nat := Nat.sqrt c.hi
def R2Cfg.period (c : R2Cfg) : Nat := c.markSteps + c.segLen + c.logSteps
def R2Cfg.firstEntry (c : R2Cfg) : Nat := c.table.headD (packEntry 2 0 1)
def R2Cfg.q0 (c : R2Cfg) : Nat := c.firstEntry % 2 ^ valBits
def R2Cfg.w0 (c : R2Cfg) : Nat := c.firstEntry / 2 ^ valBits % 2 ^ wtBits

/-- Test points and log rounds a window `[w, w+len)` produces, by an emit-time
segmented classification of that one window. -/
def windowStats (S w len root : Nat) : Nat × Nat := Id.run do
  if len = 0 then return (0, 0)
  let top := w + len - 1
  let mut cnt : Array Nat := Array.replicate len 0
  let mut prod : Array Nat := Array.replicate len 1
  for p in primesBelow (root + 1) do
    let mut q := p
    while q ≤ top do
      let mut m := ((w + q - 1) / q) * q
      while m ≤ top do
        prod := prod.set! (m - w) (prod[m - w]! * p)
        if q == p then cnt := cnt.set! (m - w) (cnt[m - w]! + 1)
        m := m + q
      q := q * p
  let mut points := 0
  let mut rounds := 0
  for i in [0:len] do
    let big := if prod[i]! == w + i then 0 else 1
    let om := cnt[i]! + big
    if om == 1 || om == 2 then
      points := points + 1
      rounds := rounds + (if big == 1 then S else 1)
  return (points, rounds)

/-- Windows to probe when sizing the two budgets.  Neither density is
monotone in `w`, and in opposite ways: the mode-`2`/`3` cells (both primes
below the *fixed* `√hi`) thin out as `w` grows, while the mode-`0`/`1` cells —
the ones that cost `S` rounds each — start almost absent just above
`lo ≈ √hi`, where a prime factor above `√hi` barely fits, and rise to their
asymptotic density.  The round count therefore *peaks a window or two in*.
Probing only the first window under-budgets the log phase by 1.3% at
`hi = 10⁷`, which the drain guard catches — it is not silently wrong — but
which costs a run.  These seven probes bracket the peak. -/
def probeWindows (segCount : Nat) : List Nat :=
  ([0, 1, 2, segCount / 4, segCount / 2, 3 * segCount / 4, segCount - 1].map
    (fun i => min i (segCount - 1))).eraseDups

/-- The configuration at `(lo, segLen, segCount)`, with both budgets set to
the maximum over the probe windows plus a `10%` margin.  Both budgets are
checked in the loop, so a mis-sized one reports a failure rather than a wrong
answer. -/
def R2Cfg.ofScale (S lo segLen segCount : Nat) : R2Cfg :=
  let hi := lo + segLen * segCount - 1
  let root := Nat.sqrt hi
  let tab := markTable S hi
  let st := (probeWindows segCount).foldl
    (fun acc i =>
      let r := windowStats S (lo + i * segLen) segLen root
      (max acc.1 r.1, max acc.2 r.2)) (0, 0)
  { lo := lo, segLen := segLen, segCount := segCount, sc := S
    markSteps := markBudget root hi segLen
    logSteps := st.2 * 110 / 100 + 128
    streamCap := st.1 * 110 / 100 + 128
    table := tab }

def R2Cfg.ofRange (lo segLen segCount : Nat) : R2Cfg :=
  R2Cfg.ofScale defaultS lo segLen segCount

/-- A **chained** artifact: it sweeps `[lo, lo + segLen·segCount − 1]`, but its
mark table and its budgets are those of the global sweep to `tableHi`.  This is
what a production chain looks like — one artifact per slice, all of them
carrying the primes of the whole range — and it is also the only way to
measure the cost of the artifact at `n ≈ 10¹⁰` without sweeping `10¹⁰`
integers.

`lo > ⌊√tableHi⌋` is the precondition, and it is the *global* one: an unmarked
cell is a prime because a composite `n ≤ tableHi` has a prime factor at most
`⌊√tableHi⌋`, all of which the table carries. -/
def R2Cfg.ofChain (S lo segLen segCount tableHi : Nat) : R2Cfg :=
  let root := Nat.sqrt tableHi
  let tab := markTable S tableHi
  let st := (probeWindows segCount).foldl
    (fun acc i =>
      let r := windowStats S (lo + i * segLen) segLen root
      (max acc.1 r.1, max acc.2 r.2)) (0, 0)
  { lo := lo, segLen := segLen, segCount := segCount, sc := S
    markSteps := markBudget root (lo + segLen * segCount - 1) segLen
    logSteps := st.2 * 110 / 100 + 128
    streamCap := st.1 * 110 / 100 + 128
    table := tab }

/-! ### Array layout

Three planes of `L` cells, their three sinks at `3L`, `4L` and `5L` — the gap
between them is address space only, never touched, and the emitted C's array
is `static`, so untouched pages cost nothing — then the mark table, the
stream, and the result cells.
-/

def R2Cfg.sink (c : R2Cfg) : Nat := 3 * c.segLen
def R2Cfg.tableBase (c : R2Cfg) : Nat := 5 * c.segLen + 1
def R2Cfg.streamBase (c : R2Cfg) : Nat := c.tableBase + c.tableLen + 1
def R2Cfg.streamSink (c : R2Cfg) : Nat := c.streamBase + 2 * c.streamCap
def R2Cfg.resultBase (c : R2Cfg) : Nat := c.streamSink + 2
def R2Cfg.arrayLen (c : R2Cfg) : Nat := c.resultBase + 12

/-! ## Register allocation

`2`–`7` and `170`–`172` the sieve core's persistent state, `8`–`138`
recomputed every iteration, `180`–`197` the residue's persistent state,
`200`–`345` the log phase, the tail and the epilogue.
-/

def rPi : Nat := 2      -- mark-table cursor
def rQ : Nat := 3       -- current entry's prime power
def rJ : Nat := 4       -- current multiple, as a cell index
def rR : Nat := 5       -- position inside the window
def rW : Nat := 6       -- window base
def rZero : Nat := 7    -- constant 0, for the clearing stores
def rBp : Nat := 170    -- current entry's base prime
def rWt : Nat := 171    -- current entry's weight, lnFix p
def rFs : Nat := 172    -- current entry's j = 1 flag

def rD : Nat := 180     -- the biased accumulator
def rErr : Nat := 181   -- the running enclosure budget
def rPrev : Nat := 182  -- last test point
def rTerms : Nat := 183
def rSq : Nat := 184    -- ⌊√n⌋
def rSq2 : Nat := 185   -- (⌊√n⌋+1)²
def rEx : Nat := 186    -- ⌊log₂ n⌋
def rTh : Nat := 187    -- 2^(rEx+1)
def rLn : Nat := 188    -- a lower bound for 2^S·log n
def rThr : Nat := 189   -- the majorant at the last test point
def rViol : Nat := 190
def rWc : Nat := 191    -- stream write cursor
def rEc : Nat := 192    -- stream read cursor
def rK : Nat := 193     -- squaring-round counter
def rNe : Nat := 194    -- latched test point
def rPl : Nat := 195    -- latched payload
def rXm : Nat := 196    -- mantissa
def rAa : Nat := 197    -- log bits so far

def regCount : Nat := 400
def outputReg : Nat := 190      -- `rViol`

/-! ## Phase one: marking, with multiplicity -/

def R2Cfg.markBody (c : R2Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let SNK := c.sink
  let q0 := c.q0
  let w0 := c.w0
  [ -- phase selectors: mark, accumulate, log
    .scalar (.binop 8 .lt (.reg rR) (.lit T))
  , .scalar (.binop 14 .lt (.reg rR) (.lit (T + L)))
  , .scalar (.binop 9 .sub (.reg 14) (.reg 8))           -- inAcc
  , .scalar (.binop 15 .sub (.lit 1) (.reg 14))          -- inLog
    -- window start: reset the cursor and the entry registers, branchlessly
  , .scalar (.binop 10 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 11 .sub (.lit 1) (.reg 10))
  , .scalar (.binop 12 .urem (.reg rW) (.lit q0))
  , .scalar (.binop 13 .sub (.lit q0) (.reg 12))
  , .scalar (.binop 16 .urem (.reg 13) (.lit q0))
  , .scalar (.binop rPi .mul (.reg 11) (.reg rPi))
  , .scalar (.binop 17 .mul (.reg 10) (.lit q0))
  , .scalar (.binop 18 .mul (.reg 11) (.reg rQ))
  , .scalar (.binop rQ .add (.reg 17) (.reg 18))
  , .scalar (.binop 19 .mul (.reg 11) (.reg rBp))
  , .scalar (.binop rBp .add (.reg 17) (.reg 19))
  , .scalar (.binop 20 .mul (.reg 10) (.lit w0))
  , .scalar (.binop 21 .mul (.reg 11) (.reg rWt))
  , .scalar (.binop rWt .add (.reg 20) (.reg 21))
  , .scalar (.binop 22 .mul (.reg 11) (.reg rFs))
  , .scalar (.binop rFs .add (.reg 10) (.reg 22))
  , .scalar (.binop 23 .mul (.reg 10) (.reg 16))
  , .scalar (.binop 24 .mul (.reg 11) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 23) (.reg 24))
    -- the mark step: three planes, or the three sinks
  , .scalar (.binop 25 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 26 .mul (.reg 25) (.reg 8))          -- inR
  , .scalar (.binop 27 .sub (.lit 1) (.reg 26))
  , .scalar (.binop 28 .mul (.reg 26) (.reg rJ))
  , .scalar (.binop 29 .mul (.reg 27) (.lit SNK))
  , .scalar (.binop 30 .add (.reg 28) (.reg 29))         -- prod cell
  , .scalar (.binop 31 .add (.reg 30) (.lit L))          -- lsum cell
  , .scalar (.binop 32 .add (.reg 30) (.lit (2 * L)))    -- W cell
  , .load 33 30
  , .scalar (.binop 34 .eq (.reg 33) (.lit 0))
  , .scalar (.binop 35 .add (.reg 33) (.reg 34))
  , .scalar (.binop 36 .mul (.reg 35) (.reg rBp))
  , .store 30 36
  , .load 37 31
  , .scalar (.binop 38 .add (.reg 37) (.reg rWt))
  , .store 31 38
  , .load 39 32
  , .scalar (.binop 40 .lshr (.reg 39) (.lit 56))        -- distinct count
  , .scalar (.binop 41 .eq (.reg 40) (.lit 0))
  , .scalar (.binop 42 .eq (.reg 40) (.lit 1))
  , .scalar (.binop 43 .lt (.reg 40) (.lit 3))
  , .scalar (.binop 44 .mul (.reg rWt) (.reg 41))
  , .scalar (.binop 45 .shl (.reg rWt) (.lit wtBits))
  , .scalar (.binop 46 .mul (.reg 45) (.reg 42))
  , .scalar (.binop 47 .shl (.reg 43) (.lit 56))
  , .scalar (.binop 48 .add (.reg 44) (.reg 46))
  , .scalar (.binop 49 .add (.reg 48) (.reg 47))
  , .scalar (.binop 50 .mul (.reg 49) (.reg rFs))
  , .scalar (.binop 51 .add (.reg 39) (.reg 50))
  , .store 32 51
    -- the multiples of the current power ran past the window: bump to the
    -- next power of the same prime if it still fits under `hi`, and only then
    -- step the cursor.  This is where the `j ≥ 2` entries come from, and why
    -- the table carries only the primes.
  , .scalar (.binop 52 .mul (.reg 8) (.reg 27))          -- advance
  , .scalar (.binop 150 .mul (.reg rQ) (.reg rBp))       -- p^{j+1}
  , .scalar (.binop 151 .le (.reg 150) (.lit c.hi))
  , .scalar (.binop 152 .mul (.reg 52) (.reg 151))       -- bump
  , .scalar (.binop 153 .sub (.reg 52) (.reg 152))       -- step
  , .scalar (.binop 53 .add (.reg rPi) (.reg 153))
  , .scalar (.binop 54 .gt (.reg 53) (.lit K))
  , .scalar (.binop 55 .sub (.lit 1) (.reg 54))
  , .scalar (.binop 56 .mul (.reg 55) (.reg 53))
  , .scalar (.binop 57 .mul (.reg 54) (.lit K))
  , .scalar (.binop rPi .add (.reg 56) (.reg 57))
  , .scalar (.binop 58 .add (.reg rPi) (.lit c.tableBase))
  , .load 59 58
  , .scalar (.binop 60 .band (.reg 59) (.lit maskVal))   -- the prime
  , .scalar (.binop 61 .lshr (.reg 59) (.lit valBits))
  , .scalar (.binop 62 .band (.reg 61) (.lit maskWt))    -- its weight
  , .scalar (.binop 64 .sub (.lit 1) (.reg 52))          -- keep
  , .scalar (.binop 65 .add (.reg rJ) (.reg rQ))         -- next multiple, old q
  , .scalar (.binop 66 .mul (.reg 152) (.reg 150))
  , .scalar (.binop 67 .mul (.reg 153) (.reg 60))
  , .scalar (.binop 68 .mul (.reg 64) (.reg rQ))
  , .scalar (.binop 69 .add (.reg 66) (.reg 67))
  , .scalar (.binop rQ .add (.reg 69) (.reg 68))
  , .scalar (.binop 70 .sub (.lit 1) (.reg 153))
  , .scalar (.binop 71 .mul (.reg 153) (.reg 60))
  , .scalar (.binop 72 .mul (.reg 70) (.reg rBp))
  , .scalar (.binop rBp .add (.reg 71) (.reg 72))
  , .scalar (.binop 73 .mul (.reg 153) (.reg 62))
  , .scalar (.binop 74 .mul (.reg 70) (.reg rWt))
  , .scalar (.binop rWt .add (.reg 73) (.reg 74))
  , .scalar (.binop 63 .mul (.reg 64) (.reg rFs))        -- `j = 1` is a step
  , .scalar (.binop rFs .add (.reg 153) (.reg 63))
  , .scalar (.binop 75 .urem (.reg rW) (.reg rQ))
  , .scalar (.binop 76 .sub (.reg rQ) (.reg 75))
  , .scalar (.binop 77 .urem (.reg 76) (.reg rQ))        -- first cell of the entry
  , .scalar (.binop 78 .eq (.reg rPi) (.lit K))          -- table exhausted
  , .scalar (.binop 79 .sub (.lit 1) (.reg 78))
  , .scalar (.binop 80 .mul (.reg 78) (.lit (L + 1)))
  , .scalar (.binop 81 .mul (.reg 79) (.reg 77))
  , .scalar (.binop 82 .add (.reg 80) (.reg 81))
  , .scalar (.binop 83 .mul (.reg 52) (.reg 82))
  , .scalar (.binop 84 .mul (.reg 64) (.reg 65))
  , .scalar (.binop rJ .add (.reg 83) (.reg 84))
    -- the mark budget, checked.  `markSteps` too small truncates the sieve
    -- *silently* — the classification is then wrong, not merely incomplete —
    -- so the phase's last iteration asserts that the cursor reached the end of
    -- the table, which it does only after the last prime's last power.
  , .scalar (.binop 154 .eq (.reg rR) (.lit (T - 1)))
  , .scalar (.binop 155 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 156 .mul (.reg 154) (.reg 155))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 156))
  ]

/-! ## Phase two: classification and compaction -/

def R2Cfg.classBody (c : R2Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let SNK := c.sink
  [ .scalar (.binop 85 .sub (.reg rR) (.lit T))
  , .scalar (.binop 86 .mul (.reg 9) (.reg 85))          -- i
  , .scalar (.binop 87 .add (.reg 86) (.reg rW))         -- n
  , .scalar (.binop 88 .add (.reg 86) (.lit L))
  , .scalar (.binop 89 .add (.reg 86) (.lit (2 * L)))
  , .load 90 86                                          -- prod
  , .load 91 88                                          -- lsum
  , .load 92 89                                          -- W
  , .scalar (.binop 93 .eq (.reg 90) (.lit 0))
  , .scalar (.binop 94 .add (.reg 90) (.reg 93))         -- prod, 0 meaning 1
  , .scalar (.binop 95 .ne (.reg 94) (.reg 87))          -- a large prime is left
  , .scalar (.binop 96 .lshr (.reg 92) (.lit 56))        -- distinct count
  , .scalar (.binop 97 .band (.reg 92) (.lit maskWt))    -- w1
  , .scalar (.binop 98 .lshr (.reg 92) (.lit wtBits))
  , .scalar (.binop 99 .band (.reg 98) (.lit maskWt))    -- w2
    -- zero the three cells just read, so the next window starts clean
  , .scalar (.binop 100 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 101 .mul (.reg 100) (.lit SNK))
  , .scalar (.binop 102 .add (.reg 86) (.reg 101))
  , .scalar (.binop 103 .add (.reg 102) (.lit L))
  , .scalar (.binop 104 .add (.reg 102) (.lit (2 * L)))
  , .store 102 rZero
  , .store 103 rZero
  , .store 104 rZero
    -- the four modes
  , .scalar (.binop 105 .eq (.reg 96) (.lit 0))
  , .scalar (.binop 106 .eq (.reg 96) (.lit 1))
  , .scalar (.binop 107 .eq (.reg 96) (.lit 2))
  , .scalar (.binop 108 .sub (.lit 1) (.reg 95))
  , .scalar (.binop 109 .mul (.reg 105) (.reg 95))       -- mode 0
  , .scalar (.binop 110 .mul (.reg 106) (.reg 95))       -- mode 1
  , .scalar (.binop 111 .mul (.reg 106) (.reg 108))      -- mode 2
  , .scalar (.binop 112 .mul (.reg 107) (.reg 108))      -- mode 3
  , .scalar (.binop 113 .add (.reg 109) (.reg 110))
  , .scalar (.binop 114 .add (.reg 111) (.reg 112))
  , .scalar (.binop 115 .add (.reg 113) (.reg 114))      -- qualifies
  , .scalar (.binop 116 .mul (.reg 115) (.reg 9))        -- push
  , .scalar (.binop 117 .shl (.reg 111) (.lit 1))
  , .scalar (.binop 118 .mul (.reg 112) (.lit 3))
  , .scalar (.binop 119 .add (.reg 110) (.reg 117))
  , .scalar (.binop 120 .add (.reg 119) (.reg 118))      -- mode
    -- aux: the second weight for mode 3, the small part's logarithm otherwise
  , .scalar (.binop 121 .mul (.reg 112) (.reg 99))
  , .scalar (.binop 122 .sub (.lit 1) (.reg 112))
  , .scalar (.binop 123 .mul (.reg 122) (.reg 91))
  , .scalar (.binop 124 .add (.reg 121) (.reg 123))
  , .scalar (.binop 125 .shl (.reg 124) (.lit wtBits))
  , .scalar (.binop 126 .shl (.reg 120) (.lit 57))
  , .scalar (.binop 127 .add (.reg 97) (.reg 125))
  , .scalar (.binop 128 .add (.reg 127) (.reg 126))      -- payload
    -- compaction: append to the stream, or to the sink with a violation
  , .scalar (.binop 129 .lt (.reg rWc) (.lit c.streamCap))
  , .scalar (.binop 130 .mul (.reg 116) (.reg 129))      -- doPush
  , .scalar (.binop 131 .sub (.reg 116) (.reg 130))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 131))
  , .scalar (.binop 132 .shl (.reg rWc) (.lit 1))
  , .scalar (.binop 133 .add (.reg 132) (.lit c.streamBase))
  , .scalar (.binop 134 .mul (.reg 130) (.reg 133))
  , .scalar (.binop 135 .sub (.lit 1) (.reg 130))
  , .scalar (.binop 136 .mul (.reg 135) (.lit c.streamSink))
  , .scalar (.binop 137 .add (.reg 134) (.reg 136))
  , .store 137 87
  , .scalar (.binop 138 .add (.reg 137) (.lit 1))
  , .store 138 128
  , .scalar (.binop rWc .add (.reg rWc) (.reg 130))
  ]

/-! ## Phase three: the logarithm, the jump and the two clauses -/

def R2Cfg.logBody (c : R2Cfg) : List AInstr :=
  let S := c.sc
  let bias := biasOf S
  let g := gammaStep S
  let l2 := ln2Up S
  [ -- the stream entry under the read cursor
    .scalar (.binop 200 .shl (.reg rEc) (.lit 1))
  , .scalar (.binop 201 .add (.reg 200) (.lit c.streamBase))
  , .load 202 201
  , .scalar (.binop 203 .add (.reg 201) (.lit 1))
  , .load 204 203
  , .scalar (.binop 205 .lt (.reg rEc) (.reg rWc))
  , .scalar (.binop 206 .mul (.reg 205) (.reg 15))       -- live
  , .scalar (.binop 207 .eq (.reg rK) (.lit 0))
  , .scalar (.binop 208 .mul (.reg 207) (.reg 206))      -- start of an entry
  , .scalar (.binop 209 .sub (.lit 1) (.reg 208))
  , .scalar (.binop 210 .mul (.reg 208) (.reg 202))
  , .scalar (.binop 211 .mul (.reg 209) (.reg rNe))
  , .scalar (.binop rNe .add (.reg 210) (.reg 211))
  , .scalar (.binop 212 .mul (.reg 208) (.reg 204))
  , .scalar (.binop 213 .mul (.reg 209) (.reg rPl))
  , .scalar (.binop rPl .add (.reg 212) (.reg 213))
    -- ⌊log₂ n⌋, incrementally: test points are denser than primes, so one
    -- step per entry suffices, and the loop checks that it did
  , .scalar (.binop 214 .ge (.reg rNe) (.reg rTh))
  , .scalar (.binop 215 .mul (.reg 214) (.reg 208))
  , .scalar (.binop rEx .add (.reg rEx) (.reg 215))
  , .scalar (.binop 216 .mul (.reg 215) (.reg rTh))
  , .scalar (.binop rTh .add (.reg rTh) (.reg 216))
  , .scalar (.binop 217 .ge (.reg rNe) (.reg rTh))
  , .scalar (.binop 218 .mul (.reg 217) (.reg 208))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 218))
    -- the normalised mantissa, reset at the entry's first round.  The mask is
    -- the only thing between a register shift amount and C's undefined
    -- behaviour at a width of 64: `rEx ≤ 62` always, so it is a no-op.
  , .scalar (.binop 219 .sub (.lit 62) (.reg rEx))
  , .scalar (.binop 220 .band (.reg 219) (.lit 63))
  , .scalar (.binop 221 .shl (.reg rNe) (.reg 220))
  , .scalar (.binop 222 .mul (.reg 208) (.reg 221))
  , .scalar (.binop 223 .mul (.reg 209) (.reg rXm))
  , .scalar (.binop rXm .add (.reg 222) (.reg 223))
  , .scalar (.binop rAa .mul (.reg rAa) (.reg 209))
    -- one squaring round: Ports/LogFixPort.logRoundBody, verbatim
  , .scalar (.binop 224 .lshr (.reg rXm) (.lit 32))
  , .scalar (.binop 225 .band (.reg rXm) (.lit 4294967295))
  , .scalar (.binop 226 .mul (.reg 224) (.reg 224))
  , .scalar (.binop 227 .mul (.reg 224) (.reg 225))
  , .scalar (.binop 228 .mul (.reg 225) (.reg 225))
  , .scalar (.binop 229 .lshr (.reg 227) (.lit 29))
  , .scalar (.binop 230 .band (.reg 227) (.lit 536870911))
  , .scalar (.binop 231 .lshr (.reg 228) (.lit 62))
  , .scalar (.binop 232 .band (.reg 228) (.lit 4611686018427387903))
  , .scalar (.binop 233 .shl (.reg 230) (.lit 33))
  , .scalar (.binop 234 .add (.reg 233) (.reg 232))
  , .scalar (.binop 235 .ge (.reg 234) (.lit 4611686018427387904))
  , .scalar (.binop 236 .shl (.reg 226) (.lit 2))
  , .scalar (.binop 237 .add (.reg 236) (.reg 229))
  , .scalar (.binop 238 .add (.reg 237) (.reg 231))
  , .scalar (.binop 239 .add (.reg 238) (.reg 235))
  , .scalar (.binop 240 .ge (.reg 239) (.lit 9223372036854775808))
  , .scalar (.binop rXm .lshr (.reg 239) (.reg 240))
  , .scalar (.binop 241 .shl (.reg rAa) (.lit 1))
  , .scalar (.binop rAa .add (.reg 241) (.reg 240))
    -- the round counter.  A mode-2 or mode-3 entry needs no logarithm and
    -- finishes after one round; the two conditions are disjoint for `S > 1`.
  , .scalar (.binop 242 .lshr (.reg rPl) (.lit 57))      -- mode
  , .scalar (.binop 243 .ge (.reg 242) (.lit 2))         -- noLog
  , .scalar (.binop 244 .add (.reg rK) (.lit 1))
  , .scalar (.binop 245 .eq (.reg 244) (.lit S))
  , .scalar (.binop 246 .add (.reg 245) (.reg 243))
  , .scalar (.binop 247 .mul (.reg 246) (.reg 206))      -- fin
  , .scalar (.binop 248 .sub (.lit 1) (.reg 246))
  , .scalar (.binop 249 .mul (.reg 244) (.reg 248))
  , .scalar (.binop rK .mul (.reg 249) (.reg 206))
    -- ⌊2^S·ln n⌋ = high word of logFix · ⌊2⁶⁴ ln 2⌋
  , .scalar (.binop 250 .shl (.reg rEx) (.lit S))
  , .scalar (.binop 251 .add (.reg 250) (.reg rAa))      -- logFix S n
  , .scalar (.binop 252 .band (.reg 251) (.lit 4294967295))
  , .scalar (.binop 253 .lshr (.reg 251) (.lit 32))
  , .scalar (.binop 254 .mul (.reg 252) (.lit L2lo))
  , .scalar (.binop 255 .mul (.reg 252) (.lit L2hi))
  , .scalar (.binop 256 .mul (.reg 253) (.lit L2lo))
  , .scalar (.binop 257 .mul (.reg 253) (.lit L2hi))
  , .scalar (.binop 258 .lshr (.reg 254) (.lit 32))
  , .scalar (.binop 259 .add (.reg 255) (.reg 256))
  , .scalar (.binop 260 .add (.reg 259) (.reg 258))
  , .scalar (.binop 261 .lshr (.reg 260) (.lit 32))
  , .scalar (.binop 262 .add (.reg 257) (.reg 261))      -- lnFix n
    -- the payload, and the two factors of the jump
  , .scalar (.binop 263 .band (.reg rPl) (.lit maskWt))  -- w1
  , .scalar (.binop 264 .lshr (.reg rPl) (.lit wtBits))
  , .scalar (.binop 265 .band (.reg 264) (.lit maskAux)) -- aux
  , .scalar (.binop 266 .band (.reg 242) (.lit 1))       -- the jump is positive
  , .scalar (.binop 267 .eq (.reg 242) (.lit 0))
  , .scalar (.binop 268 .eq (.reg 242) (.lit 2))
  , .scalar (.binop 269 .eq (.reg 242) (.lit 3))
  , .scalar (.binop 270 .sub (.reg 262) (.reg 265))      -- log Q = lnFix n − lsum
  , .scalar (.binop 271 .mul (.reg 267) (.reg 270))
  , .scalar (.binop 272 .add (.reg 263) (.reg 271))      -- u
  , .scalar (.binop 273 .sub (.lit 1) (.reg 243))
  , .scalar (.binop 274 .mul (.reg 273) (.reg 270))
  , .scalar (.binop 275 .mul (.reg 268) (.reg 263))
  , .scalar (.binop 276 .mul (.reg 269) (.reg 265))
  , .scalar (.binop 277 .add (.reg 274) (.reg 275))
  , .scalar (.binop 278 .add (.reg 277) (.reg 276))      -- v
  , .scalar (.binop 279 .mul (.reg 272) (.reg 278))
  , .scalar (.binop 280 .shl (.reg 279) (.reg 266))
  , .scalar (.binop 281 .lshr (.reg 280) (.lit S))       -- the jump
    -- the per-term enclosure: 16·log n + 2 ulps of 2^-S
  , .scalar (.binop 282 .add (.reg rEx) (.lit 1))
  , .scalar (.binop 283 .mul (.reg 282) (.lit l2))
  , .scalar (.binop 284 .lshr (.reg 283) (.lit (S - 4)))
  , .scalar (.binop 285 .add (.reg 284) (.lit 2))
    -- advance the linear part to n − 1, and check the gap fits one word
  , .scalar (.binop 286 .sub (.reg rNe) (.reg rPrev))
  , .scalar (.binop 287 .lt (.reg 286) (.lit 65536))
  , .scalar (.binop 288 .sub (.lit 1) (.reg 287))
  , .scalar (.binop 289 .mul (.reg 288) (.reg 247))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 289))
  , .scalar (.binop 290 .sub (.reg 286) (.lit 1))
  , .scalar (.binop 291 .mul (.reg 290) (.lit g))
  , .scalar (.binop 292 .mul (.reg 291) (.reg 247))
  , .scalar (.binop rD .add (.reg rD) (.reg 292))
    -- clause 1 on `[prev, n−1]`, against the majorant at `prev`
  , .scalar (.binop 293 .add (.reg rD) (.reg rErr))
  , .scalar (.binop 294 .add (.reg 293) (.reg rNe))
  , .scalar (.binop 295 .add (.lit bias) (.reg rThr))
  , .scalar (.binop 296 .gt (.reg 294) (.reg 295))
  , .scalar (.binop 297 .mul (.reg 296) (.reg 247))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 297))
    -- the last linear step, onto `n` itself
  , .scalar (.binop 298 .mul (.reg 247) (.lit g))
  , .scalar (.binop rD .add (.reg rD) (.reg 298))
    -- ⌊√n⌋, incrementally, and the check that one step sufficed
  , .scalar (.binop 299 .ge (.reg rNe) (.reg rSq2))
  , .scalar (.binop 300 .mul (.reg 299) (.reg 247))
  , .scalar (.binop rSq .add (.reg rSq) (.reg 300))
  , .scalar (.binop 301 .shl (.reg rSq) (.lit 1))
  , .scalar (.binop 302 .add (.reg 301) (.lit 1))
  , .scalar (.binop 303 .mul (.reg 300) (.reg 302))
  , .scalar (.binop rSq2 .add (.reg rSq2) (.reg 303))
  , .scalar (.binop 304 .ge (.reg rNe) (.reg rSq2))
  , .scalar (.binop 305 .mul (.reg 304) (.reg 247))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 305))
    -- the running lower bound for `2^S·log n`, refreshed at every entry that
    -- computed a logarithm; a stale one is still a lower bound
  , .scalar (.binop 306 .mul (.reg 273) (.reg 247))
  , .scalar (.binop 307 .sub (.lit 1) (.reg 306))
  , .scalar (.binop 308 .mul (.reg 307) (.reg rLn))
  , .scalar (.binop 309 .mul (.reg 306) (.reg 262))
  , .scalar (.binop rLn .add (.reg 308) (.reg 309))
    -- the majorant at `n`, which is also the next clause-1 threshold
  , .scalar (.binop 310 .mul (.reg rSq) (.lit a193))
  , .scalar (.binop 311 .mul (.reg 310) (.reg rLn))
  , .scalar (.binop 312 .lshr (.reg 311) (.lit 16))
  , .scalar (.binop 313 .mul (.reg 247) (.reg 312))
  , .scalar (.binop 314 .sub (.lit 1) (.reg 247))
  , .scalar (.binop 315 .mul (.reg 314) (.reg rThr))
  , .scalar (.binop rThr .add (.reg 313) (.reg 315))
    -- the jump
  , .scalar (.binop 316 .mul (.reg 266) (.reg 247))
  , .scalar (.binop 317 .mul (.reg 316) (.reg 281))
  , .scalar (.binop 318 .sub (.reg 247) (.reg 316))
  , .scalar (.binop 319 .mul (.reg 318) (.reg 281))
  , .scalar (.binop rD .add (.reg rD) (.reg 317))
  , .scalar (.binop rD .sub (.reg rD) (.reg 319))
  , .scalar (.binop 320 .mul (.reg 285) (.reg 247))
  , .scalar (.binop rErr .add (.reg rErr) (.reg 320))
  , .scalar (.binop rTerms .add (.reg rTerms) (.reg 247))
    -- clause 2 at `n`, immediately after the jump
  , .scalar (.binop 321 .add (.reg rD) (.reg rThr))
  , .scalar (.binop 322 .add (.lit bias) (.reg rErr))
  , .scalar (.binop 323 .lt (.reg 321) (.reg 322))
  , .scalar (.binop 324 .mul (.reg 323) (.reg 247))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 324))
    -- advance
  , .scalar (.binop 325 .mul (.reg 247) (.reg rNe))
  , .scalar (.binop 326 .mul (.reg 314) (.reg rPrev))
  , .scalar (.binop rPrev .add (.reg 325) (.reg 326))
  , .scalar (.binop rEc .add (.reg rEc) (.reg 247))
  ]

/-! ## The tail: advance the window, and reset the stream -/

def R2Cfg.tailBody (c : R2Cfg) : List AInstr :=
  let L := c.segLen
  let P := c.period
  [ .scalar (.binop 330 .add (.reg rR) (.lit 1))
  , .scalar (.binop 331 .eq (.reg 330) (.lit P))
  , .scalar (.binop 332 .sub (.lit 1) (.reg 331))
  , .scalar (.binop rR .mul (.reg 332) (.reg 330))
  , .scalar (.binop 333 .mul (.reg 331) (.lit L))
  , .scalar (.binop rW .add (.reg rW) (.reg 333))
    -- the log phase must have drained the stream before the window turns over
  , .scalar (.binop 334 .lt (.reg rEc) (.reg rWc))
  , .scalar (.binop 335 .mul (.reg 334) (.reg 331))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 335))
  , .scalar (.binop rWc .mul (.reg rWc) (.reg 332))
  , .scalar (.binop rEc .mul (.reg rEc) (.reg 332))
  , .scalar (.binop rK .mul (.reg rK) (.reg 332))
  ]

def R2Cfg.body (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ c.logBody ++ c.tailBody

/-! ## Initialization and epilogue -/

/-- The array cells the init block writes: the mark table, then a sentinel of
value `1`.  The exhausted cursor marks nothing anyway — `rPi = tableLen` sends
the multiple to `L + 1` — and value `1` makes the bump `1 · 1 = 1` a fixed
point, so `rQ` can neither reach `0` (the `urem` would be undefined) nor
overflow. -/
def R2Cfg.tableCells (c : R2Cfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [(c.tableBase + c.tableLen, packEntry 1 0 0)]

def R2Cfg.seedList (c : R2Cfg) (s : R2Seed) : List (Nat × Nat) :=
  [ (rW, c.lo)
  , (rD, s.d), (rErr, s.err), (rPrev, s.prev), (rTerms, s.terms)
  , (rSq, s.sq), (rSq2, s.sq2), (rEx, s.ex), (rTh, s.th)
  , (rLn, s.ln), (rThr, s.thr) ]

def R2Cfg.init (c : R2Cfg) (s : R2Seed) : List AInstr :=
  storeLits c.tableCells ++ seedRegs (c.seedList s)

def storeResult (c : R2Cfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .store 90 reg ]

/-- The epilogue advances the linear part from the last test point to `hi`,
runs clause 1 once more there, and stores the carry-out of a chained run. -/
def R2Cfg.epilogue (c : R2Cfg) : List AInstr :=
  let S := c.sc
  [ .scalar (.binop 340 .sub (.lit c.hi) (.reg rPrev))
  , .scalar (.binop 341 .mul (.reg 340) (.lit (gammaStep S)))
  , .scalar (.binop rD .add (.reg rD) (.reg 341))
  , .scalar (.binop 342 .add (.reg rD) (.reg rErr))
  , .scalar (.binop 343 .add (.reg 342) (.lit c.hi))
  , .scalar (.binop 344 .add (.lit (biasOf S)) (.reg rThr))
  , .scalar (.binop 345 .gt (.reg 343) (.reg 344))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 345))
  ] ++
  storeResult c 0 rD ++ storeResult c 1 rErr ++ storeResult c 2 rPrev ++
  storeResult c 3 rTerms ++ storeResult c 4 rSq ++ storeResult c 5 rEx ++
  storeResult c 6 rTh ++ storeResult c 7 rLn ++ storeResult c 8 rThr ++
  storeResult c 9 rViol

def r2Program (c : R2Cfg) (s : R2Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init s
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-! ## Well-formedness, and the bridge instantiated

`AProgram.WF` is decided by the same `Bool` mirror `ArraySegSieve` uses, so
every obligation is `rfl` at every configuration.
-/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeResult_all (c : R2Cfg) (slot reg : Nat) (h : reg < regCount) :
    (storeResult c slot reg).all (ainstrWFB regCount) = true := by
  simp only [storeResult, regCount, List.all_cons, List.all_nil, ainstrWFB,
    instrWFB, operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

set_option maxRecDepth 40000 in
theorem body_all (c : R2Cfg) : c.body.all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem seedRegs_all (l : List (Nat × Nat)) (h : ∀ x ∈ l, x.1 < regCount) :
    (seedRegs l).all (ainstrWFB regCount) = true := by
  simp only [seedRegs, List.all_map]
  refine List.all_eq_true.mpr (fun x hx => ?_)
  have hlt := h x hx
  simp only [Function.comp_apply, ainstrWFB, instrWFB, operandWFB,
    Bool.and_true, decide_eq_true_eq]
  exact hlt

theorem seedList_ok (c : R2Cfg) (s : R2Seed) :
    ∀ x ∈ c.seedList s, x.1 < regCount := by
  intro x hx
  have hall : (c.seedList s).all (fun y => decide (y.1 < regCount)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem init_all (c : R2Cfg) (s : R2Seed) :
    (c.init s).all (ainstrWFB regCount) = true :=
  all_append (storeLits_all _) (seedRegs_all _ (seedList_ok c s))

theorem epilogue_all (c : R2Cfg) :
    c.epilogue.all (ainstrWFB regCount) = true :=
  all_append (by rfl)
    (all_append (all_append (all_append (all_append (all_append (all_append
      (all_append (all_append (all_append
        (storeResult_all c 0 rD (by decide)) (storeResult_all c 1 rErr (by decide)))
        (storeResult_all c 2 rPrev (by decide)))
        (storeResult_all c 3 rTerms (by decide)))
        (storeResult_all c 4 rSq (by decide)))
        (storeResult_all c 5 rEx (by decide)))
        (storeResult_all c 6 rTh (by decide)))
        (storeResult_all c 7 rLn (by decide)))
        (storeResult_all c 8 rThr (by decide)))
        (storeResult_all c 9 rViol (by decide)))

/-- **The bridge's side condition.** -/
theorem r2Program_wf (c : R2Cfg) (s : R2Seed) : (r2Program c s).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the `R₂*` residue.**  For any array base at
which the window fits, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
number of failed clauses and guards, in the output register. -/
theorem r2Program_compiled (c : R2Cfg) (s : R2Seed) (base : Int)
    (hBase : BaseOk (r2Program c s).arrayLen base)
    (n : Nat) (hDenote : (r2Program c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((r2Program c s).initialMCC base) (r2Program c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(r2Program c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (r2Program_wf c s) base hBase n hDenote

/-! ## The reference

`refR2` is the same residue written directly as a Lean fold over `[lo, hi]`,
classified from a factorisation rather than from the sieve's three planes, and
is what the emitter compares the artifact against.  It is also what
`bench/ref_r2.c` computes, in the same fixed point.
-/

/-- `(D, err, terms, prev)` at `hi`, continuing the head at `lo − 1`. -/
def refR2 (S lo hi root : Nat) (s : R2Seed) : Nat × Nat × Nat × Nat := Id.run do
  let spf := spfTable hi
  let g := gammaStep S
  let l2 := ln2Up S
  let mut d := s.d
  let mut err := s.err
  let mut terms := s.terms
  let mut prev := s.prev
  let mut ex := s.ex
  let mut th := s.th
  for n in [lo:hi+1] do
    let mt := jumpOf S n root (factorsOf spf n)
    if mt.1 ≠ 4 then
      while n ≥ th do
        ex := ex + 1
        th := 2 * th
      d := d + g * (n - prev)
      if mt.1 % 2 == 1 then d := d + mt.2 else d := d - mt.2
      err := err + ((ex + 1) * l2) / 2 ^ (S - 4) + 2
      terms := terms + 1
      prev := n
  d := d + g * (hi - prev)
  return (d, err, terms, prev)

/-! ## Kernel sanity checks

The bridge does not depend on any of this: it says the artifact computes
`denote`, whatever `denote` is.  These checks are the other half — evidence
that `denote` is the residue it is meant to be.  They evaluate the whole
three-phase loop in the kernel at a tiny configuration and compare against a
**trial-division** reference, which shares no code with it: `factorsTD`
divides by every integer up to `√n`, where the artifact multiplies a plane by
a base prime once per marked power and compares the product against `n`.

`S = 4` here, not `24`, only so that the log phase is four rounds per entry
instead of twenty-four; the arithmetic is the same at every scale, and the
artifact repeats the comparison against `bench/ref_r2.c` at `S = 24` and
`hi = 10⁶, 10⁷, 10⁸`.
-/

/-! ## Kernel sanity checks

The bridge does not depend on any of this: it says the artifact computes
`denote`, whatever `denote` is.  These checks are the other half — evidence
that `denote` is the residue it is meant to be.  They evaluate the whole
three-phase loop in the kernel at a tiny configuration and compare against a
**trial-division** reference, which shares no code with it: `factorsTD`
divides by every integer up to `√n`, where the artifact multiplies a plane by
a base prime once per marked power and compares the product against `n`.

`S = 4` here, not `24`, only so that the log phase is four rounds per entry
instead of twenty-four; the arithmetic is the same at every scale, and the
artifact repeats the comparison against `bench/ref_r2.c` at `S = 24` and
`hi = 10⁶, 10⁷, 10⁸`.
-/

namespace Check

/-- Divide `p` out of `m` completely. -/
def divOut (m p fuel : Nat) : Nat :=
  match fuel with
  | 0 => m
  | fuel + 1 => if 1 < p && m % p = 0 then divOut (m / p) p fuel else m

/-- The distinct prime factors of `n` by trial division, structurally
recursive so that the kernel can unfold it. -/
def tdAux (m d fuel : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => if 1 < m then acc ++ [m] else acc
  | fuel + 1 =>
      if m < d * d then (if 1 < m then acc ++ [m] else acc)
      else if m % d = 0 then tdAux (divOut m d m) (d + 1) fuel (acc ++ [d])
      else tdAux m (d + 1) fuel acc

def factorsTD (n : Nat) : List Nat := tdAux n 2 (n + 2) []

/-- `(D, terms)` over `[lo, hi]`, folded from a trial-division classification
with the same fixed-point arithmetic. -/
def refFold (S lo hi root d0 t0 p0 : Nat) : Nat × Nat :=
  let step := fun (acc : Nat × Nat × Nat) (n : Nat) =>
    let mt := jumpOf S n root (factorsTD n)
    if mt.1 = 4 then acc
    else
      let d := acc.1 + gammaStep S * (n - acc.2.2)
      let d := if mt.1 % 2 = 1 then d + mt.2 else d - mt.2
      (d, acc.2.1 + 1, n)
  let r := ((List.range (hi + 1)).drop lo).foldl step (d0, t0, p0)
  (r.1 + gammaStep S * (hi - r.2.2), r.2.1)

/-- The head `[1, top]`, folded by the same trial-division reference. -/
def refHead (S top root : Nat) : Nat × Nat :=
  let step := fun (acc : Nat × Nat) (n : Nat) =>
    let mt := jumpOf S n root (factorsTD n)
    let d := acc.1 + gammaStep S
    if mt.1 = 4 then (d, acc.2)
    else ((if mt.1 % 2 = 1 then d + mt.2 else d - mt.2), acc.2 + 1)
  ((List.range (top + 1)).drop 1).foldl step (biasOf S, 0)

/-- One window of nine cells covering `[6, 14]`, at scale `S = 4`.  The mark
table is `2, 4, 8, 3, 9` — every prime power `≤ 14` with base `≤ ⌊√14⌋ = 3` —
— the loop generates `4`, `8` and `9` itself — and the window exercises all
four modes: `6 = 2·3` and `12 = 2²·3` are mode
`3`, `8 = 2³` and `9 = 3²` are mode `2`, `10 = 2·5` and `14 = 2·7` are mode
`1` (`5` and `7` exceed `⌊√14⌋ = 3`), and `7`, `11`, `13` are mode `0`.  The
three budgets are what `R2Cfg.ofScale 4 6 9 1` computes: `markBudget` is `37`,
and `windowStats 4 6 9 3 = (9, 24)`, nine test points and twenty-four rounds. -/
def cfg : R2Cfg :=
  { lo := 6, segLen := 9, segCount := 1, sc := 4
    markSteps := 37, logSteps := 40, streamCap := 12
    table := [ packEntry 2 11 1, packEntry 3 17 1 ] }

/-- The head `[1, 5]`, folded at emit time by `headFold 4 5 3`. -/
def seed : R2Seed :=
  { d := 268435475, err := 128, prev := 5, terms := 4
    sq := 2, sq2 := 9, ex := 2, th := 8, ln := 25, thr := 96, viol := 0 }

/-- …and the trial-division reference agrees with the head's accumulator and
its term count. -/
example : (seed.d, seed.terms) = refHead 4 5 3 := by decide

/-- The table is the two primes with their weights `lnFix 4 2 = 11` and
`lnFix 4 3 = 17`; it is what `markTable 4 14` builds. -/
example : cfg.table.map (fun e =>
      (e % 2 ^ valBits, e / 2 ^ valBits % 2 ^ wtBits, e / 2 ^ 63)) =
    [(2, 11, 1), (3, 17, 1)] := by decide

/-- A program with the epilogue stripped and the output pointed at one
accumulator, so a single residue register can be read off. -/
def probe (out : Nat) : AProgram :=
  { regCount := regCount, arrayLen := cfg.arrayLen
    loopCount := cfg.period * cfg.segCount
    init := cfg.init seed, body := cfg.body, epilogue := [], output := out }

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- **The accumulator.**  After the three-phase loop over `[6, 14]` the
residue register holds exactly what the trial-division reference computes:
the head's carry-in, `2γ` per integer, and one jump per test point applied in
increasing order.  Every one of the four modes occurs in this window, so the
sieve's classification — three planes, a saturating count and a product
compared against `n` — is what is being checked. -/
example : (probe rD).denote =
    some (refFold 4 6 14 3 seed.d seed.terms seed.prev).1 := by decide

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- Thirteen test points: the head's four and the window's nine. -/
example : (probe rTerms).denote =
    some (refFold 4 6 14 3 seed.d seed.terms seed.prev).2 := by decide

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- The incrementally maintained `⌊√n⌋` reaches `⌊√14⌋ = 3`, and the last test
point is the window's right end. -/
example : (probe rSq).denote = some 3 := by decide

end Check

end LeanCompCert.Ports.R2SegSieve
