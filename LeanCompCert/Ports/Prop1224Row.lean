import LeanCompCert.Verified.Prop1224Margin
import LeanCompCert.Ports.PsiSegSieve

/-!
# Helfgott Prop. 12.2.4: the per-`q` row, as a program of the proved fragment

The row phase is the dominant cost of the whole table: `3 389 047 618` values of
`q`, **including** the ones whose window turns out to be empty, because
emptiness is only known after `ϖ(q)` and `λ(q)` have been computed.  This module
is that phase as an `ArrayBridge.AProgram`, so `AProgram.evalCC_compile` applies
and the emitted C provably computes what the register machine denotes.

`Ports/Prop1224Cell.lean` is the other half — the `(q,k)` margin — and
`Verified/Prop1224Margin.lean` is the direction calculus both implement.

## What one row is

From the segmented sieve: the distinct primes of `q` and `φ(q)`.  From those,
outward enclosures for

```
L(q) = Σ_{p|q} log p / p          f₁(q) = ∏_{p|q} (1+p^{−2/3})·(1+(p^{1/3}+p^{2/3})/(p(p−1)))^{−1}
κ*(q) = (1−ω*)(log q − L(q)) + c_Δ           B(q) = (q/φ(q))·7.284(1+β*)·f₁(q)
λ(q) = (B/κ*)³                    ϖ(q) = max of three lower bounds
```

and the `k`-independent part of the cell bracket,
`(1−ω*)·log q + ω*·L(q) + 1.36`.  Directions: everything the *window* is built
from is rounded so the window can only grow (`ϖ` down, `λ` up), and everything
the *margin* is built from so the margin can only shrink.  That asymmetry is
the whole content of `Verified/Prop1224Margin.lean`, and the failure it guards
is silent: a window computed too small **skips** cells and still reports a
clean run.

## Six planes, and the mark step does the number theory

The model is `Ports/R2SegSieve.lean`.  A mark of `p^j` on the cell of `q`
updates six planes; `j = 1` marks — the base prime itself — carry the
per-prime data:

| plane | at `j = 1` | at `j ≥ 2` |
| --- | --- | --- |
| `prod` | `×= p` | `×= p` |
| `phi` | `×= p−1` | `×= p` |
| `Llo` | `+= ⌊2^E ln p⌋/p` | — |
| `Lhi` | `+= ⌈⌈2^E ln p⌉/p⌉` | — |
| `f1` | `×= f₁-factor(p)`, refolded | — |
| `om` | `+= 1` | — |

so `prod` holds `∏ p^{v_p}` over the primes `≤ ⌊√hi⌋` and `prod ≠ q` says
exactly that one prime above the root remains — `R2SegSieve`'s test, reused.
The three transcendental per-prime constants are **emit-time literals** carried
in the mark table: `5 820` primes below `⌊√(3.3·10⁹)⌋`, two cells each.  That
is the projection's "the row needs `4` `rpow`, not `12`" made concrete — every
small prime's contribution is a table lookup, and only `q`'s single large prime
costs exponentials.

## The engines, and why a slot is a slot

What is left per row is `logFix` of four numbers (`q`, the large prime, and the
two intermediate `ϖ₀` bases) and `expFix` of five (`q^τ`, the large prime's two
cube-root powers, and the two `ϖ₀` powers).  They form a **chain**:

```
log q → q^τ → (cq) → log w → w^{τ/(1−τ)} → (base) → log b → b^{1/(1−τ)} → ϖ₀
```

so the row is scheduled as `slots` of `S` squaring rounds each, one logarithm
engine and one exponential engine running **concurrently**, and the schedule
below packs the large prime's independent pair into the two slots the chain
leaves free.  Six slots, `S = 24` rounds each; a seventh only for `q < 2^17`,
where `ϖ`'s third term needs one more.

`expUnroll` copies of both round bodies go in the body, and a slot then costs
`S / expUnroll` iterations.  This is the single most important cost knob in the
module and it is **not** about the exponential: every phase's instructions
execute on every iteration, so the row's segmented sieve, its slot muxes and
its twelve divisions are paid once per iteration whether or not they are
wanted.  Raising `expUnroll` from `1` to `8` cuts the iterations per row from
`147` to `21` and the instructions per row by `2×`.

## Word size

Every arithmetic operation is on `u64` and the fragment's semantics is `Nat`
modulo `2⁶⁴`, which is C's `uint64_t` exactly.  Three sites are within a bit of
`2⁶³` and are exact only because the arithmetic is *unsigned*; a signed port
would be fatal:

* `K_CSIG_LO · rpow_lo(q, Y_TAU)`, `1.05·10¹⁹` at `q = 6 469 693 230` — **past**
  `2⁶³`;
* `⌈K_B_HI·f₁/2^E⌉ · q`, `7.85·10¹⁸` at `q = 2.2·10¹⁰`, `0.30` bits below;
* `p·(p−1)` for the large prime, `1.09·10¹⁹` at `p = 3 299 999 959` — past.

and one is load-bearing in the *order* of its shifts: `λ`'s staged cube must
shift `>>> 40` then `>>> 20`.  The other order peaks at `2.6·10¹⁹`, wraps, and
reports a window **too small** — the anti-conservative direction.
`Prop1224Margin.lamCube_ge` and its `Check` block pin it.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`: `rowProgram_wf` and
`rowProgram_compiled`, so `AProgram.evalCC_compile` applies and the emitted C
computes exactly `denote`.

**Not** proved, exactly as in `R2SegSieve` and `Prop1224Cell`: that `denote`
*is* the row.  One production row is `6.6·10⁴` register-machine instructions
over `39` iterations of a `1 625`-instruction body, and `AProgram.denote`
threads the register file as a closure chain with one link per register
write — so, as `Ports/CDEMAbelScan.lean` records for its own scan, **the
kernel cannot evaluate this program at production parameters, and there is no
kernel check of `denote` here**.  That is a real gap.  The compensating
strength is that the oracle agreement is run *at* production parameters rather
than at a toy configuration: `bench/ref_p1224.c`, written from the mathematics
by someone who had never seen this encoding, agrees on all eleven per-row
columns and all ten `SUM` fields over `[3·10⁹, 3·10⁹+65536)` with the mark
table of the full `3.3·10⁹` sweep, under both `gcc -O2` and `ccomp -O`.  See
`bench/results/p1224_row.md`.

## One place where the oracle and the proved guard disagree

`bench/ref_p1224.c` starts its `k` sweep at `k0 = ⌊ϖ_lo/2^E⌋ + 1`.
`Prop1224Margin.k0_covers` proves the guard only for `⌊ϖ_lo/2^E⌋`: the `+1`
skips `k = ⌊ϖ_lo/2^E⌋`, which is admissible exactly when `ϖ_lo` is an exact
multiple of `2^E` *and* equals `ϖ(q)`.  Measure zero, and no counterexample is
known — but it is the silent direction, so this module reports **both**: the
proved floor in result slot `3` and the oracle's convention in slot `4`.  Over
`[1, 257)` they differ by `256`, one per non-empty window, exactly as the
argument predicts; over the whole range that is about `1.3·10⁶` extra cells on
`6.7·10⁷`, under two per cent. A production run should use slot `3`.
-/

namespace LeanCompCert.Ports.Prop1224Row

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

/-! ## Scales and the paper's constants

Every literal below is the integer `bench/ref_p1224.c` carries, at the scale
`Verified/Prop1224Margin.lean` fixes.
-/

/-- Row scale. -/
def E : Nat := 26
/-- `ExpFixed` mantissa precision; `P ≤ 30` is the proved `u64` wall. -/
def P : Nat := 30
/-- `LogFixed`/`ExpFixed` exponent scale. -/
def S : Nat := 24
/-- Scale of `rpow`'s rational exponent. -/
def T : Nat := 24

def oneE : Nat := 2 ^ 26

/-- `⌊2³² ln 2⌋`, rounded **down**. -/
def l2lo32 : Nat := 2977044471
/-- `⌈2³² ln 2⌉`, rounded **up**. -/
def l2hi32 : Nat := 2977044472
/-- Shift from `logFix`'s scale times `2³²` down to the row scale. -/
def lnShift : Nat := S + 32 - E

/-- `⌊2^E ω*⌋`, `ω* = 0.627312`. -/
def kOmLo : Nat := 42098195
/-- `⌊2^E (1−ω*)⌋`. -/
def k1momLo : Nat := 25010668
/-- `⌊2^E · 1.36⌋`. -/
def k136Lo : Nat := 91268055
/-- `⌊2^E (1.36 − c_E)⌋` with `c_E` at the **upper** end of its bracket, which
is the end that makes the window **larger**. -/
def kCdLo : Nat := 1751541
/-- `⌈2^E ω*·7.284⌉`, the envelope's constant. -/
def kAHi : Nat := 306643258
/-- `⌈2^E · 7.284(1+β*)⌉`. -/
def kBHi : Nat := 500118107
/-- `⌊2^E c₂*⌋`. -/
def kCsigLo : Nat := 61190398
/-- `⌊2^E · 12.0999…⌋`, `ϖ`'s second term. -/
def kV2Lo : Nat := 812086418
/-- `ϖ`'s third-term numerator. -/
def kT3numLo : Nat := 4803288635121

/-- `⌊2^T τ⌋`, `τ = 0.4 e^{−γ}`. -/
def yTau : Nat := 3767890
/-- `⌊2^T τ/(1−τ)⌋`. -/
def yTau1mTau : Nat := 4859185
/-- `⌊2^T 1/(1−τ)⌋`. -/
def y1_1mTau : Nat := 21636401
/-- `⌈2^T 1/(1−ω*)⌉`. -/
def y1_1mOm : Nat := 45016787
/-- `⌊2^T/3⌋`. -/
def yThird : Nat := 5592405
/-- `⌊2^T·2/3⌋`. -/
def yTwoThird : Nat := 11184810

/-- `q < 2^17` is where `ϖ`'s third term can bind. -/
def smallQBound : Nat := 2 ^ 17

/-! ## Emit-time number theory

Everything in this section runs in Lean when the artifact is built.  None of it
is compiled; it only produces the literals the program carries.
-/

/-- Ceiling division. -/
def cdivN (a b : Nat) : Nat := a / b + (if a % b = 0 then 0 else 1)

/-- `⌊2^E ln n⌋`, rounded **down**.  The parentheses are load-bearing: `>>>`
binds tighter than `*` in Lean, and without them this is
`logFix · (⌊2³² ln 2⌋ >>> 30) = 2·logFix`, which the artifact then carries into
every `L(q)` and every table entry.  It cost one emit-and-compare cycle. -/
def lnLo (n : Nat) : Nat := (Verified.LogFixed.logFix S n * l2lo32) >>> lnShift

/-- `⌈2^E ln n⌉`, rounded **up**, through the logarithm's own two-ulp window. -/
def lnHi (n : Nat) : Nat :=
  cdivN ((Verified.LogFixed.logFix S n + 2) * l2hi32) (2 ^ lnShift)

/-- `⌈2^E (1+p^{−2/3})(1+(p^{1/3}+p^{2/3})/(p(p−1)))^{−1}⌉`.

Only `rpowLo` appears: the numerator's upper bound needs `p^{2/3}` **lower**
(it is inverted) and the denominator's lower bound needs both powers **lower**,
so every direction inverts to a lower bound on the exponentials. -/
def f1FactorHi (p : Nat) : Nat :=
  let a13 := Verified.ExpFixed.rpowLo P S T p yThird
  let a23 := Verified.ExpFixed.rpowLo P S T p yTwoThird
  let num := oneE + cdivN (2 ^ (E + P)) a23
  let den := oneE + ((a13 + a23) >>> (P - E)) / (p * (p - 1))
  cdivN (num <<< E) den

/-! ### The mark table

Two cells per prime.  `p < 2^18` (`⌊√(2.2·10¹⁰)⌋ = 148 324`), the per-prime
logarithm `a = ⌊2^E ln p⌋/p < 2^25`, and the gap `d` between the two directions
of `L`'s term is at most `4`, so the first cell packs all three; the second
carries `f₁`'s factor, which reaches `2^27`.

Emitting the powers as table entries too is what overflowed `ccomp`'s stack at
`27 421` entries; they are generated in the loop instead, exactly as in
`R2SegSieve`.  At the production root that leaves `2·5 820 + 2` literal stores. -/
def pBits : Nat := 18
def aBits : Nat := 25
def dShift : Nat := 43

def packEntry (p a d : Nat) : Nat := p + a * 2 ^ pBits + d * 2 ^ dShift

/-- The two cells of one prime's entry. -/
def entryOf (p : Nat) : List Nat :=
  let a := lnLo p / p
  let b := cdivN (lnHi p) p
  [packEntry p a (b - a), f1FactorHi p]

/-- The primes `≤ ⌊√hi⌋`, two cells each. -/
def markTable (hi : Nat) : List Nat :=
  (primesBelow (Nat.sqrt hi + 1)).flatMap entryOf

/-- **Every packed field must round-trip.**  A field that silently overflows
its bits corrupts the sieve's arithmetic and nothing downstream notices: an
early version had `d = 6 848 038` instead of `4`, which pushed the entry past
`2⁶⁴` and truncated it.  The emitter calls this and refuses to write a
translation unit that fails it. -/
def entryOK (p : Nat) : Bool :=
  let a := lnLo p / p
  let d := cdivN (lnHi p) p - a
  let e := packEntry p a d
  decide (p < 2 ^ pBits) && decide (a < 2 ^ aBits) &&
    decide (d < 2 ^ (63 - dShift)) && decide (e < 2 ^ 63) &&
    decide (e % 2 ^ pBits = p) && decide (e / 2 ^ pBits % 2 ^ aBits = a) &&
    decide (e / 2 ^ dShift = d) && decide (f1FactorHi p < 2 ^ 28)

def tableOK (hi : Nat) : Bool := (primesBelow (Nat.sqrt hi + 1)).all entryOK

/-- Mark steps a window of `len` cells needs: one per multiple of each prime
**power** `p^j ≤ hi`, two per power to advance or bump the cursor, and slack.
Too small truncates the sieve *silently*, so the loop checks it. -/
def markBudget (root hi len : Nat) : Nat := Id.run do
  let mut acc := 16
  for p in primesBelow (root + 1) do
    let mut q := p
    while q ≤ hi do
      acc := acc + len / q + 2
      q := q * p
  return acc

/-! ## The slot schedule

One logarithm engine and one exponential engine, `slots` slots of `S` rounds.
`logSrc` names the engine's base and `expY`/`expL` the exponent `Y·logFix`;
`expHi` selects the **upper** `rpow`, which `ϖ`'s third term needs and nothing
else does.

The chain forces six slots: `log q`, then `q^τ`, then `log w`, then
`w^{τ/(1−τ)}`, then `log b`, then `b^{1/(1−τ)}`.  The large prime's own
logarithm and its two cube-root powers fit in the gaps at no cost in
iterations, which is why the row's five exponentials cost six slots and not
ten. -/
structure Slot where
  /-- `0` idle, `1` `q`, `2` the large prime, `3` `w`, `4` `b`, `5` `q+1`. -/
  logSrc : Nat
  /-- `0` idle. -/
  expY : Nat
  /-- Which latched logarithm feeds the exponent: `0` `log q`, `1` `log Pbig`,
  `2` `log w`, `3` `log b`, `4` none. -/
  expL : Nat
  /-- Use `rpowHi` rather than `rpowLo`. -/
  expHi : Bool
  deriving Repr

/-- The production schedule.  `smallQ` appends the seventh slot, which is the
only place `rpowHi` is ever used. -/
def schedule (smallQ : Bool) : List Slot :=
  [ { logSrc := 1, expY := 0,          expL := 4, expHi := false }   -- log q
  , { logSrc := 2, expY := yTau,       expL := 0, expHi := false }   -- q^τ
  , { logSrc := 3, expY := yThird,     expL := 1, expHi := false }   -- P^{1/3}
  , { logSrc := 0, expY := yTau1mTau,  expL := 2, expHi := false }   -- w^{τ/(1−τ)}
  , { logSrc := 4, expY := yTwoThird,  expL := 1, expHi := false }   -- P^{2/3}
  , { logSrc := 0, expY := y1_1mTau,   expL := 3, expHi := false }   -- b^{1/(1−τ)}
  ] ++ (if smallQ then
      [ { logSrc := 0, expY := y1_1mOm, expL := 0, expHi := true } ] else [])

/-! ## Configuration -/

structure RowCfg where
  /-- First `q` of the sweep; must be `≥ 1`. -/
  lo : Nat
  /-- Rows per window. -/
  segLen : Nat
  /-- Windows. -/
  segCount : Nat
  /-- Squaring rounds per iteration, in both engines.  `S % expUnroll = 0`. -/
  expUnroll : Nat
  /-- Whether the seventh slot — `ϖ`'s third term — is emitted. -/
  smallQ : Bool
  /-- Mark steps budgeted per window. -/
  markSteps : Nat
  /-- The mark table, two cells per prime. -/
  table : List Nat
  deriving Repr

def RowCfg.hi (c : RowCfg) : Nat := c.lo + c.segLen * c.segCount - 1
def RowCfg.entries (c : RowCfg) : Nat := c.table.length / 2
def RowCfg.slots (c : RowCfg) : Nat := (schedule c.smallQ).length
def RowCfg.roundsPerSlot (c : RowCfg) : Nat := S / c.expUnroll
def RowCfg.transSteps (c : RowCfg) : Nat :=
  c.segLen * c.slots * c.roundsPerSlot
def RowCfg.period (c : RowCfg) : Nat := c.markSteps + c.transSteps
def RowCfg.firstEntry (c : RowCfg) : Nat := c.table.headD (packEntry 2 0 0)
def RowCfg.q0 (c : RowCfg) : Nat := c.firstEntry % 2 ^ pBits
def RowCfg.a0 (c : RowCfg) : Nat := c.firstEntry / 2 ^ pBits % 2 ^ aBits
def RowCfg.d0 (c : RowCfg) : Nat := c.firstEntry / 2 ^ dShift
def RowCfg.f0 (c : RowCfg) : Nat := (c.table.drop 1).headD oneE

/-! ### Array layout

Six sieve planes of `L` cells, their six sinks, ten per-row result planes, a
scratch cell, the mark table, and the aggregate cells.  The gaps are address
space only; the emitted C's array is `static`. -/
def RowCfg.sink (c : RowCfg) : Nat := 6 * c.segLen
def RowCfg.rowBase (c : RowCfg) : Nat := 12 * c.segLen
def RowCfg.scratch (c : RowCfg) : Nat := 22 * c.segLen
def RowCfg.tableBase (c : RowCfg) : Nat := c.scratch + 2
def RowCfg.resultBase (c : RowCfg) : Nat := c.tableBase + c.table.length + 4
def RowCfg.arrayLen (c : RowCfg) : Nat := c.resultBase + 20

/-! ## Register allocation

`2`–`8` and `170`–`174` the sieve core, `10`–`119` recomputed every iteration
by the mark phase, `180`–`211` the row's persistent state and the aggregates,
`212`–`249` the two engines, `250`–`265` the slot decode, `270`–`515` the
derivation, the latches and the row finish. -/

def rPi : Nat := 2      -- mark-table cursor, in entries
def rQp : Nat := 3      -- current entry's prime power
def rJ : Nat := 4       -- current multiple, as a cell index
def rR : Nat := 5       -- position inside the period
def rW : Nat := 6       -- window base
def rOne : Nat := 7
def rZero : Nat := 8
def rBp : Nat := 170    -- current entry's base prime
def rFs : Nat := 171    -- current entry's `j = 1` flag
def rEa : Nat := 172    -- its `⌊2^E ln p⌋/p`
def rEd : Nat := 173    -- its upper-lower gap
def rEf : Nat := 174    -- its `f₁` factor

def rCi : Nat := 180    -- cell index inside the window
def rSlot : Nat := 181
def rRnd : Nat := 182   -- round inside the slot
def rLq : Nat := 183    -- logFix q
def rLqP : Nat := 184   -- logFix of the large prime
def rLqw : Nat := 185   -- logFix w
def rLqb : Nat := 186   -- logFix b
def rLqN : Nat := 187   -- logFix (q+1), for a pipelined schedule
def rCq : Nat := 188    -- c₂*·q^τ at scale 2^E
def rA13 : Nat := 189   -- the large prime's p^{1/3}
def rA23 : Nat := 190   -- …and p^{2/3}
def rUlo : Nat := 191   -- w^{τ/(1−τ)}
def rT3m : Nat := 192   -- ϖ's third term: mantissa…
def rT3e : Nat := 193   -- …and shift, kept apart because the value is 2^75
def rV0 : Nat := 194    -- ϖ₀, at scale 2^E

def rLx : Nat := 195    -- log engine: mantissa
def rLa : Nat := 196    -- log engine: bits so far
def rLe : Nat := 197    -- log engine: ⌊log₂ base⌋
def rXx : Nat := 198    -- exp engine: mantissa
def rXr : Nat := 199    -- exp engine: remaining exponent bits

def rViol : Nat := 200
def rNemp : Nat := 201  -- rows with a non-empty window
def rCel0 : Nat := 202  -- cells at the proved floor `k0 = ⌊ϖ/2^E⌋`
def rCel1 : Nat := 203  -- …and at the oracle's `⌊ϖ/2^E⌋ + 1`
def rSVar : Nat := 204
def rSLam : Nat := 205
def rSF1 : Nat := 206
def rSPhi : Nat := 207
def rSCon : Nat := 208
def rSKap : Nat := 209
def rSQ : Nat := 210
def rRows : Nat := 211

/-! ### The eight failure classes, counted apart

`rViol` is the aggregate and stays the program's output.  It merges three very
different things — a sieve budget, a square-root certification, and the row's
own enclosure certification, which itself merges five comparisons and then
*collapses* them to one bit per row.  Kept apart:

* `rVMark` — the mark cursor had not reached the end of the table at the last
  mark step, so the sieve was silently truncated;
* `rVRootHi`, `rVRootLo` — the emitted square root failed `v² ≤ Z` or
  `Z < (v+1)²`.  They are opposite and cannot both fire on one root;
* `rVLq`, `rVPhi`, `rVLog` — the `L(q)`, `φ(q)/q` or `log q` enclosure came out
  **inverted**, lower bound above upper bound;
* `rVKap`, `rVLam` — `κ*`'s lower bound, or `λ(q)`, collapsed to `0`.

⚠ The last five count **conditions**, while `rViol` counts *rows* with at least
one of them.  So they sum to at least the aggregate, with equality exactly when
no row fails two at once; what always holds, and what the driver checks, is
that they are all zero exactly when the aggregate is. -/

def rVMark : Nat := 520
def rVRootHi : Nat := 521
def rVRootLo : Nat := 522
def rVLq : Nat := 523
def rVPhi : Nat := 524
def rVLog : Nat := 525
def rVKap : Nat := 526
def rVLam : Nat := 527

/-- The per-class counters in the order they occupy result slots `12 … 19`.
`bench/Prop1224RowEmit.lean` labels them in this order. -/
def violRegs : List Nat :=
  [rVMark, rVRootHi, rVRootLo, rVLq, rVPhi, rVLog, rVKap, rVLam]

def eqBase : Nat := 250   -- `rSlot = s`
def endBase : Nat := 258  -- …and the slot's last round

def regCount : Nat := 544
def outputReg : Nat := 200

/-! ## Small generators

Hand-numbering three hundred branchless instructions is where an encoding bug
lives, so the repeated shapes are generated. -/

/-- `dst := c ? v : dst`, for registers.  `t` must differ from all three. -/
def latchR (dst c v t : Nat) : List AInstr :=
  [ .scalar (.binop t .sub (.lit 1) (.reg c))
  , .scalar (.binop dst .mul (.reg dst) (.reg t))
  , .scalar (.binop t .mul (.reg c) (.reg v))
  , .scalar (.binop dst .add (.reg dst) (.reg t)) ]

/-- `dst := c ? v : dst`, for a literal `v`. -/
def latchL (dst c v t : Nat) : List AInstr :=
  [ .scalar (.binop t .sub (.lit 1) (.reg c))
  , .scalar (.binop dst .mul (.reg dst) (.reg t))
  , .scalar (.binop t .mul (.reg c) (.lit v))
  , .scalar (.binop dst .add (.reg dst) (.reg t)) ]

/-- `dst := Σ_s [slot = s]·srcs[s]`, for registers. -/
def muxR (dst t : Nat) (srcs : List Nat) : List AInstr :=
  .scalar (.mov dst (.lit 0)) ::
    (srcs.zipIdx.flatMap fun x =>
      [ .scalar (.binop t .mul (.reg (eqBase + x.2)) (.reg x.1))
      , .scalar (.binop dst .add (.reg dst) (.reg t)) ])

/-- `dst := Σ_s [slot = s]·vals[s]`, for literals. -/
def muxL (dst t : Nat) (vals : List Nat) : List AInstr :=
  .scalar (.mov dst (.lit 0)) ::
    (vals.zipIdx.flatMap fun x =>
      [ .scalar (.binop t .mul (.reg (eqBase + x.2)) (.lit x.1))
      , .scalar (.binop dst .add (.reg dst) (.reg t)) ])

/-- `dst := ⌈a/b⌉` for registers, in **one** division: the remainder is
recovered by a multiply, not by a second `urem`.  Divisions are the body's
scarcest resource — twelve of them execute on every iteration, wanted or
not — so this halves the row finish's division count. -/
def cdivR (dst a b t : Nat) : List AInstr :=
  [ .scalar (.binop dst .udiv (.reg a) (.reg b))
  , .scalar (.binop t .mul (.reg dst) (.reg b))
  , .scalar (.binop t .sub (.reg a) (.reg t))
  , .scalar (.binop t .ne (.reg t) (.lit 0))
  , .scalar (.binop dst .add (.reg dst) (.reg t)) ]

/-- `dst := ⌈a/b⌉` with a literal numerator. -/
def cdivLR (dst : Nat) (a : Nat) (b t : Nat) : List AInstr :=
  [ .scalar (.binop dst .udiv (.lit a) (.reg b))
  , .scalar (.binop t .mul (.reg dst) (.reg b))
  , .scalar (.binop t .sub (.lit a) (.reg t))
  , .scalar (.binop t .ne (.reg t) (.lit 0))
  , .scalar (.binop dst .add (.reg dst) (.reg t)) ]

/-- `dst := max dst v`. -/
def maxR (dst v t : Nat) : List AInstr :=
  .scalar (.binop t .gt (.reg v) (.reg dst)) :: latchR dst t v (t + 1)

/-- A store whose address is the real one at `cond` and a dead scratch cell
otherwise, so that a gated store costs no branch. -/
def gatedStore (cell base cond scratch t : Nat) (src : Nat) : List AInstr :=
  [ .scalar (.binop t .add (.reg cell) (.lit base))
  , .scalar (.binop t .mul (.reg t) (.reg cond))
  , .scalar (.binop (t + 1) .sub (.lit 1) (.reg cond))
  , .scalar (.binop (t + 1) .mul (.reg (t + 1)) (.lit scratch))
  , .scalar (.binop t .add (.reg t) (.reg (t + 1)))
  , .store t src ]

/-! ## Phase one: marking

`j = 1` marks carry the per-prime table data into four of the six planes;
`j ≥ 2` marks touch only `prod` and `phi`.  The higher powers are generated in
the loop. -/

def RowCfg.markBody (c : RowCfg) : List AInstr :=
  let L := c.segLen
  let MT := c.markSteps
  let K := c.entries
  let SNK := c.sink
  let q0 := c.q0
  [ -- phase selectors
    .scalar (.binop 10 .lt (.reg rR) (.lit MT))            -- inMark
  , .scalar (.binop 12 .sub (.lit 1) (.reg 10))            -- inTrans
    -- window start: reset the cursor and the entry registers, branchlessly
  , .scalar (.binop 14 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 15 .sub (.lit 1) (.reg 14))
  , .scalar (.binop 16 .urem (.reg rW) (.lit q0))
  , .scalar (.binop 17 .sub (.lit q0) (.reg 16))
  , .scalar (.binop 18 .urem (.reg 17) (.lit q0))
  , .scalar (.binop rPi .mul (.reg 15) (.reg rPi))
  , .scalar (.binop 19 .mul (.reg 14) (.lit q0))
  , .scalar (.binop 20 .mul (.reg 15) (.reg rQp))
  , .scalar (.binop rQp .add (.reg 19) (.reg 20))
  , .scalar (.binop 21 .mul (.reg 15) (.reg rBp))
  , .scalar (.binop rBp .add (.reg 19) (.reg 21))
  , .scalar (.binop 22 .mul (.reg 15) (.reg rFs))
  , .scalar (.binop rFs .add (.reg 14) (.reg 22))
  , .scalar (.binop 23 .mul (.reg 14) (.lit c.a0))
  , .scalar (.binop 24 .mul (.reg 15) (.reg rEa))
  , .scalar (.binop rEa .add (.reg 23) (.reg 24))
  , .scalar (.binop 25 .mul (.reg 14) (.lit c.d0))
  , .scalar (.binop 26 .mul (.reg 15) (.reg rEd))
  , .scalar (.binop rEd .add (.reg 25) (.reg 26))
  , .scalar (.binop 27 .mul (.reg 14) (.lit c.f0))
  , .scalar (.binop 28 .mul (.reg 15) (.reg rEf))
  , .scalar (.binop rEf .add (.reg 27) (.reg 28))
  , .scalar (.binop 29 .mul (.reg 14) (.reg 18))
  , .scalar (.binop 30 .mul (.reg 15) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 29) (.reg 30))
    -- the mark step: six planes, or the six sinks
  , .scalar (.binop 31 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 32 .mul (.reg 31) (.reg 10))           -- doMark
  , .scalar (.binop 33 .sub (.lit 1) (.reg 32))
  , .scalar (.binop 34 .mul (.reg 32) (.reg rJ))
  , .scalar (.binop 35 .mul (.reg 33) (.lit SNK))
  , .scalar (.binop 36 .add (.reg 34) (.reg 35))           -- prod cell
  , .scalar (.binop 37 .add (.reg 36) (.lit L))            -- phi
  , .scalar (.binop 38 .add (.reg 36) (.lit (2 * L)))      -- Llo
  , .scalar (.binop 39 .add (.reg 36) (.lit (3 * L)))      -- Lhi
  , .scalar (.binop 40 .add (.reg 36) (.lit (4 * L)))      -- f1
  , .scalar (.binop 41 .add (.reg 36) (.lit (5 * L)))      -- om
    -- prod ×= p
  , .load 42 36
  , .scalar (.binop 43 .eq (.reg 42) (.lit 0))
  , .scalar (.binop 43 .add (.reg 42) (.reg 43))
  , .scalar (.binop 43 .mul (.reg 43) (.reg rBp))
  , .store 36 43
    -- phi ×= (j = 1 ? p−1 : p)
  , .load 44 37
  , .scalar (.binop 45 .eq (.reg 44) (.lit 0))
  , .scalar (.binop 45 .add (.reg 44) (.reg 45))
  , .scalar (.binop 46 .sub (.reg rBp) (.reg rFs))
  , .scalar (.binop 45 .mul (.reg 45) (.reg 46))
  , .store 37 45
    -- L, both directions
  , .load 47 38
  , .scalar (.binop 48 .mul (.reg rFs) (.reg rEa))
  , .scalar (.binop 47 .add (.reg 47) (.reg 48))
  , .store 38 47
  , .load 49 39
  , .scalar (.binop 50 .add (.reg rEa) (.reg rEd))
  , .scalar (.binop 50 .mul (.reg rFs) (.reg 50))
  , .scalar (.binop 49 .add (.reg 49) (.reg 50))
  , .store 39 49
    -- f₁, refolded at the row scale
  , .load 51 40
  , .scalar (.binop 52 .eq (.reg 51) (.lit 0))
  , .scalar (.binop 52 .mul (.reg 52) (.lit oneE))
  , .scalar (.binop 51 .add (.reg 51) (.reg 52))           -- 0 means 2^E
  , .scalar (.binop 53 .mul (.reg 51) (.reg rEf))
  , .scalar (.binop 53 .add (.reg 53) (.lit (oneE - 1)))
  , .scalar (.binop 53 .lshr (.reg 53) (.lit E))
  , .scalar (.binop 53 .mul (.reg 53) (.reg rFs))
  , .scalar (.binop 54 .sub (.lit 1) (.reg rFs))
  , .scalar (.binop 54 .mul (.reg 54) (.reg 51))
  , .scalar (.binop 53 .add (.reg 53) (.reg 54))
  , .store 40 53
    -- ω(q)
  , .load 55 41
  , .scalar (.binop 55 .add (.reg 55) (.reg rFs))
  , .store 41 55
    -- the multiples ran past the window: bump to the next power of the same
    -- prime if it still fits under `hi`, and only then step the cursor
  , .scalar (.binop 56 .mul (.reg 10) (.reg 33))           -- advance
  , .scalar (.binop 57 .mul (.reg rQp) (.reg rBp))         -- p^{j+1}
  , .scalar (.binop 58 .le (.reg 57) (.lit c.hi))
  , .scalar (.binop 59 .mul (.reg 56) (.reg 58))           -- bump
  , .scalar (.binop 60 .sub (.reg 56) (.reg 59))           -- step
  , .scalar (.binop 61 .add (.reg rPi) (.reg 60))
  , .scalar (.binop 62 .gt (.reg 61) (.lit K))
  , .scalar (.binop 63 .sub (.lit 1) (.reg 62))
  , .scalar (.binop 64 .mul (.reg 63) (.reg 61))
  , .scalar (.binop 65 .mul (.reg 62) (.lit K))
  , .scalar (.binop rPi .add (.reg 64) (.reg 65))
  , .scalar (.binop 66 .shl (.reg rPi) (.lit 1))
  , .scalar (.binop 66 .add (.reg 66) (.lit c.tableBase))
  , .load 67 66
  , .scalar (.binop 68 .add (.reg 66) (.lit 1))
  , .load 69 68                                            -- the entry's f₁
  , .scalar (.binop 70 .band (.reg 67) (.lit (2 ^ pBits - 1)))
  , .scalar (.binop 71 .lshr (.reg 67) (.lit pBits))
  , .scalar (.binop 71 .band (.reg 71) (.lit (2 ^ aBits - 1)))
  , .scalar (.binop 72 .lshr (.reg 67) (.lit dShift))
  , .scalar (.binop 73 .sub (.lit 1) (.reg 56))            -- keep
  , .scalar (.binop 74 .add (.reg rJ) (.reg rQp))          -- next multiple
  , .scalar (.binop 75 .mul (.reg 59) (.reg 57))
  , .scalar (.binop 76 .mul (.reg 60) (.reg 70))
  , .scalar (.binop 77 .mul (.reg 73) (.reg rQp))
  , .scalar (.binop 78 .add (.reg 75) (.reg 76))
  , .scalar (.binop rQp .add (.reg 78) (.reg 77))
  , .scalar (.binop 79 .sub (.lit 1) (.reg 60))
  , .scalar (.binop 80 .mul (.reg 60) (.reg 70))
  , .scalar (.binop 81 .mul (.reg 79) (.reg rBp))
  , .scalar (.binop rBp .add (.reg 80) (.reg 81))
  , .scalar (.binop 82 .mul (.reg 60) (.reg 71))
  , .scalar (.binop 83 .mul (.reg 79) (.reg rEa))
  , .scalar (.binop rEa .add (.reg 82) (.reg 83))
  , .scalar (.binop 84 .mul (.reg 60) (.reg 72))
  , .scalar (.binop 85 .mul (.reg 79) (.reg rEd))
  , .scalar (.binop rEd .add (.reg 84) (.reg 85))
  , .scalar (.binop 86 .mul (.reg 60) (.reg 69))
  , .scalar (.binop 87 .mul (.reg 79) (.reg rEf))
  , .scalar (.binop rEf .add (.reg 86) (.reg 87))
  , .scalar (.binop 88 .mul (.reg 73) (.reg rFs))          -- `j = 1` is a step
  , .scalar (.binop rFs .add (.reg 60) (.reg 88))
  , .scalar (.binop 89 .urem (.reg rW) (.reg rQp))
  , .scalar (.binop 90 .sub (.reg rQp) (.reg 89))
  , .scalar (.binop 91 .urem (.reg 90) (.reg rQp))         -- first cell
  , .scalar (.binop 92 .eq (.reg rPi) (.lit K))            -- table exhausted
  , .scalar (.binop 93 .sub (.lit 1) (.reg 92))
  , .scalar (.binop 94 .mul (.reg 92) (.lit (L + 1)))
  , .scalar (.binop 95 .mul (.reg 93) (.reg 91))
  , .scalar (.binop 96 .add (.reg 94) (.reg 95))
  , .scalar (.binop 97 .mul (.reg 56) (.reg 96))
  , .scalar (.binop 98 .mul (.reg 73) (.reg 74))
  , .scalar (.binop rJ .add (.reg 97) (.reg 98))
    -- the mark budget, checked: too small truncates the sieve *silently*
  , .scalar (.binop 99 .eq (.reg rR) (.lit (MT - 1)))
  , .scalar (.binop 100 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 101 .mul (.reg 99) (.reg 100))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 101))
  , .scalar (.binop rVMark .add (.reg rVMark) (.reg 101))
  ]

/-! ## Phase two, part one: the row's data, and the slot decode

Read straight from the planes on every iteration: `rCi` is stable across a
row's `slots·S/expUnroll` iterations, so a load is cheaper than a latch. -/

def RowCfg.deriveBody (c : RowCfg) : List AInstr :=
  let L := c.segLen
  let sch := schedule c.smallQ
  [ .load 270 rCi                                          -- prod
  , .scalar (.binop 291 .add (.reg rCi) (.lit L))
  , .load 271 291                                          -- phi
  , .scalar (.binop 291 .add (.reg rCi) (.lit (2 * L)))
  , .load 272 291                                          -- Llo
  , .scalar (.binop 291 .add (.reg rCi) (.lit (3 * L)))
  , .load 273 291                                          -- Lhi
  , .scalar (.binop 291 .add (.reg rCi) (.lit (4 * L)))
  , .load 274 291                                          -- f1
  , .scalar (.binop 291 .add (.reg rCi) (.lit (5 * L)))
  , .load 275 291                                          -- om
  , .scalar (.binop 292 .eq (.reg 270) (.lit 0))
  , .scalar (.binop 270 .add (.reg 270) (.reg 292))
  , .scalar (.binop 292 .eq (.reg 271) (.lit 0))
  , .scalar (.binop 271 .add (.reg 271) (.reg 292))
  , .scalar (.binop 292 .eq (.reg 274) (.lit 0))
  , .scalar (.binop 292 .mul (.reg 292) (.lit oneE))
  , .scalar (.binop 274 .add (.reg 274) (.reg 292))
    -- q, the large prime, and whether there is one
  , .scalar (.binop 276 .add (.reg rW) (.reg rCi))
  , .scalar (.binop 277 .udiv (.reg 276) (.reg 270))
  , .scalar (.binop 278 .ne (.reg 270) (.reg 276))
  , .scalar (.binop 307 .add (.reg 276) (.lit 1))
    -- log q, both directions
  , .scalar (.binop 279 .mul (.reg rLq) (.lit l2lo32))
  , .scalar (.binop 279 .lshr (.reg 279) (.lit lnShift))
  , .scalar (.binop 291 .add (.reg rLq) (.lit 2))
  , .scalar (.binop 291 .mul (.reg 291) (.lit l2hi32))
  , .scalar (.binop 291 .add (.reg 291) (.lit (2 ^ lnShift - 1)))
  , .scalar (.binop 280 .lshr (.reg 291) (.lit lnShift))
    -- w = c₂*q^τ − log q, and its guard
  , .scalar (.binop 291 .add (.lit oneE) (.reg 280))
  , .scalar (.binop 305 .gt (.reg rCq) (.reg 291))
  , .scalar (.binop 293 .sub (.reg rCq) (.reg 280))
  , .scalar (.binop 293 .mul (.reg 293) (.reg 305))
  , .scalar (.binop 281 .lshr (.reg 293) (.lit E))
    -- b = c₂*q^τ − log q / w^{τ/(1−τ)}, and its guard
  , .scalar (.binop 294 .shl (.reg 280) (.lit P))
  , .scalar (.binop 295 .eq (.reg rUlo) (.lit 0))
  , .scalar (.binop 295 .add (.reg rUlo) (.reg 295))
  ] ++ cdivR 296 294 295 297 ++
  [ .scalar (.binop 306 .gt (.reg rCq) (.reg 296))
  , .scalar (.binop 299 .sub (.reg rCq) (.reg 296))
  , .scalar (.binop 299 .mul (.reg 299) (.reg 306))
  , .scalar (.binop 282 .lshr (.reg 299) (.lit E))
  ] ++
    -- the slot decode
  ((List.range c.slots).map fun s =>
      AInstr.scalar (.binop (eqBase + s) .eq (.reg rSlot) (.lit s))) ++
  muxR 283 291 (sch.map fun sl =>
    match sl.logSrc with
    | 1 => 276 | 2 => 277 | 3 => 281 | 4 => 282 | 5 => 307 | _ => rOne) ++
  muxR 285 291 (sch.map fun sl =>
    match sl.expL with
    | 0 => rLq | 1 => rLqP | 2 => rLqw | 3 => rLqb | _ => rZero) ++
  muxL 284 291 (sch.map (·.expY)) ++
  muxL 286 291 (sch.map fun sl => if sl.expHi then 1 else 0) ++
  [ .scalar (.binop 291 .shl (.reg 286) (.lit 1))
  , .scalar (.binop 291 .add (.reg 285) (.reg 291))
  , .scalar (.binop 287 .mul (.reg 284) (.reg 291))
  , .scalar (.binop 292 .mul (.reg 286) (.lit (2 ^ T - 1)))
  , .scalar (.binop 287 .add (.reg 287) (.reg 292))
  , .scalar (.binop 287 .lshr (.reg 287) (.lit T))         -- the exponent
  , .scalar (.binop 288 .band (.reg 287) (.lit (2 ^ S - 1)))
  , .scalar (.binop 289 .lshr (.reg 287) (.lit S))
  , .scalar (.binop 290 .mul (.reg 286) (.lit S))          -- expFixHi's widening
  , .scalar (.binop 308 .eq (.reg rRnd) (.lit 0))
  , .scalar (.binop 308 .mul (.reg 308) (.reg 12))         -- a slot begins
  ]

/-! ## Phase two, part two: the logarithm engine

`⌊log₂ n⌋` cannot be carried incrementally here — the bases jump between `q`,
its large prime and the two `ϖ₀` intermediates — so it is a six-step branchless
binary search, run at the slot's first round only. -/

def logRound : List AInstr :=
  [ .scalar (.binop 237 .lshr (.reg rLx) (.lit 32))
  , .scalar (.binop 238 .band (.reg rLx) (.lit 4294967295))
  , .scalar (.binop 239 .mul (.reg 237) (.reg 237))
  , .scalar (.binop 240 .mul (.reg 237) (.reg 238))
  , .scalar (.binop 241 .mul (.reg 238) (.reg 238))
  , .scalar (.binop 242 .lshr (.reg 240) (.lit 29))
  , .scalar (.binop 243 .band (.reg 240) (.lit 536870911))
  , .scalar (.binop 244 .lshr (.reg 241) (.lit 62))
  , .scalar (.binop 245 .band (.reg 241) (.lit 4611686018427387903))
  , .scalar (.binop 246 .shl (.reg 243) (.lit 33))
  , .scalar (.binop 246 .add (.reg 246) (.reg 245))
  , .scalar (.binop 246 .ge (.reg 246) (.lit 4611686018427387904))
  , .scalar (.binop 247 .shl (.reg 239) (.lit 2))
  , .scalar (.binop 247 .add (.reg 247) (.reg 242))
  , .scalar (.binop 247 .add (.reg 247) (.reg 244))
  , .scalar (.binop 247 .add (.reg 247) (.reg 246))
  , .scalar (.binop 248 .ge (.reg 247) (.lit 9223372036854775808))
  , .scalar (.binop rLx .lshr (.reg 247) (.reg 248))
  , .scalar (.binop 249 .shl (.reg rLa) (.lit 1))
  , .scalar (.binop rLa .add (.reg 249) (.reg 248))
  ]

def logEngine (unroll : Nat) : List AInstr :=
  [ .scalar (.mov 230 (.reg 283))
  , .scalar (.mov 231 (.lit 0))
  ] ++ ([32, 16, 8, 4, 2, 1].flatMap fun k =>
    [ .scalar (.binop 232 .ge (.reg 230) (.lit (2 ^ k)))
    , .scalar (.binop 232 .mul (.reg 232) (.lit k))
    , .scalar (.binop 231 .add (.reg 231) (.reg 232))
    , .scalar (.binop 230 .lshr (.reg 230) (.reg 232)) ]) ++
  [ .scalar (.binop 233 .sub (.lit 62) (.reg 231))
  , .scalar (.binop 233 .band (.reg 233) (.lit 63))
  , .scalar (.binop 234 .shl (.reg 283) (.reg 233))
  ] ++ latchR rLe 308 231 235 ++ latchR rLx 308 234 235 ++
  [ .scalar (.binop 236 .sub (.lit 1) (.reg 308))
  , .scalar (.binop rLa .mul (.reg rLa) (.reg 236))
  ] ++ (List.replicate unroll logRound).flatten

/-! ## Phase two, part three: the exponential engine

`Ports/ExpFixPort.lean`'s round, at this module's register numbers: the
restoring radix-4 square root unrolled at emit time, then `ExpFixed.expOK`'s two
comparisons.  **Nothing about the digit recurrence is proved and nothing needs
to be**: a run whose comparisons all pass *is* `expIter`, by
`ExpFixed.expOK_sound`, so `expFix_bracket` applies to it.  The comparisons feed
the violation register, which is the program's output. -/

def rootDigit (j : Nat) : List AInstr :=
  [ .scalar (.binop 217 .add (.reg 216) (.lit (4 ^ j)))
  , .scalar (.binop 218 .ge (.reg 215) (.reg 217))
  , .scalar (.binop 219 .mul (.reg 218) (.reg 217))
  , .scalar (.binop 215 .sub (.reg 215) (.reg 219))
  , .scalar (.binop 220 .shl (.reg 218) (.lit (2 * j + 1)))
  , .scalar (.binop 221 .add (.reg 216) (.reg 220))
  , .scalar (.binop 216 .lshr (.reg 221) (.lit 1))
  ]

def expRound : List AInstr :=
  [ .scalar (.binop 213 .band (.reg rXr) (.lit 1))
  , .scalar (.binop rXr .lshr (.reg rXr) (.lit 1))
  , .scalar (.binop 214 .shl (.reg rXx) (.lit P))
  , .scalar (.binop 214 .shl (.reg 214) (.reg 213))
  , .scalar (.mov 215 (.reg 214))
  , .scalar (.mov 216 (.lit 0))
  ] ++ ((List.range (P + 1)).reverse.flatMap rootDigit) ++
  [ .scalar (.mov rXx (.reg 216))
  , .scalar (.binop 222 .mul (.reg rXx) (.reg rXx))
  , .scalar (.binop 223 .gt (.reg 222) (.reg 214))
  , .scalar (.binop 224 .add (.reg rXx) (.lit 1))
  , .scalar (.binop 225 .mul (.reg 224) (.reg 224))
  , .scalar (.binop 226 .le (.reg 225) (.reg 214))
  , .scalar (.binop 227 .add (.reg 223) (.reg 226))
  , .scalar (.binop 227 .mul (.reg 227) (.reg 12))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 227))
  , .scalar (.binop 528 .mul (.reg 223) (.reg 12))
  , .scalar (.binop rVRootHi .add (.reg rVRootHi) (.reg 528))
  , .scalar (.binop 529 .mul (.reg 226) (.reg 12))
  , .scalar (.binop rVRootLo .add (.reg rVRootLo) (.reg 529))
  ]

def expEngine (unroll : Nat) : List AInstr :=
  latchL rXx 308 (2 ^ P) 212 ++ latchR rXr 308 288 212 ++
  (List.replicate unroll expRound).flatten

/-! ## Phase two, part four: the latches

At a slot's last round, the two engines' results are committed.  Everything
else the row needs is a pure function of these eight registers and is
recomputed rather than latched. -/

def RowCfg.latchBody (c : RowCfg) : List AInstr :=
  let e := endBase
  [ .scalar (.binop 300 .shl (.reg rLe) (.lit S))
  , .scalar (.binop 300 .add (.reg 300) (.reg rLa))        -- logFix
  , .scalar (.binop 301 .add (.reg rXx) (.reg 290))        -- mantissa
  , .scalar (.binop 302 .band (.reg 289) (.lit 63))
  , .scalar (.binop 302 .shl (.reg 301) (.reg 302))        -- the rpow value
  , .scalar (.binop 309 .eq (.reg rRnd) (.lit (c.roundsPerSlot - 1)))
  , .scalar (.binop 309 .mul (.reg 309) (.reg 12))
  ] ++ ((List.range c.slots).map fun s =>
      AInstr.scalar (.binop (e + s) .mul (.reg 309) (.reg (eqBase + s)))) ++
  latchR rLq (e + 0) 300 303 ++
  latchR rLqP (e + 1) 300 303 ++
  [ .scalar (.binop 304 .mul (.lit kCsigLo) (.reg 302))
  , .scalar (.binop 304 .lshr (.reg 304) (.lit P))
  ] ++ latchR rCq (e + 1) 304 303 ++
  latchR rLqw (e + 2) 300 303 ++
  latchR rA13 (e + 2) 302 303 ++
  latchR rUlo (e + 3) 302 303 ++
  latchR rLqb (e + 4) 300 303 ++
  latchR rA23 (e + 4) 302 303 ++
  [ .scalar (.binop 304 .lshr (.reg 302) (.lit (P - E)))
  , .scalar (.binop 310 .ge (.reg 281) (.lit 1))
  , .scalar (.binop 311 .ge (.reg 282) (.lit 1))
  , .scalar (.binop 312 .mul (.reg 305) (.reg 306))
  , .scalar (.binop 312 .mul (.reg 312) (.reg 310))
  , .scalar (.binop 312 .mul (.reg 312) (.reg 311))
  , .scalar (.binop 304 .mul (.reg 304) (.reg 312))
  ] ++ latchR rV0 (e + 5) 304 303 ++
  (if c.smallQ then
     latchR rT3m (e + 6) 301 303 ++ latchR rT3e (e + 6) 289 303
   else [])

/-! ## Phase two, part five: the row finish

Everything from here executes on every iteration and is committed once.  It
carries twelve divisions, which is why `expUnroll` matters. -/

/-- The six literal instructions producing register `340`, the lower word for
`(1-ω*) log q + ω* L(q) + 1.36`.  Naming this block does not change the
emitted instruction stream; it exposes a small source-refinement boundary. -/
def constLoBlock : List AInstr :=
  [ .scalar (.binop 340 .mul (.lit k1momLo) (.reg 279))
  , .scalar (.binop 340 .lshr (.reg 340) (.lit E))
  , .scalar (.binop 341 .mul (.lit kOmLo) (.reg 325))
  , .scalar (.binop 341 .lshr (.reg 341) (.lit E))
  , .scalar (.binop 340 .add (.reg 340) (.reg 341))
  , .scalar (.binop 340 .add (.reg 340) (.lit k136Lo)) ]

def RowCfg.finishBody (c : RowCfg) : List AInstr :=
  let L := c.segLen
  let endR := endBase + c.slots - 1
  let scr := c.scratch
  [ -- φ(q)
    .scalar (.binop 320 .sub (.reg 277) (.lit 1))
  , .scalar (.binop 320 .mul (.reg 320) (.reg 278))
  , .scalar (.binop 321 .sub (.lit 1) (.reg 278))
  , .scalar (.binop 320 .add (.reg 320) (.reg 321))
  , .scalar (.binop 320 .mul (.reg 271) (.reg 320))
    -- ω(q)
  , .scalar (.binop 322 .add (.reg 275) (.reg 278))
    -- the large prime's logarithm, both directions
  , .scalar (.binop 323 .mul (.reg rLqP) (.lit l2lo32))
  , .scalar (.binop 323 .lshr (.reg 323) (.lit lnShift))
  , .scalar (.binop 324 .add (.reg rLqP) (.lit 2))
  , .scalar (.binop 324 .mul (.reg 324) (.lit l2hi32))
  , .scalar (.binop 324 .add (.reg 324) (.lit (2 ^ lnShift - 1)))
  , .scalar (.binop 324 .lshr (.reg 324) (.lit lnShift))
    -- L(q), both directions
  , .scalar (.binop 325 .udiv (.reg 323) (.reg 277))
  , .scalar (.binop 325 .mul (.reg 325) (.reg 278))
  , .scalar (.binop 325 .add (.reg 272) (.reg 325))
  ] ++ cdivR 326 324 277 327 ++
  [ .scalar (.binop 326 .mul (.reg 326) (.reg 278))
  , .scalar (.binop 326 .add (.reg 273) (.reg 326))
    -- f₁(q), with the large prime's factor folded last
  , .scalar (.binop 328 .sub (.reg 277) (.lit 1))
  , .scalar (.binop 328 .mul (.reg 277) (.reg 328))
  , .scalar (.binop 328 .mul (.reg 328) (.reg 278))
  , .scalar (.binop 328 .add (.reg 328) (.reg 321))        -- never 0
  ] ++ cdivLR 330 (2 ^ (E + P)) rA23 327 ++
  [ .scalar (.binop 330 .add (.reg 330) (.lit oneE))       -- numerator
  , .scalar (.binop 331 .add (.reg rA13) (.reg rA23))
  , .scalar (.binop 331 .lshr (.reg 331) (.lit (P - E)))
  , .scalar (.binop 331 .udiv (.reg 331) (.reg 328))
  , .scalar (.binop 331 .add (.reg 331) (.lit oneE))       -- denominator
  , .scalar (.binop 332 .shl (.reg 330) (.lit E))
  ] ++ cdivR 333 332 331 327 ++
  [ .scalar (.binop 334 .mul (.reg 274) (.reg 333))
  , .scalar (.binop 334 .add (.reg 334) (.lit (oneE - 1)))
  , .scalar (.binop 334 .lshr (.reg 334) (.lit E))
  , .scalar (.binop 334 .mul (.reg 334) (.reg 278))
  , .scalar (.binop 335 .mul (.reg 274) (.reg 321))
  , .scalar (.binop 334 .add (.reg 334) (.reg 335))        -- f₁, UPPER
    -- φ/q, both directions, in one division
  , .scalar (.binop 336 .shl (.reg 320) (.lit E))
  , .scalar (.binop 337 .udiv (.reg 336) (.reg 276))
  , .scalar (.binop 338 .mul (.reg 337) (.reg 276))
  , .scalar (.binop 338 .sub (.reg 336) (.reg 338))
  , .scalar (.binop 338 .ne (.reg 338) (.lit 0))
  , .scalar (.binop 339 .add (.reg 337) (.reg 338))
  ] ++ constLoBlock ++
  [ -- κ*, LOWER: log q lower, L upper, c_Δ lower
    .scalar (.binop 342 .gt (.reg 279) (.reg 326))
  , .scalar (.binop 343 .sub (.reg 279) (.reg 326))
  , .scalar (.binop 343 .mul (.reg 343) (.reg 342))
  , .scalar (.binop 343 .mul (.lit k1momLo) (.reg 343))
  , .scalar (.binop 343 .lshr (.reg 343) (.lit E))
  , .scalar (.binop 343 .add (.reg 343) (.lit kCdLo))
    -- B(q), UPPER
  , .scalar (.binop 344 .mul (.lit kBHi) (.reg 334))
  , .scalar (.binop 344 .add (.reg 344) (.lit (oneE - 1)))
  , .scalar (.binop 344 .lshr (.reg 344) (.lit E))
  , .scalar (.binop 344 .mul (.reg 344) (.reg 276))
  ] ++ cdivR 345 344 320 327 ++
  [ .scalar (.binop 346 .shl (.reg 345) (.lit 20))
  ] ++ cdivR 347 346 343 327 ++
  [ -- λ(q), staged `>>> 40` then `>>> 20`; the other order wraps
    .scalar (.binop 348 .mul (.reg 347) (.reg 347))
  , .scalar (.binop 348 .add (.reg 348) (.lit (2 ^ 40 - 1)))
  , .scalar (.binop 348 .lshr (.reg 348) (.lit 40))
  , .scalar (.binop 348 .mul (.reg 348) (.reg 347))
  , .scalar (.binop 348 .add (.reg 348) (.lit (2 ^ 20 - 1)))
  , .scalar (.binop 348 .lshr (.reg 348) (.lit 20))
  , .scalar (.binop 348 .add (.reg 348) (.lit 1))
    -- ϖ's second term
  , .scalar (.binop 349 .gt (.lit kV2Lo) (.reg 280))
  , .scalar (.binop 350 .sub (.lit kV2Lo) (.reg 280))
  , .scalar (.binop 350 .mul (.reg 350) (.reg 349))
  ] ++
  (if c.smallQ then
     [ .scalar (.binop 366 .ge (.reg rT3e) (.lit P))
     , .scalar (.binop 367 .sub (.reg rT3e) (.lit P))
     , .scalar (.binop 368 .lt (.reg 367) (.lit 64))
     , .scalar (.binop 367 .band (.reg 367) (.lit 63))
     , .scalar (.binop 369 .lshr (.lit kT3numLo) (.reg 367))
     , .scalar (.binop 369 .mul (.reg 369) (.reg 368))
     , .scalar (.binop 369 .udiv (.reg 369) (.reg rT3m))   -- the `e ≥ P` branch
     , .scalar (.binop 370 .sub (.lit P) (.reg rT3e))
     , .scalar (.binop 370 .band (.reg 370) (.lit 63))
     , .scalar (.binop 371 .udiv (.lit kT3numLo) (.reg rT3m))
     , .scalar (.binop 372 .mul (.reg 371) (.reg rT3m))
     , .scalar (.binop 372 .sub (.lit kT3numLo) (.reg 372))
     , .scalar (.binop 371 .shl (.reg 371) (.reg 370))
     , .scalar (.binop 372 .shl (.reg 372) (.reg 370))
     , .scalar (.binop 372 .udiv (.reg 372) (.reg rT3m))
     , .scalar (.binop 371 .add (.reg 371) (.reg 372))     -- the `e < P` branch
     , .scalar (.binop 369 .mul (.reg 369) (.reg 366))
     , .scalar (.binop 373 .sub (.lit 1) (.reg 366))
     , .scalar (.binop 371 .mul (.reg 371) (.reg 373))
     , .scalar (.binop 351 .add (.reg 369) (.reg 371))
     , .scalar (.binop 374 .lt (.reg 276) (.lit smallQBound))
     , .scalar (.binop 351 .mul (.reg 351) (.reg 374)) ]
   else [ .scalar (.mov 351 (.lit 0)) ]) ++
  [ .scalar (.mov 354 (.reg rV0)) ] ++
  maxR 354 350 352 ++ maxR 354 351 352 ++
  [ -- the window, at the proved floor and at the oracle's floor-plus-one
    .scalar (.binop 355 .lshr (.reg 354) (.lit E))
  , .scalar (.binop 356 .add (.reg 355) (.lit 1))
  , .scalar (.binop 357 .gt (.reg 348) (.reg 355))
  , .scalar (.binop 358 .sub (.reg 348) (.reg 355))
  , .scalar (.binop 358 .mul (.reg 358) (.reg 357))
  , .scalar (.binop 359 .gt (.reg 348) (.reg 356))
  , .scalar (.binop 360 .sub (.reg 348) (.reg 356))
  , .scalar (.binop 360 .mul (.reg 360) (.reg 359))
    -- the row's own certification: the outward directions must be ordered.
    -- Each comparison is landed in a register of its own first, so that the
    -- collapsed aggregate below is unchanged and the five are still separable.
  , .scalar (.binop 530 .gt (.reg 325) (.reg 326))     -- L(q) inverted
  , .scalar (.binop 531 .gt (.reg 337) (.reg 339))     -- φ(q)/q inverted
  , .scalar (.binop 532 .gt (.reg 279) (.reg 280))     -- log q inverted
  , .scalar (.binop 533 .eq (.reg 343) (.lit 0))       -- κ* lower is 0
  , .scalar (.binop 534 .eq (.reg 348) (.lit 0))       -- λ(q) is 0
  , .scalar (.binop 361 .add (.reg 530) (.reg 531))
  , .scalar (.binop 361 .add (.reg 361) (.reg 532))
  , .scalar (.binop 361 .add (.reg 361) (.reg 533))
  , .scalar (.binop 361 .add (.reg 361) (.reg 534))
  , .scalar (.binop 361 .ne (.reg 361) (.lit 0))
  , .scalar (.binop 361 .mul (.reg 361) (.reg endR))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 361))
  , .scalar (.binop 362 .mul (.reg 530) (.reg endR))
  , .scalar (.binop rVLq .add (.reg rVLq) (.reg 362))
  , .scalar (.binop 362 .mul (.reg 531) (.reg endR))
  , .scalar (.binop rVPhi .add (.reg rVPhi) (.reg 362))
  , .scalar (.binop 362 .mul (.reg 532) (.reg endR))
  , .scalar (.binop rVLog .add (.reg rVLog) (.reg 362))
  , .scalar (.binop 362 .mul (.reg 533) (.reg endR))
  , .scalar (.binop rVKap .add (.reg rVKap) (.reg 362))
  , .scalar (.binop 362 .mul (.reg 534) (.reg endR))
  , .scalar (.binop rVLam .add (.reg rVLam) (.reg 362))
  ] ++
  -- the aggregates
  ([ (rNemp, 359), (rCel0, 358), (rCel1, 360), (rSVar, 354), (rSLam, 348)
   , (rSF1, 334), (rSPhi, 337), (rSCon, 340), (rSKap, 343), (rSQ, 276)
   , (rRows, rOne) ].flatMap fun x =>
    [ AInstr.scalar (.binop 363 .mul (.reg endR) (.reg x.2))
    , AInstr.scalar (.binop x.1 .add (.reg x.1) (.reg 363)) ]) ++
  -- the per-row planes, for the oracle comparison
  ([ 320, 322, 325, 326, 334, 337, 340, 343, 354, 348 ].zipIdx.flatMap
    fun x => gatedStore rCi (c.rowBase + x.2 * L) endR scr 364 x.1) ++
  -- clear the six sieve planes behind us
  ((List.range 6).flatMap fun i =>
    gatedStore rCi (i * L) endR scr 364 rZero)

/-! ## The tail -/

def RowCfg.tailBody (c : RowCfg) : List AInstr :=
  let L := c.segLen
  [ .scalar (.binop 500 .add (.reg rR) (.lit 1))
  , .scalar (.binop 501 .eq (.reg 500) (.lit c.period))
  , .scalar (.binop 502 .sub (.lit 1) (.reg 501))
  , .scalar (.binop rR .mul (.reg 502) (.reg 500))
  , .scalar (.binop 503 .mul (.reg 501) (.lit L))
  , .scalar (.binop rW .add (.reg rW) (.reg 503))
  , .scalar (.binop 504 .add (.reg rRnd) (.lit 1))
  , .scalar (.binop 505 .eq (.reg 504) (.lit c.roundsPerSlot))
  , .scalar (.binop 506 .sub (.lit 1) (.reg 505))
  , .scalar (.binop 504 .mul (.reg 504) (.reg 506))
  , .scalar (.binop rRnd .mul (.reg 504) (.reg 12))
  , .scalar (.binop 507 .mul (.reg 505) (.reg 12))         -- a slot ended
  , .scalar (.binop 508 .add (.reg rSlot) (.lit 1))
  , .scalar (.binop 509 .eq (.reg 508) (.lit c.slots))
  , .scalar (.binop 510 .sub (.lit 1) (.reg 509))
  , .scalar (.binop 508 .mul (.reg 508) (.reg 510))
  ] ++ latchR rSlot 507 508 511 ++
  [ .scalar (.binop 512 .mul (.reg 507) (.reg 509))        -- a row ended
  , .scalar (.binop 513 .add (.reg rCi) (.lit 1))
  ] ++ latchR rCi 512 513 511 ++
  [ .scalar (.binop rCi .mul (.reg rCi) (.reg 502)) ]

def RowCfg.body (c : RowCfg) : List AInstr :=
  c.markBody ++ c.deriveBody ++ logEngine c.expUnroll ++ expEngine c.expUnroll ++
    c.latchBody ++ c.finishBody ++ c.tailBody

/-! ## Initialization and epilogue -/

/-- The table, then a sentinel entry whose prime is `1`: the exhausted cursor
marks nothing anyway — `rPi = entries` sends the multiple to `L + 1` — and the
value `1` makes the bump a fixed point, so `rQp` can neither reach `0` (the
`urem` would be undefined) nor overflow. -/
def RowCfg.tableCells (c : RowCfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [ (c.tableBase + c.table.length, packEntry 1 0 0)
    , (c.tableBase + c.table.length + 1, oneE) ]

def RowCfg.seedList (c : RowCfg) : List (Nat × Nat) :=
  [ (rW, c.lo), (rOne, 1), (rZero, 0)
  , (rA13, 2 ^ P), (rA23, 2 ^ P), (rUlo, 2 ^ P), (rT3m, 2 ^ P)
  , (rXx, 2 ^ P) ]

def RowCfg.init (c : RowCfg) : List AInstr :=
  storeLits c.tableCells ++ seedRegs c.seedList

def storeResult (c : RowCfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .store 90 reg ]

/-- Store a run of registers into consecutive result cells from `slot`. -/
def storeResults (c : RowCfg) : Nat → List Nat → List AInstr
  | _, [] => []
  | slot, r :: rs => storeResult c slot r ++ storeResults c (slot + 1) rs

def RowCfg.epilogue (c : RowCfg) : List AInstr :=
  storeResult c 0 rViol ++ storeResult c 1 rRows ++ storeResult c 2 rSQ ++
  storeResult c 3 rCel0 ++ storeResult c 4 rCel1 ++ storeResult c 5 rSVar ++
  storeResult c 6 rSLam ++ storeResult c 7 rSF1 ++ storeResult c 8 rSPhi ++
  storeResult c 9 rSCon ++ storeResult c 10 rSKap ++ storeResult c 11 rNemp ++
  storeResults c 12 violRegs

def rowProgram (c : RowCfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-- Loop count for an exact prefix of the configured padded windows.  Every
complete window pays one full `period`; a final partial window still runs the
whole mark phase and then exactly `rows % segLen` transform rows. -/
def RowCfg.prefixLoopCount (c : RowCfg) (rows : Nat) : Nat :=
  let full := rows / c.segLen
  let tail := rows % c.segLen
  full * c.period +
    if tail = 0 then 0
    else c.markSteps + tail * c.slots * c.roundsPerSlot

/-- The row producer stopped after exactly `rows` rows.  Production can use
large fixed windows without sweeping padding or compiling a separate tiny
tail translation unit. -/
def rowPrefixProgram (c : RowCfg) (rows : Nat) : AProgram :=
  { rowProgram c with loopCount := c.prefixLoopCount rows }

/-! ## Emit-time configuration -/

/-- The configuration for a slice `[lo, lo + segLen·segCount)` whose mark table
is that of the **global** sweep to `tableHi`.  This is what a production chain
looks like — one artifact per slice, all of them carrying the primes of the
whole range — and it is also the only way to measure the cost at `q ≈ 3·10⁹`
without sweeping `3·10⁹` rows. -/
def RowCfg.ofChain (lo segLen segCount tableHi expUnroll : Nat) : RowCfg :=
  let hi := lo + segLen * segCount - 1
  let root := Nat.sqrt tableHi
  { lo := lo, segLen := segLen, segCount := segCount
    expUnroll := expUnroll
    smallQ := lo < smallQBound
    markSteps := markBudget root hi segLen
    table := markTable tableHi }

/-- A standalone sweep of `[lo, hi]`, whose table is its own. -/
def RowCfg.ofRange (lo segLen segCount expUnroll : Nat) : RowCfg :=
  RowCfg.ofChain lo segLen segCount (lo + segLen * segCount - 1) expUnroll

/-! ## Well-formedness, and the bridge instantiated -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem storeResult_all (c : RowCfg) (slot reg : Nat) (h : reg < regCount) :
    (storeResult c slot reg).all (ainstrWFB regCount) = true := by
  simp only [storeResult, regCount, List.all_cons, List.all_nil, ainstrWFB,
    instrWFB, operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

theorem seedRegs_all (l : List (Nat × Nat)) (h : ∀ x ∈ l, x.1 < regCount) :
    (seedRegs l).all (ainstrWFB regCount) = true := by
  simp only [seedRegs, List.all_map]
  refine List.all_eq_true.mpr (fun x hx => ?_)
  have hlt := h x hx
  simp only [Function.comp_apply, ainstrWFB, instrWFB, operandWFB,
    Bool.and_true, decide_eq_true_eq]
  exact hlt

theorem seedList_ok (c : RowCfg) : ∀ x ∈ c.seedList, x.1 < regCount := by
  intro x hx
  have hall : c.seedList.all (fun y => decide (y.1 < regCount)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem init_all (c : RowCfg) : c.init.all (ainstrWFB regCount) = true :=
  all_append (storeLits_all _) (seedRegs_all _ (seedList_ok c))

theorem latchR_all {dst c v t : Nat} (h : dst < regCount) (h1 : c < regCount)
    (h2 : v < regCount) (h3 : t < regCount) :
    (latchR dst c v t).all (ainstrWFB regCount) = true := by
  simp only [latchR, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem latchL_all {dst c t : Nat} (v : Nat) (h : dst < regCount)
    (h1 : c < regCount) (h3 : t < regCount) :
    (latchL dst c v t).all (ainstrWFB regCount) = true := by
  simp only [latchL, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem logRound_all : logRound.all (ainstrWFB regCount) = true := by rfl

theorem rootDigit_all (j : Nat) : (rootDigit j).all (ainstrWFB regCount) = true := by
  simp only [rootDigit, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, regCount, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem rootDigits_all : ((List.range (P + 1)).reverse.flatMap rootDigit).all
    (ainstrWFB regCount) = true := by
  simp only [List.all_flatMap]
  exact List.all_eq_true.mpr (fun j _ => rootDigit_all j)

theorem expRound_all : expRound.all (ainstrWFB regCount) = true := by
  simp only [expRound]
  exact all_append (all_append (by rfl) rootDigits_all) (by rfl)

theorem replicate_flatten_all (l : List AInstr) (n : Nat)
    (h : l.all (ainstrWFB regCount) = true) :
    ((List.replicate n l).flatten).all (ainstrWFB regCount) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      exact all_append h ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem logEngine_all (n : Nat) : (logEngine n).all (ainstrWFB regCount) = true := by
  simp only [logEngine]
  exact all_append (by rfl) (replicate_flatten_all _ _ logRound_all)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem expEngine_all (n : Nat) : (expEngine n).all (ainstrWFB regCount) = true := by
  simp only [expEngine]
  exact all_append (by rfl) (replicate_flatten_all _ _ expRound_all)

/-! Everything else is register-schedule-independent once `smallQ` is fixed, so
each phase's obligation is `rfl` at each of the two schedules. -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem markBody_all (c : RowCfg) : c.markBody.all (ainstrWFB regCount) = true := by
  rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem deriveBody_all (c : RowCfg) : c.deriveBody.all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem latchBody_all (c : RowCfg) : c.latchBody.all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem finishBody_all (c : RowCfg) : c.finishBody.all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem tailBody_all (c : RowCfg) : c.tailBody.all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  rfl

theorem body_all (c : RowCfg) : c.body.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (markBody_all c) (deriveBody_all c)) (logEngine_all _)) (expEngine_all _))
    (latchBody_all c)) (finishBody_all c)) (tailBody_all c)

theorem storeResults_all (c : RowCfg) : ∀ (slot : Nat) (l : List Nat),
    l.all (fun r => decide (r < regCount)) = true →
    (storeResults c slot l).all (ainstrWFB regCount) = true
  | _, [], _ => rfl
  | slot, a :: t, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact all_append (storeResult_all c slot a (of_decide_eq_true h.1))
        (storeResults_all c (slot + 1) t h.2)

theorem epilogue_all (c : RowCfg) : c.epilogue.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (all_append (all_append (all_append (all_append (all_append (all_append
    (storeResult_all c 0 rViol (by decide)) (storeResult_all c 1 rRows (by decide)))
    (storeResult_all c 2 rSQ (by decide)))
    (storeResult_all c 3 rCel0 (by decide)))
    (storeResult_all c 4 rCel1 (by decide)))
    (storeResult_all c 5 rSVar (by decide)))
    (storeResult_all c 6 rSLam (by decide)))
    (storeResult_all c 7 rSF1 (by decide)))
    (storeResult_all c 8 rSPhi (by decide)))
    (storeResult_all c 9 rSCon (by decide)))
    (storeResult_all c 10 rSKap (by decide)))
    (storeResult_all c 11 rNemp (by decide)))
    (storeResults_all c 12 violRegs (by decide))

/-- **The bridge's side condition.** -/
theorem rowProgram_wf (c : RowCfg) : (rowProgram c).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem rowPrefixProgram_wf (c : RowCfg) (rows : Nat) :
    (rowPrefixProgram c rows).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the per-`q` row.**  For any array base at
which the planes fit, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
number of failed root certifications and failed row guards, in the output
register. -/
theorem rowProgram_compiled (c : RowCfg) (base : Int)
    (hBase : BaseOk (rowProgram c).arrayLen base)
    (n : Nat) (hDenote : (rowProgram c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((rowProgram c).initialMCC base) (rowProgram c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(rowProgram c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (rowProgram_wf c) base hBase n hDenote

theorem rowPrefixProgram_compiled (c : RowCfg) (rows : Nat) (base : Int)
    (hBase : BaseOk (rowPrefixProgram c rows).arrayLen base)
    (n : Nat) (hDenote : (rowPrefixProgram c rows).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((rowPrefixProgram c rows).initialMCC base)
          (rowPrefixProgram c rows).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(rowPrefixProgram c rows).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (rowPrefixProgram_wf c rows)
    base hBase n hDenote

end LeanCompCert.Ports.Prop1224Row
