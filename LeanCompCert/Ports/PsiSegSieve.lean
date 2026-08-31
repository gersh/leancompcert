import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Ports.AddWidePort
import LeanCompCert.Verified.LogAccum

/-!
# The `ψ` residue: a fourth loop phase, and a two-word accumulator

`Ports/ArraySegSieve.lean` sieves `[lo, hi]` in windows and leaves, per
integer, the signals a Möbius residue needs.  `ψ(n) = Σ_{p^k ≤ n} log p` is not
of that shape: it sums *logarithms*, one per prime power, and the logarithm
costs `S` squaring rounds, which a data-independent body cannot spend only at
primes.  This file is the version that can.

## Four phases, not three

A window's period is `markSteps + segLen + logSteps`.  The first two are the
sieve's own mark and accumulation phases, unchanged in structure.  The third is
new:

* the **accumulation phase** no longer decodes `μ`.  It reads one plane, tests
  `prod = 0` (never marked, hence prime, since `lo > ⌊√hi⌋`), merges in the
  emit-time table of prime powers by one cursor and one comparison, and
  **compacts** the resulting test points into a stream of `(position, payload)`
  pairs;
* the **log phase** drains that stream, one squaring round per iteration,
  `S` rounds per entry, with the entry boundary carried by a wrapping counter
  rather than by a division.  At the `S`-th round it converts to natural
  logarithm, advances the residual, and runs both clauses of the family.

`logSteps = S · streamCap` is a *budget*.  Both ways it can be wrong are
checked by the artifact itself: a push past `streamCap` and a log phase that
ends with the stream undrained each increment the violation counter, so a
budget that is too small reports a failure rather than a wrong answer.

## The accumulator is two words, and has to be

`bench/results/psi_fold.md` §2 has the measurement.  In residual form
`D(n) = Σ lnFix(p^k) − 2^S·n` the family's own bound `|D| ≤ 2^S·√2·√n` caps a
single `u64` at `S ≤ 40`, where the enclosure the bracket carries — `4` ulps
per term over `π*(10¹³) = 346 065 765 710` terms — is `3.98·10⁻⁷` in a ratio
the paper prints to eight decimals.  Meeting the `10⁻⁸` margin behind
`0.79059276` needs `S ≥ 45.32`.

**`S = 48` is what this file uses.**  The enclosure is then `1.6·10⁻⁹`, one
sixth of the last printed digit, and the accumulator is 71 bits.  `S = 64` is
not available at all: `logFix S n` would exceed one word (`logFix_lt` bounds it
by `2^(S+6)`), so the per-term value itself would need two limbs.  Between the
two, `S = 48` is the largest scale at which the *term* stays one word while the
*accumulator* is two, which is exactly the cheap configuration.

The accumulator is held biased by `2⁷¹`, so it is an ordinary unsigned pair and
the fragment's `lt`/`gt` order it correctly.  `Verified/AddWide.lean` proves the
four instructions; `Verified/LogAccum.lean` proves that accumulating `logFix`
this way reproduces `logFold` exactly, so `logFold_bracket` transfers verbatim
and the error term `2·#terms` is still in the theorem.

## The comparisons are shifted by 16, and clause 1 is squared

Both clauses first shift the accumulator right by `16`:
`t = (D.lo >>> 16) + (D.hi <<< 48)` is exact because the overflow guard keeps
`D.hi < 2⁸`, and the constants are pre-shifted at emit time — **downward on
both sides**.  What that costs is `2¹⁶` ulps of `2⁻⁴⁸`, i.e. `2.3·10⁻¹⁰`
absolute, which is negligible against every margin below.

Clause 2 then compares against `⌊√2·2^S⌋·⌊√n⌋` directly.  It may: its constant
is not attained.  Over `[2, 1.11·10⁸]` the minimum of `(ψ(x) − x)/√x` is
`−0.9241`, so the slack is about `0.49·√n` against a floor loss below `√2`.

**Clause 1 may not, and used to.**  `max (ψ(x) − x)/√x = 0.7905927544` is
attained at `x = 110 102 617`, and `0.79059276` is that number rounded up; the
true margin there is `5.9·10⁻⁵` absolute while `cUp·(√n − ⌊√n⌋)` reaches
`0.791`.  Testing `D + 4·terms ≤ cUp·⌊√n⌋` therefore *fails at the extremal
point where the clause holds* — one integer below `1.11·10⁸`, and the reason a
production `ψ` run reported a violation that no smoke slice could reproduce.
Clause 1 is now `V² ≤ cUp16²·n`, exact in integers, `128`-bit on both sides and
built from `32×32` products; `rVFloor` keeps the old form as a reported
diagnostic so that the substitution loss stays visible.  It costs about `40`
instructions, which is what the earlier one-word design was buying and could
not afford to.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`: `psiProgram_wf` and
`psiProgram_compiled`, so `AProgram.evalCC_compile` applies and the emitted C
computes exactly `denote`.  The two-limb accumulator's arithmetic is proved in
`Verified/AddWide.lean` and its composition with the bracket in
`Verified/LogAccum.lean`.

Not proved, exactly as in `ArraySegSieve`: that `denote` *is* the residue.
That is checked by kernel evaluation against a trial-division reference at a
tiny configuration, and by the artifact against `bench/ref_psi.c` at `10⁶`,
`10⁷` and `10⁸`.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Ports.ArraySegSieve

/-! ## Emit-time constants

The fixed-point scale `S` is a **parameter**, carried by the configuration, not
a global.  `bench/results/psi_fold.md` §2 fixes the production value: the
family's own bound caps one `u64` at `S ≤ 40`, the printed constant's margin
needs `S ≥ 45.32`, and `logFix_lt` caps a one-word *term* at `S ≤ 58`.
`defaultS = 48` sits in that window with room on both sides.  A small `S` is
what makes the kernel check below evaluable.
-/

/-- The production fixed-point scale. -/
def defaultS : Nat := 48

/-- `⌊2⁶⁴ · ln 2⌋`, the conversion from base-2 to natural logarithm. -/
def L2 : Nat := 12786308645202655659

def L2hi : Nat := L2 / 4294967296
def L2lo : Nat := L2 % 4294967296

/-- `⌊2^S · ln n⌋`: the high word of `logFix S n · ⌊2⁶⁴ ln 2⌋`.  Two further
ulps over the bracket's two — one from this multiply, one from `L2`'s own
truncation — so the artifact's per-term window is `4` ulps of `2^-S`. -/
def lnFix (S n : Nat) : Nat := logFix S n * L2 / 18446744073709551616

/-- The accumulator's bias, `2^(S+23)`: above `2^S·√2·√hi` for every
`hi < 1.7·10¹³`, and one bit below the overflow guard.  At `S = 48` it is
`2⁷¹`, against a residual that reaches `2⁷⁰·¹` at `n = 10¹³`. -/
def biasOf (S : Nat) : Nat := 2 ^ (S + 23)

/-- The shift both sides of a clause are taken at. -/
def cmpShift : Nat := 16

def bias16Of (S : Nat) : Nat := 2 ^ (S + 7)

/-- The guard value: `D.hi ≥ guardHi` means the accumulator left `[0, 2^(S+24))`
and the shifted comparison would no longer be exact. -/
def guardHi (S : Nat) : Nat := 2 ^ (S + 24 - 64)

/-- `⌊0.79059276 · 2^S⌋`, the family's clause-1 constant, rounded **down**. -/
def cUp (S : Nat) : Nat := 79059276 * 2 ^ S / 100000000

/-- `⌊√2 · 2^S⌋`, the family's clause-2 constant, rounded **down** so that
`cDown · ⌊√n⌋ ≤ √2·2^S·√n` and the test is the stronger statement. -/
def cDown (S : Nat) : Nat := Nat.sqrt (2 * 2 ^ (2 * S))

def cUp16 (S : Nat) : Nat := cUp S / 65536
def cDown16 (S : Nat) : Nat := cDown S / 65536

/-! ### Clause 1 is tested by squaring, not against `⌊√n⌋`

`cUp` is not a constant with headroom.  `max_{x} (ψ(x) − x)/√x = 0.7905927544`
and is **attained**, at the prime `x = 110 102 617`; the clause's constant is
the same number rounded up to eight places.  At that one point the true margin
is `5.6·10⁻⁹` relative, i.e. `5.9·10⁻⁵` absolute.

Substituting `⌊√n⌋` for `√n` — which is what `cUp16 · rSq` does — costs up to
`cUp·(√n − ⌊√n⌋) < 0.791` absolute.  That is **four orders of magnitude larger
than the margin**, and at `x = 110 102 617` it is decisive: the ratio against
`⌊√x⌋` is `0.7906666`, which exceeds `cUp` by `7.4·10⁻⁵`.  A sieve over
`[2, 1.11·10⁸]` finds exactly one integer at which the `⌊√n⌋` form fails and
**none** at which the clause fails.  The conservatism that makes the floor form
sound is exactly what makes it false at the extremal point, and no window
sizing, budget or cap can reach it.

So clause 1 is tested as `V² ≤ cUp16²·n` in exact integers, `V` being the
biased-subtracted upper enclosure at scale `2^(S−16)`.  Both sides are
`128`-bit and are built from `32×32` products, which is all the fragment has;
`cUp16²` is an emit-time literal, which is why `S ≤ 48` is required — at
`S = 49` it no longer fits a word.  The floor form is *kept*, as a diagnostic
counter (`rVFloor`) that fires exactly when the substitution, and not the
mathematics, is what failed.

Clause 2 is left in floor form on purpose: its constant `√2` is not attained.
Over `[2, 1.11·10⁸]` the minimum of `(ψ(x) − x)/√x` is `−0.9241`, at `x = 2`,
so the slack is `0.49·√n` against a floor loss below `√2`; the tightest point
in that range has slack `0.107`, and it grows like `√n`. -/

/-- `cUp16²`, the clause-1 constant squared.  Below `2⁶⁴` exactly when
`S ≤ 48`; `cUp16Fits` is the side condition and the emitter refuses to build
a program that violates it. -/
def cUp16Sq (S : Nat) : Nat := cUp16 S * cUp16 S

def cUp16SqLo (S : Nat) : Nat := cUp16Sq S % 4294967296
def cUp16SqHi (S : Nat) : Nat := cUp16Sq S / 4294967296

/-- **The range of validity of the squared clause.**  `cUp16 S < 2³²` is what
makes `cUp16Sq S` a `u64` literal and `cUp16SqHi S` a `32`-bit multiplier. -/
def cUp16Fits (S : Nat) : Bool := decide (cUp16 S < 4294967296)

example : cUp16Fits 48 = true := by decide

example : cUp16Fits 49 = false := by decide

/-- The per-term enclosure width, in ulps of `2^-S`: two from
`logFix_bracket`, two from the `ln 2` conversion. -/
def ulp : Nat := 4

/-! ## Emit-time number theory: prime powers and the head -/

/-- Prime powers `p^k ≤ hi` with `k ≥ 2` and `q ≥ lo`, in increasing order,
each carrying `Λ(p^k) = log p` — so the weight is `lnFix p`, not `lnFix (p^k)`.
There are `228 871` of them below `10¹³` in all, and only about `L/(2√hi)` in
a window, but they cannot be dropped: over `[1, 10¹³]` they contribute
`2√n = 6.3·10⁶` against a budget of `0.03`. -/
def primePowers (S lo hi : Nat) : List (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for p in primesBelow (Nat.sqrt hi + 1) do
    let mut q := p * p
    while q ≤ hi do
      if lo ≤ q then out := out.push (q, lnFix S p)
      q := q * p
  return (out.qsort (fun a b => a.1 < b.1)).toList

/-- Every test point in `[2, n]`: the primes and the prime powers, merged. -/
def testPoints (S n : Nat) : List (Nat × Nat) :=
  let ps := (primesBelow (n + 1)).map (fun p => (p, lnFix S p))
  let pp := primePowers S 2 n
  ((ps ++ pp).toArray.qsort (fun a b => a.1 < b.1)).toList

/-- The carry-in the artifact needs at `n = lo − 1`: the biased residual as a
limb pair, the last test point, the term count, `⌊√(lo−1)⌋` and its next
square, and the incremental `⌊log₂⌋` state.

This is the same `logFix` arithmetic the artifact runs, executed in Lean at
emit time over the head `[1, lo−1]`.  For a chained run it is instead the
previous artifact's carry-out. -/
structure PsiSeed where
  dlo : Nat
  dhi : Nat
  prev : Nat
  terms : Nat
  sq : Nat
  sq2 : Nat
  ex : Nat
  th : Nat
  deriving Repr

def psiHead (S lo : Nat) : PsiSeed :=
  let tp := testPoints S (lo - 1)
  let total := tp.foldl (fun a e => a + e.2) 0
  let a := biasOf S + total - 2 ^ S * (lo - 1)
  let s0 := Nat.sqrt (lo - 1)
  let e0 := Nat.log2 lo
  { dlo := a % 18446744073709551616
    dhi := a / 18446744073709551616
    prev := lo - 1
    terms := tp.length
    sq := s0
    sq2 := (s0 + 1) * (s0 + 1)
    ex := e0
    th := 2 ^ (e0 + 1) }

/-! ## Configuration -/

/-- The sieve configuration plus what the fourth phase needs: the fixed-point
scale, how many test points a window is allowed to produce, and the emit-time
table of prime powers in range. -/
structure PsiCfg where
  base : Cfg
  /-- The fixed-point scale `S`. -/
  sc : Nat
  /-- Test points budgeted per window.  `logSteps = S · streamCap`, so this is
  the whole cost of the fourth phase.  Too small is *checked*, not silently
  wrong: the push clamps to a sink and counts a violation, and a log phase that
  ends undrained counts another. -/
  streamCap : Nat
  /-- Prime powers `q ∈ [lo, hi]` with `k ≥ 2`, with weight `lnFix S p`. -/
  pp : List (Nat × Nat)
  /-- Runtime-built prime-power tables carry their length as compact metadata
  instead of asking Lean to enumerate the table.  Literal-table smoke tests
  leave this absent. -/
  ppLenOverride : Option Nat := none
  deriving Repr

/-- The number of primes in `[lo, lo + len)`, by a segmented sieve over that
one window.  Emit-time only, and cheap: the base primes go up to
`√(lo+len)`, which at `lo = √(10¹³)` is `2 040`. -/
def windowPrimeCount (lo len : Nat) : Nat := Id.run do
  if len = 0 then return 0
  let top := lo + len - 1
  let base := primesBelow (Nat.sqrt top + 1)
  let mut mark : Array Bool := Array.replicate len false
  for p in base do
    let first := max (p * p) (((lo + p - 1) / p) * p)
    let mut m := first
    while m ≤ top do
      mark := mark.set! (m - lo) true
      m := m + p
  let mut cnt := 0
  for i in [0:len] do
    if !mark[i]! && lo + i ≥ 2 then cnt := cnt + 1
  return cnt

/-- The test points a window is budgeted, with a `6%` margin over the
**first** window — the densest, since prime density decreases.  The margin
covers the fluctuation of `π(x+L) − π(x)`, whose standard deviation is about
`√(L/ln x)`, i.e. `0.8%` at `x = 10¹³, L = 10⁶`.  Both ways this can be wrong
are checked by the artifact. -/
def streamBudget (S lo segLen : Nat) : Nat :=
  let np := windowPrimeCount lo segLen
  let npp := (primePowers S lo (lo + segLen - 1)).length
  (np + npp) * 106 / 100 + 128

def PsiCfg.ofScale (S lo segLen segCount : Nat) : PsiCfg :=
  let c := Cfg.ofRange lo segLen segCount
  { base := c
    sc := S
    streamCap := streamBudget S lo segLen
    pp := primePowers S lo c.hi }

def PsiCfg.ofRange (lo segLen segCount : Nat) : PsiCfg :=
  PsiCfg.ofScale defaultS lo segLen segCount

def PsiCfg.lo (c : PsiCfg) : Nat := c.base.lo
def PsiCfg.segLen (c : PsiCfg) : Nat := c.base.segLen
def PsiCfg.segCount (c : PsiCfg) : Nat := c.base.segCount
def PsiCfg.rootCount (c : PsiCfg) : Nat := c.base.rootCount
def PsiCfg.markSteps (c : PsiCfg) : Nat := c.base.markSteps
def PsiCfg.tableLen (c : PsiCfg) : Nat := c.base.tableLen
def PsiCfg.rootCap (c : PsiCfg) : Nat := c.base.rootCap
def PsiCfg.bootCount (c : PsiCfg) : Nat := c.base.bootCount
def PsiCfg.firstPrime (c : PsiCfg) : Nat := c.base.firstPrime
def PsiCfg.hi (c : PsiCfg) : Nat := c.base.hi
def PsiCfg.rootLen (c : PsiCfg) : Nat := c.base.rootLen
def PsiCfg.wDelta (c : PsiCfg) : Nat := c.base.wDelta
def PsiCfg.sentinel (c : PsiCfg) : Nat := c.base.sentinel

/-- Iterations the log phase gets per window. -/
def PsiCfg.logSteps (c : PsiCfg) : Nat := c.sc * c.streamCap

def PsiCfg.period (c : PsiCfg) : Nat :=
  c.markSteps + c.segLen + c.logSteps

def PsiCfg.rootSpan (c : PsiCfg) : Nat := c.rootCount * c.period

/-! ### Array layout

One plane, not two: `ψ` needs only "was this cell ever marked", so the flag
plane and the whole `μ` decoding disappear — nine instructions and `L` cells.
-/

/-- Sink cell for the mark phase's idle steps. -/
def PsiCfg.sinkProd (c : PsiCfg) : Nat := c.segLen
def PsiCfg.primeBase (c : PsiCfg) : Nat := c.segLen + 1
def PsiCfg.ppBase (c : PsiCfg) : Nat := c.primeBase + c.tableLen + 1
def PsiCfg.ppLen (c : PsiCfg) : Nat := c.ppLenOverride.getD c.pp.length
def PsiCfg.streamBase (c : PsiCfg) : Nat := c.ppBase + 2 * (c.ppLen + 1)
def PsiCfg.streamSink (c : PsiCfg) : Nat := c.streamBase + 2 * c.streamCap
def PsiCfg.primeSink (c : PsiCfg) : Nat := c.streamSink + 2
def PsiCfg.resultBase (c : PsiCfg) : Nat := c.primeSink + 1
/-- Seventeen result cells: the eight carry-out slots the chain reads, then
the eight per-class violation counters that sum to slot `7`, then the
substitution diagnostic that is not a failure. -/
def PsiCfg.arrayLen (c : PsiCfg) : Nat := c.resultBase + 17

/-! ## Register allocation

`0`–`99` the sieve core, `128`–`145` the root phase, `180`–`199` the residue's
persistent state, `220`–`343` recomputed every iteration.
-/

def rPi : Nat := 2
def rP : Nat := 3
def rJ : Nat := 4
def rR : Nat := 5
def rW : Nat := 6
def rZero : Nat := 7
def rLimit : Nat := 128
def rWrite : Nat := 129

def rDlo : Nat := 180
def rDhi : Nat := 181
def rCar : Nat := 182
def rPrev : Nat := 183
def rTerms : Nat := 184
def rSq : Nat := 185
def rSq2 : Nat := 186
def rWcur : Nat := 187
def rEcur : Nat := 188
def rPPc : Nat := 189
def rViol : Nat := 190
def rXm : Nat := 191
def rAa : Nat := 192
def rK : Nat := 193
def rEx : Nat := 194
def rTh : Nat := 195
def rNe : Nat := 196
def rPl : Nat := 197

/-! ### The eight failure classes, counted apart

`rViol` is the **aggregate** and remains the program's output, so `denote`
means exactly what it always meant.  Alongside it the loop keeps one counter
per way the run can fail, because they do not mean the same thing and a
reviewer holding only their sum cannot act on it.  Two of them are the
mathematics:

* `rVUp` — clause 1, `D + 4·terms ≤ ⌊0.79059276·2^S⌋·⌊√n⌋`, failed;
* `rVLo` — clause 2, `D ≥ −⌊√2·2^S⌋·⌊√n⌋`, failed.

The other six say the **run is not a test of the clauses at all**, which is
close to the opposite claim: the artifact ran outside the range in which its
own arithmetic is exact, so neither a pass nor a failure of the clauses above
means anything on that window.

* `rVCap` — a test point was pushed past `streamCap` and went to the sink, so
  a term is **missing** from `D`.  A missing positive term pushes `D` down:
  it makes clause 1 *easier* and clause 2 *harder*, so a budget overrun and a
  genuine lower-bound failure look alike in the aggregate and are opposites in
  fact;
* `rVDrain` — the window turned over with the stream undrained: `logSteps` was
  too small, and again terms are missing;
* `rVGap` — `n − prev` did not fit `16` bits, so `2^S·(n − prev)` may have
  wrapped;
* `rVSqrt` — one increment of `⌊√n⌋` did not suffice (a test-point gap wider
  than `2√n`);
* `rVLog2` — one increment of `⌊log₂ n⌋` did not suffice;
* `rVAcc` — the accumulator left `[0, 2^(S+24))`, which is what makes the
  `>>> 16` comparison exact.

Every increment of a class register sits immediately beside the `rViol`
increment it mirrors, on the same guard value, so the eight sum to the
aggregate by construction; the emitted driver checks that they do and refuses
to report a verdict if they do not. -/

def rVUp : Nat := 345      -- clause 1 failed
def rVLo : Nat := 346      -- clause 2 failed
def rVCap : Nat := 347     -- a push past `streamCap`
def rVDrain : Nat := 348   -- the stream was undrained at window turnover
def rVGap : Nat := 349     -- the test-point gap did not fit 16 bits
def rVSqrt : Nat := 350    -- one `⌊√n⌋` increment did not suffice
def rVLog2 : Nat := 351    -- one `⌊log₂ n⌋` increment did not suffice
def rVAcc : Nat := 352     -- the accumulator left `[0, 2^(S+24))`

/-- **Not a failure.**  The count of integers at which the discarded `⌊√n⌋`
form of clause 1 would have fired while the clause itself held — the
substitution loss, and nothing else.  It is reported and is deliberately *not*
part of `rViol`. -/
def rVFloor : Nat := 353

/-- The per-class counters in the order they occupy result slots `8 … 15`.
These eight sum to `rViol`.  `bench/PsiSegEmit.lean` labels them in this
order; keep the two in step. -/
def violRegs : List Nat :=
  [rVUp, rVLo, rVCap, rVDrain, rVGap, rVSqrt, rVLog2, rVAcc]

/-- Slot `16`: the diagnostic that is not a failure. -/
def diagRegs : List Nat := [rVFloor]

def regCount : Nat := 460
def outputReg : Nat := 190      -- `rViol`

/-! ## The sieve core, without the `μ` decoding -/

def PsiCfg.coreBody (c : PsiCfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let p1 := c.firstPrime
  [ -- phase selectors: mark, accumulate, log
    .scalar (.binop 8 .lt (.reg rR) (.lit T))
  , .scalar (.binop 170 .lt (.reg rR) (.lit (T + L)))
  , .scalar (.binop 9 .sub (.reg 170) (.reg 8))          -- inAcc
  , .scalar (.binop 171 .sub (.lit 1) (.reg 170))        -- inLog
    -- root phase selector, and the cursor limit it chooses
  , .scalar (.binop 130 .lt .idx (.lit c.rootSpan))
  , .scalar (.binop 131 .mul (.reg 130) (.lit (K - c.bootCount)))
  , .scalar (.binop rLimit .sub (.lit K) (.reg 131))
  , .scalar (.binop 132 .mul (.reg 9) (.reg 130))        -- inAccRoot
  , .scalar (.binop 133 .sub (.reg 9) (.reg 132))        -- inAccMain
    -- window start: reset the prime cursor, branchlessly
  , .scalar (.binop 10 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 11 .sub (.lit 1) (.reg 10))
  , .scalar (.binop 12 .urem (.reg rW) (.lit p1))
  , .scalar (.binop 13 .sub (.lit p1) (.reg 12))
  , .scalar (.binop 14 .urem (.reg 13) (.lit p1))
  , .scalar (.binop rPi .mul (.reg 11) (.reg rPi))
  , .scalar (.binop 16 .mul (.reg 10) (.lit p1))
  , .scalar (.binop 17 .mul (.reg 11) (.reg rP))
  , .scalar (.binop rP .add (.reg 16) (.reg 17))
  , .scalar (.binop 18 .mul (.reg 10) (.reg 14))
  , .scalar (.binop 19 .mul (.reg 11) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 18) (.reg 19))
    -- mark step: one plane, so "marked" is "nonzero"
  , .scalar (.binop 20 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 21 .mul (.reg 20) (.reg 8))
  , .scalar (.binop 22 .mul (.reg 21) (.reg rJ))
  , .scalar (.binop 23 .sub (.lit 1) (.reg 21))
  , .scalar (.binop 24 .mul (.reg 23) (.lit c.sinkProd))
  , .scalar (.binop 25 .add (.reg 22) (.reg 24))
  , .load 27 25
  , .scalar (.binop 28 .eq (.reg 27) (.lit 0))
  , .scalar (.binop 29 .add (.reg 27) (.reg 28))
  , .scalar (.binop 30 .mul (.reg 29) (.reg rP))
  , .store 25 30
    -- advance the prime cursor when the multiple ran past the window
  , .scalar (.binop 39 .sub (.lit 1) (.reg 21))
  , .scalar (.binop 40 .mul (.reg 8) (.reg 39))
  , .scalar (.binop 41 .add (.reg rPi) (.reg 40))
  , .scalar (.binop 42 .gt (.reg 41) (.reg rLimit))
  , .scalar (.binop 43 .sub (.lit 1) (.reg 42))
  , .scalar (.binop 44 .mul (.reg 43) (.reg 41))
  , .scalar (.binop 45 .mul (.reg 42) (.reg rLimit))
  , .scalar (.binop rPi .add (.reg 44) (.reg 45))
  , .scalar (.binop 46 .add (.reg rPi) (.lit c.primeBase))
  , .load 47 46
  , .scalar (.binop 48 .sub (.lit 1) (.reg 40))
  , .scalar (.binop 49 .add (.reg rJ) (.reg rP))
  , .scalar (.binop 50 .mul (.reg 40) (.reg 47))
  , .scalar (.binop 51 .mul (.reg 48) (.reg rP))
  , .scalar (.binop rP .add (.reg 50) (.reg 51))
  , .scalar (.binop 52 .urem (.reg rW) (.reg rP))
  , .scalar (.binop 53 .sub (.reg rP) (.reg 52))
  , .scalar (.binop 54 .urem (.reg 53) (.reg rP))
  , .scalar (.binop 55 .eq (.reg rPi) (.reg rLimit))
  , .scalar (.binop 56 .sub (.lit 1) (.reg 55))
  , .scalar (.binop 57 .mul (.reg 55) (.lit (L + 1)))
  , .scalar (.binop 58 .mul (.reg 56) (.reg 54))
  , .scalar (.binop 59 .add (.reg 57) (.reg 58))
  , .scalar (.binop 60 .mul (.reg 40) (.reg 59))
  , .scalar (.binop 61 .mul (.reg 48) (.reg 49))
  , .scalar (.binop rJ .add (.reg 60) (.reg 61))
    -- accumulation phase: the cell's integer, and whether it was ever marked
  , .scalar (.binop 62 .sub (.reg rR) (.lit T))
  , .scalar (.binop 63 .mul (.reg 9) (.reg 62))          -- i
  , .scalar (.binop 65 .add (.reg 63) (.reg rW))         -- n
  , .load 66 63
  , .scalar (.binop 67 .eq (.reg 66) (.lit 0))           -- never marked
    -- zero the cell just read, so the next window starts clean
  , .scalar (.binop 82 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 83 .mul (.reg 82) (.lit c.sinkProd))
  , .scalar (.binop 84 .add (.reg 63) (.reg 83))
  , .store 84 rZero
    -- root phase: append n to the prime table when it is an uncrossed cell
    -- with 2 ≤ n ≤ ⌊√hi⌋
  , .scalar (.binop 134 .sub (.reg 65) (.lit 2))
  , .scalar (.binop 135 .lt (.reg 134) (.lit (c.rootCap - 1)))
  , .scalar (.binop 136 .mul (.reg 135) (.reg 67))
  , .scalar (.binop 137 .mul (.reg 136) (.reg 132))
  , .scalar (.binop 138 .mul (.reg 137) (.reg rWrite))
  , .scalar (.binop 139 .sub (.lit 1) (.reg 137))
  , .scalar (.binop 140 .mul (.reg 139) (.lit c.primeSink))
  , .scalar (.binop 141 .add (.reg 138) (.reg 140))
  , .store 141 65
  , .scalar (.binop rWrite .add (.reg rWrite) (.reg 137))
  ]

/-! ## Phase three: compaction

The accumulation phase's own contribution.  It merges the emit-time prime-power
table into the prime stream by one cursor and one comparison, and writes the
merged test point into the stream — or into a sink, with a violation recorded,
if the window produced more test points than `streamCap` budgeted.
-/

def PsiCfg.compactBody (c : PsiCfg) : List AInstr :=
  [ -- the prime-power cursor's current entry
    .scalar (.binop 220 .shl (.reg rPPc) (.lit 1))
  , .scalar (.binop 221 .add (.reg 220) (.lit c.ppBase))
  , .load 222 221                                        -- its position
  , .scalar (.binop 223 .add (.reg 221) (.lit 1))
  , .load 224 223                                        -- its weight, lnFix p
  , .scalar (.binop 225 .eq (.reg 222) (.reg 65))
  , .scalar (.binop 226 .mul (.reg 225) (.reg 133))      -- isPrimePower
  , .scalar (.binop 227 .mul (.reg 67) (.reg 133))       -- isPrime
  , .scalar (.binop 228 .bor (.reg 227) (.reg 226))      -- merged-event push
  , .scalar (.binop 229 .mul (.reg 226) (.reg 224))      -- payload
    -- clamp to the sink when the budget is exhausted, and record it
  , .scalar (.binop 230 .lt (.reg rWcur) (.lit c.streamCap))
  , .scalar (.binop 231 .mul (.reg 228) (.reg 230))      -- doPush
  , .scalar (.binop 232 .sub (.reg 228) (.reg 231))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 232))
  , .scalar (.binop rVCap .add (.reg rVCap) (.reg 232))
    -- the target pair of cells
  , .scalar (.binop 233 .shl (.reg rWcur) (.lit 1))
  , .scalar (.binop 234 .add (.reg 233) (.lit c.streamBase))
  , .scalar (.binop 235 .mul (.reg 231) (.reg 234))
  , .scalar (.binop 236 .sub (.lit 1) (.reg 231))
  , .scalar (.binop 237 .mul (.reg 236) (.lit c.streamSink))
  , .scalar (.binop 238 .add (.reg 235) (.reg 237))
  , .store 238 65
  , .scalar (.binop 239 .add (.reg 238) (.lit 1))
  , .store 239 229
  , .scalar (.binop rWcur .add (.reg rWcur) (.reg 231))
  , .scalar (.binop rPPc .add (.reg rPPc) (.reg 226))
  ]

/-! ## Phase four: the logarithm and the two clauses -/

/-- The standard proved half-limb `u64 x u64 -> u128` circuit.  Keeping this
literal here avoids making the production emitter depend on the much larger
CDEM port; `PsiSegClauseCheck` proves it is exactly the generic
`Verified.MulWide.hl` realization. -/
def psiMulWideBody
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List AInstr :=
  [ .scalar (.binop s0 .band (.reg ra) (.lit 4294967295))
  , .scalar (.binop s1 .lshr (.reg ra) (.lit 32))
  , .scalar (.binop s2 .band (.reg rb) (.lit 4294967295))
  , .scalar (.binop s3 .lshr (.reg rb) (.lit 32))
  , .scalar (.binop s4 .mul (.reg s0) (.reg s2))
  , .scalar (.binop s5 .mul (.reg s0) (.reg s3))
  , .scalar (.binop s6 .mul (.reg s1) (.reg s2))
  , .scalar (.binop s7 .mul (.reg s1) (.reg s3))
  , .scalar (.binop s0 .add (.reg s5) (.reg s6))
  , .scalar (.binop s1 .lt (.reg s0) (.reg s5))
  , .scalar (.binop s2 .shl (.reg s0) (.lit 32))
  , .scalar (.binop rlo .add (.reg s4) (.reg s2))
  , .scalar (.binop s3 .lt (.reg rlo) (.reg s4))
  , .scalar (.binop s5 .lshr (.reg s0) (.lit 32))
  , .scalar (.binop s6 .mul (.reg s1) (.lit 4294967296))
  , .scalar (.binop rhi .add (.reg s7) (.reg s5))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s6))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s3)) ]

/-- Exact `V^2` limbs used by clause 1. -/
def upperSquareBody : List AInstr :=
  psiMulWideBody 402 402 410 414 403 404 405 406 407 408 409 411

/-- Exact `cUp16^2 * n` limbs used by clause 1. -/
def PsiCfg.upperRhsBody (c : PsiCfg) : List AInstr :=
  [ .scalar (.mov 415 (.lit (cUp16Sq c.sc))) ] ++
    psiMulWideBody 415 rNe 428 431 416 417 418 419 420 421 422 423

def PsiCfg.logBody (c : PsiCfg) : List AInstr :=
  [ -- the stream entry under the read cursor
    .scalar (.binop 240 .shl (.reg rEcur) (.lit 1))
  , .scalar (.binop 241 .add (.reg 240) (.lit c.streamBase))
  , .load 242 241
  , .scalar (.binop 243 .add (.reg 241) (.lit 1))
  , .load 244 243
  , .scalar (.binop 245 .lt (.reg rEcur) (.reg rWcur))   -- an entry is live
  , .scalar (.binop 246 .mul (.reg 245) (.reg 171))
  , .scalar (.binop 247 .eq (.reg rK) (.lit 0))
  , .scalar (.binop 248 .mul (.reg 247) (.reg 246))      -- start of an entry
    -- latch the entry
  , .scalar (.binop 249 .sub (.lit 1) (.reg 248))
  , .scalar (.binop 250 .mul (.reg 248) (.reg 242))
  , .scalar (.binop 251 .mul (.reg 249) (.reg rNe))
  , .scalar (.binop rNe .add (.reg 250) (.reg 251))
  , .scalar (.binop 252 .mul (.reg 248) (.reg 244))
  , .scalar (.binop 253 .mul (.reg 249) (.reg rPl))
  , .scalar (.binop rPl .add (.reg 252) (.reg 253))
    -- ⌊log₂ n⌋, incrementally: one step per entry suffices, by Bertrand
  , .scalar (.binop 254 .ge (.reg rNe) (.reg rTh))
  , .scalar (.binop 255 .mul (.reg 254) (.reg 248))
  , .scalar (.binop rEx .add (.reg rEx) (.reg 255))
  , .scalar (.binop 256 .mul (.reg 255) (.reg rTh))
  , .scalar (.binop rTh .add (.reg rTh) (.reg 256))
  , .scalar (.binop 257 .ge (.reg rNe) (.reg rTh))       -- …and it did suffice
  , .scalar (.binop 258 .mul (.reg 257) (.reg 248))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 258))
  , .scalar (.binop rVLog2 .add (.reg rVLog2) (.reg 258))
    -- the normalised mantissa, reset at the entry's first round
  , .scalar (.binop 259 .sub (.lit 62) (.reg rEx))
    -- the mask is the only thing between a *register* shift amount and C's
    -- undefined behaviour at a width of 64 or more.  `rEx ≤ 62` always, so it
    -- is a no-op; it is here so the emitted C is total, not merely correct.
  , .scalar (.binop 344 .band (.reg 259) (.lit 63))
  , .scalar (.binop 260 .shl (.reg rNe) (.reg 344))
  , .scalar (.binop 261 .mul (.reg 248) (.reg 260))
  , .scalar (.binop 262 .mul (.reg 249) (.reg rXm))
  , .scalar (.binop rXm .add (.reg 261) (.reg 262))
  , .scalar (.binop rAa .mul (.reg rAa) (.reg 249))
    -- one squaring round: Ports/LogFixPort.logRoundBody, verbatim
  , .scalar (.binop 263 .lshr (.reg rXm) (.lit 32))
  , .scalar (.binop 264 .band (.reg rXm) (.lit 4294967295))
  , .scalar (.binop 265 .mul (.reg 263) (.reg 263))
  , .scalar (.binop 266 .mul (.reg 263) (.reg 264))
  , .scalar (.binop 267 .mul (.reg 264) (.reg 264))
  , .scalar (.binop 268 .lshr (.reg 266) (.lit 29))
  , .scalar (.binop 269 .band (.reg 266) (.lit 536870911))
  , .scalar (.binop 270 .lshr (.reg 267) (.lit 62))
  , .scalar (.binop 271 .band (.reg 267) (.lit 4611686018427387903))
  , .scalar (.binop 272 .shl (.reg 269) (.lit 33))
  , .scalar (.binop 273 .add (.reg 272) (.reg 271))
  , .scalar (.binop 274 .ge (.reg 273) (.lit 4611686018427387904))
  , .scalar (.binop 275 .shl (.reg 265) (.lit 2))
  , .scalar (.binop 276 .add (.reg 275) (.reg 268))
  , .scalar (.binop 277 .add (.reg 276) (.reg 270))
  , .scalar (.binop 278 .add (.reg 277) (.reg 274))
  , .scalar (.binop 279 .ge (.reg 278) (.lit 9223372036854775808))
  , .scalar (.binop rXm .lshr (.reg 278) (.reg 279))
  , .scalar (.binop 280 .shl (.reg rAa) (.lit 1))
  , .scalar (.binop rAa .add (.reg 280) (.reg 279))
    -- the round counter, and `fin`: the round just run was the S-th
  , .scalar (.binop 281 .add (.reg rK) (.lit 1))
  , .scalar (.binop 282 .eq (.reg 281) (.lit c.sc))
  , .scalar (.binop 283 .sub (.lit 1) (.reg 282))
  , .scalar (.binop 284 .mul (.reg 281) (.reg 283))
  , .scalar (.binop rK .mul (.reg 284) (.reg 246))
  , .scalar (.binop 285 .mul (.reg 282) (.reg 246))      -- fin
    -- ⌊2^S ln n⌋ = high word of logFix · ⌊2⁶⁴ ln 2⌋, eleven instructions
  , .scalar (.binop 286 .shl (.reg rEx) (.lit c.sc))
  , .scalar (.binop 287 .add (.reg 286) (.reg rAa))      -- logFix S n
  , .scalar (.binop 288 .band (.reg 287) (.lit 4294967295))
  , .scalar (.binop 289 .lshr (.reg 287) (.lit 32))
  , .scalar (.binop 293 .mul (.reg 288) (.lit L2lo))
  , .scalar (.binop 294 .mul (.reg 288) (.lit L2hi))
  , .scalar (.binop 295 .mul (.reg 289) (.lit L2lo))
  , .scalar (.binop 296 .mul (.reg 289) (.lit L2hi))
  , .scalar (.binop 297 .lshr (.reg 293) (.lit 32))
  , .scalar (.binop 298 .add (.reg 294) (.reg 295))
  , .scalar (.binop 299 .add (.reg 298) (.reg 297))
  , .scalar (.binop 300 .lshr (.reg 299) (.lit 32))
  , .scalar (.binop 301 .add (.reg 296) (.reg 300))      -- lnFix n
    -- a prime power carries its own weight, `lnFix p`, in the payload
  , .scalar (.binop 302 .ne (.reg rPl) (.lit 0))
  , .scalar (.binop 303 .sub (.lit 1) (.reg 302))
  , .scalar (.binop 304 .mul (.reg 302) (.reg rPl))
  , .scalar (.binop 305 .mul (.reg 303) (.reg 301))
  , .scalar (.binop 306 .add (.reg 304) (.reg 305))      -- the term
    -- advance the residual to n:  D ← D − 2^S·(n − prev)
  , .scalar (.binop 307 .sub (.reg rNe) (.reg rPrev))
  , .scalar (.binop 308 .lt (.reg 307) (.lit 65536))
  , .scalar (.binop 309 .sub (.lit 1) (.reg 308))
  , .scalar (.binop 310 .mul (.reg 309) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 310))
  , .scalar (.binop rVGap .add (.reg rVGap) (.reg 310))
  , .scalar (.binop 311 .shl (.reg 307) (.lit c.sc))
  , .scalar (.binop 312 .mul (.reg 311) (.reg 285))
  , .scalar (.binop rCar .lt (.reg rDlo) (.reg 312))
  , .scalar (.binop rDlo .sub (.reg rDlo) (.reg 312))
  , .scalar (.binop rDhi .sub (.reg rDhi) (.reg rCar))
  , .scalar (.binop 313 .sub (.lit 1) (.reg 285))
  , .scalar (.binop 314 .mul (.reg 285) (.reg rNe))
  , .scalar (.binop 315 .mul (.reg 313) (.reg rPrev))
  , .scalar (.binop rPrev .add (.reg 314) (.reg 315))
    -- ⌊√n⌋, incrementally: consecutive squares are 2√n apart, prime gaps less
  , .scalar (.binop 316 .ge (.reg rNe) (.reg rSq2))
  , .scalar (.binop 317 .mul (.reg 316) (.reg 285))
  , .scalar (.binop rSq .add (.reg rSq) (.reg 317))
  , .scalar (.binop 318 .shl (.reg rSq) (.lit 1))
  , .scalar (.binop 319 .add (.reg 318) (.lit 1))
  , .scalar (.binop 320 .mul (.reg 317) (.reg 319))
  , .scalar (.binop rSq2 .add (.reg rSq2) (.reg 320))
  , .scalar (.binop 321 .ge (.reg rNe) (.reg rSq2))
  , .scalar (.binop 322 .mul (.reg 321) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 322))
  , .scalar (.binop rVSqrt .add (.reg rVSqrt) (.reg 322))
    -- clause 2, immediately before the jump: D ≥ −⌊√2·2^S⌋·⌊√n⌋
  , .scalar (.binop 323 .lshr (.reg rDlo) (.lit cmpShift))
  , .scalar (.binop 324 .shl (.reg rDhi) (.lit 48))
  , .scalar (.binop 325 .add (.reg 323) (.reg 324))
  , .scalar (.binop 326 .mul (.reg rSq) (.lit (cDown16 c.sc)))
  , .scalar (.binop 327 .sub (.lit (bias16Of c.sc)) (.reg 326))
  , .scalar (.binop 328 .lt (.reg 325) (.reg 327))
  , .scalar (.binop 329 .mul (.reg 328) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 329))
  , .scalar (.binop rVLo .add (.reg rVLo) (.reg 329))
    -- the jump: D ← D + the term
  , .scalar (.binop 330 .mul (.reg 306) (.reg 285))
  , .scalar (.binop rDlo .add (.reg rDlo) (.reg 330))
  , .scalar (.binop rCar .lt (.reg rDlo) (.reg 330))
  , .scalar (.binop rDhi .add (.reg rDhi) (.reg rCar))
  , .scalar (.binop rTerms .add (.reg rTerms) (.reg 285))
    -- clause 1, immediately after: D + 4·terms ≤ ⌊0.79059276·2^S⌋·⌊√n⌋
  , .scalar (.binop 331 .lshr (.reg rDlo) (.lit cmpShift))
  , .scalar (.binop 332 .shl (.reg rDhi) (.lit 48))
  , .scalar (.binop 333 .add (.reg 331) (.reg 332))
  , .scalar (.binop 334 .mul (.reg rTerms) (.lit ulp))
  , .scalar (.binop 335 .lshr (.reg 334) (.lit cmpShift))
    -- Two outward shift units cover the independent low-limb and term-budget
    -- remainders uniformly, including before `rTerms` reaches `2^16`.
  , .scalar (.binop 336 .add (.reg 335) (.lit 2))
  , .scalar (.binop 337 .add (.reg 333) (.reg 336))
    -- the discarded `⌊√n⌋` form, kept only to be reported: it is strictly
    -- stronger than the clause and false at the clause's extremal point
  , .scalar (.binop 338 .mul (.reg rSq) (.lit (cUp16 c.sc)))
  , .scalar (.binop 339 .add (.lit (bias16Of c.sc)) (.reg 338))
  , .scalar (.binop 340 .gt (.reg 337) (.reg 339))
    -- clause 1 itself: `V² ≤ cUp16²·n` in exact integers.  `V` is the
    -- biased-subtracted upper enclosure at scale `2^(S−16)`, clamped to `0`
    -- where the value is non-positive and the clause is trivial.
  , .scalar (.binop 400 .gt (.reg 337) (.lit (bias16Of c.sc)))
  , .scalar (.binop 401 .sub (.reg 337) (.lit (bias16Of c.sc)))
  , .scalar (.binop 402 .mul (.reg 401) (.reg 400))        -- V
  ] ++ upperSquareBody ++ c.upperRhsBody ++
  [ -- Both products above use the library's proved half-limb circuit.  The
    -- comparison below is the ordinary lexicographic order on their limbs.
    -- the 128-bit comparison; the two disjuncts are disjoint, so `add` is `or`
    .scalar (.binop 432 .gt (.reg 414) (.reg 431))
  , .scalar (.binop 433 .eq (.reg 414) (.reg 431))
  , .scalar (.binop 434 .gt (.reg 410) (.reg 428))
  , .scalar (.binop 435 .mul (.reg 433) (.reg 434))
  , .scalar (.binop 436 .add (.reg 432) (.reg 435))        -- V² > cUp16²·n
  , .scalar (.binop 437 .mul (.reg 436) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 437))
  , .scalar (.binop rVUp .add (.reg rVUp) (.reg 437))
    -- …and the substitution loss on its own: the floor form fired, the clause
    -- held.  Reported, never added to `rViol`.
  , .scalar (.binop 438 .sub (.lit 1) (.reg 436))
  , .scalar (.binop 439 .mul (.reg 340) (.reg 438))
  , .scalar (.binop 440 .mul (.reg 439) (.reg 285))
  , .scalar (.binop rVFloor .add (.reg rVFloor) (.reg 440))
    -- the accumulator stayed below 2⁷², which is what makes the shift exact
  , .scalar (.binop 342 .ge (.reg rDhi) (.lit (guardHi c.sc)))
  , .scalar (.binop 343 .mul (.reg 342) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 343))
  , .scalar (.binop rVAcc .add (.reg rVAcc) (.reg 343))
  , .scalar (.binop rEcur .add (.reg rEcur) (.reg 285))
  ]

/-! ## The tail: advance the window, and reset the stream -/

def PsiCfg.tailBody (c : PsiCfg) : List AInstr :=
  let L := c.segLen
  let P := c.period
  [ .scalar (.binop 86 .add (.reg rR) (.lit 1))
  , .scalar (.binop 87 .eq (.reg 86) (.lit P))
  , .scalar (.binop 88 .sub (.lit 1) (.reg 87))
  , .scalar (.binop rR .mul (.reg 88) (.reg 86))
  , .scalar (.binop 89 .mul (.reg 87) (.lit L))
  , .scalar (.binop 142 .eq .idx (.lit (c.rootSpan - 1)))
  , .scalar (.binop 143 .mul (.reg 142) (.lit c.wDelta))
  , .scalar (.binop 144 .add (.reg 89) (.reg 143))
  , .scalar (.binop rW .add (.reg rW) (.reg 144))
    -- the log phase must have drained the stream before the window turns over
  , .scalar (.binop 290 .lt (.reg rEcur) (.reg rWcur))
  , .scalar (.binop 291 .mul (.reg 290) (.reg 87))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 291))
  , .scalar (.binop rVDrain .add (.reg rVDrain) (.reg 291))
  , .scalar (.binop 292 .sub (.lit 1) (.reg 87))
  , .scalar (.binop rWcur .mul (.reg rWcur) (.reg 292))
  , .scalar (.binop rEcur .mul (.reg rEcur) (.reg 292))
  , .scalar (.binop rK .mul (.reg rK) (.reg 292))
  ]

def PsiCfg.body (c : PsiCfg) : List AInstr :=
  c.coreBody ++ c.compactBody ++ c.logBody ++ c.tailBody

/-! ## Initialization -/

/-- Write a literal into an array cell, using `90`/`91` as scratch. -/
def storeLit (cell value : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit cell)), .scalar (.mov 91 (.lit value)), .store 90 91 ]

/-- A whole table of `(cell, value)` pairs. -/
def storeLits (l : List (Nat × Nat)) : List AInstr :=
  l.flatMap (fun x => storeLit x.1 x.2)

/-- A whole list of `(register, value)` seeds. -/
def seedRegs (l : List (Nat × Nat)) : List AInstr :=
  l.map (fun x => .scalar (.mov x.1 (.lit x.2)))

/-- The array cells the init block writes: the bootstrap prime table with its
end guard, then the prime-power table with a sentinel above every reachable
`n`, so the merge cursor never runs off the end. -/
def PsiCfg.tableCells (c : PsiCfg) : List (Nat × Nat) :=
  (c.base.bootTable.zipIdx.map fun x => (c.primeBase + x.2, x.1)) ++
  [(c.primeBase + c.tableLen, c.sentinel)] ++
  (c.pp.zipIdx.flatMap fun x =>
    [(c.ppBase + 2 * x.2, x.1.1), (c.ppBase + 2 * x.2 + 1, x.1.2)]) ++
  [(c.ppBase + 2 * c.ppLen, 9223372036854775807),
   (c.ppBase + 2 * c.ppLen + 1, 0)]

/-- The registers the init block seeds: the walk's opening position, the
prime-collection cursor, and the residue's whole carry-in. -/
def PsiCfg.seedList (c : PsiCfg) (s : PsiSeed) : List (Nat × Nat) :=
  [ (rW, 1), (rWrite, c.primeBase + c.bootCount)
  , (rDlo, s.dlo), (rDhi, s.dhi), (rPrev, s.prev), (rTerms, s.terms)
  , (rSq, s.sq), (rSq2, s.sq2), (rEx, s.ex), (rTh, s.th) ]

def PsiCfg.init (c : PsiCfg) (s : PsiSeed) : List AInstr :=
  storeLits c.tableCells ++ seedRegs (c.seedList s)

/-! ## Epilogue and program

The result cells are the carry-out of a chained run: the residual's two limbs,
the last test point, the term count, `⌊√hi⌋` and the two `⌊log₂⌋` registers,
plus the violation count.  `ψ(hi) = prev + (D − bias)/2^S`, since `ψ` is
constant between `prev` and `hi`.
-/

def storeResult (c : PsiCfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .store 90 reg ]

/-- Store a run of registers into consecutive result cells, starting at
`slot`.  Structural recursion, so the well-formedness proof is an induction
and not a hundred-case `rfl`. -/
def storeResults (c : PsiCfg) : Nat → List Nat → List AInstr
  | _, [] => []
  | slot, r :: rs => storeResult c slot r ++ storeResults c (slot + 1) rs

def PsiCfg.epilogue (c : PsiCfg) : List AInstr :=
  storeResult c 0 rDlo ++ storeResult c 1 rDhi ++ storeResult c 2 rPrev ++
  storeResult c 3 rTerms ++ storeResult c 4 rSq ++ storeResult c 5 rEx ++
  storeResult c 6 rTh ++ storeResult c 7 rViol ++
  storeResults c 8 violRegs ++ storeResults c 16 diagRegs

def psiProgram (c : PsiCfg) (s : PsiSeed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * (c.rootCount + c.segCount)
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

theorem storeResult_all (c : PsiCfg) (slot reg : Nat) (h : reg < regCount) :
    (storeResult c slot reg).all (ainstrWFB regCount) = true := by
  simp only [storeResult, regCount, List.all_cons, List.all_nil, ainstrWFB,
    instrWFB, operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

set_option maxRecDepth 40000 in
theorem body_all (c : PsiCfg) : c.body.all (ainstrWFB regCount) = true := by rfl

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

theorem seedList_ok (c : PsiCfg) (s : PsiSeed) :
    ∀ x ∈ c.seedList s, x.1 < regCount := by
  intro x hx
  have hall : (c.seedList s).all (fun y => decide (y.1 < regCount)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem init_all (c : PsiCfg) (s : PsiSeed) :
    (c.init s).all (ainstrWFB regCount) = true :=
  all_append (storeLits_all _) (seedRegs_all _ (seedList_ok c s))

theorem storeResults_all (c : PsiCfg) : ∀ (slot : Nat) (l : List Nat),
    l.all (fun r => decide (r < regCount)) = true →
    (storeResults c slot l).all (ainstrWFB regCount) = true
  | _, [], _ => rfl
  | slot, a :: t, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact all_append (storeResult_all c slot a (of_decide_eq_true h.1))
        (storeResults_all c (slot + 1) t h.2)

theorem epilogue_all (c : PsiCfg) :
    c.epilogue.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (all_append (all_append (all_append
      (storeResult_all c 0 rDlo (by decide)) (storeResult_all c 1 rDhi (by decide)))
      (storeResult_all c 2 rPrev (by decide)))
      (storeResult_all c 3 rTerms (by decide)))
      (storeResult_all c 4 rSq (by decide)))
      (storeResult_all c 5 rEx (by decide)))
      (storeResult_all c 6 rTh (by decide)))
      (storeResult_all c 7 rViol (by decide)))
      (storeResults_all c 8 violRegs (by decide)))
      (storeResults_all c 16 diagRegs (by decide))

/-- **The bridge's side condition.** -/
theorem psiProgram_wf (c : PsiCfg) (s : PsiSeed) : (psiProgram c s).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the `ψ` residue.**  For any array base at
which the window fits, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
number of failed clauses and guards, in the output register. -/
theorem psiProgram_compiled (c : PsiCfg) (s : PsiSeed) (base : Int)
    (hBase : BaseOk (psiProgram c s).arrayLen base)
    (n : Nat) (hDenote : (psiProgram c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiProgram c s).initialMCC base) (psiProgram c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(psiProgram c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiProgram_wf c s) base hBase n hDenote

/-! ## The reference

`refPsi` is the same residue written directly as a Lean fold over the test
points — no sieve, no phases, no branchless gating — and is what the kernel
checks below compare `denote` against.  It is also what `bench/ref_psi.c`
computes, in the same fixed point.
-/

/-- `(biased residual, last test point, term count)` at `hi`, starting from the
head at `lo − 1`. -/
def refPsi (S lo hi : Nat) : Nat × Nat × Nat :=
  let s := psiHead S lo
  let tp := (testPoints S hi).filter (fun e => lo ≤ e.1)
  let total := tp.foldl (fun a e => a + e.2) 0
  let prev := (tp.map Prod.fst).foldl (fun _ q => q) s.prev
  let a := s.dlo + 18446744073709551616 * s.dhi + total
    - 2 ^ S * (prev - s.prev)
  (a, prev, s.terms + tp.length)

/-- The residual's two limbs, as the artifact reports them. -/
def refPsiLimbs (S lo hi : Nat) : Nat × Nat :=
  let a := (refPsi S lo hi).1
  (a % 18446744073709551616, a / 18446744073709551616)

/-! ## Reference audit

The small independent emit-time checks live in `PsiSegSieveChecks`.  The old
closed whole-program kernel reductions were not proof dependencies and were
retired after a capped rebuild measured a multi-gigabyte peak.  The production
route instead uses the proved compiler/denotation chain above and the compiled
agreement controls against `bench/ref_psi.c` at `S = 48` and
`hi = 10⁶, 10⁷, 10⁸`.
-/

end LeanCompCert.Ports.PsiSegSieve
