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

## The comparisons are one word, not two

A clause reads `D + 4·terms ≤ ⌊0.79059276·2^S⌋·⌊√n⌋`, and the right-hand side
is a 70-bit product.  Rather than a 128-bit multiply and a 128-bit compare, both
sides are shifted right by `16` first: `t = (D.lo >>> 16) + (D.hi <<< 48)` is
exact because the overflow guard keeps `D.hi < 2⁸`, and the constants are
pre-shifted at emit time — **downward on both sides**, so the test is strictly
stronger than the clause.  What it costs is `2¹⁶` ulps of `2⁻⁴⁸`, i.e.
`2.3·10⁻¹⁰` absolute against a margin of `10⁻⁸·√n ≥ 3·10⁻⁵`: seven orders of
magnitude of slack, for `7` instructions instead of about `40`.

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
def PsiCfg.ppLen (c : PsiCfg) : Nat := c.pp.length
def PsiCfg.streamBase (c : PsiCfg) : Nat := c.ppBase + 2 * (c.ppLen + 1)
def PsiCfg.streamSink (c : PsiCfg) : Nat := c.streamBase + 2 * c.streamCap
def PsiCfg.primeSink (c : PsiCfg) : Nat := c.streamSink + 2
def PsiCfg.resultBase (c : PsiCfg) : Nat := c.primeSink + 1
def PsiCfg.arrayLen (c : PsiCfg) : Nat := c.resultBase + 8

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

def regCount : Nat := 360
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
  , .scalar (.binop 228 .add (.reg 227) (.reg 226))      -- push
  , .scalar (.binop 229 .mul (.reg 226) (.reg 224))      -- payload
    -- clamp to the sink when the budget is exhausted, and record it
  , .scalar (.binop 230 .lt (.reg rWcur) (.lit c.streamCap))
  , .scalar (.binop 231 .mul (.reg 228) (.reg 230))      -- doPush
  , .scalar (.binop 232 .sub (.reg 228) (.reg 231))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 232))
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
    -- clause 2, immediately before the jump: D ≥ −⌊√2·2^S⌋·⌊√n⌋
  , .scalar (.binop 323 .lshr (.reg rDlo) (.lit cmpShift))
  , .scalar (.binop 324 .shl (.reg rDhi) (.lit 48))
  , .scalar (.binop 325 .add (.reg 323) (.reg 324))
  , .scalar (.binop 326 .mul (.reg rSq) (.lit (cDown16 c.sc)))
  , .scalar (.binop 327 .sub (.lit (bias16Of c.sc)) (.reg 326))
  , .scalar (.binop 328 .lt (.reg 325) (.reg 327))
  , .scalar (.binop 329 .mul (.reg 328) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 329))
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
  , .scalar (.binop 336 .add (.reg 335) (.lit 1))
  , .scalar (.binop 337 .add (.reg 333) (.reg 336))
  , .scalar (.binop 338 .mul (.reg rSq) (.lit (cUp16 c.sc)))
  , .scalar (.binop 339 .add (.lit (bias16Of c.sc)) (.reg 338))
  , .scalar (.binop 340 .gt (.reg 337) (.reg 339))
  , .scalar (.binop 341 .mul (.reg 340) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 341))
    -- the accumulator stayed below 2⁷², which is what makes the shift exact
  , .scalar (.binop 342 .ge (.reg rDhi) (.lit (guardHi c.sc)))
  , .scalar (.binop 343 .mul (.reg 342) (.reg 285))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 343))
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

def PsiCfg.epilogue (c : PsiCfg) : List AInstr :=
  storeResult c 0 rDlo ++ storeResult c 1 rDhi ++ storeResult c 2 rPrev ++
  storeResult c 3 rTerms ++ storeResult c 4 rSq ++ storeResult c 5 rEx ++
  storeResult c 6 rTh ++ storeResult c 7 rViol

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

theorem epilogue_all (c : PsiCfg) :
    c.epilogue.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (all_append
      (storeResult_all c 0 rDlo (by decide)) (storeResult_all c 1 rDhi (by decide)))
      (storeResult_all c 2 rPrev (by decide)))
      (storeResult_all c 3 rTerms (by decide)))
      (storeResult_all c 4 rSq (by decide)))
      (storeResult_all c 5 rEx (by decide)))
      (storeResult_all c 6 rTh (by decide)))
      (storeResult_all c 7 rViol (by decide))

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

/-! ## Kernel sanity checks

The bridge does not depend on any of this: it says the artifact computes
`denote`, whatever `denote` is.  These checks are the other half — evidence
that `denote` is the residue it is meant to be.  They evaluate the whole
four-phase sieve in the kernel at a tiny configuration and compare against a
**trial-division** reference, which shares no code with it: `lambdaFix` finds
the smallest factor of `n` by division and asks whether `n` is a power of it,
where the artifact reads an unmarked sieve cell and a merged emit-time table.

`S = 6` here, not `48`, only so that the log phase is 6 rounds per entry
instead of 48; the arithmetic is the same at every scale, and the artifact
repeats the comparison against `bench/ref_psi.c` at `S = 48` and
`hi = 10⁶, 10⁷, 10⁸`, where it agrees bit for bit.
-/

namespace Check

/-- The smallest prime factor of `n`, by trial division. -/
def smallestFactorAux (n d fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel + 1 => if d * d > n then n else if n % d = 0 then d else
      smallestFactorAux n (d + 1) fuel

def smallestFactor (n : Nat) : Nat := smallestFactorAux n 2 n

/-- Is `m` a power of `p`? -/
def isPowerOf (p m fuel : Nat) : Bool :=
  match fuel with
  | 0 => m == 1
  | fuel + 1 =>
      if m == 1 then true
      else if p < 2 then false
      else if m % p == 0 then isPowerOf p (m / p) fuel else false

/-- `Λ(n)` at scale `2^S`: `lnFix S p` when `n = p^k`, else `0`. -/
def lambdaFix (S n : Nat) : Nat :=
  if n < 2 then 0
  else
    let p := smallestFactor n
    if isPowerOf p n n then lnFix S p else 0

/-- `(Σ_{lo ≤ n ≤ hi} Λ(n), #test points, last test point)`. -/
def refWindow (S lo hi : Nat) : Nat × Nat × Nat :=
  ((List.range (hi + 1)).drop lo).foldl (fun acc n =>
    let w := lambdaFix S n
    if w = 0 then acc else (acc.1 + w, acc.2.1 + 1, n)) (0, 0, lo - 1)

/-- One main window of eight cells covering `[25, 32]`, behind one root window
covering `[1, 8]`.  The counts are spelled out because the emit-time sieve is
not a kernel-reducible definition; they are what `PsiCfg.ofScale 4 25 8 1`
computes — `⌊√32⌋ = 5`, `⌊√8⌋ = 2` leaves `[2]` as the bootstrap table, and the
root phase collects the two remaining primes `3`, `5` into a table of
`π(5) = 3` entries.  The prime powers in range are `25`, `27` and `32`, each
weighted by `lnFix 4 p` and **not** by `lnFix 4 (p^k)`. -/
def cfg : PsiCfg :=
  { base :=
      { lo := 25, segLen := 8, segCount := 1, rootCount := 1
        bootPrimes := [2], mainCount := 3, rootCap := 5, markSteps := 29 }
    sc := 4
    streamCap := 5
    pp := [(25, 25), (27, 17), (32, 11)] }

/-- The head `[1, 24]`, folded at emit time.  `biasOf 4 = 2²⁷`. -/
def seed : PsiSeed :=
  { dlo := 134217695, dhi := 0, prev := 24, terms := 13
    sq := 4, sq2 := 25, ex := 4, th := 32 }

/-- …and that is exactly what the trial-division reference says the head is. -/
example : seed.dlo = biasOf 4 + (refWindow 4 2 24).1 - 2 ^ 4 * 24 := by decide

example : seed.terms = (refWindow 4 2 24).2.1 := by decide

/-- A program with the epilogue stripped and the output pointed at one
accumulator, so a single residue register can be read off. -/
def probe (out : Nat) : AProgram :=
  { regCount := regCount, arrayLen := cfg.arrayLen
    loopCount := cfg.period * (cfg.rootCount + cfg.segCount)
    init := cfg.init seed, body := cfg.body, epilogue := [], output := out }

/-- The three emit-time prime-power weights are `Λ(p^k) = log p`, not
`log(p^k)`: `25 ↦ lnFix 5`, `27 ↦ lnFix 3`, `32 ↦ lnFix 2`. -/
example : cfg.pp = [(25, lnFix 4 5), (27, lnFix 4 3), (32, lnFix 4 2)] := by decide

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- **The two-limb accumulator.**  After the four-phase loop the low limb holds
the head's carry-in plus `Σ_{25 ≤ n ≤ 32} Λ(n)` minus `2⁴·(32 − 24)` — the
residual, exactly as the trial-division reference computes it. -/
example : (probe rDlo).denote
    = some (seed.dlo + (refWindow 4 25 32).1
        - 2 ^ 4 * ((refWindow 4 25 32).2.2 - seed.prev)) := by decide

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- The term count is the head's plus the window's; the window's five test
points are `25 = 5², 27 = 3³, 29, 31, 32 = 2⁵`, so both the prime stream and
the prime-power merge are exercised. -/
example : (probe rTerms).denote
    = some (seed.terms + (refWindow 4 25 32).2.1) := by decide

set_option maxRecDepth 40000000 in
set_option maxHeartbeats 20000000 in
/-- The incrementally maintained `⌊√n⌋` reaches `⌊√32⌋ = 5`. -/
example : (probe rSq).denote = some 5 := by decide

end Check

end LeanCompCert.Ports.PsiSegSieve
