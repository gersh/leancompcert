import LeanCompCert.Verified.ArrayBridge

/-!
# The offset segmented sieve, and the residues of the reduced cite families

`Ports/ArrayMobius.lean` sieves `[0, L)` in one shot: cell `i` *is* the
integer `i`, the array is `3L` cells wide, and the whole range has to fit in
memory at once.  At `L = 10⁸` that is already 1.56 GB, so `10¹²` is 15 TB and
`10¹⁶` is not a number one writes down.  This file is the offset, multi-segment
version: cell `i` of the current window represents `lo + s·L + i`, one
`AProgram` walks `segCount` consecutive windows, and the memory is `3L` cells
no matter how long the walk is.

## What changes against `ArrayMobius`

Four things, all inside the program; the bridge is untouched.

* **The offset.**  The first multiple of `p` inside the window `[w, w+L)` is at
  cell `(p − w mod p) mod p`, one `urem` when the prime cursor advances.  The
  square test `p² ∣ n` likewise reads `n = w + tgt` rather than `tgt`.
* **The segment walk.**  The single loop is `(rootCount + segCount) · (T + L)`
  iterations long; the position `r` inside a window and the window base `w` are
  ordinary registers advanced by a branchless wrap at the end of every body.
  At `r = 0` the prime cursor is reset, again branchlessly.
* **No clear pass.**  The accumulation phase writes `0` back into the two cells
  it has just read, so the next window starts from a zero array — which is
  exactly the state the bridge's `initialMem` hands to the first window.  A
  separate clear phase would have cost another `L` iterations per window.
* **The root phase.**  The prime table is *computed by the program*, not
  carried by it.  See below.

## The root phase: why the artifact no longer carries a prime table

Marking a window inside `[2, hi]` needs every prime `p ≤ √hi`.  Writing them
into the array from the init block costs three straight-line instructions per
prime, i.e. `3·π(√hi)` statements in one C function: 28 779 at `hi = 10¹⁰`,
235 497 at `10¹²`, 17 284 368 at `10¹⁶`.  Measured, `ccomp -O2` segfaults on
the `10¹²` translation unit at the default stack and reaches 30.5 GB with an
unlimited one, so past roughly `10¹⁰` no verified compiler accepts the
artifact.  The table is the whole obstruction, and the fix is to delete it.

The loop therefore runs `rootCount` **root windows** before the `segCount`
ordinary ones.  The root windows walk `[1, rootCount·L]` with the *same*
instructions — same marking, same accumulation pass — and differ only in what
the two phase selectors gate:

* the mark cursor stops after `π(⌊√(rootCount·L)⌋)` entries rather than
  `π(⌊√hi⌋)`, so a root window is sieved by the small **bootstrap** primes the
  init block does spell out;
* the accumulation pass, instead of feeding the residue, appends `n` to the
  prime table exactly when the cell was never marked and `2 ≤ n ≤ ⌊√hi⌋` —
  which for `n ≤ rootCount·L` says precisely that `n` is a prime larger than
  every bootstrap prime, because a composite that size has a prime factor at
  most `⌊√(rootCount·L)⌋`.

Bootstrap primes then main primes, both in increasing order, is exactly the
table the main phase reads.  What the init block spells out is
`π(⌊√(rootCount·L)⌋) ≈ π(hi^{1/4})` primes — 168 at `hi = 10¹²` and 1 229 at
`10¹⁶` — so the emitted C stops growing with `hi`.

The prices are honest and small: `rootCount·L ≈ √hi` extra integers swept
(one part in `√hi`), and nineteen extra instructions in a body of 93, since
the root machinery, like everything else here, executes on every iteration
and is multiplied by zero when idle.

## The residues

The point of the sieve is not `μ` but the *running* quantities the reduced
cite families bound.  Two residue blocks are provided, each a suffix of the
loop body reading the per-`n` signals the core leaves in registers:

* `mertensResidue` — the Mertens sum `M(n) = Σ_{m≤n} μ(m)` and the squarefree
  count `Q(n) = Σ_{m≤n} |μ(m)|`, together with the running extrema of `M` and
  of `G(n) = Q(n)·2³⁶ − c·n` (`c = ⌊(6/π²)·2³⁶⌋`).  These are the residues of
  `mertensM_hurst_sqrt` and of the CDEM reproducible squarefree head.
* `mobiusOverNResidue` — the fixed-point partial sum
  `T(n) = Σ_{m≤n} μ(m)·round(2⁶²/m)`, whose extrema are the residue of Platt's
  (2.11) and of Platt's stronger rigorously-computed range.

Every comparison against a real-valued majorant happens **once per artifact**,
in the epilogue, against a threshold that is an exact integer computed in Lean
(`Nat.sqrt` of an exact rational cross-multiplication, and for `6/π²` a Machin
computation of `π` in integer arithmetic).  The loop body itself only adds and
compares machine words.  This is what makes the per-integer cost small: the
√ and the π never appear in the artifact.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`:

* `segProgram_wf` — every program this file builds is well-formed, at every
  `(lo, L, segCount)` and for either residue;
* `mertensProgram_compiled` and `mobiusProgram_compiled` — hence
  `AProgram.evalCC_compile` applies: the compiled CCIR trace, and through
  `MemFragment.lowerMSequence_correct` the emitted C, computes exactly
  `denote`.

Not proved, exactly as in `ArrayMobius`: that `denote` *is* the residue —
that the sieve computes `μ`, that the accumulators are `M`, `Q`, `T`, and that
a zero output means the reduced family holds on the range.  That is an
algorithmic-correctness statement about the sieve; it is checked here by kernel
evaluation against a trial-division reference at small sizes, and by the
artifact against the reference sieve at large ones.  The distinction is the
same one `ArrayMobius` records, and it is deliberate.
-/

namespace LeanCompCert.Ports.ArraySegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-! ## Emit-time number theory

Everything in this section runs in Lean when the artifact is built.  None of
it is compiled; it only produces the literals the program carries.
-/

/-- Primes `< n`, by an array sieve (the `ArrayMobius` version is quadratic
and cannot reach the `10⁶` this file needs). -/
def primesBelow (n : Nat) : List Nat := Id.run do
  if n ≤ 2 then return []
  let mut sieve : Array Bool := Array.replicate n true
  let mut d := 2
  while d * d < n do
    if sieve[d]! then
      let mut m := d * d
      while m < n do
        sieve := sieve.set! m false
        m := m + d
    d := d + 1
  let mut out : Array Nat := #[]
  for i in [2:n] do
    if sieve[i]! then out := out.push i
  return out.toList

/-- All primes `p` with `p² ≤ hi`: exactly the primes a window inside
`[2, hi]` has to sieve by. -/
def sievingPrimes (hi : Nat) : List Nat := primesBelow (Nat.sqrt hi + 1)

/-- `(π(x), Σ_{p ≤ x} (⌊len/p⌋ + 2))` — the size of the prime table and the
mark budget a window of `len` cells needs — by a **segmented** sieve, so that
emit-time memory is `O(√x + block)` rather than `O(x)`.  At `hi = 10¹⁶` the
argument is `x = 10⁸`, where an unsegmented `Array Bool` would be 100 MB and
the list of primes 5.8 million entries; neither is ever built, because the
artifact now computes the table itself and only these two counts are needed.
Emit-time only: never compiled, never kernel-reduced. -/
def primeStats (x len : Nat) : Nat × Nat := Id.run do
  if x < 2 then return (0, 0)
  let base := primesBelow (Nat.sqrt x + 1)
  let block := 1 <<< 18
  let mut cnt := 0
  let mut sum := 0
  let mut lo := 2
  while lo ≤ x do
    let top := min x (lo + block - 1)
    let width := top + 1 - lo
    let mut mark : Array Bool := Array.replicate width false
    for p in base do
      if p * p ≤ top then
        let first := max (p * p) (((lo + p - 1) / p) * p)
        let mut m := first
        while m ≤ top do
          mark := mark.set! (m - lo) true
          m := m + p
    for i in [0:width] do
      if !mark[i]! then
        cnt := cnt + 1
        sum := sum + len / (lo + i) + 2
    lo := top + 1
  return (cnt, sum)

/-! ### `π` in integer arithmetic

`⌊π · 2^N⌋` to within a handful of ulps, by Machin's formula
`π = 16·atan(1/5) − 4·atan(1/239)`, summed with integer division only.  The
series alternates and its terms decrease, so truncating after a term of the
same sign as the tail keeps the partial sum on a known side; the `± 4096`
slack below swallows both that and the per-term floor error.
-/

/-- `Σ_{k<terms} (−1)^k ⌊2^N / ((2k+1)·x^{2k+1})⌋`, returned as
`(positive part, negative part)`. -/
def atanInvParts (x N terms : Nat) : Nat × Nat := Id.run do
  let scale := 2 ^ N
  let mut pos := 0
  let mut neg := 0
  let mut k := 0
  while k < terms do
    let den := (2 * k + 1) * x ^ (2 * k + 1)
    if den = 0 || den > scale then
      k := terms
    else
      let term := scale / den
      if k % 2 = 0 then pos := pos + term else neg := neg + term
      k := k + 1
  return (pos, neg)

/-- `⌊π·2^N⌋` up to a few thousand ulps, as a `(lower, upper)` pair. -/
def piScaled (N : Nat) : Nat × Nat :=
  let (p5, n5) := atanInvParts 5 N (N + 8)
  let (p239, n239) := atanInvParts 239 N (N + 8)
  let a := 16 * p5 + 4 * n239
  let b := 16 * n5 + 4 * p239
  let mid := a - b
  (mid - 65536, mid + 65536)

/-- `⌊(6/π²)·2^k⌋`, rounded **down** with slack: the value returned is `≤ the
true `(6/π²)·2^k`.  Clause 1 of the CDEM family wants exactly that side. -/
def sixOverPiSqScaled (k : Nat) : Nat :=
  let N := 128
  let (_, hi) := piScaled N
  -- (6/π²)·2^k = 6·2^(k+2N) / (π·2^N)²  — dividing by the *upper* π gives a
  -- lower bound, and the floor lowers it further.
  6 * 2 ^ (k + 2 * N) / (hi * hi)

/-! ## Configuration -/

/-- Everything the emitted program needs to know.  `lo ≥ 1` is required: the
`μ(n)/n` residue divides by `n`, and the "one large prime factor" decoding of
the sieve is wrong at `n = 0` (which would be read as `μ(0) = −1`).  At
`n = 1` it is right — the cell is never marked, `prod` reads back as the empty
product `1`, and `1 = n` gives no extra sign flip.

`bootPrimes`, `mainCount` and `markSteps` are numbers computed at emit time by
`Cfg.ofRange`; only `bootPrimes` becomes instructions, and its length is
`π(hi^{1/4})`. -/
structure Cfg where
  /-- First integer covered by the main phase. -/
  lo : Nat
  /-- Cells per window, root and main alike. -/
  segLen : Nat
  /-- Number of main windows. -/
  segCount : Nat
  /-- Number of leading root windows: they walk `[1, rootCount·segLen]` and
  fill the prime table.  `rootCount · segLen ≥ ⌊√hi⌋` is required. -/
  rootCount : Nat
  /-- Primes `p ≤ ⌊√(rootCount·segLen)⌋`, spelled out by the init block.
  These are the primes a root window is sieved by, and the prefix of the
  table the root phase extends. -/
  bootPrimes : List Nat
  /-- `π(⌊√hi⌋)` — the whole table's length, and the cursor limit of a main
  window.  Taken as `π(max(⌊√(rootCount·segLen)⌋, ⌊√hi⌋))` so that the
  degenerate configurations where the bootstrap list already overshoots stay
  consistent. -/
  mainCount : Nat
  /-- `⌊√hi⌋`: the largest prime the root phase collects.  A field and not a
  `Nat.sqrt` call, because the body carries it as a literal and `Nat.sqrt` is
  defined by well-founded recursion, which the kernel does not unfold. -/
  rootCap : Nat
  /-- Mark steps budgeted per window: one per multiple of each prime inside
  the window, one per prime to advance the cursor, and slack.  Too small
  silently truncates the sieve (the kernel checks below catch that); too large
  only wastes iterations. -/
  markSteps : Nat
  deriving Repr

/-- Last integer covered. -/
def Cfg.hi (c : Cfg) : Nat := c.lo + c.segLen * c.segCount - 1

/-- Integers the root phase sweeps: `[1, rootLen]`. -/
def Cfg.rootLen (c : Cfg) : Nat := c.rootCount * c.segLen

def Cfg.bootCount (c : Cfg) : Nat := c.bootPrimes.length

def Cfg.ofRange (lo segLen segCount : Nat) : Cfg :=
  let hi := lo + segLen * segCount - 1
  let rootCap := Nat.sqrt hi
  let rootCount := max 1 ((rootCap + segLen - 1) / segLen)
  let rootLen := rootCount * segLen
  -- `max … 2` is load-bearing, not cosmetic.  The window-start reset installs
  -- the literal `firstPrime = 2` and *its* first multiple, and the mark step
  -- that follows uses them before the cursor-exhausted test can intervene —
  -- so the table's entry 0 must be `2`, i.e. `bootPrimes` must be non-empty.
  -- `⌊√rootLen⌋ ≤ 1` happens whenever `rootLen ≤ 3`, i.e. `segLen ≤ 3` and
  -- `hi ≤ 15`, and there the empty bootstrap list made the root phase mark
  -- cell `0` with a prime it had not tabulated, miss collecting `2`, and
  -- leave a `0` in the table for the main phase to take a `urem` by.
  -- Widening the bootstrap list is sound: it only marks more, and
  -- `(boot+1)² > rootLen ≥ rootCap` still holds.
  let boot := max (Nat.sqrt rootLen) 2
  let (cnt, sum) := primeStats (max boot rootCap) segLen
  { lo := lo, segLen := segLen, segCount := segCount
    rootCount := rootCount
    bootPrimes := primesBelow (boot + 1)
    mainCount := cnt
    rootCap := rootCap
    markSteps := sum + 16 }

def Cfg.tableLen (c : Cfg) : Nat := c.mainCount

/-- Iterations per window: the mark phase then the accumulation phase.  There
is no clear phase — accumulation zeroes the cells it reads. -/
def Cfg.period (c : Cfg) : Nat := c.markSteps + c.segLen

/-- The first iteration index of the main phase. -/
def Cfg.rootSpan (c : Cfg) : Nat := c.rootCount * c.period

def Cfg.sinkProd (c : Cfg) : Nat := 2 * c.segLen
def Cfg.primeBase (c : Cfg) : Nat := 3 * c.segLen + 1
def Cfg.resultBase (c : Cfg) : Nat := 3 * c.segLen + c.tableLen + 2
/-- Scratch cell the prime-collecting store aims at when it is not
collecting.  It is never read. -/
def Cfg.primeSink (c : Cfg) : Nat := c.resultBase + 7
def Cfg.arrayLen (c : Cfg) : Nat := c.resultBase + 8
def Cfg.sentinel (c : Cfg) : Nat := c.segLen + 1
def Cfg.firstPrime (c : Cfg) : Nat := c.bootPrimes.headD 2

/-- The bootstrap table as written into the array: the bootstrap primes, then
a guard value.  Only its being nonzero matters — the cursor position, not the
value, is what stops the marking, but the value is still fed to a `urem`.
The root phase overwrites this cell with the first prime it collects. -/
def Cfg.bootTable (c : Cfg) : List Nat := c.bootPrimes ++ [c.sentinel]

/-- The constant the window base jumps by at the root-to-main transition:
`lo − (1 + rootLen)` in two's complement, so that one `add` retargets the walk
from `[1, rootLen]` to `[lo, hi]`. -/
def Cfg.wDelta (c : Cfg) : Nat :=
  (c.lo + Verified.Reflect.M - (1 + c.rootLen) % Verified.Reflect.M) %
    Verified.Reflect.M

/-! ## Register allocation

`0`–`7` persistent, `8`–`99` recomputed every iteration, `100`–`127` the
residue's own persistent state, `128`–`145` the root phase.
-/

def rPi : Nat := 2      -- prime-table cursor
def rP : Nat := 3       -- current prime
def rJ : Nat := 4       -- current multiple, as a cell index
def rR : Nat := 5       -- position inside the window
def rW : Nat := 6       -- window base (the integer cell 0 stands for)
def rZero : Nat := 7    -- constant 0, for the clearing stores

def rLimit : Nat := 128 -- prime-table cursor limit for the current phase
def rWrite : Nat := 129 -- prime-table write cursor, as an absolute cell index

def regCount : Nat := 192

/-! ## The core loop body

Leaves, for the accumulation phase, `pos` in `79`, `neg` in `80`, `|μ|` in
`81`, the current integer `n` in `65`, and the phase selector `inAccMain` in
`133`.  All four are already gated: during the mark phase and throughout the
root phase they are `0`.  `n` is never `0` — the root walk opens at `1`, and
`lo ≥ 1` — so the residue may divide by it unconditionally.
-/

def Cfg.coreBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let P := c.period
  let p1 := c.firstPrime
  [ -- phase selectors
    .scalar (.binop 8 .lt (.reg rR) (.lit T))            -- inMark
  , .scalar (.binop 9 .sub (.lit 1) (.reg 8))            -- inAcc
    -- root phase selector, and the cursor limit it chooses
  , .scalar (.binop 130 .lt .idx (.lit c.rootSpan))      -- inRoot
  , .scalar (.binop 131 .mul (.reg 130) (.lit (K - c.bootCount)))
  , .scalar (.binop rLimit .sub (.lit K) (.reg 131))
  , .scalar (.binop 132 .mul (.reg 9) (.reg 130))        -- inAccRoot
  , .scalar (.binop 133 .sub (.reg 9) (.reg 132))        -- inAccMain
    -- window start: reset the prime cursor, branchlessly
  , .scalar (.binop 10 .eq (.reg rR) (.lit 0))           -- isStart
  , .scalar (.binop 11 .sub (.lit 1) (.reg 10))
  , .scalar (.binop 12 .urem (.reg rW) (.lit p1))
  , .scalar (.binop 13 .sub (.lit p1) (.reg 12))
  , .scalar (.binop 14 .urem (.reg 13) (.lit p1))        -- first cell of p1
  , .scalar (.binop rPi .mul (.reg 11) (.reg rPi))
  , .scalar (.binop 16 .mul (.reg 10) (.lit p1))
  , .scalar (.binop 17 .mul (.reg 11) (.reg rP))
  , .scalar (.binop rP .add (.reg 16) (.reg 17))
  , .scalar (.binop 18 .mul (.reg 10) (.reg 14))
  , .scalar (.binop 19 .mul (.reg 11) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 18) (.reg 19))
    -- mark step: target cell, or the sink when this iteration marks nothing
  , .scalar (.binop 20 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 21 .mul (.reg 20) (.reg 8))          -- inR
  , .scalar (.binop 22 .mul (.reg 21) (.reg rJ))
  , .scalar (.binop 23 .sub (.lit 1) (.reg 21))
  , .scalar (.binop 24 .mul (.reg 23) (.lit c.sinkProd))
  , .scalar (.binop 25 .add (.reg 22) (.reg 24))         -- prod index
  , .scalar (.binop 26 .add (.reg 25) (.lit L))          -- flag index
  , .load 27 25
  , .scalar (.binop 28 .eq (.reg 27) (.lit 0))
  , .scalar (.binop 29 .add (.reg 27) (.reg 28))
  , .scalar (.binop 30 .mul (.reg 29) (.reg rP))
  , .store 25 30
  , .load 31 26
  , .scalar (.binop 32 .mul (.reg rP) (.reg rP))
  , .scalar (.binop 33 .add (.reg 25) (.reg rW))         -- the integer marked
  , .scalar (.binop 34 .urem (.reg 33) (.reg 32))
  , .scalar (.binop 35 .eq (.reg 34) (.lit 0))
  , .scalar (.binop 36 .bxor (.reg 31) (.lit 1))
  , .scalar (.binop 37 .mul (.reg 35) (.lit 2))
  , .scalar (.binop 38 .bor (.reg 36) (.reg 37))
  , .store 26 38
    -- advance the prime cursor when the multiple ran past the window
  , .scalar (.binop 39 .sub (.lit 1) (.reg 21))
  , .scalar (.binop 40 .mul (.reg 8) (.reg 39))          -- advance
  , .scalar (.binop 41 .add (.reg rPi) (.reg 40))
  , .scalar (.binop 42 .gt (.reg 41) (.reg rLimit))
  , .scalar (.binop 43 .sub (.lit 1) (.reg 42))
  , .scalar (.binop 44 .mul (.reg 43) (.reg 41))
  , .scalar (.binop 45 .mul (.reg 42) (.reg rLimit))
  , .scalar (.binop rPi .add (.reg 44) (.reg 45))
  , .scalar (.binop 46 .add (.reg rPi) (.lit c.primeBase))
  , .load 47 46
  , .scalar (.binop 48 .sub (.lit 1) (.reg 40))
  , .scalar (.binop 49 .add (.reg rJ) (.reg rP))         -- next multiple, old p
  , .scalar (.binop 50 .mul (.reg 40) (.reg 47))
  , .scalar (.binop 51 .mul (.reg 48) (.reg rP))
  , .scalar (.binop rP .add (.reg 50) (.reg 51))         -- new p
  , .scalar (.binop 52 .urem (.reg rW) (.reg rP))
  , .scalar (.binop 53 .sub (.reg rP) (.reg 52))
  , .scalar (.binop 54 .urem (.reg 53) (.reg rP))        -- first cell of new p
  , .scalar (.binop 55 .eq (.reg rPi) (.reg rLimit))     -- table exhausted
  , .scalar (.binop 56 .sub (.lit 1) (.reg 55))
  , .scalar (.binop 57 .mul (.reg 55) (.lit (L + 1)))
  , .scalar (.binop 58 .mul (.reg 56) (.reg 54))
  , .scalar (.binop 59 .add (.reg 57) (.reg 58))
  , .scalar (.binop 60 .mul (.reg 40) (.reg 59))
  , .scalar (.binop 61 .mul (.reg 48) (.reg 49))
  , .scalar (.binop rJ .add (.reg 60) (.reg 61))
    -- accumulation phase: decode μ(n) for n = w + i
  , .scalar (.binop 62 .sub (.reg rR) (.lit T))
  , .scalar (.binop 63 .mul (.reg 9) (.reg 62))          -- i
  , .scalar (.binop 64 .add (.reg 63) (.lit L))
  , .scalar (.binop 65 .add (.reg 63) (.reg rW))         -- n
  , .load 66 63
  , .load 69 64
  , .scalar (.binop 67 .eq (.reg 66) (.lit 0))
  , .scalar (.binop 68 .add (.reg 66) (.reg 67))         -- prod, 0 meaning 1
  , .scalar (.binop 70 .lshr (.reg 69) (.lit 1))
  , .scalar (.binop 71 .band (.reg 70) (.lit 1))         -- p² ∣ n
  , .scalar (.binop 72 .band (.reg 69) (.lit 1))         -- parity so far
  , .scalar (.binop 73 .ne (.reg 68) (.reg 65))          -- one large prime left
  , .scalar (.binop 74 .bxor (.reg 72) (.reg 73))
  , .scalar (.binop 75 .sub (.lit 1) (.reg 71))          -- squarefree
  , .scalar (.binop 76 .sub (.lit 1) (.reg 74))
  , .scalar (.binop 77 .mul (.reg 75) (.reg 76))
  , .scalar (.binop 78 .mul (.reg 75) (.reg 74))
  , .scalar (.binop 79 .mul (.reg 133) (.reg 77))        -- μ = +1
  , .scalar (.binop 80 .mul (.reg 133) (.reg 78))        -- μ = −1
  , .scalar (.binop 81 .mul (.reg 133) (.reg 75))        -- |μ|
    -- zero the two cells just read, so the next window starts clean
  , .scalar (.binop 82 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 83 .mul (.reg 82) (.lit c.sinkProd))
  , .scalar (.binop 84 .add (.reg 63) (.reg 83))
  , .scalar (.binop 85 .add (.reg 84) (.lit L))
  , .store 84 rZero
  , .store 85 rZero
    -- root phase: append n to the prime table when it is an uncrossed cell
    -- with 2 ≤ n ≤ ⌊√hi⌋, i.e. exactly a prime above every bootstrap prime
  , .scalar (.binop 134 .sub (.reg 65) (.lit 2))
  , .scalar (.binop 135 .lt (.reg 134) (.lit (c.rootCap - 1)))
  , .scalar (.binop 136 .mul (.reg 135) (.reg 67))
  , .scalar (.binop 137 .mul (.reg 136) (.reg 132))      -- collect
  , .scalar (.binop 138 .mul (.reg 137) (.reg rWrite))
  , .scalar (.binop 139 .sub (.lit 1) (.reg 137))
  , .scalar (.binop 140 .mul (.reg 139) (.lit c.primeSink))
  , .scalar (.binop 141 .add (.reg 138) (.reg 140))
  , .store 141 65
  , .scalar (.binop rWrite .add (.reg rWrite) (.reg 137))
    -- advance the window position, and the window base at the wrap; the
    -- transition iteration additionally retargets the walk from the root
    -- sweep `[1, rootLen]` to `[lo, hi]`
  , .scalar (.binop 86 .add (.reg rR) (.lit 1))
  , .scalar (.binop 87 .eq (.reg 86) (.lit P))
  , .scalar (.binop 88 .sub (.lit 1) (.reg 87))
  , .scalar (.binop rR .mul (.reg 88) (.reg 86))
  , .scalar (.binop 89 .mul (.reg 87) (.lit L))
  , .scalar (.binop 142 .eq .idx (.lit (c.rootSpan - 1)))
  , .scalar (.binop 143 .mul (.reg 142) (.lit c.wDelta))
  , .scalar (.binop 144 .add (.reg 89) (.reg 143))
  , .scalar (.binop rW .add (.reg rW) (.reg 144))
  ]

/-- Write the bootstrap prime table and the table-end guard, open the walk at
`1`, and point the collection cursor just past the bootstrap primes. -/
def Cfg.coreInit (c : Cfg) : List AInstr :=
  (c.bootTable.zipIdx.flatMap fun (v, t) =>
    [ AInstr.scalar (.mov 90 (.lit (c.primeBase + t)))
    , AInstr.scalar (.mov 91 (.lit v))
    , AInstr.store 90 91 ]) ++
  [ .scalar (.mov 90 (.lit (c.primeBase + c.tableLen)))
  , .scalar (.mov 91 (.lit c.sentinel))
  , .store 90 91
  , .scalar (.mov rW (.lit 1))
  , .scalar (.mov rWrite (.lit (c.primeBase + c.bootCount))) ]

/-! ## Residue: Mertens and the squarefree count

`M(n)` biased by `2⁴⁰` (it never leaves `±0.6·10⁸` on any range this can
reach), `Q(n)` plain, and `G(n) = Q(n)·2³⁶ − c·n` biased by `2⁶²`, all three
maintained by a single add per integer.  The running extrema of `M` and `G`
are what the epilogue compares.

`k = 36` is the fixed-point scale for `c = 6/π²`.  The dropped fraction costs
`n·2⁻³⁶`, which at `n = 10¹⁶` is `1.5·10⁵` against a `b√n = 7.6·10⁶` budget —
2% of the slack — while keeping `|G| < 2⁶²` so the accumulator is one word.
-/

def cdemScale : Nat := 36

def mertensBias : Nat := 2 ^ 40
def gBias : Nat := 2 ^ 62

def rM : Nat := 100
def rMmax : Nat := 103
def rMmin : Nat := 108
def rQ : Nat := 112
def rG : Nat := 116
def rGmax : Nat := 118
def rGmin : Nat := 123

/-- `c = ⌊(6/π²)·2^cdemScale⌋`, computed once at emit time. -/
def cdemC : Nat := sixOverPiSqScaled cdemScale

def mertensResidue : List AInstr :=
  [ .scalar (.binop 101 .add (.reg rM) (.reg 79))
  , .scalar (.binop rM .sub (.reg 101) (.reg 80))
    -- running maximum of M
  , .scalar (.binop 102 .gt (.reg rM) (.reg rMmax))
  , .scalar (.binop 104 .sub (.lit 1) (.reg 102))
  , .scalar (.binop 105 .mul (.reg 102) (.reg rM))
  , .scalar (.binop 106 .mul (.reg 104) (.reg rMmax))
  , .scalar (.binop rMmax .add (.reg 105) (.reg 106))
    -- running minimum of M
  , .scalar (.binop 107 .lt (.reg rM) (.reg rMmin))
  , .scalar (.binop 109 .sub (.lit 1) (.reg 107))
  , .scalar (.binop 110 .mul (.reg 107) (.reg rM))
  , .scalar (.binop 111 .mul (.reg 109) (.reg rMmin))
  , .scalar (.binop rMmin .add (.reg 110) (.reg 111))
    -- Q, and G = Q·2^k − c·n
  , .scalar (.binop rQ .add (.reg rQ) (.reg 81))
  , .scalar (.binop 113 .shl (.reg 81) (.lit cdemScale))
  , .scalar (.binop 114 .mul (.reg 133) (.lit cdemC))
  , .scalar (.binop 115 .add (.reg rG) (.reg 113))
  , .scalar (.binop rG .sub (.reg 115) (.reg 114))
    -- running extrema of G
  , .scalar (.binop 117 .gt (.reg rG) (.reg rGmax))
  , .scalar (.binop 119 .sub (.lit 1) (.reg 117))
  , .scalar (.binop 120 .mul (.reg 117) (.reg rG))
  , .scalar (.binop 121 .mul (.reg 119) (.reg rGmax))
  , .scalar (.binop rGmax .add (.reg 120) (.reg 121))
  , .scalar (.binop 122 .lt (.reg rG) (.reg rGmin))
  , .scalar (.binop 124 .sub (.lit 1) (.reg 122))
  , .scalar (.binop 125 .mul (.reg 122) (.reg rG))
  , .scalar (.binop 126 .mul (.reg 124) (.reg rGmin))
  , .scalar (.binop rGmin .add (.reg 125) (.reg 126))
  ]

/-! ## Residue: Mertens and squarefree, tested per integer

The residue above keeps four running extrema and leaves the comparison to the
epilogue.  One comparison per artifact means one threshold per artifact, so
the threshold has to be the majorant at the window's *worst* endpoint, and a
window `[lo, hi]` therefore tests a family with an increasing majorant
`√(hi/lo) − 1` more strictly than the family states.  Windows must then be
geometric — 1 684 of them at ratio 1.02 to cover `[33, 10¹⁶]` — and a family
whose constant is nearly tight can fail a test it should pass.

The weakening is removable, and cheaply.  `⌊√n⌋` increases by at most one per
integer, so it is a register and three instructions; every majorant here is
`α·√n` for a rational `α`, so `⌊α·⌊√n⌋⌋` — sound, since `⌊√n⌋ ≤ √n` and each
`α` is rounded down to a dyadic — is one multiply and one shift.  Testing all
four clauses per integer then makes the *running extrema unnecessary*: this
residue is 31 instructions against the 27 of the extremum version, a 1%
body-size increase, and it removes the schedule loss entirely.

What it costs instead is that the artifact needs the true `M(lo−1)` as its
carry-in, so a chain of these is serial where a chain of the extremum version
is not (there, every window can run with a zero carry-in and the prefix sums
are applied afterwards).  Both are provided; which one is right depends on
whether the run is one core or a thousand.

Range of validity of the word arithmetic: `⌊b·2³⁶⌋·⌊√n⌋ < 2⁶⁴` needs
`n < 1.2·10¹⁹`, and `⌊0.571·√n⌋ < 2⁴⁰` — the Mertens bias — needs
`n < 3.7·10²⁴`.  Both hold with room to spare at `10¹⁶`; the first is the
binding one and it is where the fixed-point scale `cdemScale = 36` would have
to drop if the range ever grew past `10¹⁹`.
-/

def rS : Nat := 146      -- ⌊√n⌋
def rSq : Nat := 147     -- (rS + 1)², the next square
def rViol : Nat := 148   -- running count of failed per-integer tests

/-- `⌊0.571·2³²⌋` — Hurst's constant as a dyadic rational, rounded **down**,
so that `(hurstA·s) >>> 32 ≤ 0.571·s ≤ 0.571·√n`. -/
def hurstA : Nat := 571 * 2 ^ 32 / 1000

/-- `⌊b·2^cdemScale⌋` for `b = bNum/bDen`, rounded **down**: it multiplies
`⌊√n⌋` to give a threshold at or below `b·2^k·√n`, which is the safe side for
both CDEM clauses. -/
def cdemB (bNum bDen : Nat) : Nat := bNum * 2 ^ cdemScale / bDen

/-- Mertens and squarefree with the four clauses tested at every integer.
Register `65` holds `n`, `133` gates the main accumulation phase; the count
of failed tests accumulates in `rViol`, which the epilogue moves to the
output. -/
def mertensLiveResidue (bNum bDen : Nat) : List AInstr :=
  [ -- M, Q and G = Q·2^k − c·n, exactly as above
    .scalar (.binop 101 .add (.reg rM) (.reg 79))
  , .scalar (.binop rM .sub (.reg 101) (.reg 80))
  , .scalar (.binop rQ .add (.reg rQ) (.reg 81))
  , .scalar (.binop 113 .shl (.reg 81) (.lit cdemScale))
  , .scalar (.binop 114 .mul (.reg 133) (.lit cdemC))
  , .scalar (.binop 115 .add (.reg rG) (.reg 113))
  , .scalar (.binop rG .sub (.reg 115) (.reg 114))
    -- s = ⌊√n⌋: at most one increment per integer, and then the next square
    -- moves by 2s+1
  , .scalar (.binop 149 .ge (.reg 65) (.reg rSq))
  , .scalar (.binop 150 .mul (.reg 149) (.reg 133))
  , .scalar (.binop rS .add (.reg rS) (.reg 150))
  , .scalar (.binop 151 .shl (.reg rS) (.lit 1))
  , .scalar (.binop 152 .add (.reg 151) (.lit 1))
  , .scalar (.binop 153 .mul (.reg 150) (.reg 152))
  , .scalar (.binop rSq .add (.reg rSq) (.reg 153))
    -- Hurst: |M(n)| ≤ 0.571·√n
  , .scalar (.binop 154 .mul (.reg rS) (.lit hurstA))
  , .scalar (.binop 155 .lshr (.reg 154) (.lit 32))
  , .scalar (.binop 156 .add (.lit mertensBias) (.reg 155))
  , .scalar (.binop 157 .sub (.lit mertensBias) (.reg 155))
  , .scalar (.binop 158 .gt (.reg rM) (.reg 156))
  , .scalar (.binop 159 .lt (.reg rM) (.reg 157))
    -- CDEM clause 1, `G ≤ b·2^k·√n`, and clause 2,
    -- `G ≥ c + n + 1 − b·2^k·√n`
  , .scalar (.binop 160 .mul (.reg rS) (.lit (cdemB bNum bDen)))
  , .scalar (.binop 161 .add (.lit gBias) (.reg 160))
  , .scalar (.binop 162 .add (.lit (gBias + cdemC + 1)) (.reg 65))
  , .scalar (.binop 163 .sub (.reg 162) (.reg 160))
  , .scalar (.binop 164 .gt (.reg rG) (.reg 161))
  , .scalar (.binop 165 .lt (.reg rG) (.reg 163))
    -- one counter, gated to the main accumulation phase
  , .scalar (.binop 166 .add (.reg 158) (.reg 159))
  , .scalar (.binop 167 .add (.reg 164) (.reg 165))
  , .scalar (.binop 168 .add (.reg 166) (.reg 167))
  , .scalar (.binop 169 .mul (.reg 168) (.reg 133))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 169))
  ]

/-! ## Residue: the fixed-point `Σ μ(m)/m`

`T(n) = Σ_{m≤n} μ(m)·round(2⁶²/m)`, biased by `2⁶³`.  Round-to-nearest keeps
the accumulated truncation to `n/2` ulps rather than `n`; the epilogue's
threshold subtracts that budget, so the comparison is a sound bound on the
real `Σ μ(m)/m` and not merely on its fixed-point image.
-/

def tBias : Nat := 2 ^ 63

/-- The fixed-point unit of the `Σ μ(m)/m` accumulator.  `2⁶²`, not `2⁶³`:
`|Σ_{m≤n} μ(m)/m| ≤ 1` with equality at `n = 1`, so at scale `2⁶³` the very
first term would sit exactly on the sign boundary and the unsigned running
extrema would be meaningless.  At `2⁶²` the accumulator is a signed value of
magnitude `< 2⁶²` for every `n ≥ 1`, and the biased word orders correctly. -/
def mobScale : Nat := 2 ^ 62

def rT : Nat := 100
def rTmax : Nat := 102
def rTmin : Nat := 107

def mobiusOverNResidue : List AInstr :=
  [ -- w = round(2⁶² / n); n ≥ 1 always, so the division is defined
    .scalar (.binop 101 .udiv (.lit mobScale) (.reg 65))
  , .scalar (.binop 104 .urem (.lit mobScale) (.reg 65))
  , .scalar (.binop 105 .add (.reg 104) (.reg 104))
  , .scalar (.binop 106 .ge (.reg 105) (.reg 65))
  , .scalar (.binop 109 .add (.reg 101) (.reg 106))      -- w = round(2⁶²/n)
  , .scalar (.binop 110 .mul (.reg 79) (.reg 109))
  , .scalar (.binop 111 .mul (.reg 80) (.reg 109))
  , .scalar (.binop 112 .sub (.reg 110) (.reg 111))      -- two's complement δ
  , .scalar (.binop rT .add (.reg rT) (.reg 112))
    -- running extrema
  , .scalar (.binop 113 .gt (.reg rT) (.reg rTmax))
  , .scalar (.binop 114 .sub (.lit 1) (.reg 113))
  , .scalar (.binop 115 .mul (.reg 113) (.reg rT))
  , .scalar (.binop 116 .mul (.reg 114) (.reg rTmax))
  , .scalar (.binop rTmax .add (.reg 115) (.reg 116))
  , .scalar (.binop 117 .lt (.reg rT) (.reg rTmin))
  , .scalar (.binop 118 .sub (.lit 1) (.reg 117))
  , .scalar (.binop 119 .mul (.reg 117) (.reg rT))
  , .scalar (.binop 120 .mul (.reg 118) (.reg rTmin))
  , .scalar (.binop rTmin .add (.reg 119) (.reg 120))
  ]

/-! ## Residue: `Σ μ(m)/m` tested per integer, on a two-limb accumulator

`mobiusOverNResidue` above has the same two weaknesses `mertensResidue` has,
and one more that is peculiar to it.

* **Window granularity.**  One comparison per artifact means one threshold per
  artifact, evaluated at the window's worst point.  For an *antitone* majorant
  like `1/(2√n)` the worst point is the window's right end, so a chain can only
  stop on a window boundary — and a boundary far enough below the true limit
  that the whole window survives the right end's threshold.
* **The rounding budget.**  `round(2⁶²/m)` costs half an ulp per term, so the
  threshold subtracts `⌈n/2⌉`; at `n = 7.7·10⁹` that budget is `1.5·10⁻⁴` of
  the threshold itself, which is enough to lose an integer where the family is
  nearly tight.
* **No `√` in the loop.**  Removing the first weakness the way
  `mertensLiveResidue` does is not available here: `⌊√n⌋` rises by at most one
  per integer and is therefore a register, but the threshold wants
  `2⁶¹/√(n+1)`, a *reciprocal* square root, which is not.

The third point is what this residue is about, and the fix is to divide rather
than to multiply.  With `c = ⌈√(n+1)⌉ ≥ √(n+1)`, maintained by the same increment
trick as `⌊√n⌋` (it rises exactly when `n ≥ c²`, and then `c²` rises by
`2c − 1`), the test

  `|V| + budget + 1 ≤ ⌊2⁶¹/c⌋`

is one `udiv` per integer and implies `|Σ_{m≤n} μ(m)/m| ≤ 1/(2√(n+1))`,
because `⌊2⁶¹/c⌋ ≤ 2⁶¹/c ≤ 2⁶¹/√(n+1)`.  Nothing here can overflow: every
quantity is below `2⁶³`.

The second point is fixed by carrying the accumulator at scale `2^(63+k)` in
**two limbs** — the shape `Verified/AddWide.lean` proves — and shifting it
back down to scale `2⁶²` for the comparison.  The accumulated round-to-nearest
error is `n/2` ulps at scale `2^(63+k)`, i.e. `n/2^(k+2)` ulps at scale `2⁶²`,
and the shift itself costs one more; so the budget is `⌈n/2^(k+2)⌉ + 1` rather
than `⌈n/2⌉`.  At `k = 15` — scale `2⁷⁸` — that is `65 536×` smaller: at
`n = 7.7·10⁹` it drops from `1.5·10⁻⁴` of the threshold to `2.2·10⁻⁹`.

Exactly: writing `A = Σ_{m≤n} μ(m)·round(2^(63+k)/m)` and `V = ⌊A/2^(k+1)⌋`,

  `|2⁶²·Σ μ(m)/m| ≤ |V| + 1 + n/2^(k+2)`,

the `1` being the shift's truncation and `n/2^(k+2)` the rescaled rounding.

The two-limb weight `round(2^(63+k)/m)` is built without a 128 ÷ 64 division,
which the fragment does not have: from `q₁ = ⌊2⁶³/m⌋` and `r₁ = 2⁶³ mod m`,

  `2^(63+k)/m = 2^k·q₁ + (2^k·r₁)/m`,

and `2^k·r₁ < 2^k·m` stays inside a word whenever `m < 2^(64−k)`.  So two
64-bit divisions, a shift, and a carry.

**Range of validity**, all of it needed and all of it met at `7.7·10⁹`:
`hi < 2^(64−k)` for the weight (`2⁴⁹` at `k = 15`), and `1 ≤ k ≤ 15` so that
no shift count reaches 64 — the emitted C would be undefined there.  The
accumulator itself is safe for every `n < 2^79`, since `|Σ μ(m)/m| ≤ 1` puts
`U = 2^(64+k) + A` inside `(0, 2^(65+k))`.

The price, as with `mertensLiveResidue`, is that the carry-in must be the true
`A(lo−1)`, so a chain of these is serial.
-/

/-- Extra bits the `Σ μ(m)/m` accumulator carries above `2⁶³`: the fixed-point
scale is `2^(63+k)` and the comparison scale is `2⁶²`.  Must satisfy
`1 ≤ k ≤ 15`; `15` is the production value and gives scale `2⁷⁸`. -/
def mobWideBits : Nat := 15

def rTLo : Nat := 100     -- low limb of U = 2^(64+k) + A
def rTHi : Nat := 101     -- high limb
def rCeil : Nat := 102    -- ⌈√(n+1)⌉
def rCeilSq : Nat := 103  -- (⌈√(n+1)⌉)²
def rMViol : Nat := 104   -- running count of failed per-integer tests

/-- `Σ μ(m)/m` against `1/(2√(n+1))`, tested at **every** integer, with the
accumulator at scale `2^(63+k)` in two limbs.  Register `65` holds `n`,
`79`/`80` the two `μ` indicators and `133` the main-accumulation gate; the
count of failed tests accumulates in `rMViol`. -/
def mobiusLiveResidue (k : Nat) : List AInstr :=
  [ -- (A) w = round(2^(63+k)/n), two limbs, from one 2⁶³ division
    .scalar (.binop 150 .udiv (.lit (2 ^ 63)) (.reg 65))     -- q₁
  , .scalar (.binop 151 .urem (.lit (2 ^ 63)) (.reg 65))     -- r₁
  , .scalar (.binop 152 .shl (.reg 151) (.lit k))            -- 2^k·r₁
  , .scalar (.binop 153 .udiv (.reg 152) (.reg 65))          -- q₂
  , .scalar (.binop 154 .urem (.reg 152) (.reg 65))          -- r₂
  , .scalar (.binop 155 .add (.reg 154) (.reg 154))
  , .scalar (.binop 156 .ge (.reg 155) (.reg 65))            -- round up?
  , .scalar (.binop 157 .add (.reg 153) (.reg 156))
  , .scalar (.binop 158 .shl (.reg 150) (.lit k))            -- low of 2^k·q₁
  , .scalar (.binop 159 .lshr (.reg 150) (.lit (64 - k)))    -- high of 2^k·q₁
  , .scalar (.binop 160 .add (.reg 158) (.reg 157))          -- wLo
  , .scalar (.binop 161 .lt (.reg 160) (.reg 157))           -- carry out
  , .scalar (.binop 162 .add (.reg 159) (.reg 161))          -- wHi
    -- (B) U += μ(n)·w, as a 128-bit add then a 128-bit subtract; at most one
    -- of the two is nonzero because `μ = +1` and `μ = −1` are exclusive
  , .scalar (.binop 150 .mul (.reg 79) (.reg 160))
  , .scalar (.binop 151 .mul (.reg 79) (.reg 162))
  , .scalar (.binop 152 .mul (.reg 80) (.reg 160))
  , .scalar (.binop 153 .mul (.reg 80) (.reg 162))
  , .scalar (.binop 154 .add (.reg rTLo) (.reg 150))
  , .scalar (.binop 155 .lt (.reg 154) (.reg 150))
  , .scalar (.binop 156 .add (.reg rTHi) (.reg 151))
  , .scalar (.binop 157 .add (.reg 156) (.reg 155))
  , .scalar (.binop 158 .lt (.reg 154) (.reg 152))           -- borrow
  , .scalar (.binop rTLo .sub (.reg 154) (.reg 152))
  , .scalar (.binop 159 .sub (.reg 157) (.reg 153))
  , .scalar (.binop rTHi .sub (.reg 159) (.reg 158))
    -- (C) V, biased by 2⁶³: U ≫ (k+1), which fits one word because U < 2^(65+k)
  , .scalar (.binop 150 .lshr (.reg rTLo) (.lit (k + 1)))
  , .scalar (.binop 151 .shl (.reg rTHi) (.lit (63 - k)))
  , .scalar (.binop 152 .bor (.reg 150) (.reg 151))
    -- (D) |V|, branchlessly
  , .scalar (.binop 153 .ge (.reg 152) (.lit (2 ^ 63)))
  , .scalar (.binop 154 .sub (.reg 152) (.lit (2 ^ 63)))
  , .scalar (.binop 155 .sub (.lit (2 ^ 63)) (.reg 152))
  , .scalar (.binop 156 .sub (.lit 1) (.reg 153))
  , .scalar (.binop 157 .mul (.reg 153) (.reg 154))
  , .scalar (.binop 158 .mul (.reg 156) (.reg 155))
  , .scalar (.binop 159 .add (.reg 157) (.reg 158))          -- |V|
    -- (E) c = ⌈√(n+1)⌉: it rises exactly when n+1 > c², i.e. n ≥ c², and then
    -- c² rises by 2c−1.  `n+1` and not `n` because the reduced family's
    -- majorant is `1/(2√(n+1))`, which is the majorant of the *real*-variable
    -- statement at the right end of the interval `[n, n+1)` on which the sum
    -- is constant; `1/(2√(n+1)) ≤ 1/(2√n)`, so this tests the stronger form.
  , .scalar (.binop 160 .ge (.reg 65) (.reg rCeilSq))
  , .scalar (.binop 161 .mul (.reg 160) (.reg 133))
  , .scalar (.binop rCeil .add (.reg rCeil) (.reg 161))
  , .scalar (.binop 162 .add (.reg rCeil) (.reg rCeil))
  , .scalar (.binop 163 .sub (.reg 162) (.lit 1))
  , .scalar (.binop 164 .mul (.reg 161) (.reg 163))
  , .scalar (.binop rCeilSq .add (.reg rCeilSq) (.reg 164))
    -- (F) the test: |V| + ⌈n/2^(k+2)⌉ + 1 ≤ ⌊2⁶¹/c⌋
  , .scalar (.binop 165 .udiv (.lit (2 ^ 61)) (.reg rCeil))
  , .scalar (.binop 166 .add (.reg 65) (.lit (2 ^ (k + 2) - 1)))
  , .scalar (.binop 167 .lshr (.reg 166) (.lit (k + 2)))
  , .scalar (.binop 168 .add (.reg 159) (.reg 167))
  , .scalar (.binop 169 .add (.reg 168) (.lit 1))
  , .scalar (.binop 170 .gt (.reg 169) (.reg 165))
  , .scalar (.binop 171 .mul (.reg 170) (.reg 133))
  , .scalar (.binop rMViol .add (.reg rMViol) (.reg 171))
  ]

/-! ## Programs

A program is the core plus a residue, with an init block seeding the residue's
carry-in and an epilogue comparing the running extrema against integer
thresholds and storing the carry-out for the next artifact in a chain.
-/

/-- Seed a register with a literal. -/
def seed (reg value : Nat) : List AInstr := [.scalar (.mov reg (.lit value))]

/-- Store a register into a result cell, using `90` as the address scratch. -/
def storeResult (c : Cfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .store 90 reg ]

/-- A violation test `reg > bound`, accumulated into `92`. -/
def gtTest (reg bound : Nat) : List AInstr :=
  [ .scalar (.binop 91 .gt (.reg reg) (.lit bound))
  , .scalar (.binop 92 .add (.reg 92) (.reg 91)) ]

/-- A violation test `reg < bound`, accumulated into `92`. -/
def ltTest (reg bound : Nat) : List AInstr :=
  [ .scalar (.binop 91 .lt (.reg reg) (.lit bound))
  , .scalar (.binop 92 .add (.reg 92) (.reg 91)) ]

/-- The output register: the number of failed epilogue tests. -/
def outputReg : Nat := 92

def Cfg.program (c : Cfg) (residue init epilogue : List AInstr) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * (c.rootCount + c.segCount)
  init := c.coreInit ++ init
  body := c.coreBody ++ residue
  epilogue := epilogue
  output := outputReg
}

/-! ### The Mertens / squarefree program

Thresholds, all exact integers:

* Hurst, `|M(n)| ≤ 0.571√n` on `[33, 10¹⁶]`: `⌊√(⌊326041·lo/10⁶⌋)⌋ ≤ 0.571√lo`
  and the majorant is increasing, so the window's left end is the worst point.
* CDEM clause 1, `Q(n) − (6/π²)n ≤ b√n`: `G(n)/2^k ≥ Q(n) − (6/π²)n`, so
  `G ≤ ⌊b·2^k·√lo⌋` suffices.
* CDEM clause 2, `(6/π²)(n+1) − Q(n) ≤ b√n`: bounded by
  `(−G + c + n + 1)/2^k`, worst at `n = hi`, so `G ≥ c + hi + 1 − ⌊b·2^k√lo⌋`.

`b` arrives as a rational `bNum/bDen` (`755/10⁴` and `285/10⁴` are the two
production values).
-/

/-- `⌊(bNum/bDen)·2^cdemScale·√lo⌋`, by an exact cross-multiplied `Nat.sqrt`. -/
def cdemThreshold (bNum bDen lo : Nat) : Nat :=
  Nat.sqrt (bNum * bNum * 2 ^ (2 * cdemScale) * lo / (bDen * bDen))

/-- `⌊0.571·√lo⌋`, exact. -/
def hurstThreshold (lo : Nat) : Nat :=
  Nat.sqrt (326041 * lo / 1000000)

structure MertensSeed where
  /-- `M(lo − 1)`, biased by `2⁴⁰`. -/
  m : Nat
  /-- `Q(lo − 1)`. -/
  q : Nat
  /-- `G(lo − 1)`, biased by `2⁶²`. -/
  g : Nat
  deriving Repr

def mertensInit (s : MertensSeed) : List AInstr :=
  seed rM s.m ++ seed rMmax s.m ++ seed rMmin s.m ++
  seed rQ s.q ++
  seed rG s.g ++ seed rGmax s.g ++ seed rGmin s.g

def mertensEpilogue (c : Cfg) (bNum bDen : Nat) : List AInstr :=
  let thrM := hurstThreshold c.lo
  let thrG := cdemThreshold bNum bDen c.lo
  let lowG := cdemC + c.hi + 1
  gtTest rMmax (mertensBias + thrM) ++
  ltTest rMmin (mertensBias - thrM) ++
  gtTest rGmax (gBias + thrG) ++
  ltTest rGmin (gBias + lowG - thrG) ++
  storeResult c 0 rM ++ storeResult c 1 rQ ++ storeResult c 2 rG ++
  storeResult c 3 rMmax ++ storeResult c 4 rMmin ++
  storeResult c 5 rGmax ++ storeResult c 6 rGmin

/-- The Mertens/squarefree residue program: `mertensM_hurst_sqrt` and the CDEM
reproducible squarefree head, on one sieve pass. -/
def mertensProgram (c : Cfg) (s : MertensSeed) (bNum bDen : Nat) : AProgram :=
  c.program mertensResidue (mertensInit s) (mertensEpilogue c bNum bDen)

/-! ### The per-integer Mertens / squarefree program

Same sieve, same accumulators, but every clause is tested at every integer
against `⌊α·⌊√n⌋⌋`, so no window schedule and no `√(hi/lo) − 1` loss.  The
seeds are the same three carry-ins; `⌊√(lo−1)⌋` and its next square are
computed at emit time from `lo`, so nothing extra is chained. -/

/-- `s0` is `⌊√(lo−1)⌋`, an emit-time `Nat.sqrt`; it is a parameter and not a
call here because `Nat.sqrt` is well-founded recursion, which the kernel
checks below cannot unfold. -/
def mertensLiveInit (s0 : Nat) (s : MertensSeed) : List AInstr :=
  seed rM s.m ++ seed rQ s.q ++ seed rG s.g ++
  seed rS s0 ++ seed rSq ((s0 + 1) * (s0 + 1))

/-- The output is the running count of failed per-integer tests; the three
carry-outs and the final `⌊√hi⌋` go to the result cells. -/
def mertensLiveEpilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov outputReg (.reg rViol)) ] ++
  storeResult c 0 rM ++ storeResult c 1 rQ ++ storeResult c 2 rG ++
  storeResult c 3 rS

def mertensLiveProgram (c : Cfg) (s0 : Nat) (s : MertensSeed)
    (bNum bDen : Nat) : AProgram :=
  c.program (mertensLiveResidue bNum bDen) (mertensLiveInit s0 s)
    (mertensLiveEpilogue c)

/-! ### The `Σ μ(m)/m` program

The family these two modes certify is the *cell* family — the one the
real-variable statement `|Σ_{m≤x} μ(m)/m| ≤ g(x)` on `[a, b)` reduces to.  On
the unit cell `[n, n+1)` the step `Σ_{m≤x} μ(m)/m` is constant while the
antitone `g` is falling, so the binding value is `g(n+1)`, not `g(n)`:

  `|Σ_{m≤n} μ(m)/m| ≤ g(n+1)`,   `g = √(2/·)` or `1/(2√·)`.

`g` is antitone, so over a window `[lo, hi]` the worst cell is the last one and
one threshold per artifact suffices — **provided it is evaluated at `hi + 1`.**
Evaluating it at `hi` gives a threshold larger by a relative `1/(2·hi)`, which
is the direction that lets a false claim pass: it is a test *weaker* than the
family it is supposed to certify, and it is exactly the `x <` versus `x ≤`
off-by-one that made `residual_platt_stronger_range`'s closed-interval form
false at its own endpoint.  The per-integer residue `mobiusLiveResidue` has
always tested the `⌈√(n+1)⌉` form; these two now agree with it.

The threshold is therefore `⌊2⁶²·g(hi+1)⌋ − ⌈hi/2⌉`, the subtraction being the
accumulated round-to-nearest budget, which makes the integer test a bound on
the real sum and not merely on its fixed-point image.

The `N + 1` also removes the `N = 0` corner, where `2^e / N` was `0` in `Nat`
and the threshold silently collapsed to `0`.
-/

/-- `⌊2⁶²·√(2/(N+1))⌋ − ⌈N/2⌉` — Platt's (2.11) majorant at the worst point of
the last cell of `[lo, N]`.  The subtracted `⌈N/2⌉` is the accumulated
round-to-nearest budget, so passing this test bounds the *real* `Σ μ(m)/m`,
not merely its fixed-point image.

Both roundings go the conservative way: `Nat.sqrt ∘ (· / ·)` is a double floor,
so `raw ≤ 2⁶²·√(2/(N+1))`, and the budget is `⌈N/2⌉ ≥ n/2` for every `n ≤ N`. -/
def platt211Threshold (N : Nat) : Nat :=
  let raw := Nat.sqrt (2 ^ 125 / (N + 1))
  let budget := (N + 1) / 2
  if raw ≤ budget then 0 else raw - budget

/-- `⌊2⁶²/(2√(N+1))⌋ − ⌈N/2⌉` — Platt's stronger rigorously-computed range,
again sampled at the worst point `N + 1` of the window's last cell. -/
def plattStrongerThreshold (N : Nat) : Nat :=
  let raw := Nat.sqrt (2 ^ 122 / (N + 1))
  let budget := (N + 1) / 2
  if raw ≤ budget then 0 else raw - budget

def mobiusInit (t : Nat) : List AInstr :=
  seed rT t ++ seed rTmax t ++ seed rTmin t

def mobiusEpilogue (c : Cfg) (thr : Nat) : List AInstr :=
  gtTest rTmax (tBias + thr) ++
  ltTest rTmin (tBias - thr) ++
  storeResult c 0 rT ++ storeResult c 1 rTmax ++ storeResult c 2 rTmin

/-- The `Σ μ(m)/m` residue program.  `thr` is `platt211Threshold c.hi` or
`plattStrongerThreshold c.hi`. -/
def mobiusProgram (c : Cfg) (t thr : Nat) : AProgram :=
  c.program mobiusOverNResidue (mobiusInit t) (mobiusEpilogue c thr)

/-! ### The per-integer `Σ μ(m)/m` program

No threshold literal at all: the majorant `1/(2√n)` is tested inside the loop
against `⌊2⁶¹/⌈√n⌉⌋`.  What the artifact carries instead is the carry-in — the
two limbs of `U(lo−1) = 2^(64+k) + A(lo−1)`, and the two registers `⌈√(lo−1)⌉`
and its square — and what it returns is the number of integers in `[lo, hi]`
at which the test failed.  All four carry-outs go to the result cells, so a
chain link is checkable against a manifest and not only against "zero
violations".
-/

/-- `⌈√n⌉`, at emit time.  A parameter of `mobiusLiveInit` and not a call
inside it, for the same reason `mertensLiveInit` takes `s0`: `Nat.sqrt` is
well-founded recursion and the kernel does not unfold it. -/
def ceilSqrt (n : Nat) : Nat :=
  let s := Nat.sqrt n
  if s * s = n then s else s + 1

/-- The four carry-ins of a per-integer `Σ μ(m)/m` link. -/
structure MobLiveSeed where
  /-- Low limb of `U(lo−1) = 2^(64+k) + Σ_{m<lo} μ(m)·round(2^(63+k)/m)`. -/
  tLo : Nat
  /-- High limb of the same. -/
  tHi : Nat
  /-- `max 1 ⌈√lo⌉` — the value `⌈√(n+1)⌉` takes at `n = lo − 1`, clamped to
  `1` so the in-loop `udiv` is defined. -/
  c : Nat
  /-- The square of the field above. -/
  cSq : Nat
  deriving Repr

/-- The seed a link starting at `lo` needs, given the previous link's two
accumulator limbs.  At `lo = 1` the accumulator is the bare bias `2^(64+k)`,
i.e. `tLo = 0`, `tHi = 2^k`. -/
def mobLiveSeed (lo tLo tHi : Nat) : MobLiveSeed :=
  let c := max 1 (ceilSqrt lo)
  { tLo := tLo, tHi := tHi, c := c, cSq := c * c }

def mobLiveSeedStart (k : Nat) : MobLiveSeed :=
  { tLo := 0, tHi := 2 ^ k, c := 1, cSq := 1 }

def mobiusLiveInit (s : MobLiveSeed) : List AInstr :=
  seed rTLo s.tLo ++ seed rTHi s.tHi ++ seed rCeil s.c ++ seed rCeilSq s.cSq ++
  seed rMViol 0

def mobiusLiveEpilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov outputReg (.reg rMViol)) ] ++
  storeResult c 0 rTLo ++ storeResult c 1 rTHi ++
  storeResult c 2 rCeil ++ storeResult c 3 rCeilSq

/-- The per-integer `Σ μ(m)/m` program at accumulator scale `2^(63+k)`.
Requires `1 ≤ k ≤ 15` and `c.hi < 2^(64−k)`. -/
def mobiusLiveProgram (c : Cfg) (k : Nat) (s : MobLiveSeed) : AProgram :=
  c.program (mobiusLiveResidue k) (mobiusLiveInit s) (mobiusLiveEpilogue c)

/-! ## Well-formedness, and the bridge instantiated

`AProgram.WF` is the only obligation `AProgram.evalCC_compile` carries.  It is
decided by a `Bool` mirror that reduces definitionally, so the proof is `rfl`
at every configuration — no case split over a hundred instructions.
-/

def operandWFB (r : Nat) : Operand → Bool
  | .reg i => decide (i < r)
  | _ => true

theorem operandWFB_correct {r : Nat} {o : Operand} (h : operandWFB r o = true) :
    o.WF r := by
  cases o with
  | reg i => exact of_decide_eq_true h
  | lit _ => trivial
  | idx => trivial

def instrWFB (r : Nat) : Instr → Bool
  | .mov d s => decide (d < r) && operandWFB r s
  | .binop d _ l rr => decide (d < r) && operandWFB r l && operandWFB r rr

theorem instrWFB_correct {r : Nat} {i : Instr} (h : instrWFB r i = true) :
    i.WF r := by
  cases i with
  | mov d s =>
      simp only [instrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, operandWFB_correct h.2⟩
  | binop d op l rr =>
      simp only [instrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1, operandWFB_correct h.1.2,
        operandWFB_correct h.2⟩

def ainstrWFB (r : Nat) : AInstr → Bool
  | .scalar i => instrWFB r i
  | .load d i => decide (d < r) && decide (i < r)
  | .store i s => decide (i < r) && decide (s < r)

theorem ainstrWFB_correct {r : Nat} {a : AInstr} (h : ainstrWFB r a = true) :
    a.WF r := by
  cases a with
  | scalar i => exact instrWFB_correct h
  | load d i =>
      simp only [ainstrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  | store i s =>
      simp only [ainstrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

theorem forall_wf_of_all {r : Nat} {l : List AInstr}
    (h : l.all (ainstrWFB r) = true) : ∀ a ∈ l, a.WF r := by
  intro a ha
  exact ainstrWFB_correct (List.all_eq_true.mp h a ha)

theorem all_append {r : Nat} {l₁ l₂ : List AInstr}
    (h₁ : l₁.all (ainstrWFB r) = true) (h₂ : l₂.all (ainstrWFB r) = true) :
    (l₁ ++ l₂).all (ainstrWFB r) = true := by
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h₁, h₂⟩

theorem coreInit_all (c : Cfg) : c.coreInit.all (ainstrWFB regCount) = true := by
  simp only [Cfg.coreInit, List.all_append, List.all_flatMap, Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr ?_, by rfl⟩
  intro x _
  rfl

theorem coreBody_all (c : Cfg) : c.coreBody.all (ainstrWFB regCount) = true := by
  rfl

theorem mertensResidue_all : mertensResidue.all (ainstrWFB regCount) = true := by
  rfl

theorem mobiusOverNResidue_all :
    mobiusOverNResidue.all (ainstrWFB regCount) = true := by
  rfl

theorem seed_all (reg value : Nat) (h : reg < regCount) :
    (seed reg value).all (ainstrWFB regCount) = true := by
  simp only [seed, regCount, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, Bool.and_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

theorem storeResult_all (c : Cfg) (slot reg : Nat) (h : reg < regCount) :
    (storeResult c slot reg).all (ainstrWFB regCount) = true := by
  simp only [storeResult, regCount, List.all_cons, List.all_nil, ainstrWFB,
    instrWFB, operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

theorem gtTest_all (reg bound : Nat) (h : reg < regCount) :
    (gtTest reg bound).all (ainstrWFB regCount) = true := by
  simp only [gtTest, regCount, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

theorem ltTest_all (reg bound : Nat) (h : reg < regCount) :
    (ltTest reg bound).all (ainstrWFB regCount) = true := by
  simp only [ltTest, regCount, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [regCount] at h
  omega

/-- **The bridge's side condition, once for every program this file builds.** -/
theorem segProgram_wf (c : Cfg) {residue init epilogue : List AInstr}
    (hr : residue.all (ainstrWFB regCount) = true)
    (hi : init.all (ainstrWFB regCount) = true)
    (he : epilogue.all (ainstrWFB regCount) = true) :
    (c.program residue init epilogue).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (all_append (coreInit_all c) hi),
   forall_wf_of_all (all_append (coreBody_all c) hr),
   forall_wf_of_all he⟩

theorem mertensInit_all (s : MertensSeed) :
    (mertensInit s).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (seed_all rM s.m (by decide)) (seed_all rMmax s.m (by decide)))
    (seed_all rMmin s.m (by decide))) (seed_all rQ s.q (by decide)))
    (seed_all rG s.g (by decide))) (seed_all rGmax s.g (by decide)))
    (seed_all rGmin s.g (by decide))

theorem mertensEpilogue_all (c : Cfg) (bNum bDen : Nat) :
    (mertensEpilogue c bNum bDen).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (all_append (all_append (all_append (all_append
      (gtTest_all rMmax _ (by decide)) (ltTest_all rMmin _ (by decide)))
      (gtTest_all rGmax _ (by decide))) (ltTest_all rGmin _ (by decide)))
      (storeResult_all c 0 rM (by decide)))
      (storeResult_all c 1 rQ (by decide)))
      (storeResult_all c 2 rG (by decide)))
      (storeResult_all c 3 rMmax (by decide)))
      (storeResult_all c 4 rMmin (by decide)))
      (storeResult_all c 5 rGmax (by decide)))
      (storeResult_all c 6 rGmin (by decide))

theorem mertensLiveResidue_all (bNum bDen : Nat) :
    (mertensLiveResidue bNum bDen).all (ainstrWFB regCount) = true := by
  rfl

theorem mertensLiveInit_all (s0 : Nat) (s : MertensSeed) :
    (mertensLiveInit s0 s).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append
    (seed_all rM s.m (by decide)) (seed_all rQ s.q (by decide)))
    (seed_all rG s.g (by decide)))
    (seed_all rS _ (by decide))) (seed_all rSq _ (by decide))

theorem mertensLiveEpilogue_all (c : Cfg) :
    (mertensLiveEpilogue c).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append
    (by rfl) (storeResult_all c 0 rM (by decide)))
    (storeResult_all c 1 rQ (by decide)))
    (storeResult_all c 2 rG (by decide)))
    (storeResult_all c 3 rS (by decide))

theorem mobiusInit_all (t : Nat) :
    (mobiusInit t).all (ainstrWFB regCount) = true :=
  all_append (all_append (seed_all rT t (by decide)) (seed_all rTmax t (by decide)))
    (seed_all rTmin t (by decide))

theorem mobiusEpilogue_all (c : Cfg) (thr : Nat) :
    (mobiusEpilogue c thr).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append
    (gtTest_all rTmax _ (by decide)) (ltTest_all rTmin _ (by decide)))
    (storeResult_all c 0 rT (by decide)))
    (storeResult_all c 1 rTmax (by decide)))
    (storeResult_all c 2 rTmin (by decide))

theorem mobiusLiveResidue_all (k : Nat) :
    (mobiusLiveResidue k).all (ainstrWFB regCount) = true := by
  rfl

theorem mobiusLiveInit_all (s : MobLiveSeed) :
    (mobiusLiveInit s).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append
    (seed_all rTLo s.tLo (by decide)) (seed_all rTHi s.tHi (by decide)))
    (seed_all rCeil s.c (by decide)))
    (seed_all rCeilSq s.cSq (by decide)))
    (seed_all rMViol 0 (by decide))

theorem mobiusLiveEpilogue_all (c : Cfg) :
    (mobiusLiveEpilogue c).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append
    (by rfl) (storeResult_all c 0 rTLo (by decide)))
    (storeResult_all c 1 rTHi (by decide)))
    (storeResult_all c 2 rCeil (by decide)))
    (storeResult_all c 3 rCeilSq (by decide))

theorem mertensProgram_wf (c : Cfg) (s : MertensSeed) (bNum bDen : Nat) :
    (mertensProgram c s bNum bDen).WF :=
  segProgram_wf c mertensResidue_all (mertensInit_all s)
    (mertensEpilogue_all c bNum bDen)

theorem mertensLiveProgram_wf (c : Cfg) (s0 : Nat) (s : MertensSeed)
    (bNum bDen : Nat) : (mertensLiveProgram c s0 s bNum bDen).WF :=
  segProgram_wf c (mertensLiveResidue_all bNum bDen) (mertensLiveInit_all s0 s)
    (mertensLiveEpilogue_all c)

theorem mobiusProgram_wf (c : Cfg) (t thr : Nat) :
    (mobiusProgram c t thr).WF :=
  segProgram_wf c mobiusOverNResidue_all (mobiusInit_all t)
    (mobiusEpilogue_all c thr)

theorem mobiusLiveProgram_wf (c : Cfg) (k : Nat) (s : MobLiveSeed) :
    (mobiusLiveProgram c k s).WF :=
  segProgram_wf c (mobiusLiveResidue_all k) (mobiusLiveInit_all s)
    (mobiusLiveEpilogue_all c)

/--
**The bridge, instantiated for the Mertens / squarefree residue.**  For any
array base at which the window fits, the compiled CCIR trace leaves the
program's denotation — the number of failed threshold tests — in the output
register.
-/
theorem mertensProgram_compiled (c : Cfg) (s : MertensSeed) (bNum bDen : Nat)
    (base : Int)
    (hBase : BaseOk (mertensProgram c s bNum bDen).arrayLen base)
    (n : Nat) (hDenote : (mertensProgram c s bNum bDen).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((mertensProgram c s bNum bDen).initialMCC base)
          (mertensProgram c s bNum bDen).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mertensProgram c s bNum bDen).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mertensProgram_wf c s bNum bDen) base hBase n hDenote

/-- **The bridge, instantiated for the per-integer Mertens / squarefree
residue.**  The denotation is the number of integers in `[lo, hi]` at which
one of the four clauses fails. -/
theorem mertensLiveProgram_compiled (c : Cfg) (s0 : Nat) (s : MertensSeed)
    (bNum bDen : Nat) (base : Int)
    (hBase : BaseOk (mertensLiveProgram c s0 s bNum bDen).arrayLen base)
    (n : Nat) (hDenote : (mertensLiveProgram c s0 s bNum bDen).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((mertensLiveProgram c s0 s bNum bDen).initialMCC base)
          (mertensLiveProgram c s0 s bNum bDen).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mertensLiveProgram c s0 s bNum bDen).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mertensLiveProgram_wf c s0 s bNum bDen) base hBase
    n hDenote

/-- **The bridge, instantiated for the `Σ μ(m)/m` residue.** -/
theorem mobiusProgram_compiled (c : Cfg) (t thr : Nat) (base : Int)
    (hBase : BaseOk (mobiusProgram c t thr).arrayLen base)
    (n : Nat) (hDenote : (mobiusProgram c t thr).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((mobiusProgram c t thr).initialMCC base)
          (mobiusProgram c t thr).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mobiusProgram c t thr).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mobiusProgram_wf c t thr) base hBase n hDenote

/-- **The bridge, instantiated for the per-integer `Σ μ(m)/m` residue.**  The
denotation is the number of integers in `[lo, hi]` at which
`|Σ_{m≤n} μ(m)/m| ≤ 1/(2√n)` failed the in-loop test. -/
theorem mobiusLiveProgram_compiled (c : Cfg) (k : Nat) (s : MobLiveSeed)
    (base : Int)
    (hBase : BaseOk (mobiusLiveProgram c k s).arrayLen base)
    (n : Nat) (hDenote : (mobiusLiveProgram c k s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((mobiusLiveProgram c k s).initialMCC base)
          (mobiusLiveProgram c k s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mobiusLiveProgram c k s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mobiusLiveProgram_wf c k s) base hBase n hDenote


/-! ## Kernel sanity checks

The bridge does not depend on any of this: it says the artifact computes
`denote`, whatever `denote` is.  These checks are the other half — evidence
that `denote` is the residue it is meant to be.  They evaluate the sieve in
the kernel at a tiny configuration and compare against a trial-division
reference, exactly as `ArrayMobius` does; the artifact repeats the comparison
against `bench/ref_seg.c` at `10⁸`, where `M(10⁸) = 1928` and
`Q(10⁸) = 60 792 694` are the published values.
-/

namespace Check

/-- Trial-division `μ`, encoded `0 ↦ μ = 0`, `1 ↦ μ = 1`, `2 ↦ μ = −1`. -/
def refMuCode (n : Nat) : Nat :=
  if n = 0 then 0 else
  let rec go (m d fuel : Nat) (par : Nat) : Nat :=
    match fuel with
    | 0 => if m = 1 then (if par = 0 then 1 else 2) else (if par = 0 then 2 else 1)
    | fuel + 1 =>
        if d * d > m then
          (if m = 1 then (if par = 0 then 1 else 2) else (if par = 0 then 2 else 1))
        else if m % d = 0 then
          let m' := m / d
          if m' % d = 0 then 0 else go m' (d + 1) fuel (1 - par)
        else go m (d + 1) fuel par
  go n 2 (n + 2) 0

def window (lo hi : Nat) : List Nat := (List.range (hi + 1)).drop lo

/-- `2⁴⁰ + M(hi) − M(lo−1)`, the biased Mertens accumulator. -/
def refM (lo hi : Nat) : Nat :=
  (window lo hi).foldl (fun acc n =>
    match refMuCode n with
    | 1 => acc + 1
    | 2 => acc - 1
    | _ => acc) mertensBias

/-- `Q(hi) − Q(lo−1)`. -/
def refQ (lo hi : Nat) : Nat :=
  (window lo hi).foldl (fun acc n =>
    if refMuCode n = 0 then acc else acc + 1) 0

/-- `2⁶³ + Σ μ(m)·round(2⁶²/m)`, mod `2⁶⁴`. -/
def refT (lo hi : Nat) : Nat :=
  (window lo hi).foldl (fun acc n =>
    let w := (mobScale + n / 2) / n
    match refMuCode n with
    | 1 => (acc + w) % Verified.Reflect.M
    | 2 => (acc + (Verified.Reflect.M - w)) % Verified.Reflect.M
    | _ => acc) tBias

/-- `Σ_{lo ≤ m ≤ hi} μ(m)·round(2^(63+k)/m)`, as a signed integer.  The
round-to-nearest is `⌊(2^(63+k) + m/2)/m⌋`, which is exactly what the
residue's two-step division computes: `2^(63+k) = 2^k·q₁·m + 2^k·r₁` and the
second division carries the same remainder. -/
def refWideA (k lo hi : Nat) : Int :=
  (window lo hi).foldl (fun acc n =>
    let w : Int := ((2 ^ (63 + k) + n / 2) / n : Nat)
    match refMuCode n with
    | 1 => acc + w
    | 2 => acc - w
    | _ => acc) 0

/-- `U = 2^(64+k) + A`, split into the two limbs the residue keeps. -/
def refWideLimbs (k lo hi : Nat) : Nat × Nat :=
  let u := ((2 ^ (64 + k) + refWideA k lo hi) % (2 ^ 128)).toNat
  (u % Verified.Reflect.M, u / Verified.Reflect.M)

/-- The per-integer test of `mobiusLiveResidue`, run on the reference: the
number of `n ∈ [lo, hi]` at which `|V| + ⌈n/2^(k+2)⌉ + 1 > ⌊2⁶¹/⌈√(n+1)⌉⌋`, with
`V = ⌊A(n)/2^(k+1)⌋` the *floor* division of a signed accumulator. -/
def refWideViol (k lo hi c0 cSq0 : Nat) : Nat :=
  ((window lo hi).foldl (fun st n =>
    let (a, c, cq, v) := st
    let w : Int := ((2 ^ (63 + k) + n / 2) / n : Nat)
    let a : Int := match refMuCode n with | 1 => a + w | 2 => a - w | _ => a
    let (c, cq) := if n ≥ cq then (c + 1, cq + 2 * (c + 1) - 1) else (c, cq)
    let bad :=
      (Int.fdiv a (2 ^ (k + 1))).natAbs + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1
        > 2 ^ 61 / c
    (a, c, cq, v + (if bad then 1 else 0)))
    ((0 : Int), c0, cSq0, 0)).2.2.2

/-- A program with the epilogue stripped and the output pointed at one
accumulator, so a single residue register can be read off. -/
def probe (c : Cfg) (residue init : List AInstr) (out : Nat) : AProgram :=
  { regCount := regCount, arrayLen := c.arrayLen
    loopCount := c.period * (c.rootCount + c.segCount)
    init := c.coreInit ++ init
    body := c.coreBody ++ residue
    epilogue := [], output := out }

/-- Three main windows of eight cells covering `[1, 24]`, behind one root
window covering `[1, 8]`.  The counts are spelled out because the emit-time
sieve is not a kernel-reducible definition; they are what `Cfg.ofRange 1 8 3`
computes — `⌊√24⌋ = 4`, so the root sweep must reach `4`, one window of eight
cells does, `⌊√8⌋ = 2` leaves `[2]` as the bootstrap table, and the root phase
collects the one remaining prime `3` into a table of `π(4) = 2` entries. -/
def cfg : Cfg :=
  { lo := 1, segLen := 8, segCount := 3, rootCount := 1
    bootPrimes := [2], mainCount := 2, rootCap := 4, markSteps := 26 }

def mertensProbe (out : Nat) : AProgram :=
  probe cfg mertensResidue (mertensInit ⟨mertensBias, 0, gBias⟩) out

def mobiusProbe : AProgram := probe cfg mobiusOverNResidue (mobiusInit tBias) rT

/-- The per-integer residue at the same configuration.  `lo = 1`, so the
`⌊√n⌋` register starts at `⌊√0⌋ = 0` and must reach `⌊√24⌋ = 4`. -/
def liveProbe (out : Nat) : AProgram :=
  probe cfg (mertensLiveResidue 755 10000)
    (mertensLiveInit 0 ⟨mertensBias, 0, gBias⟩) out

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mertensProbe rM).denote = some (refM 1 24) := by decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mertensProbe rQ).denote = some (refQ 1 24) := by decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : mobiusProbe.denote = some (refT 1 24) := by decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (liveProbe rM).denote = some (refM 1 24) := by decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (liveProbe rQ).denote = some (refQ 1 24) := by decide

-- `G` is not kernel-checked here: `cdemC` is a Machin computation of `π` at
-- 128 bits, and reducing it once per fold step costs more than the check is
-- worth.  `G` is checked instead against `bench/ref_seg.c`, which carries the
-- identical fixed-point convention, at `10⁸` and at `lo = 10¹⁰` (slot 2).

-- The incrementally maintained `⌊√n⌋` reaches `⌊√24⌋ = 4`.
set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (liveProbe rS).denote = some 4 := by decide

/-! ### The per-integer `Σ μ(m)/m` residue, at the same configuration

`k = 3` rather than the production `15`, only so that the reference's
`2^(63+k)` literals stay small enough for the kernel fold to be cheap; every
instruction exercised is the same one, including the two-limb carry, the
borrow, the `≫ (k+1)` recombination and the `⌈√n⌉` increment. -/

def mobLiveK : Nat := 3

def mobLiveProbe (out : Nat) : AProgram :=
  probe cfg (mobiusLiveResidue mobLiveK) (mobiusLiveInit (mobLiveSeedStart mobLiveK))
    out

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mobLiveProbe rTLo).denote = some (refWideLimbs mobLiveK 1 24).1 := by
  decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mobLiveProbe rTHi).denote = some (refWideLimbs mobLiveK 1 24).2 := by
  decide

-- `⌈√25⌉ = 5`, maintained by the same increment trick as `⌊√n⌋`.
set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mobLiveProbe rCeil).denote = some 5 := by decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : (mobLiveProbe rCeilSq).denote = some 25 := by decide

-- The whole program, epilogue included: its denotation is the number of
-- integers at which the per-integer test failed, and it agrees with the
-- trial-division reference.  The count on `[1, 24]` is `3`, not `0`, so this
-- check is not vacuous: `n = 1` and `n = 2` are below the family's range and
-- genuinely violate it (`1 > 1/(2√2)`, `1/2 > 1/(2√3)`), and `n = 4` is an
-- exact tie the `⌈·⌉` relaxation cannot resolve — `Σ_{m≤4} μ(m)/m = 1/6` and
-- `⌈√5⌉ = 3`, so `|V|` lands exactly on `⌊2⁶¹/3⌋` and the `+1` for the
-- shift's truncation tips it over.  Swept exhaustively, `n = 4` is the only
-- integer in `[3, 7.727·10⁹]` at which the relaxation costs anything.
set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example :
    (mobiusLiveProgram cfg mobLiveK (mobLiveSeedStart mobLiveK)).denote
      = some (refWideViol mobLiveK 1 24 1 1) := by
  decide

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
example : refWideViol mobLiveK 1 24 1 1 = 3 := by decide

end Check

end LeanCompCert.Ports.ArraySegSieve
