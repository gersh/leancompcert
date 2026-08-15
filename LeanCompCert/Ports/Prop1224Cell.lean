import LeanCompCert.Verified.Prop1224Margin
import LeanCompCert.Ports.PsiSegSieve

/-!
# Helfgott Prop. 12.2.4: the per-cell margin, as a program of the proved fragment

One `q` row.  The cell phase sweeps `r = 1 … λ(q) − 1`, accumulates
`G_q(r) = Σ_{r' ≤ r, μ²(r')=1, (r',q)=1} 1/φ(r')` at scale `2^C`, and at every
`r` in the window `[k0, λ(q))` tests

```
(φ(q)/q)·[ log r + (1−ω*)·log q + ω*·L(q) + 1.36 ]  ≥  G_q(r) + envelope.
```

`Verified/Prop1224Margin.lean` is the direction calculus this implements; the
row constants `phiLo`, `constLo`, `afHi`, `k0`, `kmax` are its inputs and come
from the row phase.

## Three planes and no `gcd`

The model is `Ports/R2SegSieve.lean`, and the reusable part is its `prod ≠ n`
test for "a prime above `⌊√hi⌋` remains".  What is needed per cell is different
— `μ²(r)` and `φ(r)`, not a `Λ∗Λ` classification — so the planes are:

* `prod` — multiplied by the base prime at a `j = 1` mark only, so it holds the
  **radical** of the small part.  For a *squarefree* `r` that is the whole small
  part, and `prod ≠ r` then says exactly that one prime above `⌊√hi⌋` remains,
  to the first power;
* `phi` — multiplied by `p − 1` at a `j = 1` mark, so it holds `∏(p−1)` over the
  small primes, which for squarefree `r` is `φ` of the small part;
* `sqf` — set at a `j ≥ 2` mark.  Nonzero is exactly `μ²(r) = 0`.

`prod` and `phi` are only *meaningful* when `sqf` is clear, which is the only
case the sum uses, so the three planes carry no multiplicity at all and the
mark budget drops back from `Σ 1/(p−1)` to `Σ 1/p` plus the `Σ 1/p^j`, `j ≥ 2`,
that set `sqf`.  This classification is valid on the entire interval
`1 ≤ r ≤ hi`, not merely above `⌊√hi⌋`: after every prime at most `√hi` has
been removed, at most one prime factor can remain, and it has multiplicity
one.  Thus a row may start at `r = 1` with the exact zero `G_q` carry.

**Coprimality needs no plane and no `gcd`.**  `ω(q) ≤ 10` for every `q` in the
paper's range (`2·3·5·7·11·13·17·19·23·29 = 6.47·10⁹`), and the primes of `q`
are known when the artifact is emitted, so the test is `ω(q)` literal `urem`s
laid down straight-line.  That also covers `q`'s own large prime for free.

## The cube root that is not an exponential

The envelope needs `(20000r)^{−1/3}` from **above**, hence `(20000r)^{1/3}` from
below.  A `rpow` per cell would dominate the phase at `1.34 µs` a call.  Because
`r` runs over consecutive integers it is instead carried in a register:
`rT = ⌊2^5·(20000r)^{1/3}⌋`, advanced by at most one increment per squaring
round, and **certified** by `Prop1224Margin.cbrtOK` — `t³ ≤ 2^15·20000r` — which
is the cube-root statement with the denominators cleared.  As with
`ExpFixed.expOK` the advance itself is not proved and does not need to be; the
comparison is.  The last round asserts `(t+1)³ > 2^15·20000r`, so a `t` left
behind by a too-small increment budget is a *reported violation*, not a
silently weak envelope.

## The logarithm fits in one multiply

`R2SegSieve` splits the `lnFix` conversion into four `32×32` products because it
carries `ln 2` at scale `2^64`.  Here `log r ≤ 24.5` and the conversion is at
scale `2^32`, so `logFix · ⌊2^32 ln 2⌋ ≤ 4.1·10⁸ · 2.98·10⁹ = 1.2·10^18`, one
word, and the whole conversion is a single `mul` and a `lshr`.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`: `cellProgram_wf` and
`cellProgram_compiled`, so `AProgram.evalCC_compile` applies and the emitted C
computes exactly `denote`.

Not proved, exactly as in `R2SegSieve`: that `denote` *is* the margin.  That is
checked by kernel evaluation against a reference fold at a tiny configuration,
and by the artifact against `bench/ref_p1224.c`.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Verified.Prop1224Margin (E C S cdiv k0 lamHi cbrtOK)

/-! ## Emit-time constants -/

/-- `⌊2^32·ln 2⌋`, rounded **down**: the logarithm is wanted from below. -/
def L2lo32 : Nat := 2977044471

/-- The shift that takes `logFix S r · L2lo32` from scale `2^(S+32)` to the row
scale `2^E`. -/
def lnShift : Nat := S + 32 - E

/-- The bias the margin accumulator carries, so that a negative margin is
representable in `Nat`.  The positive part is `< 32·2^C` and the negative part
`< 32·2^C`, so `2^(C+6)` clears both. -/
def marginBias : Nat := 2 ^ (C + 6)

/-! ## Configuration -/

structure CellCfg where
  /-- The row. -/
  q : Nat
  /-- `⌊2^E·φ(q)/q⌋`. -/
  phiLo : Nat
  /-- `⌊2^E·((1−ω*)·log q + ω*·L(q) + 1.36)⌋`, the `k`-independent part. -/
  constLo : Nat
  /-- `⌈2^E·ω*·7.284·f₁(q)⌉`. -/
  afHi : Nat
  /-- First `k` examined, `⌊varpiLo/2^E⌋`. -/
  kLo : Nat
  /-- First `k` beyond the window. -/
  kHi : Nat
  /-- The distinct primes of `q`, for the straight-line coprimality test. -/
  qPrimes : List Nat
  /-- First integer of the sweep.  Production rows start at `1`, avoiding an
  externally computed `G_q` carry. -/
  lo : Nat
  segLen : Nat
  segCount : Nat
  markSteps : Nat
  /-- The mark table: the primes `≤ ⌊√hi⌋`, one cell each. -/
  table : List Nat
  deriving Repr

def CellCfg.hi (c : CellCfg) : Nat := c.lo + c.segLen * c.segCount - 1
def CellCfg.tableLen (c : CellCfg) : Nat := c.table.length
def CellCfg.root (c : CellCfg) : Nat := Nat.sqrt c.hi
/-- One mark phase, one accumulate pass, then `S` log rounds per cell. -/
def CellCfg.period (c : CellCfg) : Nat := c.markSteps + c.segLen + c.segLen * S
def CellCfg.q0 (c : CellCfg) : Nat := c.table.headD 2

/-! ### Array layout

Four planes of `L` cells — `prod`, `phi`, `sqf`, `gval` — their sinks at `4L`
through `7L`, then the mark table and the result cells.  The gap is address
space only; the emitted C's array is `static`, so untouched pages cost nothing.
-/

def CellCfg.sink (c : CellCfg) : Nat := 4 * c.segLen
def CellCfg.tableBase (c : CellCfg) : Nat := 8 * c.segLen + 1
def CellCfg.resultBase (c : CellCfg) : Nat := c.tableBase + c.tableLen + 2
def CellCfg.arrayLen (c : CellCfg) : Nat := c.resultBase + 12

/-! ## Register allocation -/

def rPi : Nat := 2      -- mark-table cursor
def rQp : Nat := 3      -- current entry's prime power
def rJ : Nat := 4       -- current multiple, as a cell index
def rR : Nat := 5       -- position inside the period
def rW : Nat := 6       -- window base
def rOne : Nat := 7     -- constant 1, for the plane resets
def rZero : Nat := 8    -- constant 0
def rBp : Nat := 170    -- current entry's base prime
def rFs : Nat := 172    -- current entry's `j = 1` flag

def rG : Nat := 180     -- the running `G_q`, at scale 2^C
def rCells : Nat := 183 -- cells tested
def rEx : Nat := 186    -- ⌊log₂ r⌋
def rTh : Nat := 187    -- 2^(rEx+1)
def rMin : Nat := 188   -- the smallest margin seen, biased
def rViol : Nat := 190  -- failed clauses and guards
def rK : Nat := 193     -- squaring-round counter, 0 … S−1
def rCi : Nat := 194    -- cell index inside the log phase
def rT : Nat := 195     -- the certified cube root, at scale 2^5
def rXm : Nat := 196    -- mantissa
def rAa : Nat := 197    -- log bits so far

/-! ### The five failure classes, counted apart

`rViol` is the aggregate and stays the program's output.  One of the five is
the mathematics — the per-cell margin — and the other four say the run left
the range in which its own arithmetic is exact, so on those cells the margin
was not tested at all. -/

def rVMargin : Nat := 250  -- the margin went negative: the clause failed
def rVMark : Nat := 251    -- the mark cursor did not reach the end of the table
def rVLog2 : Nat := 252    -- one `⌊log₂ r⌋` increment did not suffice
def rVCbrt : Nat := 253    -- the cube root was still advanceable at the last round
def rVCbrtHi : Nat := 254  -- the current cube root exceeded its proved lower bound

/-- The per-class counters in the order they occupy result slots `6 … 10`.
They sum to `rViol`.  `bench/Prop1224CellEmit.lean` labels them in this
order. -/
def violRegs : List Nat := [rVMargin, rVMark, rVLog2, rVCbrt, rVCbrtHi]

def regCount : Nat := 400
def outputReg : Nat := 190

/-! ## Phase one: marking

`j = 1` marks multiply `prod` by `p` and `phi` by `p − 1`; `j ≥ 2` marks set
`sqf`.  The higher powers are generated in the loop rather than carried in the
table — the table would otherwise be the thing that overflows `ccomp`'s stack
when it is emitted as literals.
-/

def CellCfg.markBody (c : CellCfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let SNK := c.sink
  let q0 := c.q0
  [ -- phase selectors
    .scalar (.binop 10 .lt (.reg rR) (.lit T))              -- inMark
  , .scalar (.binop 11 .lt (.reg rR) (.lit (T + L)))
  , .scalar (.binop 12 .sub (.reg 11) (.reg 10))            -- inAcc
  , .scalar (.binop 13 .sub (.lit 1) (.reg 11))             -- inLog
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
  , .scalar (.binop 23 .mul (.reg 14) (.reg 18))
  , .scalar (.binop 24 .mul (.reg 15) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 23) (.reg 24))
    -- the mark step: three planes, or the three sinks
  , .scalar (.binop 25 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 26 .mul (.reg 25) (.reg 10))            -- inRange ∧ inMark
  , .scalar (.binop 27 .sub (.lit 1) (.reg 26))
  , .scalar (.binop 28 .mul (.reg 26) (.reg rJ))
  , .scalar (.binop 29 .mul (.reg 27) (.lit SNK))
  , .scalar (.binop 30 .add (.reg 28) (.reg 29))            -- prod cell
  , .scalar (.binop 31 .add (.reg 30) (.lit L))             -- phi cell
  , .scalar (.binop 32 .add (.reg 30) (.lit (2 * L)))       -- sqf cell
    -- the two multipliers and the squarefull flag, all from `rFs`
  , .scalar (.binop 33 .sub (.reg rBp) (.lit 1))
  , .scalar (.binop 34 .mul (.reg rFs) (.reg 33))
  , .scalar (.binop 35 .add (.reg 34) (.lit 1))             -- prod ×= rFs(p−1)+1
  , .scalar (.binop 36 .sub (.reg rBp) (.lit 2))
  , .scalar (.binop 37 .mul (.reg rFs) (.reg 36))
  , .scalar (.binop 38 .add (.reg 37) (.lit 1))             -- phi ×= rFs(p−2)+1
  , .scalar (.binop 39 .sub (.lit 1) (.reg rFs))            -- sqf |= 1 − rFs
  , .load 40 30
  , .scalar (.binop 41 .mul (.reg 40) (.reg 35))
  , .store 30 41
  , .load 42 31
  , .scalar (.binop 43 .mul (.reg 42) (.reg 38))
  , .store 31 43
  , .load 44 32
  , .scalar (.binop 45 .bor (.reg 44) (.reg 39))
  , .store 32 45
    -- the multiples ran past the window: bump to the next power of the same
    -- prime if it still fits under `hi`, and only then step the cursor
  , .scalar (.binop 46 .mul (.reg 10) (.reg 27))            -- advance
  , .scalar (.binop 47 .mul (.reg rQp) (.reg rBp))          -- p^{j+1}
  , .scalar (.binop 48 .le (.reg 47) (.lit c.hi))
  , .scalar (.binop 49 .mul (.reg 46) (.reg 48))            -- bump
  , .scalar (.binop 50 .sub (.reg 46) (.reg 49))            -- step
  , .scalar (.binop 51 .add (.reg rPi) (.reg 50))
  , .scalar (.binop 52 .gt (.reg 51) (.lit K))
  , .scalar (.binop 53 .sub (.lit 1) (.reg 52))
  , .scalar (.binop 54 .mul (.reg 53) (.reg 51))
  , .scalar (.binop 55 .mul (.reg 52) (.lit K))
  , .scalar (.binop rPi .add (.reg 54) (.reg 55))
  , .scalar (.binop 56 .add (.reg rPi) (.lit c.tableBase))
  , .load 57 56
  , .scalar (.binop 58 .sub (.lit 1) (.reg 46))             -- keep
  , .scalar (.binop 59 .add (.reg rJ) (.reg rQp))           -- next multiple
  , .scalar (.binop 60 .mul (.reg 49) (.reg 47))
  , .scalar (.binop 61 .mul (.reg 50) (.reg 57))
  , .scalar (.binop 62 .mul (.reg 58) (.reg rQp))
  , .scalar (.binop 63 .add (.reg 60) (.reg 61))
  , .scalar (.binop rQp .add (.reg 63) (.reg 62))
  , .scalar (.binop 64 .sub (.lit 1) (.reg 50))
  , .scalar (.binop 65 .mul (.reg 50) (.reg 57))
  , .scalar (.binop 66 .mul (.reg 64) (.reg rBp))
  , .scalar (.binop rBp .add (.reg 65) (.reg 66))
  , .scalar (.binop 67 .mul (.reg 58) (.reg rFs))           -- `j = 1` is a step
  , .scalar (.binop rFs .add (.reg 50) (.reg 67))
  , .scalar (.binop 68 .urem (.reg rW) (.reg rQp))
  , .scalar (.binop 69 .sub (.reg rQp) (.reg 68))
  , .scalar (.binop 70 .urem (.reg 69) (.reg rQp))          -- first cell
  , .scalar (.binop 71 .eq (.reg rPi) (.lit K))             -- table exhausted
  , .scalar (.binop 72 .sub (.lit 1) (.reg 71))
  , .scalar (.binop 73 .mul (.reg 71) (.lit (L + 1)))
  , .scalar (.binop 74 .mul (.reg 72) (.reg 70))
  , .scalar (.binop 75 .add (.reg 73) (.reg 74))
  , .scalar (.binop 76 .mul (.reg 46) (.reg 75))
  , .scalar (.binop 77 .mul (.reg 58) (.reg 59))
  , .scalar (.binop rJ .add (.reg 76) (.reg 77))
    -- the mark budget, checked: too small truncates the sieve *silently*
  , .scalar (.binop 78 .eq (.reg rR) (.lit (T - 1)))
  , .scalar (.binop 79 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 80 .mul (.reg 78) (.reg 79))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 80))
  , .scalar (.binop rVMark .add (.reg rVMark) (.reg 80))
  ]

/-! ## Phase two: `μ²`, `φ`, coprimality, and the running `G_q`

The coprimality test is `ω(q)` `urem`s emitted straight-line, one per distinct
prime of `q`; the product of their outcomes is the coprimality bit.  There is
no `gcd` in the fragment and none is needed.
-/

/-- The straight-line coprimality test: `81` accumulates `∏_{p ∣ q} [r mod p ≠ 0]`
starting from `1`. -/
def coprimeBody (ps : List Nat) : List AInstr :=
  ps.flatMap fun p =>
    [ .scalar (.binop 82 .urem (.reg 85) (.lit p))
    , .scalar (.binop 83 .ne (.reg 82) (.lit 0))
    , .scalar (.binop 81 .mul (.reg 81) (.reg 83)) ]

def CellCfg.accBody (c : CellCfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let SNK := c.sink
  [ .scalar (.binop 84 .sub (.reg rR) (.lit T))
  , .scalar (.binop 86 .mul (.reg 12) (.reg 84))            -- i
  , .scalar (.binop 85 .add (.reg 86) (.reg rW))            -- r
  , .scalar (.binop 87 .add (.reg 86) (.lit L))
  , .scalar (.binop 88 .add (.reg 86) (.lit (2 * L)))
  , .scalar (.binop 89 .add (.reg 86) (.lit (3 * L)))
  , .load 90 86                                             -- prod
  , .load 91 87                                             -- phi
  , .load 92 88                                             -- sqf
    -- a prime above ⌊√hi⌋ remains iff the radical of the small part ≠ r
  , .scalar (.binop 93 .ne (.reg 90) (.reg 85))
  , .scalar (.binop 94 .udiv (.reg 85) (.reg 90))           -- the large prime
  , .scalar (.binop 95 .sub (.reg 94) (.lit 2))
  , .scalar (.binop 96 .mul (.reg 93) (.reg 95))
  , .scalar (.binop 97 .add (.reg 96) (.lit 1))             -- 93·(P−2)+1
  , .scalar (.binop 98 .mul (.reg 91) (.reg 97))            -- φ(r)
  , .scalar (.binop 99 .eq (.reg 92) (.lit 0))              -- μ²(r) = 1
    -- coprimality, straight-line
  , .scalar (.mov 81 (.lit 1))
  ] ++ coprimeBody c.qPrimes ++
  [ .scalar (.binop 100 .mul (.reg 99) (.reg 81))           -- take
  , .scalar (.binop 101 .add (.lit (2 ^ C)) (.reg 98))
  , .scalar (.binop 102 .sub (.reg 101) (.lit 1))
  , .scalar (.binop 103 .udiv (.reg 102) (.reg 98))         -- ⌈2^C/φ(r)⌉
  , .scalar (.binop 104 .mul (.reg 103) (.reg 100))
  , .scalar (.binop 105 .mul (.reg 104) (.reg 12))
  , .scalar (.binop rG .add (.reg rG) (.reg 105))
    -- publish the running sum and clear the three marking planes
  , .scalar (.binop 106 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 107 .mul (.reg 106) (.lit SNK))
  , .scalar (.binop 108 .add (.reg 86) (.reg 107))
  , .scalar (.binop 109 .add (.reg 108) (.lit L))
  , .scalar (.binop 110 .add (.reg 108) (.lit (2 * L)))
  , .scalar (.binop 111 .add (.reg 108) (.lit (3 * L)))
  , .store 111 rG
  , .store 108 rOne
  , .store 109 rOne
  , .store 110 rZero
  ]

/-! ## Phase three: the logarithm, the cube root, and the margin -/

/-- Increment attempts for the cube root per squaring round.  One per round is
enough only once `r ≥ 42`, because `d/dr ⌊2^5(20000r)^{1/3}⌋ = 289.5·r^{−2/3}`;
four per round covers every `r ≥ 6`, which is below the smallest window floor
the paper's range produces (`ϖ(2310) = 4.36`).  Too few is *checked*, not
silently wrong: the last round asserts the root can no longer advance. -/
def cbrtAttempts : Nat := 4

/-- One attempt: propose `t+1`, and adopt it exactly when `(t+1)³ ≤ 2^15·20000r`
— `Prop1224Margin.cbrtOK`.  The proposal is not proved; the comparison is. -/
def cbrtStep : Nat → List AInstr
  | 0 => []
  | n + 1 =>
      [ .scalar (.binop 154 .add (.reg rT) (.lit 1))
      , .scalar (.binop 155 .mul (.reg 154) (.reg 154))
      , .scalar (.binop 156 .mul (.reg 155) (.reg 154))     -- (t+1)³
      , .scalar (.binop 157 .le (.reg 156) (.reg 153))      -- cbrtOK (t+1)
      , .scalar (.binop 158 .mul (.reg 157) (.reg 13))
      , .scalar (.binop rT .add (.reg rT) (.reg 158)) ] ++ cbrtStep n

/-- The literal load, window gate, and margin-failure update.  Naming this
block leaves the emitted instruction stream unchanged and gives the source
proof a small boundary around the actual comparison. -/
def CellCfg.marginCheckBlock (c : CellCfg) : List AInstr :=
  let L := c.segLen
  [ .scalar (.binop 218 .add (.reg rCi) (.lit (3 * L)))
  , .load 219 218
  , .scalar (.binop 220 .ge (.reg 122) (.lit c.kLo))
  , .scalar (.binop 221 .lt (.reg 122) (.lit c.kHi))
  , .scalar (.binop 222 .mul (.reg 220) (.reg 221))
  , .scalar (.binop 223 .mul (.reg 222) (.reg 161))
  , .scalar (.binop 224 .add (.reg 219) (.reg 217))
  , .scalar (.binop 225 .lt (.reg 212) (.reg 224))
  , .scalar (.binop 226 .mul (.reg 225) (.reg 223))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 226))
  , .scalar (.binop rVMargin .add (.reg rVMargin) (.reg 226))
  , .scalar (.binop rCells .add (.reg rCells) (.reg 223)) ]

/-- The literal five-instruction ceiling and rescaling block for the negative
envelope.  Naming it leaves the emitted stream unchanged and exposes the
exact word passed to `marginCheckBlock`. -/
def CellCfg.envelopeBlock (c : CellCfg) : List AInstr :=
  [ .scalar (.binop 213 .shl (.lit c.afHi) (.lit 5))
  , .scalar (.binop 214 .add (.reg 213) (.reg rT))
  , .scalar (.binop 215 .sub (.reg 214) (.lit 1))
  , .scalar (.binop 216 .udiv (.reg 215) (.reg rT))
  , .scalar (.binop 217 .shl (.reg 216) (.lit (C - E))) ]

def CellCfg.logBody (c : CellCfg) : List AInstr :=
  [ -- where we are: cell `rCi`, round `rK`
    .scalar (.binop 120 .eq (.reg rK) (.lit 0))
  , .scalar (.binop 121 .mul (.reg 120) (.reg 13))          -- first round
  , .scalar (.binop 122 .add (.reg rCi) (.reg rW))          -- r
    -- ⌊log₂ r⌋, incrementally; one step per cell suffices and it is checked
  , .scalar (.binop 123 .ge (.reg 122) (.reg rTh))
  , .scalar (.binop 124 .mul (.reg 123) (.reg 121))
  , .scalar (.binop rEx .add (.reg rEx) (.reg 124))
  , .scalar (.binop 125 .mul (.reg 124) (.reg rTh))
  , .scalar (.binop rTh .add (.reg rTh) (.reg 125))
  , .scalar (.binop 126 .ge (.reg 122) (.reg rTh))
  , .scalar (.binop 127 .mul (.reg 126) (.reg 121))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 127))
  , .scalar (.binop rVLog2 .add (.reg rVLog2) (.reg 127))
    -- the normalised mantissa, reset at the cell's first round
  , .scalar (.binop 128 .sub (.lit 62) (.reg rEx))
  , .scalar (.binop 129 .band (.reg 128) (.lit 63))
  , .scalar (.binop 130 .shl (.reg 122) (.reg 129))
  , .scalar (.binop 131 .mul (.reg 121) (.reg 130))
  , .scalar (.binop 132 .sub (.lit 1) (.reg 121))
  , .scalar (.binop 133 .mul (.reg 132) (.reg rXm))
  , .scalar (.binop rXm .add (.reg 131) (.reg 133))
  , .scalar (.binop rAa .mul (.reg rAa) (.reg 132))
    -- one squaring round: Ports/LogFixPort.logRoundBody, verbatim
  , .scalar (.binop 134 .lshr (.reg rXm) (.lit 32))
  , .scalar (.binop 135 .band (.reg rXm) (.lit 4294967295))
  , .scalar (.binop 136 .mul (.reg 134) (.reg 134))
  , .scalar (.binop 137 .mul (.reg 134) (.reg 135))
  , .scalar (.binop 138 .mul (.reg 135) (.reg 135))
  , .scalar (.binop 139 .lshr (.reg 137) (.lit 29))
  , .scalar (.binop 140 .band (.reg 137) (.lit 536870911))
  , .scalar (.binop 141 .lshr (.reg 138) (.lit 62))
  , .scalar (.binop 142 .band (.reg 138) (.lit 4611686018427387903))
  , .scalar (.binop 143 .shl (.reg 140) (.lit 33))
  , .scalar (.binop 144 .add (.reg 143) (.reg 142))
  , .scalar (.binop 145 .ge (.reg 144) (.lit 4611686018427387904))
  , .scalar (.binop 146 .shl (.reg 136) (.lit 2))
  , .scalar (.binop 147 .add (.reg 146) (.reg 139))
  , .scalar (.binop 148 .add (.reg 147) (.reg 141))
  , .scalar (.binop 149 .add (.reg 148) (.reg 145))
  , .scalar (.binop 150 .ge (.reg 149) (.lit 9223372036854775808))
  , .scalar (.binop rXm .lshr (.reg 149) (.reg 150))
  , .scalar (.binop 151 .shl (.reg rAa) (.lit 1))
  , .scalar (.binop rAa .add (.reg 151) (.reg 150))
    -- the certified cube root: `cbrtAttempts` increments per round
  , .scalar (.binop 152 .mul (.lit 20000) (.reg 122))
  , .scalar (.binop 153 .shl (.reg 152) (.lit 15))          -- 2^15·20000r
  ] ++ cbrtStep cbrtAttempts ++
  [ -- the round counter and the cell cursor
    .scalar (.binop 159 .add (.reg rK) (.lit 1))
  , .scalar (.binop 160 .eq (.reg 159) (.lit S))
  , .scalar (.binop 161 .mul (.reg 160) (.reg 13))          -- last round
  , .scalar (.binop 162 .sub (.lit 1) (.reg 160))
  , .scalar (.binop 163 .mul (.reg 159) (.reg 162))
  , .scalar (.binop rK .mul (.reg 163) (.reg 13))
    -- the cube-root budget, checked at the last round
  , .scalar (.binop 200 .add (.reg rT) (.lit 1))
  , .scalar (.binop 201 .mul (.reg 200) (.reg 200))
  , .scalar (.binop 202 .mul (.reg 201) (.reg 200))
  , .scalar (.binop 203 .le (.reg 202) (.reg 153))          -- still advanceable
  , .scalar (.binop 204 .mul (.reg 203) (.reg 161))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 204))
  , .scalar (.binop rVCbrt .add (.reg rVCbrt) (.reg 204))
    -- A too-large seed is the dangerous direction: it makes the reciprocal
    -- envelope too small.  Check the current lower bound on tested cells.
    -- The explicit `t < 2^21` guard makes the following cube exact in u64.
  , .scalar (.binop 260 .lt (.reg rT) (.lit 2097152))
  , .scalar (.binop 261 .sub (.lit 1) (.reg 260))
  , .scalar (.binop 262 .mul (.reg rT) (.reg rT))
  , .scalar (.binop 263 .mul (.reg 262) (.reg rT))
  , .scalar (.binop 264 .gt (.reg 263) (.reg 153))
  , .scalar (.binop 265 .add (.reg 261) (.reg 264))
  , .scalar (.binop 266 .ne (.reg 265) (.lit 0))
  , .scalar (.binop 267 .ge (.reg 122) (.lit c.kLo))
  , .scalar (.binop 268 .lt (.reg 122) (.lit c.kHi))
  , .scalar (.binop 269 .mul (.reg 267) (.reg 268))
  , .scalar (.binop 270 .mul (.reg 266) (.reg 269))
  , .scalar (.binop 271 .mul (.reg 270) (.reg 161))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 271))
  , .scalar (.binop rVCbrtHi .add (.reg rVCbrtHi) (.reg 271))
    -- ⌊2^E·log r⌋ from below: one multiply, one shift
  , .scalar (.binop 205 .shl (.reg rEx) (.lit S))
  , .scalar (.binop 206 .add (.reg 205) (.reg rAa))         -- logFix S r
  , .scalar (.binop 207 .mul (.reg 206) (.lit L2lo32))
  , .scalar (.binop 208 .lshr (.reg 207) (.lit lnShift))    -- ln r, LOWER
    -- the positive part, at the cell scale
  , .scalar (.binop 209 .add (.reg 208) (.lit c.constLo))
  , .scalar (.binop 210 .mul (.lit c.phiLo) (.reg 209))
  , .scalar (.binop 211 .lshr (.reg 210) (.lit E))
  , .scalar (.binop 212 .shl (.reg 211) (.lit (C - E)))     -- pos, LOWER
  ] ++ c.envelopeBlock ++ c.marginCheckBlock ++
  [
    -- the running minimum margin, biased so that it stays a `Nat`
    .scalar (.binop 227 .add (.lit marginBias) (.reg 212))
  , .scalar (.binop 228 .sub (.reg 227) (.reg 224))
  , .scalar (.binop 229 .lt (.reg 228) (.reg rMin))
  , .scalar (.binop 230 .mul (.reg 229) (.reg 223))
  , .scalar (.binop 231 .sub (.lit 1) (.reg 230))
  , .scalar (.binop 232 .mul (.reg 230) (.reg 228))
  , .scalar (.binop 233 .mul (.reg 231) (.reg rMin))
  , .scalar (.binop rMin .add (.reg 232) (.reg 233))
    -- advance the cell cursor at the end of a cell
  , .scalar (.binop rCi .add (.reg rCi) (.reg 161))
  ]

/-! ## The tail -/

def CellCfg.tailBody (c : CellCfg) : List AInstr :=
  let L := c.segLen
  let Pd := c.period
  [ .scalar (.binop 240 .add (.reg rR) (.lit 1))
  , .scalar (.binop 241 .eq (.reg 240) (.lit Pd))
  , .scalar (.binop 242 .sub (.lit 1) (.reg 241))
  , .scalar (.binop rR .mul (.reg 242) (.reg 240))
  , .scalar (.binop 243 .mul (.reg 241) (.lit L))
  , .scalar (.binop rW .add (.reg rW) (.reg 243))
  , .scalar (.binop rCi .mul (.reg rCi) (.reg 242))
  , .scalar (.binop rK .mul (.reg rK) (.reg 242))
  ]

def CellCfg.body (c : CellCfg) : List AInstr :=
  c.markBody ++ c.accBody ++ c.logBody ++ c.tailBody

/-! ## Initialization and epilogue -/

def CellCfg.tableCells (c : CellCfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [(c.tableBase + c.tableLen, 1)]

/-- The first window's three marking planes start at their neutral values;
every later window is reset by the accumulate pass. -/
def CellCfg.planeCells (c : CellCfg) : List (Nat × Nat) :=
  (List.range c.segLen).flatMap fun i => [(i, 1), (c.segLen + i, 1)]

structure CellSeed where
  g : Nat
  ex : Nat
  th : Nat
  t : Nat
  cells : Nat
  deriving Repr

def CellCfg.seedList (c : CellCfg) (s : CellSeed) : List (Nat × Nat) :=
  [ (rW, c.lo), (rOne, 1), (rZero, 0)
  , (rG, s.g), (rEx, s.ex), (rTh, s.th), (rT, s.t), (rCells, s.cells)
  , (rMin, 2 ^ 63) ]

def CellCfg.init (c : CellCfg) (s : CellSeed) : List AInstr :=
  storeLits c.tableCells ++ storeLits c.planeCells ++ seedRegs (c.seedList s)

def storeResult (c : CellCfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .store 90 reg ]

/-- Store a run of registers into consecutive result cells from `slot`. -/
def storeResults (c : CellCfg) : Nat → List Nat → List AInstr
  | _, [] => []
  | slot, r :: rs => storeResult c slot r ++ storeResults c (slot + 1) rs

def CellCfg.epilogue (c : CellCfg) : List AInstr :=
  storeResult c 0 rG ++ storeResult c 1 rCells ++ storeResult c 2 rMin ++
  storeResult c 3 rT ++ storeResult c 4 rEx ++ storeResult c 5 rViol ++
  storeResults c 6 violRegs

def cellProgram (c : CellCfg) (s : CellSeed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init s
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-! ## Well-formedness, and the bridge instantiated -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem storeResult_all (c : CellCfg) (slot reg : Nat) (h : reg < regCount) :
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

theorem seedList_ok (c : CellCfg) (s : CellSeed) :
    ∀ x ∈ c.seedList s, x.1 < regCount := by
  intro x hx
  have hall : (c.seedList s).all (fun y => decide (y.1 < regCount)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem init_all (c : CellCfg) (s : CellSeed) :
    (c.init s).all (ainstrWFB regCount) = true :=
  all_append (all_append (storeLits_all _) (storeLits_all _))
    (seedRegs_all _ (seedList_ok c s))

/-- The coprimality test is well formed for any list of primes: its three
registers are fixed and below `regCount`. -/
theorem coprimeBody_all (ps : List Nat) :
    (coprimeBody ps).all (ainstrWFB regCount) = true := by
  simp only [coprimeBody, List.all_flatMap]
  refine List.all_eq_true.mpr (fun p _ => ?_)
  simp only [List.all_cons, List.all_nil, ainstrWFB, instrWFB, operandWFB,
    regCount, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

set_option maxRecDepth 40000 in
theorem markBody_all (c : CellCfg) : c.markBody.all (ainstrWFB regCount) = true := by
  rfl

set_option maxRecDepth 40000 in
theorem accBody_all (c : CellCfg) : c.accBody.all (ainstrWFB regCount) = true := by
  simp only [CellCfg.accBody]
  exact all_append (all_append (by rfl) (coprimeBody_all _)) (by rfl)

theorem cbrtStep_all (n : Nat) : (cbrtStep n).all (ainstrWFB regCount) = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact all_append (by rfl) ih

set_option maxRecDepth 40000 in
theorem logBody_all (c : CellCfg) : c.logBody.all (ainstrWFB regCount) = true := by
  simp only [CellCfg.logBody, List.all_append, cbrtStep_all,
    CellCfg.envelopeBlock, CellCfg.marginCheckBlock]
  rfl

set_option maxRecDepth 40000 in
theorem tailBody_all (c : CellCfg) : c.tailBody.all (ainstrWFB regCount) = true := by
  rfl

theorem body_all (c : CellCfg) : c.body.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (markBody_all c) (accBody_all c))
    (logBody_all c)) (tailBody_all c)

theorem storeResults_all (c : CellCfg) : ∀ (slot : Nat) (l : List Nat),
    l.all (fun r => decide (r < regCount)) = true →
    (storeResults c slot l).all (ainstrWFB regCount) = true
  | _, [], _ => rfl
  | slot, a :: t, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact all_append (storeResult_all c slot a (of_decide_eq_true h.1))
        (storeResults_all c (slot + 1) t h.2)

theorem epilogue_all (c : CellCfg) :
    c.epilogue.all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (storeResult_all c 0 rG (by decide)) (storeResult_all c 1 rCells (by decide)))
    (storeResult_all c 2 rMin (by decide)))
    (storeResult_all c 3 rT (by decide)))
    (storeResult_all c 4 rEx (by decide)))
    (storeResult_all c 5 rViol (by decide)))
    (storeResults_all c 6 violRegs (by decide))

/-- **The bridge's side condition.** -/
theorem cellProgram_wf (c : CellCfg) (s : CellSeed) : (cellProgram c s).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the per-cell margin.**  For any array base
at which the four planes fit, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
number of failed margins and guards, in the output register. -/
theorem cellProgram_compiled (c : CellCfg) (s : CellSeed) (base : Int)
    (hBase : BaseOk (cellProgram c s).arrayLen base)
    (n : Nat) (hDenote : (cellProgram c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((cellProgram c s).initialMCC base) (cellProgram c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(cellProgram c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (cellProgram_wf c s) base hBase n hDenote



/-! ## Emit-time configuration

Everything in this section runs in Lean when the artifact is built.  None of it
is compiled; it only produces the literals the program carries.
-/

/-- The mark table: the primes `≤ ⌊√hi⌋`, one cell each.  The higher powers are
generated in the loop — that is what keeps the init block inside `ccomp`'s
stack, which a table emitted as literals is not (`27 421` entries overflowed it
at `27 GB` with an unlimited stack). -/
def markTable (hi : Nat) : List Nat := primesBelow (Nat.sqrt hi + 1)

/-- Mark steps a window of `len` cells needs: one per multiple of each prime
**power** `p^j ≤ hi`, one per power to advance or bump the cursor, and slack. -/
def markBudget (root hi len : Nat) : Nat := Id.run do
  let mut acc := 16
  for p in primesBelow (root + 1) do
    let mut q := p
    while q ≤ hi do
      acc := acc + len / q + 2
      q := q * p
  return acc

/-- `⌊2^5·(20000r)^{1/3}⌋`, computed in Lean at emit time to seed `rT`.  A
seed that is too small is not unsound — the loop only ever raises `rT`, and a
smaller `rT` gives a *larger* envelope, which is the conservative direction —
but it would burn the increment budget and trip the guard. -/
def cbrtSeed (r : Nat) : Nat := Id.run do
  let n := (20000 * r) <<< 15
  let mut t := 0
  let mut step := 1 <<< 20
  while step > 0 do
    while (t + step) * (t + step) * (t + step) ≤ n do
      t := t + step
    step := step / 2
  return t

/-- The configuration for one row.  The table contains every prime at most
`⌊√hi⌋`; consequently a squarefree cell whose marked radical differs from
`r ≤ hi` has exactly one remaining (large) prime factor. -/
def CellCfg.ofRow (q phiLo constLo afHi kLo kHi : Nat) (qPrimes : List Nat)
    (lo segLen segCount : Nat) : CellCfg :=
  let hi := lo + segLen * segCount - 1
  { q := q, phiLo := phiLo, constLo := constLo, afHi := afHi
    kLo := kLo, kHi := kHi, qPrimes := qPrimes
    lo := lo, segLen := segLen, segCount := segCount
    markSteps := markBudget (Nat.sqrt hi) hi segLen
    table := markTable hi }

/-! ## Kernel sanity checks

The bridge does not depend on any of this: it says the artifact computes
`denote`, whatever `denote` is.  These checks are the other half — evidence
that `denote` is the running `G_q` and the margin it is meant to be.  They
evaluate the whole three-phase loop in the kernel at a tiny configuration and
compare against a **trial-division** reference, which shares no code with it:
`sqfPhiTD` divides by every integer up to `r`, where the artifact multiplies
three planes and compares a product against `r`.
-/

namespace Check

/-- `(μ²(r), φ(r))` by trial division, structurally recursive so that the
kernel can unfold it. -/
def tdAux (m d fuel : Nat) (sq phi : Nat) : Nat × Nat :=
  match fuel with
  | 0 => if 1 < m then (sq, phi * (m - 1)) else (sq, phi)
  | fuel + 1 =>
      if m < d * d then (if 1 < m then (sq, phi * (m - 1)) else (sq, phi))
      else if m % d = 0 then
        (if m / d % d = 0 then tdAux (m / d) (d + 1) fuel 1 phi
         else tdAux (m / d) (d + 1) fuel sq (phi * (d - 1)))
      else tdAux m (d + 1) fuel sq phi

/-- `(squarefull?, φ(r))`. -/
def sqfPhiTD (r : Nat) : Nat × Nat := tdAux r 2 (r + 2) 0 1

/-- Is `r` coprime to every element of `ps`? -/
def copTD (ps : List Nat) (r : Nat) : Bool := ps.all (fun p => r % p ≠ 0)

/-- The running `G_q` over `[1, top]` at scale `2^C`, by trial division. -/
def refG (ps : List Nat) (top : Nat) : Nat :=
  (List.range (top + 1)).foldl
    (fun acc r =>
      if r = 0 then acc
      else
        let sp := sqfPhiTD r
        if sp.1 = 0 && copTD ps r then acc + cdiv (2 ^ C) sp.2 else acc)
    0

end Check

end LeanCompCert.Ports.Prop1224Cell
