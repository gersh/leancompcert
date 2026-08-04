import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Verified.ScalarLift
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined
import LeanCompCert.Verified.MulWide

/-!
# The Ramaré `m★` 140-million-point sweep as an array program

The `ternary-goldbach-lean` atom `MStar140MCert.full_run` evaluates

```
TGNativeCertificates.Ramare.MStar140MEngine.checkLimit 140000000 = true
```

and the goldbach tree has already reduced that Boolean, by three proved
equalities (`MStar140MScanReduction`, `MStar140MStarSum`,
`MStar140MTableSpecs`), to the **array-free** statement `checkStarMath
140000000 = true`, whose ingredients are only

* `L(q) = Σ_{k ≤ q} μ(k)·⌊2⁴⁸/k⌋` (`littleMertens`), through `Nat.minFac`;
* `star(n) = Σ_{w=1}^{⌊√limit⌋} ⌈(|L(⌊n/w²⌋)| + ⌊n/w²⌋)/w²⌉` (`starSumMath`);
* the RS62 upper log ladder above the LeanCert handoff `10⁴`, and 69 direct
  LeanCert enclosures below it; and
* the dyadic-block discipline: every `n < 64` is checked individually, and
  thereafter the block maximum is checked at `n + 1 = 2·blockStart` and at
  `n = limit`.

This file is the artifact.

## Shape

One flat loop of `len · B` rounds over a single array of `limit + 1 + tab`
cells.  A *block* of `B` consecutive rounds is one candidate `n`:

* rounds `r ∈ [0, B−2)` carry `d = w = r + 2`.  Each one advances the trial
  scan (`s := d` at the first `d` with `d² ≤ n` and `d ∣ n`, exactly
  `Ports/RamareWM217.lean`'s `spfIn`) **and** adds the `w`-term
  `⌈(|L(⌊n/w²⌋)| + ⌊n/w²⌋)/w²⌉` read from cell `⌊n/w²⌋`;
* round `r = B−2` reads cell `q = n / p`, where `p` is the committed factor
  (`n` itself when the scan is empty, i.e. when `n` is prime), and latches the
  Möbius value stored there;
* round `r = B−1` commits: it reads the log-constant cell, forms
  `μ(n) = 0` if `p ∣ q` and `−μ(q)` otherwise, advances `L`, forms
  `star(n) = acc + |L(n)| + n` (the `w = 1` term needs no cell), runs the
  dyadic check, and writes cell `n`.

The store is **unconditional at index `n`**: rounds before the commit write
the previous candidate's cell there, which is sound because no round of block
`n` reads cell `n` (every read index is `⌊n/w²⌋ ≤ n/4` for `w ≥ 2`, or
`q = n/p ≤ n/2`, or a log-constant cell above `limit`).

## Packed cells

Cell `q ≤ limit` holds `|L(q)| + 2⁵² · (μ(q) + 1)`: the magnitude in the low
52 bits and the Möbius value, biased to `{0,1,2}`, above them.  One load
therefore serves both consumers — the `w`-term needs `|L|`, the commit needs
`μ`.  The running `L` itself is carried **biased at `2⁶²`** in a register, so
the signed accumulator never leaves the unsigned word.

## The 69 + 1 log constants

`nextLogUpper n logUp` ignores `logUp` whenever `n + 1 ≤ 10⁴`, so the ladder
only ever *consumes* a direct LeanCert enclosure at a check point below the
handoff.  Those are exactly `n + 1 ∈ {3, …, 64} ∪ {128, 256, …, 8192}` — 69
values — plus the seed `directLogUpper 10⁴` from which the ladder runs.  The
69 live in the array above `limit`, indexed by a counter that increments at
every check; the seed is a scalar constant.  (Enumerated and verified against
the control flow; the whole table certifies in the kernel by `decide +kernel`
in about two seconds.)

## Width discipline

`|L| ≤ 2⁵⁰`, `star ≈ 2⁴⁴`, `logUp ≤ 2⁵³`, so `5·star·logUp ≈ 2⁹⁸` — over a
word.  The row test is therefore a **128-bit** comparison against
`4·2⁴⁸·2⁴⁸ = 2⁹⁸`, computed by the half-limb circuit of
`Verified/MulWide.lean`.  Everything else fits `u64`, and a run that exits `0`
certifies that too: the body counts a violation whenever the partial sum, the
`|L|` magnitude or the ladder leaves its declared cap, so no quantity can have
wrapped in a passing run.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RS62
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.InstrBlock
  (srun sval sdest SDefined SAllDefined NoDivI srun_append SAllDefined_append)

/-! ## Numeric constants -/

/-- `2⁴⁸`, the fixed-point denominator of the goldbach development. -/
def fpDlit : Nat := 281474976710656

/-- `3 · 2⁴⁸`, as a plain numeral (see `Ports/RamareWM217.lean`). -/
def fpD3 : Nat := 844424930131968

theorem fpD3_eq : fpD3 = 3 * fpD := rfl

theorem fpDlit_eq : fpDlit = fpD := rfl

/-- `2⁶²`, the bias carried by the signed little-Mertens accumulator. -/
def bias : Nat := 4611686018427387904

/-- `2⁵²`, the packing base: cell `= |L| + pack · (μ + 1)`. -/
def pack : Nat := 4503599627370496

/-- `2³²`, the half-limb base of `Verified/MulWide.lean`. -/
def b32 : Nat := 4294967296

/-- `4·2⁴⁸·2⁴⁸ = 2⁹⁸`, as a 128-bit pair: `rhsHi · 2⁶⁴ + 0`. -/
def rhsHi : Nat := 17179869184

/-! ## Configuration -/

/-- Every constant the artifact is compiled against. -/
structure Cfg where
  /-- First candidate (production: `2`). -/
  n0 : Nat
  /-- Number of candidates (production: `139 999 999`). -/
  len : Nat
  /-- Rounds per candidate (production: `11833 = ⌊√limit⌋ + 1`). -/
  B : Nat
  /-- Last candidate (production: `140 000 000`). -/
  limit : Nat
  /-- Log-constant slots above the table (a power of two; production `128`). -/
  tab : Nat
  /-- The LeanCert handoff (production: `10 000`). -/
  handoff : Nat
  /-- `directLogUpper handoff`, the ladder seed. -/
  seed : Nat
  /-- The packed cell for `q = 1`: `2⁴⁸ + 2·2⁵²`. -/
  cell1 : Nat
  /-- Cap on `|L|` (must be below the packing base). -/
  capL : Nat
  /-- Cap on the partial `star` sum. -/
  capS : Nat
  /-- Cap on the ladder value. -/
  capLog : Nat
  /-- The 69 log constants, as `(slot, value)` rows. -/
  logs : List (Nat × Nat)
  deriving Repr

/-- Structural sanity, all decidable: the block shape, the square-root
coverage, the packing budget and the width budget. -/
def msOK (c : Cfg) : Bool :=
  decide (2 ≤ c.n0) && decide (3 ≤ c.B) && decide (1 ≤ c.len) &&
  decide (c.limit = c.n0 + c.len - 1) &&
  decide (c.limit < c.B * c.B) &&
  decide (c.B + 1 < 2 ^ 20) &&
  decide (c.limit < 2 ^ 32) &&
  decide (0 < c.tab) && decide (c.tab ≤ 2 ^ 10) &&
  decide (c.handoff < 2 ^ 32) &&
  decide (c.capL ≤ 2 ^ 51) && decide (c.capS ≤ 2 ^ 56) &&
  decide (c.capLog ≤ 2 ^ 56) &&
  decide (c.seed < 2 ^ 56) && decide (c.cell1 = fpDlit + 2 * pack) &&
  c.logs.all (fun e => decide (e.1 < c.tab) && decide (e.2 < 2 ^ 56))

/-! ## Register conventions -/

/-- Violation counter; the output.  `0` is the passing verdict. -/
def rBad : Nat := 0
/-- `2⁶² + L(n−1)`, advanced to `2⁶² + L(n)` at the commit. -/
def rLb : Nat := 1
/-- The RS62 ladder accumulator, seeded at the handoff. -/
def rLam : Nat := 2
/-- The log-constant slot: the number of checks fired so far. -/
def rIdx : Nat := 3
/-- The dyadic block start. -/
def rBs : Nat := 4
/-- The dyadic block maximum. -/
def rMax : Nat := 5
/-- The partial `w`-sum of the current candidate. -/
def rAcc : Nat := 6
/-- The trial-scan accumulator (`0` = nothing found yet). -/
def rS : Nat := 7
/-- `μ(q) + 1`, latched at round `B − 2`. -/
def rMuQ : Nat := 8
/-- The packed cell written at index `n`. -/
def rCell : Nat := 9
/-- The candidate. -/
def rN : Nat := 10
/-- The round `k % B`. -/
def rR : Nat := 11
/-- `d = w = r + 2`. -/
def rD : Nat := 12
/-- `d²`. -/
def rSq : Nat := 13
/-- Work-round gate `r < B − 2`. -/
def rW : Nat := 14
/-- Möbius-read gate `r = B − 2`. -/
def rQg : Nat := 15
/-- Commit gate `r = B − 1`. -/
def rC : Nat := 16
/-- Block-start gate `r = 0`. -/
def rZ : Nat := 17
/-- The committed factor. -/
def rP : Nat := 18
/-- `n / p`. -/
def rQ : Nat := 19
/-- `⌊n / d²⌋`. -/
def rQq : Nat := 20
/-- The load index. -/
def rI : Nat := 21
/-- The loaded cell. -/
def rV : Nat := 22
/-- `μ + 1` of the loaded cell. -/
def rMu1 : Nat := 23
/-- `|L|` of the loaded cell. -/
def rAbs : Nat := 24
/-- `μ(n) + 1`. -/
def rMun : Nat := 25
/-- `|L(n)|`. -/
def rAbsN : Nat := 26
/-- `star(n)`. -/
def rSt : Nat := 27
/-- `max(blockMax, star)`. -/
def rMx : Nat := 28
/-- The value the check compares. -/
def rCv : Nat := 29
/-- The check gate. -/
def rFire : Nat := 30
/-- The logarithm the check uses. -/
def rLU : Nat := 31
/-- `incUWord n`. -/
def rIU : Nat := 32
/-- `⌊2⁴⁸/n⌋`. -/
def rDn : Nat := 33
/-- The row verdict. -/
def rOk : Nat := 34
/-- Low word of the 128-bit product. -/
def rLo : Nat := 35
/-- High word of the 128-bit product. -/
def rHi : Nat := 36
/-- Middle partial sum of the half-limb circuit. -/
def rMid : Nat := 37
/-- Half-limb partial product `a₀b₀`. -/
def rP00 : Nat := 38
/-- Half-limb partial product `a₀b₁`. -/
def rP01 : Nat := 39
/-- Half-limb partial product `a₁b₀`. -/
def rP10 : Nat := 40
/-- Half-limb partial product `a₁b₁`. -/
def rP11 : Nat := 41
/-- Middle carry. -/
def rCM : Nat := 42
/-- Low carry. -/
def rCL : Nat := 43
/-- Scratch. -/
def rT1 : Nat := 44
/-- Scratch. -/
def rT2 : Nat := 45
/-- Scratch. -/
def rT3 : Nat := 46
/-- Scratch. -/
def rG : Nat := 47
/-- Scratch. -/
def rH : Nat := 48

/-- Registers used. -/
def msRegCount : Nat := 49

/-! ## The body, in blocks

Every block below is a list of **scalar** instructions.  The body has exactly
two array instructions — one `load` in the middle and one `store` at the end —
so it is written as

```text
lift (msPre c) ++ (.load rV rI :: lift (msPost c)) ++ [.store rN rCell]
```

and `Verified/ArrayScalarBlock.lean` reduces each scalar stage to the ordinary
scalar machine, carrying the array along untouched.
-/

/-- Decode the flat index, and clear the per-candidate scratch at `r = 0`. -/
def decodeBlock (c : Cfg) : List Instr :=
  [ .binop rR .urem .idx (.lit c.B)
  , .binop rN .udiv .idx (.lit c.B)
  , .binop rN .add (.lit c.n0) (.reg rN)
  , .binop rD .add (.lit 2) (.reg rR)
  , .binop rSq .mul (.reg rD) (.reg rD)
  , .binop rW .lt (.reg rR) (.lit (c.B - 2))
  , .binop rQg .eq (.reg rR) (.lit (c.B - 2))
  , .binop rC .eq (.reg rR) (.lit (c.B - 1))
  , .binop rZ .eq (.reg rR) (.lit 0)
  , .binop rT1 .sub (.lit 1) (.reg rZ)
  , .binop rS .mul (.reg rS) (.reg rT1)
  , .binop rAcc .mul (.reg rAcc) (.reg rT1) ]

/-- One trial round, gated by the work window:
`s := if s = 0 ∧ d² ≤ n ∧ n % d = 0 then d else s`. -/
def scanBlock : List Instr :=
  [ .binop rG .eq (.reg rS) (.lit 0)
  , .binop rT1 .le (.reg rSq) (.reg rN)
  , .binop rG .mul (.reg rG) (.reg rT1)
  , .binop rT2 .urem (.reg rN) (.reg rD)
  , .binop rT2 .eq (.reg rT2) (.lit 0)
  , .binop rG .mul (.reg rG) (.reg rT2)
  , .binop rG .mul (.reg rG) (.reg rW)
  , .binop rT1 .sub (.lit 1) (.reg rG)
  , .binop rT1 .mul (.reg rT1) (.reg rS)
  , .binop rT2 .mul (.reg rG) (.reg rD)
  , .binop rS .add (.reg rT1) (.reg rT2) ]

/-- The committed factor `p` (the candidate itself when the scan is empty)
and the cofactor `q = n / p`. -/
def selectBlock : List Instr :=
  [ .binop rT1 .eq (.reg rS) (.lit 0)
  , .binop rT2 .sub (.lit 1) (.reg rT1)
  , .binop rT2 .mul (.reg rT2) (.reg rS)
  , .binop rT3 .mul (.reg rT1) (.reg rN)
  , .binop rP .add (.reg rT3) (.reg rT2)
  , .binop rQ .udiv (.reg rN) (.reg rP) ]

/-- The load index: `⌊n/d²⌋` on a work round, `q` on the Möbius round, and
the log-constant cell on the commit round. -/
def indexBlock (c : Cfg) : List Instr :=
  [ .binop rQq .udiv (.reg rN) (.reg rSq)
  , .binop rI .mul (.reg rW) (.reg rQq)
  , .binop rT1 .mul (.reg rQg) (.reg rQ)
  , .binop rI .add (.reg rI) (.reg rT1)
  , .binop rT1 .add (.lit (c.limit + 1)) (.reg rIdx)
  , .binop rT1 .mul (.reg rC) (.reg rT1)
  , .binop rI .add (.reg rI) (.reg rT1) ]

/-- Unpack the loaded cell into its Möbius and magnitude halves. -/
def unpackBlock : List Instr :=
  [ .binop rMu1 .lshr (.reg rV) (.lit 52)
  , .binop rT1 .shl (.reg rMu1) (.lit 52)
  , .binop rAbs .sub (.reg rV) (.reg rT1) ]

/-- The `w`-term `⌈(|L| + ⌊n/w²⌋)/w²⌉`, gated by the work window. -/
def termBlock : List Instr :=
  [ .binop rT1 .add (.reg rAbs) (.reg rQq)
  , .binop rT1 .add (.reg rT1) (.reg rSq)
  , .binop rT1 .sub (.reg rT1) (.lit 1)
  , .binop rT1 .udiv (.reg rT1) (.reg rSq)
  , .binop rT1 .mul (.reg rT1) (.reg rW)
  , .binop rAcc .add (.reg rAcc) (.reg rT1) ]

/-- Latch `μ(q) + 1` at round `B − 2`. -/
def latchBlock : List Instr :=
  [ .binop rT1 .sub (.lit 1) (.reg rQg)
  , .binop rT1 .mul (.reg rT1) (.reg rMuQ)
  , .binop rT2 .mul (.reg rQg) (.reg rMu1)
  , .binop rMuQ .add (.reg rT1) (.reg rT2) ]

/-- `μ(n) + 1`: zero when `p ∣ q`, and `−μ(q)` otherwise. -/
def muBlock : List Instr :=
  [ .binop rT1 .urem (.reg rQ) (.reg rP)
  , .binop rT1 .eq (.reg rT1) (.lit 0)
  , .binop rT2 .sub (.lit 1) (.reg rT1)
  , .binop rT3 .sub (.lit 2) (.reg rMuQ)
  , .binop rT3 .mul (.reg rT3) (.reg rT2)
  , .binop rMun .add (.reg rT1) (.reg rT3) ]

/-- Advance the biased little-Mertens accumulator at the commit, then read off
its magnitude. -/
def lbBlock : List Instr :=
  [ .binop rDn .udiv (.lit fpDlit) (.reg rN)
  , .binop rT1 .eq (.reg rMun) (.lit 2)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rT1 .mul (.reg rT1) (.reg rDn)
  , .binop rLb .add (.reg rLb) (.reg rT1)
  , .binop rT2 .eq (.reg rMun) (.lit 0)
  , .binop rT2 .mul (.reg rT2) (.reg rC)
  , .binop rT2 .mul (.reg rT2) (.reg rDn)
  , .binop rLb .sub (.reg rLb) (.reg rT2)
  , .binop rT1 .ge (.reg rLb) (.lit bias)
  , .binop rT2 .sub (.reg rLb) (.lit bias)
  , .binop rT2 .mul (.reg rT2) (.reg rT1)
  , .binop rT3 .sub (.lit bias) (.reg rLb)
  , .binop rG .sub (.lit 1) (.reg rT1)
  , .binop rT3 .mul (.reg rT3) (.reg rG)
  , .binop rAbsN .add (.reg rT2) (.reg rT3) ]

/-- `star(n) = acc + |L(n)| + n`: the `w = 1` term needs no cell. -/
def starBlock : List Instr :=
  [ .binop rSt .add (.reg rAcc) (.reg rAbsN)
  , .binop rSt .add (.reg rSt) (.reg rN) ]

/-- The block maximum, the compared value, and the check gate. -/
def gateBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .gt (.reg rSt) (.reg rMax)
  , .binop rT2 .sub (.lit 1) (.reg rT1)
  , .binop rT3 .mul (.reg rT1) (.reg rSt)
  , .binop rT2 .mul (.reg rT2) (.reg rMax)
  , .binop rMx .add (.reg rT3) (.reg rT2)
  , .binop rT1 .lt (.reg rN) (.lit 64)
  , .binop rT2 .sub (.lit 1) (.reg rT1)
  , .binop rT3 .mul (.reg rT1) (.reg rSt)
  , .binop rG .mul (.reg rT2) (.reg rMx)
  , .binop rCv .add (.reg rT3) (.reg rG)
  , .binop rT2 .eq (.reg rN) (.lit c.limit)
  , .binop rT3 .mul (.lit 2) (.reg rBs)
  , .binop rG .add (.lit 1) (.reg rN)
  , .binop rG .eq (.reg rG) (.reg rT3)
  , .binop rFire .bor (.reg rT1) (.reg rT2)
  , .binop rFire .bor (.reg rFire) (.reg rG) ]

/-- `incUWord n` instruction for instruction (`Ports/RS62Increments.lean`),
the gated ladder advance, and the logarithm the check uses. -/
def ladderBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .mul (.lit 2) (.reg rN)
  , .binop rT1 .add (.lit fpD3) (.reg rT1)
  , .binop rT2 .add (.lit fpD3) (.reg rN)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT2 .udiv (.reg rT2) (.reg rN)
  , .binop rT1 .sub (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.lit 2) (.reg rN)
  , .binop rT1 .udiv (.reg rT1) (.reg rT2)
  , .binop rT2 .add (.lit fpDlit) (.reg rN)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT1 .sub (.reg rT2) (.reg rT1)
  , .binop rT2 .sub (.reg rN) (.lit 1)
  , .binop rIU .udiv (.reg rT1) (.reg rT2)
  , .binop rT1 .ge (.reg rN) (.lit c.handoff)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rT1 .mul (.reg rT1) (.reg rIU)
  , .binop rLam .add (.reg rLam) (.reg rT1)
  , .binop rT1 .lt (.reg rN) (.lit c.handoff)
  , .binop rT2 .sub (.lit 1) (.reg rT1)
  , .binop rT3 .mul (.reg rT1) (.reg rV)
  , .binop rG .mul (.reg rT2) (.reg rLam)
  , .binop rLU .add (.reg rT3) (.reg rG) ]

/-- The row test `5·star·logUp ≤ 4·2⁴⁸·2⁴⁸`, as a 128-bit comparison through
the half-limb product circuit of `Verified/MulWide.lean`. -/
def productBlock : List Instr :=
  [ .binop rT1 .mul (.lit 5) (.reg rCv)
  , .binop rT2 .urem (.reg rT1) (.lit b32)
  , .binop rT3 .udiv (.reg rT1) (.lit b32)
  , .binop rG .urem (.reg rLU) (.lit b32)
  , .binop rH .udiv (.reg rLU) (.lit b32)
  , .binop rP00 .mul (.reg rT2) (.reg rG)
  , .binop rP01 .mul (.reg rT2) (.reg rH)
  , .binop rP10 .mul (.reg rT3) (.reg rG)
  , .binop rP11 .mul (.reg rT3) (.reg rH)
  , .binop rMid .add (.reg rP01) (.reg rP10)
  , .binop rCM .lt (.reg rMid) (.reg rP01)
  , .binop rT2 .mul (.lit b32) (.reg rMid)
  , .binop rLo .add (.reg rP00) (.reg rT2)
  , .binop rCL .lt (.reg rLo) (.reg rP00)
  , .binop rHi .udiv (.reg rMid) (.lit b32)
  , .binop rHi .add (.reg rHi) (.reg rP11)
  , .binop rT2 .mul (.lit b32) (.reg rCM)
  , .binop rHi .add (.reg rHi) (.reg rT2)
  , .binop rHi .add (.reg rHi) (.reg rCL)
  , .binop rT1 .lt (.reg rHi) (.lit rhsHi)
  , .binop rT2 .eq (.reg rHi) (.lit rhsHi)
  , .binop rT3 .eq (.reg rLo) (.lit 0)
  , .binop rT2 .mul (.reg rT2) (.reg rT3)
  , .binop rOk .bor (.reg rT1) (.reg rT2) ]

/-- The violation counter: one for a failed row, and one for every quantity
that leaves its declared cap — so a `0` verdict certifies the width budget as
well as the rows. -/
def badBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .sub (.lit 1) (.reg rOk)
  , .binop rT1 .mul (.reg rT1) (.reg rFire)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rBad .add (.reg rBad) (.reg rT1)
  , .binop rT2 .gt (.reg rAcc) (.lit c.capS)
  , .binop rT3 .gt (.reg rAbs) (.lit c.capL)
  , .binop rT2 .bor (.reg rT2) (.reg rT3)
  , .binop rT2 .mul (.reg rT2) (.reg rW)
  , .binop rBad .add (.reg rBad) (.reg rT2)
  , .binop rT2 .gt (.reg rSt) (.lit c.capS)
  , .binop rT3 .gt (.reg rAbsN) (.lit c.capL)
  , .binop rT2 .bor (.reg rT2) (.reg rT3)
  , .binop rT3 .gt (.reg rLam) (.lit c.capLog)
  , .binop rT2 .bor (.reg rT2) (.reg rT3)
  , .binop rT2 .mul (.reg rT2) (.reg rC)
  , .binop rBad .add (.reg rBad) (.reg rT2) ]

/-- The carried state at the commit: the packed cell, the block maximum, the
block start and the log slot. -/
def updateBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .mul (.lit pack) (.reg rMun)
  , .binop rT1 .add (.reg rT1) (.reg rAbsN)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rT2 .sub (.lit 1) (.reg rC)
  , .binop rT2 .mul (.reg rT2) (.reg rCell)
  , .binop rCell .add (.reg rT1) (.reg rT2)
  , .binop rT1 .sub (.lit 1) (.reg rFire)
  , .binop rT1 .mul (.reg rT1) (.reg rMx)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rT2 .sub (.lit 1) (.reg rC)
  , .binop rT2 .mul (.reg rT2) (.reg rMax)
  , .binop rMax .add (.reg rT1) (.reg rT2)
  , .binop rT1 .lt (.reg rN) (.lit 64)
  , .binop rT2 .mul (.lit 64) (.reg rT1)
  , .binop rT3 .sub (.lit 1) (.reg rT1)
  , .binop rG .add (.lit 1) (.reg rN)
  , .binop rG .mul (.reg rG) (.reg rFire)
  , .binop rH .sub (.lit 1) (.reg rFire)
  , .binop rH .mul (.reg rH) (.reg rBs)
  , .binop rG .add (.reg rG) (.reg rH)
  , .binop rG .mul (.reg rG) (.reg rT3)
  , .binop rT2 .add (.reg rT2) (.reg rG)
  , .binop rT2 .mul (.reg rT2) (.reg rC)
  , .binop rT3 .sub (.lit 1) (.reg rC)
  , .binop rT3 .mul (.reg rT3) (.reg rBs)
  , .binop rBs .add (.reg rT2) (.reg rT3)
  , .binop rT1 .mul (.reg rC) (.reg rFire)
  , .binop rIdx .add (.reg rIdx) (.reg rT1)
  , .binop rIdx .urem (.reg rIdx) (.lit c.tab) ]

/-- Everything before the array read. -/
def msPre (c : Cfg) : List Instr :=
  decodeBlock c ++ scanBlock ++ selectBlock ++ indexBlock c

/-- Everything after it. -/
def msPost (c : Cfg) : List Instr :=
  unpackBlock ++ termBlock ++ latchBlock ++ muBlock ++ lbBlock ++ starBlock ++
    gateBlock c ++ ladderBlock c ++ productBlock ++ badBlock c ++ updateBlock c

/-- The loop body: one `load` in the middle, one `store` at the end. -/
def msBody (c : Cfg) : List AInstr :=
  lift (msPre c) ++ (.load rV rI :: lift (msPost c)) ++ [.store rN rCell]

/-- Initialization: the carried registers, the cell for `q = 1`, and the log
constants. -/
def msInit (c : Cfg) : List AInstr :=
  lift [ .mov rLb (.lit (bias + fpDlit))
       , .mov rLam (.lit c.seed)
       , .mov rBs (.lit 64)
       , .mov rCell (.lit c.cell1)
       , .mov rMuQ (.lit 2)
       , .mov rT1 (.lit 1)
       , .mov rT2 (.lit c.cell1) ] ++
  [ .store rT1 rT2 ] ++
  c.logs.flatMap (fun e =>
    [ .scalar (.mov rT1 (.lit (c.limit + 1 + e.1)))
    , .scalar (.mov rT2 (.lit e.2))
    , .store rT1 rT2 ])

/-- **The artifact.** -/
def msProgram (c : Cfg) : AProgram :=
  { regCount := msRegCount
  , arrayLen := c.limit + 1 + c.tab
  , loopCount := c.len * c.B
  , init := msInit c
  , body := msBody c
  , epilogue := []
  , output := rBad }

/-! ## Well-formedness -/

/-- Register bounds for one operand, as a Boolean. -/
def operandOK : Operand → Bool
  | .reg j => decide (j < msRegCount)
  | _ => true

/-- Register bounds for a scalar instruction, as a Boolean. -/
def instrOK : Instr → Bool
  | .mov d src => decide (d < msRegCount) && operandOK src
  | .binop d _ l r => decide (d < msRegCount) && operandOK l && operandOK r

theorem operand_wf_of_ok {o : Operand} (h : operandOK o = true) :
    o.WF msRegCount := by
  cases o with
  | reg j => simpa [operandOK, Operand.WF] using h
  | lit v => exact trivial
  | idx => exact trivial

theorem wf_of_instrOK {i : Instr} (h : instrOK i = true) : i.WF msRegCount := by
  cases i with
  | mov d src =>
      simp only [instrOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, operand_wf_of_ok h.2⟩
  | binop d op l r =>
      simp only [instrOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, operand_wf_of_ok h.1.2, operand_wf_of_ok h.2⟩

theorem lift_wf {xs : List Instr} (h : xs.all instrOK = true) :
    ∀ a ∈ lift xs, a.WF msRegCount := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_lift ha
  exact wf_of_instrOK ((List.all_eq_true.mp h) i hi)

theorem msPre_ok (c : Cfg) : (msPre c).all instrOK = true := by
  simp +decide [msPre, decodeBlock, scanBlock, selectBlock, indexBlock,
    List.all_append, instrOK, operandOK, msRegCount, rBad, rLb, rLam, rIdx,
    rBs, rMax, rAcc, rS, rMuQ, rCell, rN, rR, rD, rSq, rW, rQg, rC, rZ, rP,
    rQ, rQq, rI, rV, rMu1, rAbs, rMun, rAbsN, rSt, rMx, rCv, rFire, rLU, rIU,
    rDn, rOk, rLo, rHi, rMid, rP00, rP01, rP10, rP11, rCM, rCL, rT1, rT2, rT3,
    rG, rH]

theorem msPost_ok (c : Cfg) : (msPost c).all instrOK = true := by
  simp +decide [msPost, unpackBlock, termBlock, latchBlock, muBlock, lbBlock,
    starBlock, gateBlock, ladderBlock, productBlock, badBlock, updateBlock,
    List.all_append, instrOK, operandOK, msRegCount, rBad, rLb, rLam, rIdx,
    rBs, rMax, rAcc, rS, rMuQ, rCell, rN, rR, rD, rSq, rW, rQg, rC, rZ, rP,
    rQ, rQq, rI, rV, rMu1, rAbs, rMun, rAbsN, rSt, rMx, rCv, rFire, rLU, rIU,
    rDn, rOk, rLo, rHi, rMid, rP00, rP01, rP10, rP11, rCM, rCL, rT1, rT2, rT3,
    rG, rH]

theorem msBody_wf (c : Cfg) : ∀ a ∈ msBody c, a.WF msRegCount := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · rcases List.mem_append.mp h with h | h
    · exact lift_wf (msPre_ok c) a h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by simp [msRegCount, rV], by simp [msRegCount, rI]⟩
      · exact lift_wf (msPost_ok c) a h
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by simp [msRegCount, rN], by simp [msRegCount, rCell]⟩
    · exact absurd h (by simp)

theorem msInit_wf (c : Cfg) : ∀ a ∈ msInit c, a.WF msRegCount := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · rcases List.mem_append.mp h with h | h
    · refine lift_wf ?_ a h
      simp +decide [instrOK, operandOK, msRegCount, rLb, rLam, rBs, rCell, rMuQ,
        rT1, rT2]
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by simp [msRegCount, rT1], by simp [msRegCount, rT2]⟩
      · exact absurd h (by simp)
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨by simp [msRegCount, rT1], trivial⟩
    · exact ⟨by simp [msRegCount, rT2], trivial⟩
    · exact ⟨by simp [msRegCount, rT1], by simp [msRegCount, rT2]⟩

/-- **The program is well formed** at every configuration, so
`AProgram.evalCC_compile` applies: the compiled trace and the emitted C
compute exactly `AProgram.denote`. -/
theorem msProgram_wf (c : Cfg) : (msProgram c).WF := by
  refine ⟨by simp [msProgram, msRegCount, rBad], ?_, ?_, ?_⟩
  · exact msInit_wf c
  · exact msBody_wf c
  · intro a ha
    exact absurd ha (by simp [msProgram])


/-! ## The candidate-level reference

An independently written mirror of what one candidate contributes.  It carries
the machine's `% 2⁶⁴` at every point the machine has one, so the kernel smoke
checks below compare two genuinely different transcriptions of the same
computation: `msRef` at candidate granularity against the 182-instruction body
run `len · B` times.
-/

/-- `(a + b) % 2⁶⁴`. -/
def MA (a b : Nat) : Nat := (a + b) % M
/-- `(a − b) % 2⁶⁴`, the machine's wrapping subtraction. -/
def MS (a b : Nat) : Nat := (a + (M - b)) % M
/-- `(a · b) % 2⁶⁴`. -/
def MMul (a b : Nat) : Nat := (a * b) % M
/-- A comparison result, as the machine materialises it. -/
def bitOf (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The observable machine state at candidate granularity. -/
structure St where
  /-- Violation counter. -/
  bad : Nat
  /-- `2⁶² + L`. -/
  lb : Nat
  /-- Ladder accumulator. -/
  lam : Nat
  /-- Log slot. -/
  idx : Nat
  /-- Dyadic block start. -/
  bs : Nat
  /-- Dyadic block maximum. -/
  mx : Nat
  /-- Packed cell to store. -/
  cell : Nat
  /-- The array. -/
  arr : Nat → Nat

/-- One work round: the trial scan and one `w`-term, with the caps. -/
def workRound (c : Cfg) (arr : Nat → Nat) (n : Nat)
    (x : Nat × Nat × Nat) (r : Nat) : Nat × Nat × Nat :=
  let d := r + 2
  let sq := MMul d d
  let g := bitOf (x.2.2 = 0 ∧ sq ≤ n ∧ n % d = 0)
  let s' := MA (MMul (MS 1 g) x.2.2) (MMul g d)
  let q := n / sq
  let v := arr q
  let mu1 := v >>> 52
  let ab := MS v ((mu1 <<< 52) % M)
  let term := MMul ((MS (MA (MA ab q) sq) 1) / sq) 1
  let acc' := MA x.2.1 term
  let bad' := MA x.1 (bitOf (c.capS < acc' ∨ c.capL < ab))
  (bad', acc', s')

/-- All `B − 2` work rounds of one candidate. -/
def workFold (c : Cfg) (arr : Nat → Nat) (n bad : Nat) : Nat × Nat × Nat :=
  (List.range (c.B - 2)).foldl (workRound c arr n) (bad, 0, 0)

/-- **What one candidate does.** -/
def msStep (c : Cfg) (n : Nat) (st : St) : St :=
  let w := workFold c st.arr n st.bad
  let acc := w.2.1
  let s := w.2.2
  let p := if s = 0 then n else s
  let qn := n / p
  let muQ := (st.arr qn) >>> 52
  let vlog := st.arr (c.limit + 1 + st.idx)
  let sqdiv := bitOf (qn % p = 0)
  let mun := MA sqdiv (MMul (MS 2 muQ) (MS 1 sqdiv))
  let dn := fpDlit / n
  let lb1 := MS (MA st.lb (MMul (bitOf (mun = 2)) dn)) (MMul (bitOf (mun = 0)) dn)
  let bge := bitOf (bias ≤ lb1)
  let absN := MA (MMul (MS lb1 bias) bge) (MMul (MS bias lb1) (MS 1 bge))
  let star := MA (MA acc absN) n
  let gt := bitOf (st.mx < star)
  let mx := MA (MMul gt star) (MMul (MS 1 gt) st.mx)
  let small := bitOf (n < 64)
  let cv := MA (MMul small star) (MMul (MS 1 small) mx)
  let fire := bitOf (n < 64 ∨ n = c.limit ∨ MA 1 n = MMul 2 st.bs)
  let iu := incUWord n
  let lam1 := MA st.lam (MMul (bitOf (c.handoff ≤ n)) iu)
  let lo := bitOf (n < c.handoff)
  let lu := MA (MMul lo vlog) (MMul (MS 1 lo) lam1)
  let hl := Verified.MulWide.hl (MMul 5 cv) lu
  let ok := bitOf (hl.2 < rhsHi ∨ (hl.2 = rhsHi ∧ hl.1 = 0))
  let bad2 := MA w.1 (MMul (MS 1 ok) fire)
  let bad3 := MA bad2 (bitOf (c.capS < star ∨ c.capL < absN ∨ c.capLog < lam1))
  { bad := bad3
  , lb := lb1
  , lam := lam1
  , idx := MA st.idx fire % c.tab
  , bs := MA (MMul 64 small) (MMul (MS 1 small)
      (MA (MMul (MA 1 n) fire) (MMul (MS 1 fire) st.bs)))
  , mx := MMul (MS 1 fire) mx
  , cell := MA (MMul pack mun) absN
  , arr := fun i => if i = n then MA (MMul pack mun) absN else st.arr i }

/-- Last-store-wins view of the log table. -/
def logAt (c : Cfg) (i : Nat) : Nat :=
  (((c.logs.reverse.find? (fun e => c.limit + 1 + e.1 = i)).map
    (fun e => e.2)).getD 0) % M

/-- The array after `msInit`. -/
def arr0 (c : Cfg) (i : Nat) : Nat :=
  if c.limit + 1 ≤ i then logAt c i else if i = 1 then c.cell1 % M else 0

/-- The state after `msInit`. -/
def msEntry (c : Cfg) : St :=
  { bad := 0, lb := (bias + fpDlit) % M, lam := c.seed % M, idx := 0
  , bs := 64, mx := 0, cell := c.cell1 % M, arr := arr0 c }

/-- **The whole sweep**, candidate-level; the machine's output is its `bad`. -/
def msRef (c : Cfg) : Nat :=
  ((List.range c.len).foldl (fun st q => msStep c (c.n0 + q) st) (msEntry c)).bad

/-! ## The encoding obligation -/

/-- **The encoding obligation** for a run of `msProgram` to say anything at
all: the program denotes the candidate-level reference. -/
def MSEncoding (c : Cfg) : Prop :=
  msOK c = true → (msProgram c).denote = some (msRef c)


/-! ## Kernel smoke checks

Two tiny configurations exercised in both verdicts.  These evaluate the full
182-instruction body against `msRef` in the kernel — the two are written at
different granularity (flat rounds against candidates), so agreement is a real
cross-check of every gate, clamp and truncation above.
-/

/-- Seven candidates `2 … 8`, three rounds each; the seven direct LeanCert
enclosures `directLogUpper 3 … directLogUpper 9`. -/
def tinyCfg : Cfg :=
  { n0 := 2, len := 7, B := 3, limit := 8, tab := 8, handoff := 10000
  , seed := 2592538163685609, cell1 := 9288674231451648
  , capL := 2251799813685248, capS := 72057594037927936
  , capLog := 72057594037927936
  , logs := [(0, 309236329538252), (1, 390216068699726), (2, 453025394627560),
             (3, 504344363888114), (4, 547734356265810), (5, 585324103049589),
             (6, 618477080267896)] }

theorem tiny_ok : msOK tinyCfg = true := by decide

set_option maxRecDepth 400000 in
example : (msProgram tinyCfg).denote = some (msRef tinyCfg) := by decide

set_option maxRecDepth 400000 in
example : (msProgram tinyCfg).denote = some 0 := by decide

/-- The same sweep with a starving `|L|` cap: the cap violations fire and the
machine still matches the reference. -/
def tinyCfgBad : Cfg :=
  { tinyCfg with capL := 10 }

set_option maxRecDepth 400000 in
example : (msProgram tinyCfgBad).denote = some (msRef tinyCfgBad) := by decide

set_option maxRecDepth 400000 in
example : ∃ v, (msProgram tinyCfgBad).denote = some v ∧ 0 < v :=
  ⟨msRef tinyCfgBad, by decide, by decide⟩

end LeanCompCert.Ports.RamareMStar140M
