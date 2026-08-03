import LeanCompCert.Ports.Section413Sweep
import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Ports.CDEMAbelScan

/-!
# The §4.1.3 `g₂` sweep as an array program

The ARRAY-MACHINE stage of the §4.1.3 conversion, `g₂` instance (atom 2):
one `AProgram` intended to compute `Section413Sweep.g2SweepOK R checkLo N`
— the model Boolean that `claude_math` has already proved implies the
production atom at `(R, checkLo, N) = (999, 33, 10⁶)`.

## Shape

One flat loop, `(N−1)·R + N·(2S+2)` rounds (`S = ⌊√N⌋`), branchless, every
round executing the whole body with inactive stages gated to no-ops:

* **Phase 1** (`idx < (N−1)·R`, candidate-major): trial division of
  `n = idx/R + 2` by `d = idx%R + 2`, carrying `(res, sq, par)` in
  registers — exactly `MertensCDEM.trialStep`, so the downstream μ bridge
  applies verbatim.  At `d`'s last round the μ code (`0/1/2`) is written to
  plane 0.  `μ(1) = +1` is seeded by the init block.
* **Phase 2** (per candidate `X = 1 … N`, fixed `2S+2` rounds each):
  - rounds `0 … S−1` (**pass A**): `σ(X)` by `√`-pairing, gated on
    `r² ≤ X ∧ r ∣ X` — the same divisor set as `sigmaPair`;
  - round `S` (**weight**): `w = μ(X)/σ(X)·SCALE` as an outward-rounded
    encoded cell for odd `X`, else the zero cell; then `ww = cmul w w`;
  - rounds `S+1 … 2S` (**pass B**): for divisor `r = pos − S` and its
    partner `X/r` (partner suppressed when equal), the model's `touch`:
    read `acc[d]`, form `deltaTerm = μ(d)·(2·(A·w) + w²)` through the
    sign-magnitude 128-bit product circuit and the exact `10¹⁸` divider of
    `Ports/Section413Cells.lean`, push `w` into the slot, accumulate the
    delta cell;
  - round `2S+1` (**finalize**): `g += delta`, and for `X ≥ checkLo` the
    endpoint test `−21·SCALE ≤ g.lo·10X ∧ g.hi·10X ≤ 21·SCALE` against the
    two-limb literal `21·10¹⁸`, failures OR-ed into register 0.

**Array layout** (`arrayLen = 3(N+1)`): plane 0 = μ codes, plane 1 / plane 2
= the accumulator cells' encoded `lo` / `hi` endpoints.  The zero-filled
initial array *is* the model's all-zero cell table
(`Section413Cells.decodeZ_zero`).

**Runtime width guards** (the C.17 `accCap` discipline): every magnitude
that enters a product, and every accumulator after every update, is tested
against `CAP = 2⁶⁰`; a violation ORs into register 0.  The measured maxima
at the production configuration are all `≤ 10¹⁸ < 2⁶⁰` (see
`bench/ref_section413_g2.c`), so the guards are expected silent — their
role is to make the future simulation proof's no-wrap argument *per-step*:
with the flag still `0`, no `u64` truncation has occurred in any signed
quantity, and products stay below `10¹⁸·2⁶⁴`, inside `divP18q_spec`'s cap.

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`:

* `g2Program_wf` — well-formedness, for every configuration; hence
* `g2Program_compiled` — `AProgram.evalCC_compile` instantiated: the
  compiled CCIR trace (and through `Verified.MemFragment` the emitted C)
  computes exactly `(g2Program c).denote`.

**Not proved here** (stated as the two obligations they are; nothing below
asserts them):

1. `(g2Program c).denote = some (tFlag c)` — that the machine denotes the
   transparent model `tstep`/`tRun` below.  The intended route is the
   per-stage `arun` specs against `AllDefined` (the
   `ArrayMobiusDenotation`/`SingSeriesC17` architecture) assembled by
   `Verified.Algorithm.ArrayBridge.ArrayLoop`.
2. `tFlag c = 0 → g2SweepOK c.rounds c.checkLo c.cap = true` — that the
   transparent model with a clean flag equals the reference model.  The
   intended route is the encode/decode and divider lemmas of
   `Ports/Section413Cells.lean` under the guard invariant.

Until both land, a run of the emitted artifact is evidence about the C
only; the campaign registry entry `section413_g2_small_1e6` carries
`evaluates_atom_predicate: false` accordingly.

The transparent model *is* executable: `bench/Section413SweepEmit.lean`'s
`check` mode runs `tRun` against `g2Run` at small configurations and the
independent C oracle `bench/ref_section413_g2.c` covers the production
configuration; the emitted artifact's flag can then be compared against
both.
-/

namespace LeanCompCert.Ports.Section413G2Program

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB instrWFB operandWFB
  forall_wf_of_all all_append)
open LeanCompCert.Ports.CDEMAbelScan (mulWideBody muxBody storeLit)

/-! ## §1 Constants -/

/-- The fixed-point scale `10¹⁸`. -/
def SCALE : Nat := 1000000000000000000

/-- The uniform runtime magnitude cap `2⁶⁰`.  Measured production maxima
are `≤ 10¹⁸`, fifteen percent inside. -/
def CAP : Nat := 1152921504606846976

/-- `2⁶³`, the two's-complement sign boundary. -/
def H63 : Nat := 9223372036854775808

/-- `5¹⁸`, the odd part of the scale. -/
def D5 : Nat := 3814697265625

/-- `21·10¹⁸ − 2⁶⁴`: the low limb of the check threshold `21·10¹⁸`,
whose high limb is `1`. -/
def KLO : Nat := 2553255926290448384

/-! ## §2 Configuration -/

/-- Everything the emitted program depends on. -/
structure Cfg where
  /-- The candidate cap `N`.  `10⁶` in production. -/
  cap : Nat
  /-- Trial-division rounds `R`: divisors `2 … R+1`.  `999` in production. -/
  rounds : Nat
  /-- First checked candidate.  `33` in production. -/
  checkLo : Nat
  deriving Repr

/-- `S = ⌊√N⌋`: the pass length of the divisor pairing. -/
def Cfg.s (c : Cfg) : Nat := Nat.sqrt c.cap

/-- Rounds per candidate in phase 2. -/
def Cfg.p (c : Cfg) : Nat := 2 * c.s + 2

/-- Length of phase 1. -/
def Cfg.phase1 (c : Cfg) : Nat := (c.cap - 1) * c.rounds

def Cfg.loopCount (c : Cfg) : Nat := c.phase1 + c.cap * c.p

/-- Plane 1 base: accumulator `lo` endpoints. -/
def Cfg.plane1 (c : Cfg) : Nat := c.cap + 1

/-- Plane 2 base: accumulator `hi` endpoints. -/
def Cfg.plane2 (c : Cfg) : Nat := 2 * (c.cap + 1)

def Cfg.arrayLen (c : Cfg) : Nat := 3 * (c.cap + 1)

/-- The production configuration. -/
def production : Cfg := ⟨1000000, 999, 33⟩

/-- The smoke configuration: same `R`, small cap. -/
def smoke : Cfg := ⟨2000, 999, 33⟩

/-! ## §3 Register allocation

Persistent (live across iterations):

| reg | name | holds |
| --- | ---- | ----- |
| 0 | `rViol` | the output: OR of all failed checks and guards |
| 1 | `rZero` | the constant `0` |
| 2–4 | `rRes rSq rPar` | the phase-1 trial-division state |
| 5 | `rSigma` | pass A's running `σ(X)` |
| 6–7 | `rWLo rWHi` | the weight cell `w`, encoded |
| 8–9 | `rWWLo rWWHi` | `ww = cmul w w`, encoded |
| 10–11 | `rDLo rDHi` | the delta cell of the current `X` |
| 12–13 | `rGLo rGHi` | the running `g` cell |

Scratch: 20–39 decode, 40–55 trial, 56–70 pass A, 71–99 weight,
100–179 the `cmul` block, 180–209 touch, 210–219 pass-B gates,
220–255 finalize; 240–241 are also the init block's store scratch.
-/

def regCount : Nat := 256
def rViol : Nat := 0

/-! ## §4 Reusable blocks -/

/-- Accumulator width guard: OR `viol` with `gate` when the encoded `w`
decodes outside `[−CAP, CAP]` (`(w + CAP) mod 2⁶⁴ > 2·CAP`). -/
def guardBody (gate w s : Nat) : List AInstr :=
  [ .scalar (.binop s .add (.reg w) (.lit CAP))
  , .scalar (.binop s .gt (.reg s) (.lit (2 * CAP)))
  , .scalar (.binop s .mul (.reg s) (.reg gate))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg s)) ]

/-- Decompose the encoded word `w` into a sign bit (`s`) and a magnitude
(`m`), and guard the magnitude against `CAP` (gated).  Scratch: 108–110. -/
def smDecomp (gate w s m : Nat) : List AInstr :=
  [ .scalar (.binop s .ge (.reg w) (.lit H63))
  , .scalar (.binop 108 .sub (.lit 0) (.reg w)) ]
  ++ muxBody m s 108 w 109
  ++ [ .scalar (.binop 110 .gt (.reg m) (.lit CAP))
     , .scalar (.binop 110 .mul (.reg 110) (.reg gate))
     , .scalar (.binop rViol .bor (.reg rViol) (.reg 110)) ]

/-- Strict signed comparison of two canonical sign-magnitude 128-bit
triples: `dst := (sa,la,ha) < (sb,lb,hb)`.  Scratch: 126–131, 139–143. -/
def cmpLtBody (sa la ha sb lb hb dst : Nat) : List AInstr :=
  [ .scalar (.binop 126 .lt (.reg ha) (.reg hb))
  , .scalar (.binop 127 .eq (.reg ha) (.reg hb))
  , .scalar (.binop 128 .lt (.reg la) (.reg lb))
  , .scalar (.binop 129 .lt (.reg hb) (.reg ha))
  , .scalar (.binop 130 .lt (.reg lb) (.reg la))
  , .scalar (.binop 131 .mul (.reg 127) (.reg 128))
  , .scalar (.binop 131 .add (.reg 131) (.reg 126))     -- |a| < |b|
  , .scalar (.binop 139 .mul (.reg 127) (.reg 130))
  , .scalar (.binop 139 .add (.reg 139) (.reg 129))     -- |b| < |a|
  , .scalar (.binop 140 .sub (.lit 1) (.reg sb))
  , .scalar (.binop 141 .mul (.reg sa) (.reg 140))      -- a neg, b nonneg
  , .scalar (.binop 142 .mul (.reg sa) (.reg sb))
  , .scalar (.binop 142 .mul (.reg 142) (.reg 139))     -- both neg
  , .scalar (.binop 143 .sub (.lit 1) (.reg sa))
  , .scalar (.binop 143 .mul (.reg 143) (.reg 140))
  , .scalar (.binop 143 .mul (.reg 143) (.reg 131))     -- both nonneg
  , .scalar (.binop dst .add (.reg 141) (.reg 142))
  , .scalar (.binop dst .add (.reg dst) (.reg 143)) ]

/-- Triple select: `(sd,ld,hd) := t ? (sa,la,ha) : (sb,lb,hb)`.
Scratch: 144. -/
def selTriple (t sa la ha sb lb hb sd ld hd : Nat) : List AInstr :=
  muxBody sd t sa sb 144 ++ muxBody ld t la lb 144 ++ muxBody hd t ha hb 144

/-- The exact `10¹⁸` divider of `Ports/Section413Cells.lean`, as
instructions: magnitude `(lo, hi)` to floor quotient `q` and ceiling `qc`.
Shift right 18, then base-`2²²` long division by `5¹⁸`, five digits, one
`udiv`/`urem` each; exactness decided from `lo`'s low 18 bits and the last
remainder.  Scratch: 168–175. -/
def divP18Body (lo hi q qc : Nat) : List AInstr :=
  [ .scalar (.binop 168 .lshr (.reg lo) (.lit 18))
  , .scalar (.binop 169 .shl (.reg hi) (.lit 46))
  , .scalar (.binop 168 .add (.reg 168) (.reg 169))     -- yLo
  , .scalar (.binop 169 .lshr (.reg hi) (.lit 18))      -- yHi
    -- digit 4
  , .scalar (.binop 170 .lshr (.reg 169) (.lit 24))
  , .scalar (.binop q .udiv (.reg 170) (.lit D5))
  , .scalar (.binop 172 .urem (.reg 170) (.lit D5))
    -- digit 3
  , .scalar (.binop 173 .lshr (.reg 169) (.lit 2))
  , .scalar (.binop 173 .band (.reg 173) (.lit 4194303))
  , .scalar (.binop 170 .mul (.reg 172) (.lit 4194304))
  , .scalar (.binop 170 .add (.reg 170) (.reg 173))
  , .scalar (.binop 171 .udiv (.reg 170) (.lit D5))
  , .scalar (.binop q .mul (.reg q) (.lit 4194304))
  , .scalar (.binop q .add (.reg q) (.reg 171))
  , .scalar (.binop 172 .urem (.reg 170) (.lit D5))
    -- digit 2 (spans the word boundary)
  , .scalar (.binop 173 .lshr (.reg 168) (.lit 44))
  , .scalar (.binop 174 .band (.reg 169) (.lit 3))
  , .scalar (.binop 174 .mul (.reg 174) (.lit 1048576))
  , .scalar (.binop 173 .add (.reg 173) (.reg 174))
  , .scalar (.binop 170 .mul (.reg 172) (.lit 4194304))
  , .scalar (.binop 170 .add (.reg 170) (.reg 173))
  , .scalar (.binop 171 .udiv (.reg 170) (.lit D5))
  , .scalar (.binop q .mul (.reg q) (.lit 4194304))
  , .scalar (.binop q .add (.reg q) (.reg 171))
  , .scalar (.binop 172 .urem (.reg 170) (.lit D5))
    -- digit 1
  , .scalar (.binop 173 .lshr (.reg 168) (.lit 22))
  , .scalar (.binop 173 .band (.reg 173) (.lit 4194303))
  , .scalar (.binop 170 .mul (.reg 172) (.lit 4194304))
  , .scalar (.binop 170 .add (.reg 170) (.reg 173))
  , .scalar (.binop 171 .udiv (.reg 170) (.lit D5))
  , .scalar (.binop q .mul (.reg q) (.lit 4194304))
  , .scalar (.binop q .add (.reg q) (.reg 171))
  , .scalar (.binop 172 .urem (.reg 170) (.lit D5))
    -- digit 0
  , .scalar (.binop 173 .band (.reg 168) (.lit 4194303))
  , .scalar (.binop 170 .mul (.reg 172) (.lit 4194304))
  , .scalar (.binop 170 .add (.reg 170) (.reg 173))
  , .scalar (.binop 171 .udiv (.reg 170) (.lit D5))
  , .scalar (.binop q .mul (.reg q) (.lit 4194304))
  , .scalar (.binop q .add (.reg q) (.reg 171))
  , .scalar (.binop 172 .urem (.reg 170) (.lit D5))
    -- ceiling
  , .scalar (.binop 174 .band (.reg lo) (.lit 262143))
  , .scalar (.binop 174 .eq (.reg 174) (.lit 0))
  , .scalar (.binop 175 .eq (.reg 172) (.lit 0))
  , .scalar (.binop 174 .mul (.reg 174) (.reg 175))     -- exact
  , .scalar (.binop qc .sub (.lit 1) (.reg 174))
  , .scalar (.binop qc .add (.reg qc) (.reg q)) ]

/-- The outward-rounded interval product `cmul` on encoded cells:
`(cLo, cHi) := cmul (aLo, aHi) (bLo, bHi)`, with the four input magnitudes
guarded against `CAP` (gated by `gate`).  Sign-magnitude decomposition,
four `MulWide.hl` products, canonicalized signs, branchless 4-way min and
max, then one exact `10¹⁸` division each with the rounding chosen by the
result sign.  Scratch: 100–179 (see the register map). -/
def cmulBody (gate aLo aHi bLo bHi cLo cHi : Nat) : List AInstr :=
  smDecomp gate aLo 100 104 ++ smDecomp gate aHi 101 105 ++
  smDecomp gate bLo 102 106 ++ smDecomp gate bHi 103 107 ++
  mulWideBody 104 106 111 112 154 155 156 157 158 159 160 161 ++
  mulWideBody 104 107 113 114 154 155 156 157 158 159 160 161 ++
  mulWideBody 105 106 115 116 154 155 156 157 158 159 160 161 ++
  mulWideBody 105 107 117 118 154 155 156 157 158 159 160 161 ++
  [ .scalar (.binop 119 .bxor (.reg 100) (.reg 102))
  , .scalar (.binop 123 .eq (.reg 111) (.lit 0))
  , .scalar (.binop 124 .eq (.reg 112) (.lit 0))
  , .scalar (.binop 125 .mul (.reg 123) (.reg 124))
  , .scalar (.binop 125 .sub (.lit 1) (.reg 125))
  , .scalar (.binop 119 .mul (.reg 119) (.reg 125))     -- sign p1, canonical
  , .scalar (.binop 120 .bxor (.reg 100) (.reg 103))
  , .scalar (.binop 123 .eq (.reg 113) (.lit 0))
  , .scalar (.binop 124 .eq (.reg 114) (.lit 0))
  , .scalar (.binop 125 .mul (.reg 123) (.reg 124))
  , .scalar (.binop 125 .sub (.lit 1) (.reg 125))
  , .scalar (.binop 120 .mul (.reg 120) (.reg 125))     -- sign p2
  , .scalar (.binop 121 .bxor (.reg 101) (.reg 102))
  , .scalar (.binop 123 .eq (.reg 115) (.lit 0))
  , .scalar (.binop 124 .eq (.reg 116) (.lit 0))
  , .scalar (.binop 125 .mul (.reg 123) (.reg 124))
  , .scalar (.binop 125 .sub (.lit 1) (.reg 125))
  , .scalar (.binop 121 .mul (.reg 121) (.reg 125))     -- sign p3
  , .scalar (.binop 122 .bxor (.reg 101) (.reg 103))
  , .scalar (.binop 123 .eq (.reg 117) (.lit 0))
  , .scalar (.binop 124 .eq (.reg 118) (.lit 0))
  , .scalar (.binop 125 .mul (.reg 123) (.reg 124))
  , .scalar (.binop 125 .sub (.lit 1) (.reg 125))
  , .scalar (.binop 122 .mul (.reg 122) (.reg 125)) ]   -- sign p4
  ++ cmpLtBody 119 111 112 120 113 114 132              -- p1 < p2
  ++ cmpLtBody 121 115 116 122 117 118 133              -- p3 < p4
  ++ selTriple 132 119 111 112 120 113 114 134 135 136  -- min12
  ++ selTriple 132 120 113 114 119 111 112 137 138 153  -- max12
  ++ selTriple 133 121 115 116 122 117 118 162 163 164  -- min34
  ++ selTriple 133 122 117 118 121 115 116 165 166 167  -- max34
  ++ cmpLtBody 134 135 136 162 163 164 176              -- min12 < min34
  ++ cmpLtBody 137 138 153 165 166 167 177              -- max12 < max34
  ++ selTriple 176 134 135 136 162 163 164 134 135 136  -- MIN
  ++ selTriple 177 165 166 167 137 138 153 137 138 153  -- MAX
  ++ divP18Body 135 136 178 179
  ++ [ .scalar (.binop 108 .sub (.lit 0) (.reg 179))    -- enc(−⌈min/SCALE⌉)
     , .scalar (.binop 109 .sub (.lit 1) (.reg 134))
     , .scalar (.binop cLo .mul (.reg 109) (.reg 178))
     , .scalar (.binop 108 .mul (.reg 134) (.reg 108))
     , .scalar (.binop cLo .add (.reg cLo) (.reg 108)) ]
  ++ divP18Body 138 153 178 179
  ++ [ .scalar (.binop 108 .sub (.lit 0) (.reg 178))    -- enc(−⌊max/SCALE⌋)
     , .scalar (.binop 109 .sub (.lit 1) (.reg 137))
     , .scalar (.binop cHi .mul (.reg 109) (.reg 179))
     , .scalar (.binop 108 .mul (.reg 137) (.reg 108))
     , .scalar (.binop cHi .add (.reg cHi) (.reg 108)) ]

/-! ## §5 The six body stages -/

/-- Selectors and index decode. -/
def Cfg.selBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 20 .lt .idx (.lit c.phase1))              -- inP1
  , .scalar (.binop 21 .sub (.lit 1) (.reg 20))               -- inP2
  , .scalar (.binop 22 .udiv .idx (.lit c.rounds))
  , .scalar (.binop 23 .urem .idx (.lit c.rounds))
  , .scalar (.binop 24 .add (.reg 22) (.lit 2))               -- n = candidate
  , .scalar (.binop 25 .add (.reg 23) (.lit 2))               -- d = divisor
  , .scalar (.binop 26 .eq (.reg 23) (.lit 0))
  , .scalar (.binop 26 .mul (.reg 26) (.reg 20))              -- first round of n
  , .scalar (.binop 27 .eq (.reg 23) (.lit (c.rounds - 1)))
  , .scalar (.binop 27 .mul (.reg 27) (.reg 20))              -- last round of n
  , .scalar (.binop 28 .sub .idx (.lit c.phase1))
  , .scalar (.binop 29 .udiv (.reg 28) (.lit c.p))
  , .scalar (.binop 30 .urem (.reg 28) (.lit c.p))            -- pos in block
  , .scalar (.binop 31 .add (.reg 29) (.lit 1))               -- X
  , .scalar (.binop 32 .lt (.reg 30) (.lit c.s))
  , .scalar (.binop 32 .mul (.reg 32) (.reg 21))              -- inA
  , .scalar (.binop 33 .eq (.reg 30) (.lit c.s))
  , .scalar (.binop 33 .mul (.reg 33) (.reg 21))              -- isW
  , .scalar (.binop 34 .ge (.reg 30) (.lit (c.s + 1)))
  , .scalar (.binop 39 .le (.reg 30) (.lit (2 * c.s)))
  , .scalar (.binop 34 .mul (.reg 34) (.reg 39))
  , .scalar (.binop 34 .mul (.reg 34) (.reg 21))              -- inB
  , .scalar (.binop 35 .eq (.reg 30) (.lit (2 * c.s + 1)))
  , .scalar (.binop 35 .mul (.reg 35) (.reg 21))              -- isF
  , .scalar (.binop 36 .add (.reg 30) (.lit 1))               -- pass A r
  , .scalar (.binop 37 .sub (.reg 30) (.lit c.s))
  , .scalar (.binop 38 .eq (.reg 37) (.lit 0))
  , .scalar (.binop 38 .add (.reg 38) (.reg 37)) ]            -- pass B r, or-1

/-- Phase 1: one trial-division round (`MertensCDEM.trialStep` at the
decoded divisor), with the state reset at each candidate's first round and
the μ code written at its last. -/
def trialBody : List AInstr :=
  muxBody 2 26 24 2 40
  ++ [ .scalar (.binop 41 .sub (.lit 1) (.reg 26))
     , .scalar (.binop 3 .mul (.reg 3) (.reg 41))
     , .scalar (.binop 4 .mul (.reg 4) (.reg 41))
     , .scalar (.binop 42 .urem (.reg 2) (.reg 25))
     , .scalar (.binop 43 .eq (.reg 42) (.lit 0))
     , .scalar (.binop 43 .mul (.reg 43) (.reg 20))           -- hit
     , .scalar (.binop 44 .udiv (.reg 2) (.reg 25)) ]
  ++ muxBody 2 43 44 2 45
  ++ [ .scalar (.binop 46 .urem (.reg 2) (.reg 25))
     , .scalar (.binop 47 .eq (.reg 46) (.lit 0))
     , .scalar (.binop 47 .mul (.reg 47) (.reg 43))           -- hit²
     , .scalar (.binop 3 .bor (.reg 3) (.reg 47))
     , .scalar (.binop 4 .bxor (.reg 4) (.reg 43))
     , .scalar (.binop 48 .ne (.reg 2) (.lit 1))
     , .scalar (.binop 49 .bxor (.reg 4) (.reg 48))           -- ω parity
     , .scalar (.binop 50 .sub (.lit 1) (.reg 3))
     , .scalar (.binop 51 .add (.reg 49) (.lit 1))
     , .scalar (.binop 51 .mul (.reg 51) (.reg 50))           -- the μ code
     , .scalar (.binop 52 .mul (.reg 27) (.reg 24))
     , .scalar (.binop 53 .mul (.reg 27) (.reg 51))
     , .store 52 53 ]

/-- Pass A: `σ(X)` over the divisor pairs, reset at each candidate's first
round. -/
def passABody : List AInstr :=
  [ .scalar (.binop 56 .eq (.reg 30) (.lit 0))
  , .scalar (.binop 56 .mul (.reg 56) (.reg 21)) ]
  ++ muxBody 5 56 1 5 57
  ++ [ .scalar (.binop 58 .urem (.reg 31) (.reg 36))
     , .scalar (.binop 59 .eq (.reg 58) (.lit 0))
     , .scalar (.binop 60 .mul (.reg 36) (.reg 36))
     , .scalar (.binop 61 .le (.reg 60) (.reg 31))            -- r² ≤ X
     , .scalar (.binop 62 .mul (.reg 59) (.reg 61))
     , .scalar (.binop 62 .mul (.reg 62) (.reg 32))
     , .scalar (.binop 63 .udiv (.reg 31) (.reg 36))
     , .scalar (.binop 64 .eq (.reg 63) (.reg 36))
     , .scalar (.binop 65 .sub (.lit 1) (.reg 64))
     , .scalar (.binop 65 .mul (.reg 65) (.reg 63))
     , .scalar (.binop 66 .add (.reg 36) (.reg 65))
     , .scalar (.binop 66 .mul (.reg 66) (.reg 62))
     , .scalar (.binop 5 .add (.reg 5) (.reg 66)) ]

/-- The weight round: `w`, then `ww = cmul w w`. -/
def Cfg.weightBody (_c : Cfg) : List AInstr :=
  [ .scalar (.binop 71 .mul (.reg 33) (.reg 31))
  , .load 72 71                                               -- μ code of X
  , .scalar (.binop 73 .eq (.reg 72) (.lit 1))
  , .scalar (.binop 74 .eq (.reg 72) (.lit 2))
  , .scalar (.binop 75 .urem (.reg 31) (.lit 2))
  , .scalar (.binop 76 .eq (.reg 75) (.lit 1))
  , .scalar (.binop 77 .add (.reg 73) (.reg 74))
  , .scalar (.binop 77 .mul (.reg 77) (.reg 76))
  , .scalar (.binop 77 .mul (.reg 77) (.reg 33))              -- live
  , .scalar (.binop 78 .eq (.reg 5) (.lit 0))
  , .scalar (.binop 79 .add (.reg 5) (.reg 78))               -- σ, or-1
  , .scalar (.binop 80 .udiv (.lit SCALE) (.reg 79))          -- ⌊SCALE/σ⌋
  , .scalar (.binop 81 .add (.reg 79) (.lit (SCALE - 1)))
  , .scalar (.binop 81 .udiv (.reg 81) (.reg 79))             -- ⌈SCALE/σ⌉
  , .scalar (.binop 82 .sub (.lit 0) (.reg 81))
  , .scalar (.binop 83 .sub (.lit 0) (.reg 80))
  , .scalar (.binop 84 .mul (.reg 73) (.reg 80))
  , .scalar (.binop 85 .mul (.reg 74) (.reg 82))
  , .scalar (.binop 86 .add (.reg 84) (.reg 85))
  , .scalar (.binop 86 .mul (.reg 86) (.reg 77))              -- w.lo
  , .scalar (.binop 87 .mul (.reg 73) (.reg 81))
  , .scalar (.binop 88 .mul (.reg 74) (.reg 83))
  , .scalar (.binop 89 .add (.reg 87) (.reg 88))
  , .scalar (.binop 89 .mul (.reg 89) (.reg 77)) ]            -- w.hi
  ++ muxBody 6 33 86 6 90
  ++ muxBody 7 33 89 7 90
  ++ cmulBody 33 6 7 6 7 98 99
  ++ muxBody 8 33 98 8 90
  ++ muxBody 9 33 99 9 90

/-- One divisor-slot touch, gated: read `acc[d]`, delta-term, push `w`. -/
def Cfg.touchBody (c : Cfg) (g dSlot : Nat) : List AInstr :=
  [ .scalar (.binop 194 .mul (.reg g) (.reg dSlot))
  , .scalar (.binop 191 .add (.reg 194) (.lit c.plane1))
  , .scalar (.binop 192 .add (.reg 194) (.lit c.plane2))
  , .load 180 191                                             -- A.lo
  , .load 181 192 ]                                           -- A.hi
  ++ cmulBody g 180 181 6 7 182 183                           -- P = cmul A w
  ++ guardBody g 182 195 ++ guardBody g 183 195
  ++ [ .scalar (.binop 184 .add (.reg 182) (.reg 182))
     , .scalar (.binop 184 .add (.reg 184) (.reg 8))          -- T.lo = 2P.lo + ww.lo
     , .scalar (.binop 185 .add (.reg 183) (.reg 183))
     , .scalar (.binop 185 .add (.reg 185) (.reg 9)) ]        -- T.hi
  ++ guardBody g 184 195 ++ guardBody g 185 195
  ++ [ .load 186 194                                          -- μ code of the slot
     , .scalar (.binop 187 .eq (.reg 186) (.lit 1))
     , .scalar (.binop 188 .eq (.reg 186) (.lit 2))
     , .scalar (.binop 196 .sub (.lit 0) (.reg 185))
     , .scalar (.binop 197 .sub (.lit 0) (.reg 184))
     , .scalar (.binop 189 .mul (.reg 187) (.reg 184))
     , .scalar (.binop 198 .mul (.reg 188) (.reg 196))
     , .scalar (.binop 189 .add (.reg 189) (.reg 198))        -- dT.lo
     , .scalar (.binop 190 .mul (.reg 187) (.reg 185))
     , .scalar (.binop 199 .mul (.reg 188) (.reg 197))
     , .scalar (.binop 190 .add (.reg 190) (.reg 199))        -- dT.hi
     , .scalar (.binop 10 .add (.reg 10) (.reg 189))
     , .scalar (.binop 11 .add (.reg 11) (.reg 190)) ]
  ++ guardBody g 10 195 ++ guardBody g 11 195
  ++ [ .scalar (.binop 196 .mul (.reg g) (.reg 6))
     , .scalar (.binop 197 .add (.reg 180) (.reg 196))
     , .store 191 197                                         -- acc.lo += w.lo
     , .scalar (.binop 198 .mul (.reg g) (.reg 7))
     , .scalar (.binop 199 .add (.reg 181) (.reg 198))
     , .store 192 199 ]                                       -- acc.hi += w.hi

/-- Pass B: the two touches of the divisor pair `(r, X/r)`. -/
def Cfg.passBBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 210 .urem (.reg 31) (.reg 38))
  , .scalar (.binop 211 .eq (.reg 210) (.lit 0))
  , .scalar (.binop 212 .mul (.reg 38) (.reg 38))
  , .scalar (.binop 213 .le (.reg 212) (.reg 31))
  , .scalar (.binop 214 .mul (.reg 211) (.reg 213))
  , .scalar (.binop 214 .mul (.reg 214) (.reg 34))            -- gate 1
  , .scalar (.binop 215 .udiv (.reg 31) (.reg 38))            -- the partner
  , .scalar (.binop 216 .eq (.reg 215) (.reg 38))
  , .scalar (.binop 217 .sub (.lit 1) (.reg 216))
  , .scalar (.binop 218 .mul (.reg 214) (.reg 217)) ]         -- gate 2
  ++ c.touchBody 214 38
  ++ c.touchBody 218 215

/-- Finalize: `g += delta`, reset `delta`, and the `g₂` endpoint test. -/
def Cfg.finBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 220 .mul (.reg 35) (.reg 10))
  , .scalar (.binop 12 .add (.reg 12) (.reg 220))
  , .scalar (.binop 221 .mul (.reg 35) (.reg 11))
  , .scalar (.binop 13 .add (.reg 13) (.reg 221))
  , .scalar (.binop 222 .sub (.lit 1) (.reg 35))
  , .scalar (.binop 10 .mul (.reg 10) (.reg 222))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 222)) ]
  ++ guardBody 35 12 223 ++ guardBody 35 13 223
  ++ [ .scalar (.binop 224 .ge (.reg 31) (.lit c.checkLo))
     , .scalar (.binop 225 .mul (.reg 35) (.reg 224))         -- checking
     , .scalar (.binop 226 .mul (.reg 31) (.lit 10))          -- 10·X
     , .scalar (.binop 227 .ge (.reg 12) (.lit H63))          -- g.lo < 0 ?
     , .scalar (.binop 228 .sub (.lit 0) (.reg 12)) ]
  ++ muxBody 229 227 228 12 230                               -- |g.lo|
  ++ mulWideBody 229 226 231 232 233 234 235 236 237 238 239 240
  ++ [ .scalar (.binop 241 .gt (.reg 232) (.lit 1))
     , .scalar (.binop 242 .eq (.reg 232) (.lit 1))
     , .scalar (.binop 243 .gt (.reg 231) (.lit KLO))
     , .scalar (.binop 244 .mul (.reg 242) (.reg 243))
     , .scalar (.binop 245 .add (.reg 241) (.reg 244))        -- > 21·SCALE
     , .scalar (.binop 246 .mul (.reg 227) (.reg 245))
     , .scalar (.binop 246 .mul (.reg 246) (.reg 225))
     , .scalar (.binop rViol .bor (.reg rViol) (.reg 246))    -- lower check
     , .scalar (.binop 247 .ge (.reg 13) (.lit H63))
     , .scalar (.binop 248 .sub (.lit 1) (.reg 247))          -- g.hi ≥ 0
     , .scalar (.binop 249 .sub (.lit 0) (.reg 13)) ]
  ++ muxBody 250 247 249 13 251                               -- |g.hi|
  ++ mulWideBody 250 226 252 253 233 234 235 236 237 238 239 240
  ++ [ .scalar (.binop 241 .gt (.reg 253) (.lit 1))
     , .scalar (.binop 242 .eq (.reg 253) (.lit 1))
     , .scalar (.binop 243 .gt (.reg 252) (.lit KLO))
     , .scalar (.binop 244 .mul (.reg 242) (.reg 243))
     , .scalar (.binop 245 .add (.reg 241) (.reg 244))
     , .scalar (.binop 246 .mul (.reg 248) (.reg 245))
     , .scalar (.binop 246 .mul (.reg 246) (.reg 225))
     , .scalar (.binop rViol .bor (.reg rViol) (.reg 246)) ]  -- upper check

/-! ## §6 The program -/

def Cfg.body (c : Cfg) : List AInstr :=
  c.selBody ++ trialBody ++ passABody ++ c.weightBody ++ c.passBBody ++
    c.finBody

/-- The init block: `μ(1) = +1` into plane 0, slot 1. -/
def Cfg.init (_c : Cfg) : List AInstr := storeLit 1 1

def g2Program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.loopCount
  init := c.init
  body := c.body
  epilogue := []
  output := rViol
}

/-! ## §7 Well-formedness, and the bridge instantiated -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem selBody_all (c : Cfg) :
    (c.selBody).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem trialBody_all :
    trialBody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem passABody_all :
    passABody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1600000 in
set_option maxHeartbeats 8000000 in
theorem weightBody_all (c : Cfg) :
    (c.weightBody).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1600000 in
set_option maxHeartbeats 16000000 in
theorem passBBody_all (c : Cfg) :
    (c.passBBody).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1600000 in
set_option maxHeartbeats 8000000 in
theorem finBody_all (c : Cfg) :
    (c.finBody).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 1000000 in
theorem init_all (c : Cfg) :
    (c.init).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
theorem body_all (c : Cfg) : (c.body).all (ainstrWFB regCount) = true := by
  show (c.selBody ++ (trialBody ++ (passABody ++ (c.weightBody ++
    (c.passBBody ++ c.finBody))))).all (ainstrWFB regCount) = true
  exact all_append (selBody_all c)
    (all_append trialBody_all
      (all_append passABody_all
        (all_append (weightBody_all c)
          (all_append (passBBody_all c) (finBody_all c)))))

/-- **The bridge's side condition**, for every configuration. -/
theorem g2Program_wf (c : Cfg) : (g2Program c).WF :=
  ⟨show rViol < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   fun _ ha => nomatch ha⟩

/-- **The bridge, instantiated for the `g₂` sweep.**  For any array base at
which the working set fits, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
OR of all failed checks and guards, in the output register. -/
theorem g2Program_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (g2Program c).arrayLen base)
    (n : Nat) (hDenote : (g2Program c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((g2Program c).initialMCC base) (g2Program c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(g2Program c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (g2Program_wf c) base hBase n hDenote

/-! ## §8 The transparent model

The machine step in plain `Nat` arithmetic, at block granularity, with the
`u64` truncations the machine performs written out (`% M`, and subtraction
as `tsub`).  The 128-bit products are `Verified.MulWide.hl` — the exact
function `mulWideBody` inlines — and the `10¹⁸` divider is transcribed
instruction for instruction (its untruncated counterpart is
`Section413Cells.divP18w`, equal on every guarded input).

The two obligations this model splits the simulation into (see the module
docstring; **neither is proved here**):

```text
(1)  (g2Program c).denote = some (c.tFlag)                 [machine ⇒ model]
(2)  c.tFlag = 0 → g2SweepOK c.rounds c.checkLo c.cap      [model ⇒ reference]
```
-/

/-- `0`/`1` of a decidable proposition. -/
def bnat (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- Machine subtraction: `(a − b) mod 2⁶⁴`. -/
def tsub (a b : Nat) : Nat := (a + (M - b)) % M

/-- What the loop carries: the fourteen persistent registers and the
array. -/
structure TState where
  viol : Nat
  res : Nat
  sq : Nat
  par : Nat
  sigma : Nat
  wLo : Nat
  wHi : Nat
  wwLo : Nat
  wwHi : Nat
  dLo : Nat
  dHi : Nat
  gLo : Nat
  gHi : Nat
  arr : Nat → Nat

/-- The width guard (`guardBody`). -/
def tguard (gate w viol : Nat) : Nat :=
  viol ||| (bnat (2 * CAP < (w + CAP) % M) * gate)

/-- Sign bit and magnitude of an encoded word (`smDecomp`, sans guard). -/
def tmag (w : Nat) : Nat × Nat :=
  (bnat (H63 ≤ w), if H63 ≤ w then tsub 0 w else w)

/-- The strict signed sign-magnitude comparison (`cmpLtBody`). -/
def tlt (sa la ha sb lb hb : Nat) : Nat :=
  let mab := bnat (ha < hb) + bnat (ha = hb) * bnat (la < lb)
  let mba := bnat (hb < ha) + bnat (ha = hb) * bnat (lb < la)
  sa * (1 - sb) + sa * sb * mba + (1 - sa) * (1 - sb) * mab

/-- The exact `10¹⁸` divider (`divP18Body`): floor and ceiling quotients of
the magnitude `lo + 2⁶⁴·hi`, with the machine's truncations. -/
def tdiv18 (lo hi : Nat) : Nat × Nat :=
  let yLo := ((lo >>> 18) + (hi <<< 46) % M) % M
  let yHi := hi >>> 18
  let cur := yHi >>> 24
  let q := cur / D5
  let rem := cur % D5
  let cur := (rem * 4194304 % M + ((yHi >>> 2) &&& 4194303)) % M
  let q := (q * 4194304 % M + cur / D5) % M
  let rem := cur % D5
  let d2 := ((yLo >>> 44) + ((yHi &&& 3) * 1048576) % M) % M
  let cur := (rem * 4194304 % M + d2) % M
  let q := (q * 4194304 % M + cur / D5) % M
  let rem := cur % D5
  let cur := (rem * 4194304 % M + ((yLo >>> 22) &&& 4194303)) % M
  let q := (q * 4194304 % M + cur / D5) % M
  let rem := cur % D5
  let cur := (rem * 4194304 % M + (yLo &&& 4194303)) % M
  let q := (q * 4194304 % M + cur / D5) % M
  let rem := cur % D5
  let ex := bnat (lo &&& 262143 = 0) * bnat (rem = 0)
  (q, (tsub 1 ex + q) % M)

/-- The interval product (`cmulBody`): `(cLo, cHi, viol')`. -/
def tcmul (gate aLo aHi bLo bHi viol : Nat) : Nat × Nat × Nat :=
  let (saL, maL) := tmag aLo
  let viol := viol ||| (bnat (CAP < maL) * gate)
  let (saH, maH) := tmag aHi
  let viol := viol ||| (bnat (CAP < maH) * gate)
  let (sbL, mbL) := tmag bLo
  let viol := viol ||| (bnat (CAP < mbL) * gate)
  let (sbH, mbH) := tmag bHi
  let viol := viol ||| (bnat (CAP < mbH) * gate)
  let p1 := Verified.MulWide.hl maL mbL
  let p2 := Verified.MulWide.hl maL mbH
  let p3 := Verified.MulWide.hl maH mbL
  let p4 := Verified.MulWide.hl maH mbH
  let s1 := (saL ^^^ sbL) * (1 - bnat (p1.1 = 0) * bnat (p1.2 = 0))
  let s2 := (saL ^^^ sbH) * (1 - bnat (p2.1 = 0) * bnat (p2.2 = 0))
  let s3 := (saH ^^^ sbL) * (1 - bnat (p3.1 = 0) * bnat (p3.2 = 0))
  let s4 := (saH ^^^ sbH) * (1 - bnat (p4.1 = 0) * bnat (p4.2 = 0))
  let t12 := tlt s1 p1.1 p1.2 s2 p2.1 p2.2
  let t34 := tlt s3 p3.1 p3.2 s4 p4.1 p4.2
  let mn12 := if t12 = 1 then (s1, p1.1, p1.2) else (s2, p2.1, p2.2)
  let mx12 := if t12 = 1 then (s2, p2.1, p2.2) else (s1, p1.1, p1.2)
  let mn34 := if t34 = 1 then (s3, p3.1, p3.2) else (s4, p4.1, p4.2)
  let mx34 := if t34 = 1 then (s4, p4.1, p4.2) else (s3, p3.1, p3.2)
  let tn := tlt mn12.1 mn12.2.1 mn12.2.2 mn34.1 mn34.2.1 mn34.2.2
  let tx := tlt mx12.1 mx12.2.1 mx12.2.2 mx34.1 mx34.2.1 mx34.2.2
  let mn := if tn = 1 then mn12 else mn34
  let mx := if tx = 1 then mx34 else mx12
  let qn := tdiv18 mn.2.1 mn.2.2
  let cLo := if mn.1 = 1 then tsub 0 qn.2 else qn.1
  let qx := tdiv18 mx.2.1 mx.2.2
  let cHi := if mx.1 = 1 then tsub 0 qx.1 else qx.2
  (cLo, cHi, viol)

/-- One gated divisor-slot touch (`touchBody`). -/
def Cfg.ttouch (c : Cfg) (g dSlot : Nat) (t : TState) : TState :=
  let base := g * dSlot % M
  let a1 := (base + c.plane1) % M
  let a2 := (base + c.plane2) % M
  let aLo := t.arr a1
  let aHi := t.arr a2
  let r := tcmul g aLo aHi t.wLo t.wHi t.viol
  let viol := tguard g r.1 r.2.2
  let viol := tguard g r.2.1 viol
  let tLo := ((r.1 + r.1) % M + t.wwLo) % M
  let tHi := ((r.2.1 + r.2.1) % M + t.wwHi) % M
  let viol := tguard g tLo viol
  let viol := tguard g tHi viol
  let mc := t.arr base
  let muP := bnat (mc = 1)
  let muM := bnat (mc = 2)
  let dLo := (t.dLo + (muP * tLo % M + muM * (tsub 0 tHi) % M) % M) % M
  let dHi := (t.dHi + (muP * tHi % M + muM * (tsub 0 tLo) % M) % M) % M
  let viol := tguard g dLo viol
  let viol := tguard g dHi viol
  let nLo := (aLo + g * t.wLo % M) % M
  let nHi := (aHi + g * t.wHi % M) % M
  let arr' := fun i => if i = a2 then nHi else if i = a1 then nLo else t.arr i
  { t with viol := viol, dLo := dLo, dHi := dHi, arr := arr' }

/-- **One full iteration of the loop**, in plain arithmetic. -/
def Cfg.tstep (c : Cfg) (idx : Nat) (t : TState) : TState :=
  -- selectors and decode
  let inP1 := bnat (idx < c.phase1)
  let inP2 := 1 - inP1
  let r1 := idx % c.rounds
  let n1 := (idx / c.rounds + 2) % M
  let d1 := (r1 + 2) % M
  let isD0 := bnat (r1 = 0) * inP1
  let isDL := bnat (r1 = c.rounds - 1) * inP1
  let b2 := tsub idx c.phase1
  let pX := b2 % c.p
  let X := (b2 / c.p + 1) % M
  let inA := bnat (pX < c.s) * inP2
  let isW := bnat (pX = c.s) * inP2
  let inB := bnat (c.s + 1 ≤ pX) * bnat (pX ≤ 2 * c.s) * inP2
  let isF := bnat (pX = 2 * c.s + 1) * inP2
  let rA := (pX + 1) % M
  let rBr := tsub pX c.s
  let rB := (bnat (rBr = 0) + rBr) % M
  -- phase 1: trial division
  let res := if isD0 = 1 then n1 else t.res
  let sq := t.sq * (1 - isD0)
  let par := t.par * (1 - isD0)
  let hit := bnat (res % d1 = 0) * inP1
  let res := if hit = 1 then res / d1 else res
  let hit2 := bnat (res % d1 = 0) * hit
  let sq := sq ||| hit2
  let par := par ^^^ hit
  let om := par ^^^ bnat (res ≠ 1)
  let code := ((om + 1) % M) * (1 - sq) % M
  let wrAddr := isDL * n1 % M
  let arr := fun i => if i = wrAddr then isDL * code % M else t.arr i
  -- pass A: sigma
  let isX0 := bnat (pX = 0) * inP2
  let sigma := if isX0 = 1 then 0 else t.sigma
  let hitA := bnat (X % rA = 0) * bnat (rA * rA % M ≤ X) * inA
  let qA := X / rA
  let addA := ((rA + (1 - bnat (qA = rA)) * qA % M) % M) * hitA % M
  let sigma := (sigma + addA) % M
  -- weight
  let muX := arr (isW * X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * bnat (X % 2 = 1) * isW
  let sig1 := (sigma + bnat (sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  let wLo := if isW = 1 then (isP * magF + isM * tsub 0 magC) % M * live % M
    else t.wLo
  let wHi := if isW = 1 then (isP * magC + isM * tsub 0 magF) % M * live % M
    else t.wHi
  let ww := tcmul isW wLo wHi wLo wHi t.viol
  let wwLo := if isW = 1 then ww.1 else t.wwLo
  let wwHi := if isW = 1 then ww.2.1 else t.wwHi
  let t1 : TState := ⟨ww.2.2, res, sq, par, sigma, wLo, wHi,
    wwLo, wwHi, t.dLo, t.dHi, t.gLo, t.gHi, arr⟩
  -- pass B: the divisor pair
  let g1 := bnat (X % rB = 0) * bnat (rB * rB % M ≤ X) * inB
  let q2 := X / rB
  let g2 := g1 * (1 - bnat (q2 = rB))
  let t2 := c.ttouch g1 rB t1
  let t3 := c.ttouch g2 q2 t2
  -- finalize
  let gLo := (t3.gLo + isF * t3.dLo % M) % M
  let gHi := (t3.gHi + isF * t3.dHi % M) % M
  let dLo := t3.dLo * (1 - isF) % M
  let dHi := t3.dHi * (1 - isF) % M
  let viol := tguard isF gLo t3.viol
  let viol := tguard isF gHi viol
  let chk := isF * bnat (c.checkLo ≤ X)
  let tenX := X * 10 % M
  let sLo := bnat (H63 ≤ gLo)
  let mLo := if sLo = 1 then tsub 0 gLo else gLo
  let pl := Verified.MulWide.hl mLo tenX
  let bad1 := sLo * ((bnat (1 < pl.2) + bnat (pl.2 = 1) * bnat (KLO < pl.1))) * chk
  let sHi := bnat (H63 ≤ gHi)
  let mHi := if sHi = 1 then tsub 0 gHi else gHi
  let ph := Verified.MulWide.hl mHi tenX
  let bad2 := (1 - sHi) * ((bnat (1 < ph.2) + bnat (ph.2 = 1) * bnat (KLO < ph.1))) * chk
  ⟨viol ||| bad1 ||| bad2, res, sq, par, sigma, wLo, wHi,
    wwLo, wwHi, dLo, dHi, gLo, gHi, t3.arr⟩

/-- The state the init block reaches: zero registers, `μ(1) = +1` seeded. -/
def tInit : TState :=
  { viol := 0, res := 0, sq := 0, par := 0, sigma := 0, wLo := 0, wHi := 0,
    wwLo := 0, wwHi := 0, dLo := 0, dHi := 0, gLo := 0, gHi := 0,
    arr := fun i => if i = 1 then 1 else 0 }

/-- The whole transparent run. -/
def Cfg.tRun (c : Cfg) : TState :=
  (List.range c.loopCount).foldl (fun t i => c.tstep i t) tInit

/-- The transparent model's violation flag — obligation (1) is that the
machine denotes exactly this number; obligation (2) is that its vanishing
forces `g2SweepOK`. -/
def Cfg.tFlag (c : Cfg) : Nat := c.tRun.viol

/-- The transparent model's final `g` cell (both endpoints encoded), for
cross-checks. -/
def Cfg.tG (c : Cfg) : Nat × Nat := (c.tRun.gLo, c.tRun.gHi)

end LeanCompCert.Ports.Section413G2Program
