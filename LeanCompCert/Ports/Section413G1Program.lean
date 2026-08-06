import LeanCompCert.Ports.Section413Sweep
import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Ports.CDEMAbelScan

/-!
# The §4.1.3 `g₂` sweep as an array program

The ARRAY-MACHINE stage of the §4.1.3 conversion, `g₂` instance (atom 2):
one `AProgram` intended to compute `Section413Sweep.g1SweepOK R checkLo N`
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

* `g1Program_wf` — well-formedness, for every configuration; hence
* `g1Program_compiled` — `AProgram.evalCC_compile` instantiated: the
  compiled CCIR trace (and through `Verified.MemFragment` the emitted C)
  computes exactly `(g1Program c).denote`.

**Not proved here** (stated as the two obligations they are; nothing below
asserts them):

1. `(g1Program c).denote = some (tFlag c)` — that the machine denotes the
   transparent model `tstep`/`tRun` below.  The intended route is the
   per-stage `arun` specs against `AllDefined` (the
   `ArrayMobiusDenotation`/`SingSeriesC17` architecture) assembled by
   `Verified.Algorithm.ArrayBridge.ArrayLoop`.
2. `tFlag c = 0 → g1SweepOK c.rounds c.checkLo c.cap = true` — that the
   transparent model with a clean flag equals the reference model.  The
   intended route is the encode/decode and divider lemmas of
   `Ports/Section413Cells.lean` under the guard invariant.  Its divider
   piece **is proved below** (§9, `tdiv18_eq`): on every guarded input the
   transparent `10¹⁸` divider equals the proved `divP18q`/`divP18ceil`.

Until both land, a run of the emitted artifact is evidence about the C
only; the campaign registry entry `section413_g2_small_1e6` carries
`evaluates_atom_predicate: false` accordingly.

The transparent model *is* executable: `bench/Section413SweepEmit.lean`'s
`check` mode runs `tRun` against `g1Run` at small configurations and the
independent C oracle `bench/ref_section413_g2.c` covers the production
configuration; the emitted artifact's flag can then be compared against
both.
-/

namespace LeanCompCert.Ports.Section413G1Program

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

/-- Canonicalize one unsigned two-limb product's sign: zero has sign `0`;
a nonzero product has the xor of the operand signs.  Scratch: 123--125. -/
def canonSignBody (sa sb lo hi dst : Nat) : List AInstr :=
  [ .scalar (.binop dst .bxor (.reg sa) (.reg sb))
  , .scalar (.binop 123 .eq (.reg lo) (.lit 0))
  , .scalar (.binop 124 .eq (.reg hi) (.lit 0))
  , .scalar (.binop 125 .mul (.reg 123) (.reg 124))
  , .scalar (.binop 125 .sub (.lit 1) (.reg 125))
  , .scalar (.binop dst .mul (.reg dst) (.reg 125)) ]

/-- Canonical signs for the four endpoint products in `cmulBody`. -/
def cmulSignsBody : List AInstr :=
  canonSignBody 100 102 111 112 119 ++
  canonSignBody 100 103 113 114 120 ++
  canonSignBody 101 102 115 116 121 ++
  canonSignBody 101 103 117 118 122

/-- Encode a lower endpoint after division: negative uses `-ceil`, while
nonnegative uses `floor`.  Scratch: 108--109. -/
def cmulLowerBody (sign q qc dst : Nat) : List AInstr :=
  [ .scalar (.binop 108 .sub (.lit 0) (.reg qc))
  , .scalar (.binop 109 .sub (.lit 1) (.reg sign))
  , .scalar (.binop dst .mul (.reg 109) (.reg q))
  , .scalar (.binop 108 .mul (.reg sign) (.reg 108))
  , .scalar (.binop dst .add (.reg dst) (.reg 108)) ]

/-- Encode an upper endpoint after division: negative uses `-floor`, while
nonnegative uses `ceil`.  Scratch: 108--109. -/
def cmulUpperBody (sign q qc dst : Nat) : List AInstr :=
  [ .scalar (.binop 108 .sub (.lit 0) (.reg q))
  , .scalar (.binop 109 .sub (.lit 1) (.reg sign))
  , .scalar (.binop dst .mul (.reg 109) (.reg qc))
  , .scalar (.binop 108 .mul (.reg sign) (.reg 108))
  , .scalar (.binop dst .add (.reg dst) (.reg 108)) ]

/-- Decode and guard the four input endpoints of `cmulBody`. -/
def cmulDecompBody (gate aLo aHi bLo bHi : Nat) : List AInstr :=
  smDecomp gate aLo 100 104 ++ smDecomp gate aHi 101 105 ++
  smDecomp gate bLo 102 106 ++ smDecomp gate bHi 103 107

/-- The four unsigned two-limb endpoint products of `cmulBody`. -/
def cmulProductsBody : List AInstr :=
  mulWideBody 104 106 111 112 154 155 156 157 158 159 160 161 ++
  mulWideBody 104 107 113 114 154 155 156 157 158 159 160 161 ++
  mulWideBody 105 106 115 116 154 155 156 157 158 159 160 161 ++
  mulWideBody 105 107 117 118 154 155 156 157 158 159 160 161

/-- Compare endpoint products 1/2 and 3/4. -/
def cmulPairFlagsBody : List AInstr :=
  cmpLtBody 119 111 112 120 113 114 132 ++
  cmpLtBody 121 115 116 122 117 118 133

/-- Select the pairwise minima and maxima. -/
def cmulPairSelectsBody : List AInstr :=
  selTriple 132 119 111 112 120 113 114 134 135 136 ++
  selTriple 132 120 113 114 119 111 112 137 138 153 ++
  selTriple 133 121 115 116 122 117 118 162 163 164 ++
  selTriple 133 122 117 118 121 115 116 165 166 167

/-- Compare the two pairwise minima and the two pairwise maxima. -/
def cmulExtremaFlagsBody : List AInstr :=
  cmpLtBody 134 135 136 162 163 164 176 ++
  cmpLtBody 137 138 153 165 166 167 177

/-- Select the global minimum and maximum. -/
def cmulExtremaSelectsBody : List AInstr :=
  selTriple 176 134 135 136 162 163 164 134 135 136 ++
  selTriple 177 165 166 167 137 138 153 137 138 153

/-- Branchless four-way signed minimum and maximum for `cmulBody`. -/
def cmulOrderBody : List AInstr :=
  cmulPairFlagsBody ++ cmulPairSelectsBody ++
  cmulExtremaFlagsBody ++ cmulExtremaSelectsBody

/-- Divide the selected extrema and encode the outward-rounded endpoints. -/
def cmulFinishBody (cLo cHi : Nat) : List AInstr :=
  divP18Body 135 136 178 179 ++ cmulLowerBody 134 178 179 cLo ++
  divP18Body 138 153 178 179 ++ cmulUpperBody 137 178 179 cHi

/-- The outward-rounded interval product `cmul` on encoded cells:
`(cLo, cHi) := cmul (aLo, aHi) (bLo, bHi)`, with the four input magnitudes
guarded against `CAP` (gated by `gate`).  Sign-magnitude decomposition,
four `MulWide.hl` products, canonicalized signs, branchless 4-way min and
max, then one exact `10¹⁸` division each with the rounding chosen by the
result sign.  Scratch: 100–179 (see the register map). -/
def cmulBody (gate aLo aHi bLo bHi cLo cHi : Nat) : List AInstr :=
  cmulDecompBody gate aLo aHi bLo bHi ++ cmulProductsBody ++
  cmulSignsBody ++ cmulOrderBody ++ cmulFinishBody cLo cHi

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

/-- Scalar prefix of one phase-1 trial-division round. -/
def trialScalarBody : List AInstr :=
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
     , .scalar (.binop 53 .mul (.reg 27) (.reg 51)) ]

/-- Phase 1: one trial-division round (`MertensCDEM.trialStep` at the
decoded divisor), with the state reset at each candidate's first round and
the μ code written at its last. -/
def trialBody : List AInstr := trialScalarBody ++ [.store 52 53]

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

/-- Address of the Möbius-code load in the weight round. -/
def weightAddrBody : List AInstr :=
  [ .scalar (.binop 71 .mul (.reg 33) (.reg 31)) ]

/-- Scalar arithmetic that forms the two weight endpoints after loading the
Möbius code into register `72`. -/
def weightCalcBody : List AInstr :=
  [ .scalar (.binop 73 .eq (.reg 72) (.lit 1))
  , .scalar (.binop 74 .eq (.reg 72) (.lit 2))
  , .scalar (.binop 75 .urem (.reg 31) (.lit 2))
  , .scalar (.mov 76 (.lit 1))
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

/-- Select the live weight, square it, and select the live square. -/
def weightFinishBody : List AInstr :=
  muxBody 6 33 86 6 90
  ++ muxBody 7 33 89 7 90
  ++ cmulBody 33 6 7 6 7 98 99
  ++ muxBody 8 33 98 8 90
  ++ muxBody 9 33 99 9 90

/-- The weight round: `w`, then `ww = cmul w w`. -/
def Cfg.weightBody (_c : Cfg) : List AInstr :=
  weightAddrBody ++ [.load 72 71] ++ weightCalcBody ++ weightFinishBody

/-- Address calculation and the two accumulator-plane loads of one touch. -/
def Cfg.touchLoadBody (c : Cfg) (g dSlot : Nat) : List AInstr :=
  [ .scalar (.binop 194 .mul (.reg g) (.reg dSlot))
  , .scalar (.binop 191 .add (.reg 194) (.lit c.plane1))
  , .scalar (.binop 192 .add (.reg 194) (.lit c.plane2))
  , .load 180 191                                             -- A.lo
  , .load 181 192 ]                                           -- A.hi

/-- Scalar product/guard prefix after the accumulator endpoints are loaded. -/
def Cfg.touchProductBody (_c : Cfg) (g : Nat) : List AInstr :=
  cmulBody g 180 181 6 7 182 183                              -- P = cmul A w
  ++ guardBody g 182 195 ++ guardBody g 183 195

/-- Scalar part of `T = 2P + w²` and its two width guards. -/
def Cfg.touchTermScalarBody (_c : Cfg) (g : Nat) : List AInstr :=
  [ .scalar (.binop 184 .add (.reg 182) (.reg 182))
     , .scalar (.binop 184 .add (.reg 184) (.reg 8))          -- T.lo = 2P.lo + ww.lo
     , .scalar (.binop 185 .add (.reg 183) (.reg 183))
     , .scalar (.binop 185 .add (.reg 185) (.reg 9)) ]        -- T.hi
  ++ guardBody g 184 195 ++ guardBody g 185 195

/-- Load the touched slot's Möbius code. -/
def Cfg.touchMuLoadBody (_c : Cfg) : List AInstr :=
  [ .load 186 194 ]                                           -- μ code of the slot

/-- Form `T = 2P + w²`, guard it, and load the slot's Möbius code. -/
def Cfg.touchTermBody (c : Cfg) (g : Nat) : List AInstr :=
  c.touchTermScalarBody g ++ c.touchMuLoadBody

/-- Scalar arithmetic for the signed `μ·T` contribution. -/
def Cfg.touchDeltaCalcBody (_c : Cfg) : List AInstr :=
  [ .scalar (.binop 187 .eq (.reg 186) (.lit 1))
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

/-- Add the signed `μ·T` contribution into the delta accumulator. -/
def Cfg.touchDeltaBody (c : Cfg) (g : Nat) : List AInstr :=
  c.touchDeltaCalcBody ++ guardBody g 10 195 ++ guardBody g 11 195

/-- Push the gated weight into both accumulator-plane cells. -/
def Cfg.touchStoreBody (_c : Cfg) (g : Nat) : List AInstr :=
  [ .scalar (.binop 196 .mul (.reg g) (.reg 6))
     , .scalar (.binop 197 .add (.reg 180) (.reg 196))
     , .store 191 197                                         -- acc.lo += w.lo
     , .scalar (.binop 198 .mul (.reg g) (.reg 7))
     , .scalar (.binop 199 .add (.reg 181) (.reg 198))
     , .store 192 199 ]                                       -- acc.hi += w.hi

/-- One divisor-slot touch, gated: read `acc[d]`, delta-term, push `w`. -/
def Cfg.touchBody (c : Cfg) (g dSlot : Nat) : List AInstr :=
  c.touchLoadBody g dSlot ++ c.touchProductBody g ++ c.touchTermBody g ++
    c.touchDeltaBody g ++ c.touchStoreBody g

/-- Compute the two gates and partner divisor used by pass B. -/
def passBGateBody : List AInstr :=
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

/-- Pass B: the two touches of the divisor pair `(r, X/r)`. -/
def Cfg.passBBody (c : Cfg) : List AInstr :=
  passBGateBody ++ c.touchBody 214 38 ++ c.touchBody 218 215

/-- Finalize the current candidate's delta into `g`, then reset delta. -/
def finAccumBody : List AInstr :=
  [ .scalar (.binop 220 .mul (.reg 35) (.reg 10))
  , .scalar (.binop 12 .add (.reg 12) (.reg 220))
  , .scalar (.binop 221 .mul (.reg 35) (.reg 11))
  , .scalar (.binop 13 .add (.reg 13) (.reg 221))
  , .scalar (.binop 222 .sub (.lit 1) (.reg 35))
  , .scalar (.binop 10 .mul (.reg 10) (.reg 222))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 222)) ]

/-- Guard both newly accumulated `g` endpoints. -/
def finGuardBody : List AInstr := guardBody 35 12 223 ++ guardBody 35 13 223

/-- Lower-check setup through the encoded absolute-value input. -/
def Cfg.finLowPreBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 224 .ge (.reg 31) (.lit c.checkLo))
     , .scalar (.binop 225 .mul (.reg 35) (.reg 224))         -- checking
     , .scalar (.binop 226 .mul (.reg 31) (.lit 10))          -- 10·X
     , .scalar (.binop 227 .ge (.reg 12) (.lit H63))          -- g.lo < 0 ?
     , .scalar (.binop 228 .sub (.lit 0) (.reg 12)) ]

/-- Lower-check comparison and violation update after the wide product. -/
def finLowPostBody : List AInstr :=
  [ .scalar (.binop 241 .gt (.reg 232) (.lit 1))
     , .scalar (.binop 242 .eq (.reg 232) (.lit 1))
     , .scalar (.binop 243 .gt (.reg 231) (.lit KLO))
     , .scalar (.binop 244 .mul (.reg 242) (.reg 243))
     , .scalar (.binop 245 .add (.reg 241) (.reg 244))        -- > 21·SCALE
     , .scalar (.binop 246 .mul (.reg 227) (.reg 245))
     , .scalar (.binop 246 .mul (.reg 246) (.reg 225))
     , .scalar (.binop rViol .bor (.reg rViol) (.reg 246)) ]  -- lower check

/-- Lower-endpoint sign and `21/10` magnitude check. -/
def Cfg.finLowBody (c : Cfg) : List AInstr :=
  c.finLowPreBody
  ++ muxBody 229 227 228 12 230                               -- |g.lo|
  ++ mulWideBody 229 226 231 232 233 234 235 236 237 238 239 240
  ++ finLowPostBody

/-- Upper-check setup through the encoded absolute-value input. -/
def finHighPreBody : List AInstr :=
  [ .scalar (.binop 247 .ge (.reg 13) (.lit H63))
     , .scalar (.binop 248 .sub (.lit 1) (.reg 247))          -- g.hi ≥ 0
     , .scalar (.binop 249 .sub (.lit 0) (.reg 13)) ]

/-- Upper-check comparison and violation update after the wide product. -/
def finHighPostBody : List AInstr :=
  [ .scalar (.binop 241 .gt (.reg 253) (.lit 1))
     , .scalar (.binop 242 .eq (.reg 253) (.lit 1))
     , .scalar (.binop 243 .gt (.reg 252) (.lit KLO))
     , .scalar (.binop 244 .mul (.reg 242) (.reg 243))
     , .scalar (.binop 245 .add (.reg 241) (.reg 244))
     , .scalar (.binop 246 .mul (.reg 248) (.reg 245))
     , .scalar (.binop 246 .mul (.reg 246) (.reg 225))
     , .scalar (.binop rViol .bor (.reg rViol) (.reg 246)) ]  -- upper check

/-- Upper-endpoint sign and `21/10` magnitude check. -/
def finHighBody : List AInstr :=
  finHighPreBody
  ++ muxBody 250 247 249 13 251                               -- |g.hi|
  ++ mulWideBody 250 226 252 253 233 234 235 236 237 238 239 240
  ++ finHighPostBody

/-- Finalize: `g += delta`, reset `delta`, and the `g₂` endpoint test. -/
def Cfg.finBody (c : Cfg) : List AInstr :=
  finAccumBody ++ finGuardBody ++ c.finLowBody ++ finHighBody

/-! ## §6 The program -/

def Cfg.body (c : Cfg) : List AInstr :=
  c.selBody ++ trialBody ++ passABody ++ c.weightBody ++ c.passBBody ++
    c.finBody

/-- The init block: `μ(1) = +1` into plane 0, slot 1. -/
def Cfg.init (_c : Cfg) : List AInstr := storeLit 1 1

def g1Program (c : Cfg) : AProgram := {
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
theorem g1Program_wf (c : Cfg) : (g1Program c).WF :=
  ⟨show rViol < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   fun _ ha => nomatch ha⟩

/-- **The bridge, instantiated for the `g₂` sweep.**  For any array base at
which the working set fits, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
OR of all failed checks and guards, in the output register. -/
theorem g1Program_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (g1Program c).arrayLen base)
    (n : Nat) (hDenote : (g1Program c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((g1Program c).initialMCC base) (g1Program c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(g1Program c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (g1Program_wf c) base hBase n hDenote

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
(1)  (g1Program c).denote = some (c.tFlag)                 [machine ⇒ model]
(2)  c.tFlag = 0 → g1SweepOK c.rounds c.checkLo c.cap      [model ⇒ reference]
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

/-- One truncated long-division step (`divP18Body`'s per-digit block):
`Section413Cells.ldStep` with the machine's `u64` truncations. -/
def tld (st : Nat × Nat) (dig : Nat) : Nat × Nat :=
  ((st.1 * 4194304 % M + (st.2 * 4194304 % M + dig) % M / D5) % M,
   (st.2 * 4194304 % M + dig) % M % D5)

/-- The divider tail over an arbitrary digit list: the truncated long
division and the exactness-corrected ceiling. -/
def ttail (lo : Nat) (ds : List Nat) : Nat × Nat :=
  let st := ds.foldl tld (0, 0)
  let ex := bnat (lo &&& 262143 = 0) * bnat (st.2 = 0)
  (st.1, (tsub 1 ex + st.1) % M)

/-- The exact `10¹⁸` divider (`divP18Body`): floor and ceiling quotients of
the magnitude `lo + 2⁶⁴·hi`, with the machine's truncations. -/
def tdiv18 (lo hi : Nat) : Nat × Nat :=
  let yLo := ((lo >>> 18) + (hi <<< 46) % M) % M
  let yHi := hi >>> 18
  ttail lo
    [ yHi >>> 24
    , (yHi >>> 2) &&& 4194303
    , ((yLo >>> 44) + ((yHi &&& 3) * 1048576) % M) % M
    , (yLo >>> 22) &&& 4194303
    , yLo &&& 4194303 ]

/-- Canonical signed product tuple from two sign bits and a wide magnitude. -/
def tproduct (sa sb : Nat) (p : Nat × Nat) : Nat × Nat × Nat :=
  ((sa ^^^ sb) * (1 - bnat (p.1 = 0) * bnat (p.2 = 0)), p.1, p.2)

/-- Branchless minimum/maximum ordering for four canonical signed two-limb
values.  Factoring this transparent helper avoids duplicating the full
four-product expression at every projection in `tcmul`. -/
def torder (p1 p2 p3 p4 : Nat × Nat × Nat) :
    (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  let t12 := tlt p1.1 p1.2.1 p1.2.2 p2.1 p2.2.1 p2.2.2
  let t34 := tlt p3.1 p3.2.1 p3.2.2 p4.1 p4.2.1 p4.2.2
  let mn12 := if t12 = 1 then p1 else p2
  let mx12 := if t12 = 1 then p2 else p1
  let mn34 := if t34 = 1 then p3 else p4
  let mx34 := if t34 = 1 then p4 else p3
  let tn := tlt mn12.1 mn12.2.1 mn12.2.2 mn34.1 mn34.2.1 mn34.2.2
  let tx := tlt mx12.1 mx12.2.1 mx12.2.2 mx34.1 mx34.2.1 mx34.2.2
  (if tn = 1 then mn12 else mn34, if tx = 1 then mx34 else mx12)

def troundLo (mn : Nat × Nat × Nat) : Nat :=
  if mn.1 = 1 then tsub 0 (tdiv18 mn.2.1 mn.2.2).2
  else (tdiv18 mn.2.1 mn.2.2).1

def troundHi (mx : Nat × Nat × Nat) : Nat :=
  if mx.1 = 1 then tsub 0 (tdiv18 mx.2.1 mx.2.2).1
  else (tdiv18 mx.2.1 mx.2.2).2

def torderedLo (p1 p2 p3 p4 : Nat × Nat × Nat) : Nat :=
  troundLo (torder p1 p2 p3 p4).1

def torderedHi (p1 p2 p3 p4 : Nat × Nat × Nat) : Nat :=
  troundHi (torder p1 p2 p3 p4).2

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
  let cLo := torderedLo (tproduct saL sbL p1) (tproduct saL sbH p2)
    (tproduct saH sbL p3) (tproduct saH sbH p4)
  let cHi := torderedHi (tproduct saL sbL p1) (tproduct saL sbH p2)
    (tproduct saH sbL p3) (tproduct saH sbH p4)
  (cLo, cHi, viol)

/-- Base and plane addresses used by a gated divisor-slot touch. -/
def Cfg.touchBase (_c : Cfg) (g dSlot : Nat) : Nat := g * dSlot % M

def Cfg.touchA1 (c : Cfg) (g dSlot : Nat) : Nat :=
  (c.touchBase g dSlot + c.plane1) % M

def Cfg.touchA2 (c : Cfg) (g dSlot : Nat) : Nat :=
  (c.touchBase g dSlot + c.plane2) % M

/-- Transparent flag update for the two interval-product endpoint guards. -/
def ttouchProductViol (g pLo pHi viol : Nat) : Nat :=
  tguard g pHi (tguard g pLo viol)

/-- Transparent scalar model of the `2P + w²` stage and its guards. -/
def ttouchTerm (g pLo pHi wwLo wwHi viol : Nat) : Nat × Nat × Nat :=
  let tLo := ((pLo + pLo) % M + wwLo) % M
  let tHi := ((pHi + pHi) % M + wwHi) % M
  let viol := tguard g tLo viol
  let viol := tguard g tHi viol
  (tLo, tHi, viol)

/-- Transparent scalar model of the signed Möbius contribution stage. -/
def ttouchDelta (g mc tLo tHi dLo dHi viol : Nat) : Nat × Nat × Nat :=
  let muP := bnat (mc = 1)
  let muM := bnat (mc = 2)
  let dLo := (dLo + (muP * tLo % M + muM * (tsub 0 tHi) % M) % M) % M
  let dHi := (dHi + (muP * tHi % M + muM * (tsub 0 tLo) % M) % M) % M
  let viol := tguard g dLo viol
  let viol := tguard g dHi viol
  (dLo, dHi, viol)

/-- Transparent scalar model of the two accumulator-plane stores. -/
def ttouchStore (g aLo aHi wLo wHi : Nat) : Nat × Nat :=
  ((aLo + g * wLo % M) % M, (aHi + g * wHi % M) % M)

/-- One gated divisor-slot touch (`touchBody`). -/
def Cfg.ttouch (c : Cfg) (g dSlot : Nat) (t : TState) : TState :=
  let base := c.touchBase g dSlot
  let a1 := c.touchA1 g dSlot
  let a2 := c.touchA2 g dSlot
  let aLo := t.arr a1
  let aHi := t.arr a2
  let r := tcmul g aLo aHi t.wLo t.wHi t.viol
  let pViol := ttouchProductViol g r.1 r.2.1 r.2.2
  let term := ttouchTerm g r.1 r.2.1 t.wwLo t.wwHi pViol
  let tLo := term.1
  let tHi := term.2.1
  let mc := t.arr base
  let delta := ttouchDelta g mc tLo tHi t.dLo t.dHi term.2.2
  let stored := ttouchStore g aLo aHi t.wLo t.wHi
  let nLo := stored.1
  let nHi := stored.2
  let arr' := fun i => if i = a2 then nHi else if i = a1 then nLo else t.arr i
  { t with viol := delta.2.2, dLo := delta.1, dHi := delta.2.1, arr := arr' }

/-- Transparent result of `selBody`, including the intermediate quotient and
shifted pass-B divisor retained in machine registers. -/
structure TSel where
  inP1 : Nat
  inP2 : Nat
  q1 : Nat
  r1 : Nat
  n1 : Nat
  d1 : Nat
  isD0 : Nat
  isDL : Nat
  b2 : Nat
  x0 : Nat
  pX : Nat
  X : Nat
  inA : Nat
  isW : Nat
  inB : Nat
  isF : Nat
  rA : Nat
  rBr : Nat
  rB : Nat

/-- The transparent selector/index-decode stage. -/
def Cfg.tsel (c : Cfg) (idx : Nat) : TSel :=
  let inP1 := bnat (idx < c.phase1)
  let inP2 := 1 - inP1
  let q1 := idx / c.rounds
  let r1 := idx % c.rounds
  let n1 := (q1 + 2) % M
  let d1 := (r1 + 2) % M
  let isD0 := bnat (r1 = 0) * inP1
  let isDL := bnat (r1 = c.rounds - 1) * inP1
  let b2 := tsub idx c.phase1
  let x0 := b2 / c.p
  let pX := b2 % c.p
  let X := (x0 + 1) % M
  let inA := bnat (pX < c.s) * inP2
  let isW := bnat (pX = c.s) * inP2
  let inB := bnat (c.s + 1 ≤ pX) * bnat (pX ≤ 2 * c.s) * inP2
  let isF := bnat (pX = 2 * c.s + 1) * inP2
  let rA := (pX + 1) % M
  let rBr := tsub pX c.s
  let rB := (bnat (rBr = 0) + rBr) % M
  ⟨inP1, inP2, q1, r1, n1, d1, isD0, isDL, b2, x0, pX, X,
    inA, isW, inB, isF, rA, rBr, rB⟩

/-- Transparent phase-1 trial-division stage. -/
def ttrial (z : TSel) (t : TState) : TState :=
  let res := if z.isD0 = 1 then z.n1 else t.res
  let sq := t.sq * (1 - z.isD0)
  let par := t.par * (1 - z.isD0)
  let hit := bnat (res % z.d1 = 0) * z.inP1
  let res := if hit = 1 then res / z.d1 else res
  let hit2 := bnat (res % z.d1 = 0) * hit
  let sq := sq ||| hit2
  let par := par ^^^ hit
  let om := par ^^^ bnat (res ≠ 1)
  let code := ((om + 1) % M) * (1 - sq) % M
  let wrAddr := z.isDL * z.n1 % M
  let arr := fun i => if i = wrAddr then z.isDL * code % M else t.arr i
  { t with res := res, sq := sq, par := par, arr := arr }

/-- Transparent phase-2 divisor-pair accumulation for `passABody`. -/
def tpassA (z : TSel) (t : TState) : TState :=
  let isX0 := bnat (z.pX = 0) * z.inP2
  let sigma := if isX0 = 1 then 0 else t.sigma
  let hitA := bnat (z.X % z.rA = 0) * bnat (z.rA * z.rA % M ≤ z.X) * z.inA
  let qA := z.X / z.rA
  let addA := ((z.rA + (1 - bnat (qA = z.rA)) * qA % M) % M) * hitA % M
  { t with sigma := (sigma + addA) % M }

/-- Transparent phase-2 weight stage (`weightBody`): form the interval
weight `μ(X)/σ(X)` at the live weight round and square it. -/
def tweight (z : TSel) (t : TState) : TState :=
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * z.isW
  let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  let wLo := if z.isW = 1 then
      (isP * magF + isM * tsub 0 magC) % M * live % M
    else t.wLo
  let wHi := if z.isW = 1 then
      (isP * magC + isM * tsub 0 magF) % M * live % M
    else t.wHi
  let ww := tcmul z.isW wLo wHi wLo wHi t.viol
  let wwLo := if z.isW = 1 then ww.1 else t.wwLo
  let wwHi := if z.isW = 1 then ww.2.1 else t.wwHi
  ⟨ww.2.2, t.res, t.sq, t.par, t.sigma, wLo, wHi, wwLo, wwHi,
    t.dLo, t.dHi, t.gLo, t.gHi, t.arr⟩

/-- Transparent phase-2 divisor-pair touch stage (`passBBody`). -/
def Cfg.tpassB (c : Cfg) (z : TSel) (t : TState) : TState :=
  let g1 := bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q2 := z.X / z.rB
  let g2 := g1 * (1 - bnat (q2 = z.rB))
  c.ttouch g2 q2 (c.ttouch g1 z.rB t)

/-- Finalized lower accumulator endpoint. -/
def tfinGLo (z : TSel) (t : TState) : Nat :=
  (t.gLo + z.isF * t.dLo % M) % M

/-- Finalized upper accumulator endpoint. -/
def tfinGHi (z : TSel) (t : TState) : Nat :=
  (t.gHi + z.isF * t.dHi % M) % M

/-- Reset lower delta. -/
def tfinDLo (z : TSel) (t : TState) : Nat :=
  t.dLo * (1 - z.isF) % M

/-- Reset upper delta. -/
def tfinDHi (z : TSel) (t : TState) : Nat :=
  t.dHi * (1 - z.isF) % M

/-- Shared finalization check gate. -/
def Cfg.tfinChk (c : Cfg) (z : TSel) : Nat :=
  z.isF * bnat (c.checkLo ≤ z.X)

/-- The strict `21/10` comparison on a sign-magnitude endpoint. -/
def tfinBadCore (w tenX : Nat) : Nat :=
  let p := Verified.MulWide.hl w tenX
  bnat (1 < p.2) + bnat (p.2 = 1) * bnat (KLO < p.1)

/-- Lower-endpoint violation bit. -/
def Cfg.tfinBadLo (c : Cfg) (z : TSel) (t : TState) : Nat :=
  let g := tfinGLo z t
  let sign := bnat (H63 ≤ g)
  let mag := if sign = 1 then tsub 0 g else g
  sign * tfinBadCore mag (z.X * 10 % M) * c.tfinChk z

/-- Upper-endpoint violation bit. -/
def Cfg.tfinBadHi (c : Cfg) (z : TSel) (t : TState) : Nat :=
  let g := tfinGHi z t
  let sign := bnat (H63 ≤ g)
  let mag := if sign = 1 then tsub 0 g else g
  (1 - sign) * tfinBadCore mag (z.X * 10 % M) * c.tfinChk z

/-- Finalization violation flag, factored for modular denotation proofs. -/
def Cfg.tfinViol (c : Cfg) (z : TSel) (t : TState) : Nat :=
  tguard z.isF (tfinGHi z t)
      (tguard z.isF (tfinGLo z t) t.viol) |||
    c.tfinBadLo z t ||| c.tfinBadHi z t

/-- Transparent finalization transition (`finBody`). -/
def Cfg.tfin (c : Cfg) (z : TSel) (t : TState) : TState :=
  ⟨c.tfinViol z t, t.res, t.sq, t.par, t.sigma,
    t.wLo, t.wHi, t.wwLo, t.wwHi, tfinDLo z t, tfinDHi z t,
    tfinGLo z t, tfinGHi z t, t.arr⟩

/-- **One full iteration of the loop**, in plain arithmetic. -/
def Cfg.tstep (c : Cfg) (idx : Nat) (t : TState) : TState :=
  -- selectors and decode
  let z := c.tsel idx
  -- phase 1: trial division
  let u := ttrial z t
  -- pass A: sigma
  let v := tpassA z u
  -- weight
  let t1 := tweight z v
  -- pass B: the divisor pair
  let t3 := c.tpassB z t1
  -- finalize
  c.tfin z t3

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
forces `g1SweepOK`. -/
def Cfg.tFlag (c : Cfg) : Nat := c.tRun.viol

/-- The transparent model's final `g` cell (both endpoints encoded), for
cross-checks. -/
def Cfg.tG (c : Cfg) : Nat × Nat := (c.tRun.gLo, c.tRun.gHi)


/-! ## §9 First simulation pieces: the truncated divider is the proved one

The start of obligation (2) (`tFlag = 0 → g1SweepOK`): the transparent
model's `10¹⁸` divider — truncations and all — equals the *proved* divider
of `Ports/Section413Cells.lean` on every input the width guards admit.
`tdiv18_eq` composes: one truncated long-division step below the quotient
cap (`tld_eq_ldStep`), the five-digit run (`tld_run5`), the fold-free digit
cleanup (`clean_digits`), and the tail characterization (`ttail_char`);
`divP18q_spec`/`divP18ceil_spec` then give the exact `⌊x/10¹⁸⌋`/`⌈x/10¹⁸⌉`
semantics.  The guarded regime is `x < 2¹²¹`; the guards cap each factor's
magnitude at `2⁶⁰`, so every product the sweep divides is `≤ 2¹²⁰`.
-/

open LeanCompCert.Ports.Section413Cells (ldStep longDivStep ldStep_fold
  divP18q divP18ceil divP18w digitsW shr18 divP18q_spec divP18ceil_spec)

set_option linter.unusedSimpArgs false

/-! Helper lemmas proved in Probe6 (inlined here). -/

theorem tld_eq_ldStep (st : Nat × Nat) (dig : Nat)
    (hq : st.1 < 4398046511104) (hr : st.2 < 3814697265625)
    (hd : dig < 4194304) :
    tld st dig = ldStep st dig := by
  obtain ⟨q, r⟩ := st
  simp only at hq hr
  have h1 : r * 4194304 % 18446744073709551616 = r * 4194304 :=
    Nat.mod_eq_of_lt (by omega)
  have h2 : (r * 4194304 + dig) % 18446744073709551616 =
      r * 4194304 + dig := Nat.mod_eq_of_lt (by omega)
  have h3 : q * 4194304 % 18446744073709551616 = q * 4194304 :=
    Nat.mod_eq_of_lt (by omega)
  have h4 : (q * 4194304 + (r * 4194304 + dig) / 3814697265625) %
      18446744073709551616 =
      q * 4194304 + (r * 4194304 + dig) / 3814697265625 :=
    Nat.mod_eq_of_lt (by omega)
  simp only [tld, ldStep, LeanCompCert.Ports.Section413Cells.D5,
    LeanCompCert.Ports.Section413Cells.B22, D5,
    LeanCompCert.Verified.Reflect.M, Nat.reducePow]
  rw [h1, h2, h3, h4]

theorem tld_run5 (d4 d3 d2 d1 d0 : Nat)
    (h4 : d4 < 4194304) (h3 : d3 < 4194304) (h2 : d2 < 4194304)
    (h1 : d1 < 4194304) (h0 : d0 < 4194304)
    (hv : ((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1
      < 2417851639229258349412352) :
    [d4, d3, d2, d1, d0].foldl tld (0, 0) =
      [d4, d3, d2, d1, d0].foldl ldStep (0, 0) := by
  have hD : (0:Nat) < 3814697265625 := by omega
  simp only [List.foldl_cons, List.foldl_nil]
  rw [tld_eq_ldStep (0, 0) d4 (by omega) (by omega) h4]
  have e1 : ldStep (0, 0) d4 = (0, d4) := by
    simp only [ldStep, LeanCompCert.Ports.Section413Cells.D5,
      LeanCompCert.Ports.Section413Cells.B22, Prod.mk.injEq]
    refine ⟨by omega, by omega⟩
  rw [e1]
  rw [tld_eq_ldStep (0, d4) d3 (by omega) (by omega) h3]
  have e2 : ldStep (0, d4) d3 =
      ((d4 * 4194304 + d3) / 3814697265625,
       (d4 * 4194304 + d3) % 3814697265625) := by
    simp only [ldStep, LeanCompCert.Ports.Section413Cells.D5,
      LeanCompCert.Ports.Section413Cells.B22, Prod.mk.injEq]
    exact ⟨by omega, trivial⟩
  rw [e2]
  rw [tld_eq_ldStep ((d4 * 4194304 + d3) / 3814697265625,
    (d4 * 4194304 + d3) % 3814697265625) d2
    (by show (d4 * 4194304 + d3) / 3814697265625 < 4398046511104; omega)
    (by show (d4 * 4194304 + d3) % 3814697265625 < 3814697265625; omega) h2]
  have e3 : ldStep ((d4 * 4194304 + d3) / 3814697265625,
      (d4 * 4194304 + d3) % 3814697265625) d2 =
      (((d4 * 4194304 + d3) * 4194304 + d2) / 3814697265625,
       ((d4 * 4194304 + d3) * 4194304 + d2) % 3814697265625) := by
    have h := longDivStep (d4 * 4194304 + d3) d2 4194304 3814697265625 hD
    simp only [ldStep, LeanCompCert.Ports.Section413Cells.D5,
      LeanCompCert.Ports.Section413Cells.B22, Prod.mk.injEq]
    exact ⟨h.1.symm, h.2.symm⟩
  rw [e3]
  rw [tld_eq_ldStep (((d4 * 4194304 + d3) * 4194304 + d2) / 3814697265625,
    ((d4 * 4194304 + d3) * 4194304 + d2) % 3814697265625) d1
    (by show ((d4 * 4194304 + d3) * 4194304 + d2) / 3814697265625
      < 4398046511104; omega)
    (by show ((d4 * 4194304 + d3) * 4194304 + d2) % 3814697265625
      < 3814697265625; omega) h1]
  have e4 : ldStep (((d4 * 4194304 + d3) * 4194304 + d2) / 3814697265625,
      ((d4 * 4194304 + d3) * 4194304 + d2) % 3814697265625) d1 =
      ((((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) / 3814697265625,
       (((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) %
         3814697265625) := by
    have h := longDivStep ((d4 * 4194304 + d3) * 4194304 + d2) d1 4194304
      3814697265625 hD
    simp only [ldStep, LeanCompCert.Ports.Section413Cells.D5,
      LeanCompCert.Ports.Section413Cells.B22, Prod.mk.injEq]
    exact ⟨h.1.symm, h.2.symm⟩
  rw [e4]
  rw [tld_eq_ldStep
    ((((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) / 3814697265625,
     (((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) % 3814697265625)
    d0
    (by show (((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) /
      3814697265625 < 4398046511104; omega)
    (by show (((d4 * 4194304 + d3) * 4194304 + d2) * 4194304 + d1) %
      3814697265625 < 3814697265625; omega) h0]

/-! The main chain: `tdiv18 = ttail (messy digits)` definitionally, the
digit list cleans up by a fold-free list equality, and the clean tail is
evaluated by `tld_run5` + `ldStep_fold`. -/

theorem clean_digits (lo hi : Nat) (hlo : lo < 18446744073709551616)
    (_hhi : hi < 18446744073709551616) :
      ([ (hi >>> 18) >>> 24
       , ((hi >>> 18) >>> 2) &&& 4194303
       , (((((lo >>> 18) + (hi <<< 46) % M) % M) >>> 44) + (((hi >>> 18) &&& 3) * 1048576) % M) % M
       , ((((lo >>> 18) + (hi <<< 46) % M) % M) >>> 22) &&& 4194303
       , (((lo >>> 18) + (hi <<< 46) % M) % M) &&& 4194303 ] : List Nat) =
      [ hi / 262144 / 16777216
      , hi / 262144 / 4 % 4194304
      , (lo / 262144 + hi % 262144 * 70368744177664) / 17592186044416 + hi / 262144 % 4 * 1048576
      , (lo / 262144 + hi % 262144 * 70368744177664) / 4194304 % 4194304
      , (lo / 262144 + hi % 262144 * 70368744177664) % 4194304 ] := by
  have hA22 : forall n : Nat, n &&& 4194303 = n % 4194304 := fun n => by
    have := Nat.and_two_pow_sub_one_eq_mod n 22
    simpa using this
  have hA2 : forall n : Nat, n &&& 3 = n % 4 := fun n => by
    have := Nat.and_two_pow_sub_one_eq_mod n 2
    simpa using this
  have hR : forall (n k : Nat), n >>> k = n / 2 ^ k :=
    fun n k => Nat.shiftRight_eq_div_pow n k
  have hL : hi <<< 46 = hi * 70368744177664 := by
    have := Nat.shiftLeft_eq hi 46
    simpa using this
  have hyLo : (((lo >>> 18) + (hi <<< 46) % M) % M) = (lo / 262144 + hi % 262144 * 70368744177664) := by
    rw [hR lo 18, hL]
    simp only [LeanCompCert.Verified.Reflect.M, Nat.reducePow]
    omega
  have c4 : (hi >>> 18) >>> 24 = hi / 262144 / 16777216 := by
    rw [hR hi 18, hR _ 24]
  have c3 : ((hi >>> 18) >>> 2) &&& 4194303 = hi / 262144 / 4 % 4194304 := by
    rw [hR hi 18, hR _ 2, hA22]
  have c2 : (((((lo >>> 18) + (hi <<< 46) % M) % M) >>> 44) + (((hi >>> 18) &&& 3) * 1048576) % M) % M = (lo / 262144 + hi % 262144 * 70368744177664) / 17592186044416 + hi / 262144 % 4 * 1048576 := by
    rw [hyLo, hR _ 44, hR hi 18, hA2]
    simp only [LeanCompCert.Verified.Reflect.M, Nat.reducePow]
    omega
  have c1 : ((((lo >>> 18) + (hi <<< 46) % M) % M) >>> 22) &&& 4194303 = (lo / 262144 + hi % 262144 * 70368744177664) / 4194304 % 4194304 := by
    rw [hyLo, hR _ 22, hA22]
  have c0 : (((lo >>> 18) + (hi <<< 46) % M) % M) &&& 4194303 = (lo / 262144 + hi % 262144 * 70368744177664) % 4194304 := by
    rw [hyLo, hA22]
  rw [c4, c3, c2, c1, c0]

theorem ttail_char (lo : Nat) (ds : List Nat) (q r : Nat)
    (h : ds.foldl tld (0, 0) = (q, r)) (hq : q < 9223372036854775808) :
    ttail lo ds =
      (q, (if lo &&& 262143 = 0 ∧ r = 0 then 0 else 1) + q) := by
  unfold ttail
  rw [h]
  dsimp only
  simp only [bnat, tsub, LeanCompCert.Verified.Reflect.M, Nat.reducePow,
    Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  by_cases h1 : lo &&& 262143 = 0 <;> by_cases h2 : r = 0 <;>
    simp only [h1, h2, reduceIte, if_true, if_false, and_true, and_false,
      true_and, false_and, and_self] <;>
    omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- `tdiv18` through `ttail` at the clean digit list. -/
theorem tdiv18_ttail_clean (lo hi : Nat) (hlo : lo < 18446744073709551616)
    (hhi : hi < 18446744073709551616) :
    tdiv18 lo hi = ttail lo
      [ hi / 262144 / 16777216
      , hi / 262144 / 4 % 4194304
      , ((lo / 262144 + hi % 262144 * 70368744177664) / 17592186044416 + hi / 262144 % 4 * 1048576)
      , (lo / 262144 + hi % 262144 * 70368744177664) / 4194304 % 4194304
      , (lo / 262144 + hi % 262144 * 70368744177664) % 4194304 ] := by
  unfold tdiv18
  dsimp only
  rw [clean_digits lo hi hlo hhi]

set_option maxHeartbeats 16000000 in
/-- **The transparent divider is the proved divider**, on every input the
width guards admit (`x < 2^121`; guarded products are at most `2^120`). -/
theorem tdiv18_eq (lo hi : Nat) (hlo : lo < 18446744073709551616)
    (hhi : hi < 18446744073709551616)
    (hx : lo + 18446744073709551616 * hi
      < 2658455991569831745807614120560689152) :
    tdiv18 lo hi = (divP18q lo hi, divP18ceil lo hi) := by
  have hA18 : lo &&& 262143 = lo % 262144 := by
    have := Nat.and_two_pow_sub_one_eq_mod lo 18
    simpa using this
  have hfold :
      ([ hi / 262144 / 16777216
       , hi / 262144 / 4 % 4194304
       , ((lo / 262144 + hi % 262144 * 70368744177664) / 17592186044416 + hi / 262144 % 4 * 1048576)
       , (lo / 262144 + hi % 262144 * 70368744177664) / 4194304 % 4194304
       , (lo / 262144 + hi % 262144 * 70368744177664) % 4194304 ] : List Nat).foldl tld (0, 0) =
      ((divP18w lo hi).1, (divP18w lo hi).2) :=
    (tld_run5 (hi / 262144 / 16777216) (hi / 262144 / 4 % 4194304) ((lo / 262144 + hi % 262144 * 70368744177664) / 17592186044416 + hi / 262144 % 4 * 1048576) ((lo / 262144 + hi % 262144 * 70368744177664) / 4194304 % 4194304) ((lo / 262144 + hi % 262144 * 70368744177664) % 4194304) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)).trans rfl
  have hq1 : (divP18w lo hi).1 =
      (lo + 18446744073709551616 * hi) / 1000000000000000000 :=
    divP18q_spec lo hi hlo hhi
  rw [tdiv18_ttail_clean lo hi hlo hhi]
  rw [ttail_char lo _ _ _ hfold (by omega)]
  simp only [LeanCompCert.Ports.Section413Cells.divP18ceil,
    LeanCompCert.Ports.Section413Cells.E18, hA18, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  have hqd : divP18q lo hi = (divP18w lo hi).1 := rfl
  by_cases h1 : lo % 262144 = 0 <;>
    by_cases h2 : (divP18w lo hi).2 = 0 <;>
    simp only [h1, h2, if_true, if_false, and_true, and_false, true_and,
      false_and, and_self] <;>
    omega

set_option linter.unusedSimpArgs true

end LeanCompCert.Ports.Section413G1Program
