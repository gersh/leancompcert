import LeanCompCert.Verified.ArrayBridge

/-!
# A Dirichlet `L`-function zero-ladder checker in the array fragment

The Dirichlet analogue of the zeta-side PT21 ladder: a streaming, integer-only
checker for the finite computation behind

> D. J. Platt, *Numerical computations concerning the GRH*,
> arXiv:1305.3087v1 Theorem 7.1 = Math. Comp. **85** (2016) Theorem 10.1.

As on the zeta side, this is the **checker**, not the prover.  The search — the
all-character Hurwitz/Bluestein transform that produces `Λ(1/2 + it, χ)` — is
not expressible here and never will be: `AProgram` is integer-only, with no
floating point, no complex numbers, a fixed trip count and no recursion.  What
*is* expressible is the entire integer consequence of that search, which is
what the theorem's finite content actually rests on:

* **sign-change bracket counting** — each `Λ` sample is reduced by the producer
  to one bit, and the checker *derives* the bracket count from the bitmap
  rather than reading an advertised one;
* **the Turing closure arithmetic** — Rumely's Theorem 2 one-sided bound,
  evaluated in scaled integers with outward rounding, pinning the zero count of
  each character;
* **per-character counting and roster closure** — that the block chain is
  gap-free, that every character's grid covers its exact source height
  `T_q = max(10⁸/q, 200 + c/q)`, and that the conjugation pairing is an
  involution on the roster.

## Why Rumely's Theorem 2, and not Platt's printed Theorem 3.2

Platt's arXiv v1 Theorem 3.2 prints a `+2h` term inside a bracket which, under
the corrected scaling, contributes `2/π = 0.63662…` out of a decision budget
whose total width is `1`.  That term is not in the identity, is not in
Trudgian's (2.3), and has been refuted numerically (measured residual `+0.0107`
for `q = 3` and `+0.0252` for `q = 5`, against the `+0.6366` the printed term
requires).  The bound encoded here is therefore the one-sided form

```text
  N_χ(t₀)  ≤  (1/(hπ))[ ((2ht₀ + h²)/2)·log(q/π) + 2∫ Im log Γ ]
             − (1/h)[ Σ_{B,χ} + Σ_{B,χ̄} ]
             + 2·R(q,t₀,h)/h,        R(q,t₀,h) = 1.8397 + 0.1242·log(q(t₀+h)/2π)
```

with the staircase `Σ_B` entering with a minus sign, so that an *under*-estimate
of it weakens the bound in the safe direction.

## What a record commits to, and what it does not

An independent oracle, written from this file's specification and sharing no
code with it, swept 370,621 single-word mutations of a source-parameter stream.
Ten of the thirteen fields came back pinned exactly at every position class.
The other two were design decisions, and both are now taken:

* **`uElem`** is an interval endpoint, so an upper-bound check alone leaves it a
  range — measured at `1.125·10¹²` wide, dominated by a `2⁴⁰` sign bias.  That
  bias turned out to be dead weight: `U ≈ N·h` is positive and large, and the
  genuinely negative case is already rejected by the underflow guard.  It is
  gone, and the lower Turing side is now checked too, which confines the field
  to one `henc` — about `10⁵` times tighter.

* **`bits`** was constrained only through its transition count, so any of the
  `C(63, trI)` bitmaps with the right count passed — `4.9·10¹⁷` of them in the
  first record alone.  The ladder is a counting argument and does not *need*
  the positions; but a certificate produced once and replayed later should
  commit to the bytes it was checked against, not to an equivalence class of
  them.  Each record now carries a digest chaining the bitmaps.

The chain runs across the **whole stream**, not per character, and the epilogue
checks the final value against `Cfg.termDigest`.  Both details are load-bearing,
and a first draft got them wrong: with a chain that restarted at each character
and no terminal check, nothing downstream ever re-derived a closing record's
digest, so at those records — and only those — an adversary could move `bits`
and `digest` together for two words with no downstream consequence.  The oracle
demonstrated it with concrete witnesses at records 77 and 155, `sj`- and
`trI`-preserving so every other check stayed satisfied.  Those were exactly the
records carrying the Turing data, which is the worst possible place for the
cheapest forgery.  A global chain plus a terminal commitment makes the cost
uniform: any single-record change forces rewriting every digest after it, and
the last one is pinned from outside.

### What the digest is not

**The chain makes forgery cost *uniform*, which was the defect it was built to
fix.  It does not make forgery *hard*, and it must never be quoted as if it
did.**  That is the whole claim, and it depends only on the structure of the
recurrence, not on any cost estimate.

The figures below are supporting detail.  They are recorded because a reader
deciding how much weight to put on this field needs the real number, and
because two plausible-sounding wrong ones — "one record at ≈2.7%" and
"two records at ≈2³² work" — were considered and refuted during review.  Do
not reintroduce them.

The recurrence `d ↦ d·M + bits mod 2⁶⁴` with `M = 2654435761` is linear, and
`M` is odd and therefore invertible mod `2⁶⁴`
(`M⁻¹ = 14962265741255716689`).  An adversary who controls a tail does not
search for a collision; he solves for one.  The exact costs, all checked
constructively rather than estimated:

* with **one** free record there is *no* freedom at all.  Fixing everything
  else, `d_last = termDigest` is a single affine constraint in `bits_k` with
  leading coefficient `M^(last−k)`, so it has a unique solution — and the
  honest stream already satisfies it, so the forced value *is* the original.
  Solving backwards from `termDigest` at all 156 positions of the source
  stream reproduced the original bitmap in 156 of 156 cases.  A full-tail
  rewrite at `k = 10` lands the terminal digest on `14195738217445398444`
  instead of `4027133456908973396`, and is rejected;

* with **two** free records it is immediate.  The terminal digest moves by
  `δ₁·M^(last−k₁) + δ₂·M^(last−k₂)`, so `δ₂ = −δ₁·M^(k₂−k₁)` is a direct
  linear solve — no search.  The only filter is that both forged bitmaps land
  in their own `trI` class, about `5%` each near `trI = 32`.  A witness was
  found in 43 random draws, sub-second, and accepted with `termDigest`
  unchanged.

So the minimum forgery is **two records, and it takes seconds** — not one
record, and not `2³²` work.  Both of those figures appeared in an earlier draft
of this comment; both were wrong, in opposite directions, and neither had been
computed.

This is not a defect to be repaired here.  An arithmetic checker in an
integer fragment — no rotations, no S-boxes, 64-bit words — is the wrong place
to build collision resistance, and attempting it would spend instructions
without achieving it.

The division of labour, which is the thing to remember:

> this program validates **structure** — counts, windows, chaining, coverage;
> the campaign-level SHA-256 tier validates **identity**.
> Neither substitutes for the other.

The `digest` field exists so that corruption is detectable at *uniform* cost
across positions, which is what the closing-record asymmetry violated.  It is
not an integrity mechanism.  Integrity is carried by the hash tier above, the
same L2/L3/L4 chaining the zeta side uses, where a skeptic compares 32-byte
roots.

And the digest does not make a bit *true*: a producer who forges the whole
stream forges the digests with it.  The truth of the bits is the L0 obligation,
and no integer check on a record can discharge it.

## The arithmetic shape, and why there is no division

Write the right-hand side as `U/h`.  The decision is `U/h < N + 1`, which pins
`N` against the certified lower bound `N ≥ derivedCount`.  Since `h > 0`, that
is `U < (N+1)·h` — **a multiplication and a comparison, no division at all.**
With `Uenc = ⌈U·SCALE⌉` and `henc = ⌊h·SCALE⌋` the check is exactly

```text
  N · henc  ≤  Uenc  <  (N + 1) · henc
```

which is sound because `U ≤ Uenc/SCALE` and `h ≥ henc/SCALE`.  Both sides are
checked: the Turing argument bounds `uElem` from below (`N ≤ U/h`) exactly as
firmly as the pinning bounds it from above, so the field is confined to a
window of width one `henc`.  This is strictly better than the zeta ladder's
`floor_div`/`ceil_div` pair, which had to round in two directions.

The staircase is *derived*, never read.  A block is exactly 64 samples at
Platt's grid spacing `δ = 5/64` (§7 of the source: "steps of 5/64, … about 5
times the expected zero density"), so a block spans exactly `Δt = 5` and its
bitmap is exactly one `uint64_t`.  With `SCALE = 2²⁰`, `SCALE·δ = 81920`
exactly — the same exact-scaling trick the zeta ladder used to make `δ = 21/512`
land on the integer `42`.

The Turing window is the last `2` blocks of each character, i.e. `h = 10`, and
the checker *verifies* `henc = 10·SCALE` rather than trusting the producer's
window width.

## Record format

`13` words per record, one record per (character, t-block), streamed in order:

| off | field | meaning |
|----:|-------|---------|
| 0 | `tag` | `q·2²⁰ + charOrdinal`; non-decreasing, constant within a character |
| 1 | `blk` | 0-based block index within the character |
| 2 | `lower` | zeros with `0 < γ ≤ t_lo` |
| 3 | `slots` | advertised brackets in this block |
| 4 | `upper` | advertised `lower + slots` |
| 5 | `bits` | 64 sign samples; bit `j` set ⟺ the producer's enclosure of `Λ` at that lattice ordinate was strictly positive |
| 6 | `stat` | resolved stationary (double-zero) cells, `≤ 4` |
| 7 | `isLast` | `1` on the character's final block, else `0` |
| 8 | `uElem` | `⌈U_elem·SCALE⌉`, the elementary + log-Γ + `2R` group |
| 9 | `henc` | `⌊h·SCALE⌋`; must be `10·SCALE` |
| 10 | `tqNum` | `q·T_q`, the exact integer `max(10⁸, 200q + c)` |
| 11 | `conjFirst` | record index of the conjugate character's first block |
| 12 | `digest` | running digest of the whole stream's bitmaps through this record |

Every word is constrained on every record.  `uElem` and `henc` carry meaning
only on a closing block, so off one they are required to be *zero* rather than
left free; `tqNum` must equal the derived height everywhere; `conjFirst` must
be constant across a character.  An earlier draft gated the last three on
`isLast`/`newch`, which left them corruptible without detection on the other
records — a defect an independent oracle found by mutating them there and
getting a clean bill from both compilers.

### The recurring trap, and the test that catches it

Every defect found in this port was the same shape: **a check that looks like
it constrains something but is quietly parameterised by the thing it is meant
to constrain.**  The gated fields above were one instance.  The closing-record
digest asymmetry was another.  A third was in the *test harness* rather than
the checker: `termDigest` was being derived from the words under test, so a
forgery moved the commitment along with itself and every `bits`/`digest`
mutation scored as caught when it was not.

The obvious diagnostic — "was this derived from the data it constrains?" — is
the wrong one, because it condemns benign cases.  The oracle's own
`termDigest` is read off the stream data and is perfectly sound.  The right
question is:

> **did deriving it leave any freedom?**

Deriving `termDigest` once from the *conforming* input leaves nobody free: given
the bitmaps and the chain rule there is no choice to make, so it is uniquely
determined.  Deriving it from the words *under test* leaves the forger free to
move it.  Same provenance, opposite answers — and it is the freedom, not the
provenance, that decides.

The detection discipline that actually worked, for whoever extends this: compute
every commitment once from the conforming input and hold it fixed; sweep
mechanically rather than testing hand-picked guesses; commit to a prediction
before running the sweep; exhibit witnesses rather than survivor counts; and
check the harness itself before trusting a clean sweep.

## What the program returns

The count of failed checks.  The artifact's `main` returns 0 exactly when that
count is zero, which is the "violation counter" discipline: no early exit, no
branch, every test executed on every record.

## What is proved here, and what is not

Proved: `program_wf`, hence `program_compiled` — `AProgram.evalCC_compile`
instantiated, so the compiled CCIR trace and the emitted C compute exactly this
program's denotation.

Proved by kernel evaluation: that the denotation *is* the specification, on
small rosters, against `refCheck` below — which is written from the record
format, not from the encoding — **including configurations that must fail**.

Not proved here, and deliberately visible:

* that a bit is the true sign of `Λ(1/2 + it, χ)` at that ordinate.  That is the
  entire empirical content, and it is exactly the obligation the zeta ladder
  leaves open too;
* that `uElem` encloses the real elementary/log-Γ/Rumely group;
* Rumely's Theorem 2 itself, which is a cited external atom;
* that the roster of records is the complete roster of primitive characters
  with `q ≤ 400000`.

Discharging this program therefore **relocates** `platt_theorem_7_1_dirichlet_
verification_source`; it does not remove it.  See the module's report for what
would.
-/

namespace LeanCompCert.Ports.DirichletLadder

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-! ## Format constants -/

/-- Words per block record. -/
def recW : Nat := 13
/-- Fixed-point scale for the Turing arithmetic, `2^20`. -/
def scaleB : Nat := 1048576
/-- The digest multiplier for the per-character bitmap chain. -/
def digMul : Nat := 2654435761
/-- Blocks in the Turing window; `h = 5·winW`. -/
def winW : Nat := 2
/-- The window width `h`, scaled: `winW · 5 · scaleB`. -/
def hExpect : Nat := 10485760
/-- Maximum resolved stationary cells per block. -/
def maxStat : Nat := 4
/-- Bits 0..62 of the transition word; bit 63 is the spurious wrap. -/
def mask63 : Nat := 9223372036854775807

/-! ## The byte weight table

`tbl v = popcount v + 256 · Σ_{k<8} k·bit_k v`.  One load per byte gives both
the transition count and the position moment, which is what the staircase
needs; there is no popcount instruction in the fragment. -/

def popc8 (v : Nat) : Nat :=
  (List.range 8).foldl (fun a k => a + (v >>> k) % 2) 0

def mom8 (v : Nat) : Nat :=
  (List.range 8).foldl (fun a k => a + k * ((v >>> k) % 2)) 0

def tblEntry (v : Nat) : Nat := popc8 v + 256 * mom8 v

/-! ## Register allocation -/

def rViol : Nat := 0        -- output: number of failed checks
def rPrevTag : Nat := 1
def rPrevBlk : Nat := 2
def rPrevUpper : Nat := 3
def rPrevBit : Nat := 4     -- last sample bit of the previous block
def rFirstBit : Nat := 5    -- first sample bit of the current character
def rTrI0 : Nat := 6        -- window slot 0 (older block): intra transitions
def rSj0 : Nat := 7         -- window slot 0: Σ j over transitions
def rTrI1 : Nat := 8        -- window slot 1 (current block)
def rSj1 : Nat := 9
def rPrevLast : Nat := 10   -- previous record's `isLast`
def rPrevConj : Nat := 11   -- previous record's `conjFirst`
def rPrevDig : Nat := 12    -- previous record's bitmap digest

def regCount : Nat := 200

/-! ## Configuration -/

structure Cfg where
  /-- Number of block records in the stream. -/
  records : Nat
  /-- `T_q = max(hFloor/q, hLin + c_q/q)`; the floor branch, times `q`. -/
  hFloor : Nat
  /-- The constant term of the linear branch. -/
  hLin : Nat
  /-- The linear branch's numerator for even `q`. -/
  hEven : Nat
  /-- The linear branch's numerator for odd `q`. -/
  hOdd : Nat
  /-- The digest the whole stream must end on.  This terminates the chain: it
  is the only thing that makes forgery cost uniform, because without it the
  final record's `(bits, digest)` pair can be moved together with no downstream
  consequence. -/
  termDigest : Nat
  deriving Repr

def Cfg.tblBase (c : Cfg) : Nat := recW * c.records
def Cfg.arrayLen (c : Cfg) : Nat := recW * c.records + 256

/-! ## Program text -/

abbrev I := AInstr

def bo (d : Nat) (o : Op) (a b : Operand) : I := .scalar (.binop d o a b)
def mvl (d v : Nat) : I := .scalar (.mov d (.lit v))
def mvr (d s : Nat) : I := .scalar (.mov d (.reg s))

/-! Keep the digest instructions as lightweight named program constants.  In
particular, denotation proofs can expose the fixed multiplier without reducing
the entire 250-instruction `bodyBlock` at the same time. -/
def digestMulInstr : I := bo 159 .mul (.reg rPrevDig) (.lit digMul)
def digestAddInstr : I := bo 159 .add (.reg 159) (.reg 26)
def digestCompareInstr : I := bo 160 .ne (.reg 158) (.reg 159)
def digestBumpInstr : I := bo rViol .add (.reg rViol) (.reg 160)

/-- Write the 256-entry byte-weight lookup table. -/
def Cfg.tableEntryBlock (c : Cfg) (v : Nat) : List I :=
  [mvl 20 (c.tblBase + v), mvl 21 (tblEntry v), AInstr.store 20 21]

def Cfg.tableBlock (c : Cfg) : List I :=
  (List.range 256).flatMap c.tableEntryBlock

/-- Write the byte table, and seed the stream state. -/
def Cfg.initBlock (c : Cfg) : List I :=
  c.tableBlock ++ [mvl rPrevLast 1]

/--
One record.  Straight-line, data-independent: every test runs on every record
and contributes `0` or `1` to `rViol`.
-/
def Cfg.bodyBlock (c : Cfg) : List I :=
  [ -- ---- load the record: reg 20 is a running address ----
    bo 20 .mul .idx (.lit recW)
  , AInstr.load 21 20                                   -- tag
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 22 20    -- blk
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 23 20    -- lower
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 24 20    -- slots
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 25 20    -- upper
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 26 20    -- bits
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 27 20    -- stat
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 28 20    -- isLast
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 29 20    -- uElem
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 30 20    -- henc
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 31 20    -- tqNum
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 32 20    -- conjFirst
  , bo 20 .add (.reg 20) (.lit 1), AInstr.load 158 20   -- digest

    -- ---- character framing ----
  , bo 33 .eq (.reg 21) (.reg rPrevTag)            -- same
  , bo 34 .sub (.lit 1) (.reg 33)                  -- newch
  , bo 35 .ge (.reg 21) (.reg rPrevTag)            -- tags non-decreasing
  , bo 36 .sub (.lit 1) (.reg 35)
  , bo rViol .add (.reg rViol) (.reg 36)

    -- a new character may only start after the previous one closed
  , bo 37 .sub (.lit 1) (.reg rPrevLast)
  , bo 38 .mul (.reg 34) (.reg 37)
  , bo rViol .add (.reg rViol) (.reg 38)
    -- and a character may not continue past its own closing block
  , bo 39 .mul (.reg 33) (.reg rPrevLast)
  , bo rViol .add (.reg rViol) (.reg 39)

    -- block index: 0 at a new character, prev+1 inside one
  , bo 40 .add (.reg rPrevBlk) (.lit 1)
  , bo 41 .mul (.reg 33) (.reg 40)
  , bo 42 .ne (.reg 22) (.reg 41)
  , bo rViol .add (.reg rViol) (.reg 42)

    -- count cursor: 0 at a new character, prev upper inside one
  , bo 43 .mul (.reg 33) (.reg rPrevUpper)
  , bo 44 .ne (.reg 23) (.reg 43)
  , bo rViol .add (.reg rViol) (.reg 44)

    -- slot closure
  , bo 45 .add (.reg 23) (.reg 24)
  , bo 46 .ne (.reg 25) (.reg 45)
  , bo rViol .add (.reg rViol) (.reg 46)

    -- `isLast` and `stat` must be in range
  , bo 47 .gt (.reg 28) (.lit 1)
  , bo rViol .add (.reg rViol) (.reg 47)
  , bo 48 .eq (.reg 28) (.lit 1)                   -- isLastB
  , bo 49 .gt (.reg 27) (.lit maxStat)
  , bo rViol .add (.reg rViol) (.reg 49)

    -- ---- transition word and its byte decomposition ----
  , bo 50 .lshr (.reg 26) (.lit 1)
  , bo 51 .bxor (.reg 26) (.reg 50)
  , bo 52 .band (.reg 51) (.lit mask63)            -- t

  , bo 53 .band (.reg 52) (.lit 255)
  , bo 53 .add (.reg 53) (.lit c.tblBase), AInstr.load 54 53
  , bo 55 .lshr (.reg 52) (.lit 8), bo 55 .band (.reg 55) (.lit 255)
  , bo 55 .add (.reg 55) (.lit c.tblBase), AInstr.load 56 55
  , bo 57 .lshr (.reg 52) (.lit 16), bo 57 .band (.reg 57) (.lit 255)
  , bo 57 .add (.reg 57) (.lit c.tblBase), AInstr.load 58 57
  , bo 59 .lshr (.reg 52) (.lit 24), bo 59 .band (.reg 59) (.lit 255)
  , bo 59 .add (.reg 59) (.lit c.tblBase), AInstr.load 60 59
  , bo 61 .lshr (.reg 52) (.lit 32), bo 61 .band (.reg 61) (.lit 255)
  , bo 61 .add (.reg 61) (.lit c.tblBase), AInstr.load 62 61
  , bo 63 .lshr (.reg 52) (.lit 40), bo 63 .band (.reg 63) (.lit 255)
  , bo 63 .add (.reg 63) (.lit c.tblBase), AInstr.load 64 63
  , bo 65 .lshr (.reg 52) (.lit 48), bo 65 .band (.reg 65) (.lit 255)
  , bo 65 .add (.reg 65) (.lit c.tblBase), AInstr.load 66 65
  , bo 67 .lshr (.reg 52) (.lit 56), bo 67 .band (.reg 67) (.lit 255)
  , bo 67 .add (.reg 67) (.lit c.tblBase), AInstr.load 68 67

    -- trI = Σ_b popcount(byte b);  sj = Σ_b (8b·popcount + moment)
  , bo 69 .band (.reg 54) (.lit 255)
  , bo 70 .band (.reg 56) (.lit 255)
  , bo 71 .band (.reg 58) (.lit 255)
  , bo 72 .band (.reg 60) (.lit 255)
  , bo 73 .band (.reg 62) (.lit 255)
  , bo 74 .band (.reg 64) (.lit 255)
  , bo 75 .band (.reg 66) (.lit 255)
  , bo 76 .band (.reg 68) (.lit 255)
  , bo 77 .add (.reg 69) (.reg 70)
  , bo 77 .add (.reg 77) (.reg 71)
  , bo 77 .add (.reg 77) (.reg 72)
  , bo 77 .add (.reg 77) (.reg 73)
  , bo 77 .add (.reg 77) (.reg 74)
  , bo 77 .add (.reg 77) (.reg 75)
  , bo 77 .add (.reg 77) (.reg 76)                 -- trI

    -- moment accumulation, written out so each byte's 8b·popcount is explicit
  , bo 80 .lshr (.reg 54) (.lit 8)                 -- b = 0: 0·pc + mom
  , bo 81 .lshr (.reg 56) (.lit 8)
  , bo 82 .mul (.reg 70) (.lit 8)
  , bo 81 .add (.reg 81) (.reg 82)
  , bo 83 .lshr (.reg 58) (.lit 8)
  , bo 84 .mul (.reg 71) (.lit 16)
  , bo 83 .add (.reg 83) (.reg 84)
  , bo 85 .lshr (.reg 60) (.lit 8)
  , bo 86 .mul (.reg 72) (.lit 24)
  , bo 85 .add (.reg 85) (.reg 86)
  , bo 87 .lshr (.reg 62) (.lit 8)
  , bo 88 .mul (.reg 73) (.lit 32)
  , bo 87 .add (.reg 87) (.reg 88)
  , bo 89 .lshr (.reg 64) (.lit 8)
  , bo 90 .mul (.reg 74) (.lit 40)
  , bo 89 .add (.reg 89) (.reg 90)
  , bo 91 .lshr (.reg 66) (.lit 8)
  , bo 92 .mul (.reg 75) (.lit 48)
  , bo 91 .add (.reg 91) (.reg 92)
  , bo 93 .lshr (.reg 68) (.lit 8)
  , bo 94 .mul (.reg 76) (.lit 56)
  , bo 93 .add (.reg 93) (.reg 94)
  , bo 95 .add (.reg 80) (.reg 81)
  , bo 95 .add (.reg 95) (.reg 83)
  , bo 95 .add (.reg 95) (.reg 85)
  , bo 95 .add (.reg 95) (.reg 87)
  , bo 95 .add (.reg 95) (.reg 89)
  , bo 95 .add (.reg 95) (.reg 91)
  , bo 95 .add (.reg 95) (.reg 93)                 -- sj

    -- ---- derived slot count ----
  , bo 96 .band (.reg 26) (.lit 1)                 -- firstBit
  , bo 97 .lshr (.reg 26) (.lit 63)
  , bo 97 .band (.reg 97) (.lit 1)                 -- lastBit
  , bo 98 .bxor (.reg rPrevBit) (.reg 96)
  , bo 98 .mul (.reg 33) (.reg 98)                 -- cross (only inside a character)
  , bo 99 .mul (.reg 27) (.lit 2)
  , bo 100 .add (.reg 77) (.reg 98)
  , bo 100 .add (.reg 100) (.reg 99)               -- derived
  , bo 101 .ne (.reg 24) (.reg 100)
  , bo rViol .add (.reg rViol) (.reg 101)

    -- ---- final-block obligations, all gated by isLastB (reg 48) ----
    -- the Turing window needs at least `winW` blocks
  , bo 102 .lt (.reg 22) (.lit (winW - 1))
  , bo 102 .mul (.reg 48) (.reg 102)
  , bo rViol .add (.reg rViol) (.reg 102)

    -- the declared window width is not trusted
  , bo 103 .ne (.reg 30) (.lit hExpect)
  , bo 103 .mul (.reg 48) (.reg 103)
  , bo rViol .add (.reg rViol) (.reg 103)

    -- staircase, derived: 127·trI0 − sj0 + 64·cross + 63·trI1 − sj1
  , bo 104 .mul (.reg rTrI0) (.lit 127)
  , bo 105 .mul (.reg 77) (.lit 63)
  , bo 106 .mul (.reg 98) (.lit 64)
  , bo 107 .add (.reg 104) (.reg 105)
  , bo 107 .add (.reg 107) (.reg 106)
  , bo 108 .add (.reg rSj0) (.reg 95)
  , bo 109 .ge (.reg 107) (.reg 108)               -- non-negativity, structural
  , bo 110 .sub (.lit 1) (.reg 109)
  , bo 110 .mul (.reg 48) (.reg 110)
  , bo rViol .add (.reg rViol) (.reg 110)
  , bo 111 .mul (.reg 109) (.reg 107)
  , bo 112 .mul (.reg 109) (.reg 108)
  , bo 113 .sub (.reg 111) (.reg 112)              -- stairWeight
  , bo 114 .mul (.reg 113) (.lit 81920)            -- scaled by SCALE·δ, exact

    -- Uenc = uElem − stairScaled, with an explicit underflow test
  , bo 115 .ge (.reg 29) (.reg 114)
  , bo 116 .sub (.lit 1) (.reg 115)
  , bo 116 .mul (.reg 48) (.reg 116)
  , bo rViol .add (.reg rViol) (.reg 116)
  , bo 117 .mul (.reg 115) (.reg 29)
  , bo 118 .mul (.reg 115) (.reg 114)
  , bo 119 .sub (.reg 117) (.reg 118)              -- Uenc

    -- the decision: Uenc < BIAS + (N+1)·henc
  , bo 120 .add (.reg 25) (.lit 1)
  , bo 121 .mul (.reg 120) (.reg 30)               -- (N+1)·henc
  , bo 122 .lt (.reg 119) (.reg 121)
  , bo 123 .sub (.lit 1) (.reg 122)
  , bo 123 .mul (.reg 48) (.reg 123)
  , bo rViol .add (.reg rViol) (.reg 123)
    -- and the lower side: `N ≤ U/h` forces `Uenc ≥ N·henc`, which pins `uElem`
    -- to a window of width exactly one `henc` instead of leaving it free
  , bo 161 .mul (.reg 25) (.reg 30)                -- N·henc
  , bo 162 .lt (.reg 119) (.reg 161)
  , bo 162 .mul (.reg 48) (.reg 162)
  , bo rViol .add (.reg rViol) (.reg 162)

    -- parity: the endpoint signs agree iff the bracket total is even
  , bo 124 .eq (.reg rFirstBit) (.reg 97)
  , bo 125 .band (.reg 25) (.lit 1)
  , bo 126 .sub (.lit 1) (.reg 125)
  , bo 127 .ne (.reg 124) (.reg 126)
  , bo 127 .mul (.reg 48) (.reg 127)
  , bo rViol .add (.reg rViol) (.reg 127)

    -- The source height is *derived* from `q` by Theorem 7.1's own formula,
    -- not read from the record.  Without this a producer could declare a tiny
    -- `T_q` and a grid covering almost nothing would be accepted.
  , bo 128 .lshr (.reg 21) (.lit 20)               -- q
  , bo 144 .band (.reg 128) (.lit 1)               -- q odd
  , bo 145 .mul (.reg 144) (.lit c.hOdd)
  , bo 146 .sub (.lit 1) (.reg 144)
  , bo 146 .mul (.reg 146) (.lit c.hEven)
  , bo 147 .add (.reg 145) (.reg 146)              -- c_q
  , bo 148 .mul (.reg 128) (.lit c.hLin)
  , bo 148 .add (.reg 148) (.reg 147)              -- hLin·q + c_q
  , bo 149 .ge (.reg 148) (.lit c.hFloor)
  , bo 150 .mul (.reg 149) (.reg 148)
  , bo 151 .sub (.lit 1) (.reg 149)
  , bo 151 .mul (.reg 151) (.lit c.hFloor)
  , bo 152 .add (.reg 150) (.reg 151)              -- q·T_q, exact
  , bo 153 .ne (.reg 31) (.reg 152)
  , bo rViol .add (.reg rViol) (.reg 153)          -- on EVERY record, not just a closing one
  , bo 129 .add (.reg 22) (.lit 1)                 -- blockCount
  , bo 130 .mul (.reg 129) (.lit 5)
  , bo 130 .mul (.reg 130) (.reg 128)              -- 5·blockCount·q
  , bo 131 .lt (.reg 130) (.reg 152)
  , bo 131 .mul (.reg 48) (.reg 131)
  , bo rViol .add (.reg rViol) (.reg 131)          -- must cover
  , bo 132 .mul (.reg 22) (.lit 5)
  , bo 132 .mul (.reg 132) (.reg 128)              -- 5·(blockCount−1)·q
  , bo 133 .ge (.reg 132) (.reg 152)
  , bo 133 .mul (.reg 48) (.reg 133)
  , bo rViol .add (.reg rViol) (.reg 133)          -- must not overshoot by a block

    -- ---- conjugation is an involution, checked by load at a character start ----
  , bo 134 .mul (.reg 32) (.lit recW)
  , bo 134 .add (.reg 134) (.lit 11)
  , bo 135 .lt (.reg 134) (.lit c.tblBase)
  , bo 136 .sub (.lit 1) (.reg 135)
  , bo 136 .mul (.reg 34) (.reg 136)
  , bo rViol .add (.reg rViol) (.reg 136)          -- conj pointer in range
  , bo 137 .mul (.reg 135) (.reg 134)              -- clamp to 0 when out of range
  , AInstr.load 138 137
  , bo 139 .ne (.reg 138) .idx
  , bo 139 .mul (.reg 34) (.reg 139)
  , bo 139 .mul (.reg 135) (.reg 139)
  , bo rViol .add (.reg rViol) (.reg 139)

    -- `conjFirst` is a per-character field, so it must be constant across the
    -- character: otherwise a corrupted copy on a non-first block hides behind
    -- the `newch` gate and is never read at all.
  , bo 154 .ne (.reg 32) (.reg rPrevConj)
  , bo 154 .mul (.reg 33) (.reg 154)
  , bo rViol .add (.reg rViol) (.reg 154)

    -- the Turing fields carry no meaning off a closing block, so they must be
    -- absent there rather than unconstrained
  , bo 155 .sub (.lit 1) (.reg 48)
  , bo 156 .ne (.reg 29) (.lit 0)
  , bo 156 .mul (.reg 155) (.reg 156)
  , bo rViol .add (.reg rViol) (.reg 156)
  , bo 157 .ne (.reg 30) (.lit 0)
  , bo 157 .mul (.reg 155) (.reg 157)
  , bo rViol .add (.reg rViol) (.reg 157)

    -- the bitmap digest chain: each record commits to the exact 64 sign
    -- samples, so the accepted object is one bitmap sequence rather than an
    -- equivalence class of them
  , digestMulInstr
  , digestAddInstr
  , digestCompareInstr
  , digestBumpInstr

    -- ---- state update.  Every mux reads its keep operand before writing. ----
  , bo 140 .mul (.reg 33) (.reg rTrI1)
  , bo 141 .mul (.reg 33) (.reg rSj1)
  , mvr rTrI0 140
  , mvr rSj0 141
  , mvr rTrI1 77
  , mvr rSj1 95
  , bo 142 .mul (.reg 33) (.reg rFirstBit)
  , bo 143 .mul (.reg 34) (.reg 96)
  , bo rFirstBit .add (.reg 142) (.reg 143)
  , mvr rPrevTag 21
  , mvr rPrevBlk 22
  , mvr rPrevUpper 25
  , mvr rPrevBit 97
  , mvr rPrevLast 28
  , mvr rPrevConj 32
  , mvr rPrevDig 158
  ]

/-! Lightweight projections used by denotation proofs.  Keeping these
reductions next to `bodyBlock` prevents downstream modules from re-elaborating
the whole record checker merely to expose the digest instructions. -/
theorem Cfg.bodyBlock_digestMul (c : Cfg) :
    (c.bodyBlock.drop 230).take 1 = [digestMulInstr] := by rfl

theorem Cfg.bodyBlock_digestAdd (c : Cfg) :
    (c.bodyBlock.drop 231).take 1 = [digestAddInstr] := by rfl

theorem Cfg.bodyBlock_digestFlag (c : Cfg) :
    (c.bodyBlock.drop 232).take 2 = [digestCompareInstr, digestBumpInstr] := by rfl

theorem Cfg.bodyBlock_digest (c : Cfg) :
    (c.bodyBlock.drop 230).take 4 =
      [digestMulInstr, digestAddInstr, digestCompareInstr, digestBumpInstr] := by rfl

/-- The stream must end on a closing block, and on the declared digest. -/
def Cfg.epilogueBlock (c : Cfg) : List I :=
  [ bo 20 .ne (.reg rPrevLast) (.lit 1)
  , bo rViol .add (.reg rViol) (.reg 20)
  , bo 21 .ne (.reg rPrevDig) (.lit c.termDigest)
  , bo rViol .add (.reg rViol) (.reg 21) ]

/-- Write a record stream into the array.  Production supplies the stream from
outside (the driver fills the cells); this is for the kernel checks and for the
self-contained native certificate. -/
def seedBlock (words : List Nat) : List I :=
  words.zipIdx.flatMap fun (v, t) =>
    [ mvl 20 t, mvl 21 v, AInstr.store 20 21 ]

def Cfg.program (c : Cfg) : AProgram :=
  { regCount := regCount
    arrayLen := c.arrayLen
    loopCount := c.records
    init := c.initBlock
    body := c.bodyBlock
    epilogue := c.epilogueBlock
    output := rViol }

/-- Platt's Theorem 7.1 schedule: `T_q = max(10⁸/q, 200 + 7.5·10⁷/q)` for even
`q` and `max(10⁸/q, 200 + 3.75·10⁷/q)` for odd `q`. -/
def sourceCfg (n termDig : Nat) : Cfg :=
  ⟨n, 100000000, 200, 75000000, 37500000, termDig⟩

/-- A scaled-down schedule, so the same code path is reachable by kernel
evaluation: heights of a few tens rather than a few hundreds. -/
def testCfg (n termDig : Nat) : Cfg := ⟨n, 1, 10, 0, 10, termDig⟩

/-- The digest the stream `words` ends on: `d ↦ d·digMul + bits` over every
record, wrapping at `2^64`.  Used to instantiate `termDigest`.

For a *seeded* program this is derived from the same words the program writes,
so it commits nothing extra — the seeded artifact is a demonstration.  For
`ladderProgram`, whose array is filled by the caller, it is an externally
supplied constant, and it is what terminates the chain. -/
def terminalDigest (words : List Nat) : Nat :=
  (List.range (words.length / recW)).foldl
    (fun d i => (d * digMul + words.getD (recW * i + 5) 0) % 18446744073709551616) 0

/-- The Dirichlet ladder checker for a stream of `n` block records, supplied by
the caller in the array, at the source schedule. -/
def ladderProgram (n termDig : Nat) : AProgram := (sourceCfg n termDig).program

/-- The same checker with the record stream written by the program itself, so
that its denotation is a closed number. -/
def seededWith (c : Cfg) (words : List Nat) : AProgram :=
  { c.program with init := seedBlock words ++ c.initBlock }

def seededSource (words : List Nat) : AProgram :=
  seededWith (sourceCfg (words.length / recW) (terminalDigest words)) words

/-- The test checker at an explicitly supplied terminal commitment.

This is the honest shape.  `termDigest` is a property of the *certificate*, not
of whatever bytes happen to be in the array, so a corrupted stream must be
checked against the commitment the good stream fixed.  Deriving it from the
words under test instead would let a forger move the goalposts with the
forgery, which is exactly what the terminal check exists to prevent — and it is
the error a first draft of these tests made. -/
def seededTestWith (termDig : Nat) (words : List Nat) : AProgram :=
  seededWith (testCfg (words.length / recW) termDig) words

def seededTest (words : List Nat) : AProgram :=
  seededTestWith (terminalDigest words) words

/-! ## Well-formedness, and the bridge instantiated

A `Bool` mirror of `AInstr.WF` that never inspects a literal's *value*, so it
reduces definitionally even though the program text mentions `c.tblBase`.  Every
obligation below is then `rfl` at every configuration, with no case split over
two hundred instructions.

This duplicates the mirror in `Ports.ArraySegSieve` deliberately: that file is
being rewritten on another branch, and this port should not depend on it. -/

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
    (h : l.all (ainstrWFB r) = true) : ∀ a ∈ l, a.WF r := fun a ha =>
  ainstrWFB_correct (List.all_eq_true.mp h a ha)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem bodyBlock_wf (c : Cfg) : ∀ a ∈ c.bodyBlock, a.WF regCount :=
  forall_wf_of_all (by rfl)

theorem initBlock_all (c : Cfg) : c.initBlock.all (ainstrWFB regCount) = true := by
  simp only [Cfg.initBlock, Cfg.tableBlock, Cfg.tableEntryBlock,
    List.all_append, List.all_flatMap, Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr (fun v _ => rfl), rfl⟩

theorem seedBlock_all (words : List Nat) :
    (seedBlock words).all (ainstrWFB regCount) = true := by
  simp only [seedBlock, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => rfl)

theorem initBlock_wf (c : Cfg) : ∀ a ∈ c.initBlock, a.WF regCount :=
  forall_wf_of_all (initBlock_all c)

theorem epilogueBlock_wf (c : Cfg) : ∀ a ∈ c.epilogueBlock, a.WF regCount :=
  forall_wf_of_all (by rfl)

theorem ladderProgram_wf (n termDig : Nat) : (ladderProgram n termDig).WF :=
  ⟨by show rViol < regCount; decide, initBlock_wf (sourceCfg n termDig),
    bodyBlock_wf (sourceCfg n termDig), epilogueBlock_wf (sourceCfg n termDig)⟩

theorem seededWith_wf (c : Cfg) (words : List Nat) : (seededWith c words).WF := by
  refine ⟨by show rViol < regCount; decide, ?_, bodyBlock_wf c, epilogueBlock_wf c⟩
  refine forall_wf_of_all ?_
  show ((seedBlock words ++ c.initBlock).all (ainstrWFB regCount)) = true
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨seedBlock_all words, initBlock_all c⟩

/--
**The bridge.**  For any array base at which the record stream fits, the
compiled CCIR trace of the Dirichlet ladder checker leaves the program's
denotation — the number of failed checks — in the output register.
-/
theorem ladderProgram_compiled (n termDig : Nat) (base : Int)
    (hBase : BaseOk (ladderProgram n termDig).arrayLen base)
    (v : Nat) (hDenote : (ladderProgram n termDig).denote = some v) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence ((ladderProgram n termDig).initialMCC base)
          (ladderProgram n termDig).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(ladderProgram n termDig).output + 1⟩) = some ((v : Nat) : Int) :=
  AProgram.evalCC_compile _ (ladderProgram_wf n termDig) base hBase v hDenote

/-! ## Reference model (specification side)

Written from the record-format table in the module docstring, not from the
register encoding above.  Never compiled; it exists so the kernel can compare
the two. -/

def transWord (bits : Nat) : Nat := (bits ^^^ (bits >>> 1)) &&& mask63

def bitCount (t : Nat) : Nat :=
  (List.range 63).foldl (fun a k => a + (t >>> k) % 2) 0

def bitMoment (t : Nat) : Nat :=
  (List.range 63).foldl (fun a k => a + k * ((t >>> k) % 2)) 0

structure RefState where
  viol : Nat
  prevTag : Nat
  prevBlk : Nat
  prevUpper : Nat
  prevBit : Nat
  firstBit : Nat
  trI0 : Nat
  sj0 : Nat
  trI1 : Nat
  sj1 : Nat
  prevLast : Nat
  prevConj : Nat
  prevDig : Nat
  deriving Repr, DecidableEq

def refInit : RefState := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩

def bump (c : Bool) (n : Nat) : Nat := if c then n + 1 else n

/-- Accumulate a finite list of reference-check failures.  Keeping the flags
as a list exposes the exact per-record no-wrap budget to symbolic proofs. -/
def bumps (conditions : List Bool) (n : Nat) : Nat :=
  conditions.foldl (fun total condition => bump condition total) n

/-- One record of the reference checker. -/
def refStep (c : Cfg) (s : List Nat) (st : RefState) (idx : Nat) : RefState :=
  let W : Nat → Nat := fun i => s.getD i 0
  let b := recW * idx
  let tag := W b
  let blk := W (b + 1)
  let lower := W (b + 2)
  let slots := W (b + 3)
  let upper := W (b + 4)
  let bits := W (b + 5)
  let stat := W (b + 6)
  let isL := W (b + 7)
  let uElem := W (b + 8)
  let henc := W (b + 9)
  let tqNum := W (b + 10)
  let cj := W (b + 11)
  let dig := W (b + 12)
  let same := tag == st.prevTag
  let isLastB := isL == 1
  let t := transWord bits
  let trI := bitCount t
  let sj := bitMoment t
  let fb := bits % 2
  let lb := (bits >>> 63) % 2
  let cross := if same && st.prevBit != fb then 1 else 0
  let derived := trI + cross + 2 * stat
  let stair := 127 * st.trI0 + 63 * trI + 64 * cross
  let stairSub := st.sj0 + sj
  let stairOk := stairSub ≤ stair
  let stairScaled := (if stairOk then stair - stairSub else 0) * 81920
  let uOk := stairScaled ≤ uElem
  let uEnc := if uOk then uElem - stairScaled else 0
  let q := tag >>> 20
  let cq := if q % 2 = 1 then c.hOdd else c.hEven
  let alt := c.hLin * q + cq
  let tq := if c.hFloor ≤ alt then alt else c.hFloor
  let addr := recW * cj + 11
  let inR := addr < recW * c.records
  let v := bumps
    [ tag < st.prevTag
    , !same && st.prevLast != 1
    , same && st.prevLast == 1
    , blk != (if same then st.prevBlk + 1 else 0)
    , lower != (if same then st.prevUpper else 0)
    , upper != lower + slots
    , isL > 1
    , stat > maxStat
    , slots != derived
    , isLastB && blk < winW - 1
    , isLastB && henc != hExpect
    , isLastB && !stairOk
    , isLastB && !uOk
    , isLastB && !(uEnc < (upper + 1) * henc)
    , isLastB && uEnc < upper * henc
    , dig != (st.prevDig * digMul + bits) % 18446744073709551616
    , isLastB && ((st.firstBit == lb) != (upper % 2 == 0))
    , tqNum != tq
    , isLastB && 5 * (blk + 1) * q < tq
    , isLastB && tq ≤ 5 * blk * q
    , same && cj != st.prevConj
    , !isLastB && uElem != 0
    , !isLastB && henc != 0
    , !same && !inR
    , !same && inR && W addr != idx ] st.viol
  { viol := v, prevTag := tag, prevBlk := blk, prevUpper := upper,
    prevBit := lb, firstBit := if same then st.firstBit else fb,
    trI0 := if same then st.trI1 else 0, sj0 := if same then st.sj1 else 0,
    trI1 := trI, sj1 := sj, prevLast := isL, prevConj := cj, prevDig := dig }

/-- The reference violation count for a flat record stream. -/
def refViolations (c : Cfg) (s : List Nat) : Nat :=
  let st := (List.range c.records).foldl (refStep c s) refInit
  bump (st.prevDig != c.termDigest) (bump (st.prevLast != 1) st.viol)

/-! ## Kernel checks: the encoding means the specification

Two primitive characters, three blocks each.  The heights are synthetic — the
real `T_q` for `q = 3` needs `6.7·10⁶` blocks, far past what the kernel can
evaluate — but the *arithmetic* under test is the source arithmetic.  The
failing configurations are the point: without them a checker that always
returns zero would pass. -/

def goodStream : List Nat :=
  [ 3145729, 0, 0, 3, 3, 5, 0, 0, 0, 0, 40, 3, 5
  , 3145729, 1, 3, 2, 5, 3, 0, 0, 0, 0, 40, 3, 13272178808
  , 3145729, 2, 5, 2, 7, 1, 0, 1, 120012800, 10485760, 40, 3, 16783401980632001273
  , 5242881, 0, 0, 3, 3, 5, 0, 0, 0, 0, 60, 0, 7994887169443407662
  , 5242881, 1, 3, 2, 5, 3, 0, 0, 0, 0, 60, 0, 4762022776277718225
  , 5242881, 2, 5, 2, 7, 1, 0, 1, 120012800, 10485760, 60, 0, 7745614187404094850 ]

/-- `goodStream` with word `i` replaced by `v`. -/
def mutate (i v : Nat) : List Nat :=
  goodStream.zipIdx.map fun (w, t) => if t = i then v else w

-- `refViolations` folds a long `let`-chain over every record, and every
-- `decide` below evaluates it in the kernel.
set_option maxRecDepth 100000

/-- A conforming stream is accepted. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) goodStream = 0 := by decide

/-- A flipped sign bit that the advertised bracket count no longer explains. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 5 7) = 3 := by decide
/-- A forged running count on a closing block: caught twice, by the slot
closure and — because the forged total changes parity — by the endpoint-sign
consistency check. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 30 8) = 3 := by decide
/-- An inflated Turing numerator no longer pins the integer. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 73 1000000000000000) = 1 := by decide
/-- Conjugation that is not an involution on the roster: the involution check
fires, and so does the constancy check on the following block. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 50 1) = 2 := by decide
/-- A height that is not the one Theorem 7.1's formula gives for this `q`. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 36 100) = 1 := by decide

/-! Three fields that an earlier draft left unconstrained off their "own" block.
The independent oracle found them by mutating a **non-final** and a
**non-first** record and getting `0` from both compilers.  A field that can be
corrupted without detection is not a field the checker checks, so the height
agreement is now tested on every record, `conjFirst` must be constant across a
character, and the Turing fields must be absent off a closing block. -/

/-- A forged height on a *non-final* block. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 10 99) = 1 := by decide
/-- A forged conjugate pointer on a *non-first* block. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 24 1) = 2 := by decide
/-- A Turing numerator smuggled onto a *non-closing* block. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 21 7) = 1 := by decide

/-! The independent oracle's 370,621-mutation sweep left exactly two fields
free: `uElem` within an interval, and `bits` up to permutation of its
sign-change positions.  Both are now closed as far as an integer checker can
close them — `uElem` by the lower Turing side, `bits` by the digest chain. -/

/-- A bitmap permuted to a different one with the same transition count. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 18 9) = 2 := by decide
/-- A forged digest. -/
example : refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 12 0) = 2 := by decide

set_option maxRecDepth 60000 in
example : (seededTest goodStream).denote = some (refViolations (testCfg 6 (terminalDigest goodStream)) goodStream) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 5 7)).denote = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 5 7)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 30 8)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 30 8)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 73 1000000000000000)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 73 1000000000000000)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 50 1)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 50 1)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 36 100)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 36 100)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 10 99)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 10 99)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 24 1)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 24 1)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 21 7)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 21 7)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 18 9)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 18 9)) := by
  decide +kernel

set_option maxRecDepth 60000 in
example : (seededTestWith (terminalDigest goodStream) (mutate 12 0)).denote
    = some (refViolations (testCfg 6 (terminalDigest goodStream)) (mutate 12 0)) := by
  decide +kernel

end LeanCompCert.Ports.DirichletLadder
