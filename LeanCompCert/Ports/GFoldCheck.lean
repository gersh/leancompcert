import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Ports.TrialDivisionBlockSpec
import LeanCompCert.Verified.Straight

/-!
# The Ramaré `G(R) ≤ log R + 1.4709` running check, in the 64-bit fragment

The consumer's certificate (`AnalyticNT.LargeSieve.gFold_cert`) is a running
fold: for every candidate `n` in a range it adds the squarefree-`1/φ`
fixed-point term `⌈2⁴⁴/φ(n)⌉` to an accumulator and tests the accumulator
against a per-`n` threshold `2⁴⁴·(ceBest n + 1.4709)`, where `ceBest n` is an
exponent-pair rational lower bound for `log n` — a maximum over up to `48`
candidate pairs, whose exact-`ℚ` evaluation reaches `1411` bits.

This module is the register-program replacement.  Width never blocks a
bounded quantity; it selects the route:

* the factorisation is the flattened trial-division peel of
  `Ports/TrialDivisionFold.lean` — candidate and divisor decoded from the
  single flat loop index;
* the per-`n` threshold is evaluated in `u64` fixed point from a **truncated
  65-bit mantissa** `X = 2⁶⁴ + xlo` of `n^b / 2^k`, advanced by one
  half-word split per exponent step and renormalised by a proved two-case
  shift — `n^b` itself is never materialised;
* both members of the exponent pair are tested: the Padé lower bound
  `3(x²−1)/(x²+4x+1) ≤ log x` at `x = X/2⁶⁴`, and the sinh upper bound
  subtracted from `(k+1)·log 2` at `2^{k+1}/n^b ≤ 2⁶⁵/X`, the latter behind a
  distance-to-`2⁶⁵` guard that keeps the mantissa exponent honest;
* every division is by a register that is provably nonzero in every reachable
  state, so the body's denotation is total under the loop invariant.

The mantissa update was replayed, bit for bit, against the exact-`ℚ`
certificate over its entire production range before anything here was proved
(`ext/analytic_nt/scripts/width_replay.py` in the consumer repository and the
machine-mirror replay recorded with the campaign): zero failures, and the
per-candidate soundness inequality holds with margin at every `n`.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated: the program is well-formed; its
denotation is the flat fold of a transparent `Nat` round function
(`gfProgram_denote`); the flat fold re-blocks per candidate; and acceptance
(`denote = some 1`) yields, for every candidate, the exact accumulator value
and a passing per-candidate check (`rows_of_denote`, in
`Ports/GFoldCheckSpec.lean`).

Left to the consumer (which has Mathlib): that the trial-division block
computes `Nat.totient`, and that the passing `u64` check implies the
certificate's own `ℚ` comparison against `ceBest`.  Those statements mention
`Nat.totient`, `Squarefree` and `ℚ`; they are imported there, not assumed
here.
-/

namespace LeanCompCert.Ports.GFoldCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 4000

/-! ## §1 Parameters -/

/-- One instance of the family: candidates `n ∈ [lo, lo + len)`, `tdiv + 1`
trial divisors `2 … tdiv + 2` per candidate, `bmax` exponent-pair rounds per
candidate, the dyadic-only branch above `split`, and the accumulator seeded
at `m0`. -/
structure Params where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial rounds; divisors are `2 … tdiv + 2` (round `q` divides by `q+2`,
  and peeling continues through the exponent rounds). -/
  tdiv : Nat
  /-- Exponent-pair rounds per candidate (`b = 1 … bmax`). -/
  bmax : Nat
  /-- Candidates above this only use the `b = 1` pair. -/
  split : Nat
  /-- Accumulator seed. -/
  m0 : Nat
  deriving Repr, DecidableEq

/-- Rounds per candidate. -/
def Params.R (c : Params) : Nat := c.tdiv + c.bmax

/-- The sizing side conditions; all decidable, discharged by `decide` at each
concrete instance. -/
structure Params.Sane (c : Params) : Prop where
  /-- Candidates start at `2`, so `log₂ n ≥ 1`. -/
  loPos : 2 ≤ c.lo
  /-- At least one candidate. -/
  lenPos : 0 < c.len
  /-- At least one trial round. -/
  tdivPos : 0 < c.tdiv
  /-- At least one exponent round. -/
  bmaxPos : 0 < c.bmax
  /-- At most `48` exponent rounds (keeps `CC · b` inside a word). -/
  bmaxLe : c.bmax ≤ 48
  /-- Every candidate is below `2¹⁷` (mantissa half-word split). -/
  topSmall : c.lo + c.len ≤ 2 ^ 17
  /-- The flat index is a word. -/
  loopSmall : c.len * (c.tdiv + c.bmax) < 2 ^ 48
  /-- The per-round literals are words. -/
  roundsSmall : c.tdiv + c.bmax < 2 ^ 31
  /-- The seed is below the running cap, so acceptance forces exactness. -/
  m0Le : c.m0 ≤ 2 ^ 56
  /-- The dyadic-branch threshold is a word. -/
  splitLt : c.split < 2 ^ 17

/-- `⌊2³²·0.6931471803⌋`, the fixed-point image of the consumer's
`ceL2LB = 6931471803/10¹⁰` lower bound for `log 2`. -/
def CL : Nat := 2977044470

/-- `⌊2⁴⁴·1.4709⌋`, the fixed-point image of the certificate's additive
constant `14709/10⁴`. -/
def CC : Nat := 25876346452731

/-- The kk-register clamp; the reference recurrence stays `≤ 815`, so the
clamp is inert on every real run and only serves the state invariant. -/
def KCAP : Nat := 1024

/-- The accumulator cap a passing check re-tests; keeps `acc · b` exact. -/
def ACAP : Nat := 2 ^ 56

/-! ## §2 Register layout

Carried across rounds (the `Vals` below):

| reg | meaning | | reg | meaning |
| --- | --- | --- | --- | --- |
| `0` | good flag (output) | | `4` | accumulator |
| `1` | `m`, the cofactor | | `5` | candidate pass flag |
| `2` | `φ` product | | `13` | mantissa `xlo = X − 2⁶⁴` |
| `3` | squarefree flag | | `14` | mantissa exponent `k` |

Scratch, recomputed every round: `6`–`12`, `15`–`53`.  Temporaries of the
expression compiler start at `cursor = 56`. -/

def cursor : Nat := 56

/-- Branchless select for a `0/1` condition: `c * a + (c ^^^ 1) * b`. -/
def sel (c a b : Expr) : Expr :=
  .bin .add (.bin .mul c a) (.bin .mul (.bin .bxor c (.lit 1)) b)

/-- One `udiv` instruction's `Nat`-level effect. -/
def divStep (dest : Nat) (op : Op) (a b : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp op (s a) (s b)).getD 0)

/-- The two index-decoding divisions, whose divisor is a literal. -/
def idxDivStep (R : Nat) (k : Nat) (s : RegState) : RegState :=
  (s.set 6 ((denoteOp .udiv (k % M) (R % M)).getD 0)).set 7
    ((denoteOp .urem (k % M) (R % M)).getD 0)

/-- `n ≥ v`, as a `0/1` expression on register `8`. -/
def geBit (v : Nat) : Expr := .bin .ge (.reg 8) (.lit v)

/-- The low half of the `⌊log₂ n⌋` indicator sum. -/
def aLoExpr : Expr :=
  .bin .add
    (.bin .add (.bin .add (geBit 2) (geBit 4)) (.bin .add (geBit 8) (geBit 16)))
    (.bin .add (.bin .add (geBit 32) (geBit 64))
      (.bin .add (geBit 128) (geBit 256)))

/-- The high half of the `⌊log₂ n⌋` indicator sum. -/
def aHiExpr : Expr :=
  .bin .add
    (.bin .add (.bin .add (geBit 512) (geBit 1024))
      (.bin .add (geBit 2048) (geBit 4096)))
    (.bin .add (.bin .add (geBit 8192) (geBit 16384))
      (.bin .add (geBit 32768) (geBit 65536)))

/-- Decode, per-candidate reset and masks. -/
def blkA1 (c : Params) : List Assign :=
  [ ⟨8, .bin .add (.reg 6) (.lit c.lo)⟩
  , ⟨9, .bin .add (.reg 7) (.lit 2)⟩
  , ⟨49, .bin .eq (.reg 7) (.lit 0)⟩
  , ⟨17, .bin .eq (.reg 7) (.lit (c.R - 1))⟩
  , ⟨18, .bin .eq (.reg 7) (.lit c.tdiv)⟩
  , ⟨19, .bin .ge (.reg 7) (.lit c.tdiv)⟩
  , ⟨1, sel (.reg 49) (.reg 8) (.reg 1)⟩
  , ⟨2, sel (.reg 49) (.lit 1) (.reg 2)⟩
  , ⟨3, sel (.reg 49) (.lit 1) (.reg 3)⟩
  , ⟨5, sel (.reg 49) (.lit 0) (.reg 5)⟩ ]

/-- `⌊log₂ n⌋` and `2^{⌊log₂ n⌋}`. -/
def blkA2 : List Assign :=
  [ ⟨15, aLoExpr⟩
  , ⟨15, .bin .add (.reg 15) aHiExpr⟩
  , ⟨16, .bin .shl (.lit 1) (.reg 15)⟩ ]

/-- Decode, per-candidate reset, masks, and `⌊log₂ n⌋`. -/
def blkA (c : Params) : List Assign := blkA1 c ++ blkA2

/-- The divisibility flag and the squarefree update. -/
def blkBa1 : List Assign :=
  [ ⟨12, .bin .eq (.bin .sub (.reg 1) (.bin .mul (.reg 10) (.reg 9))) (.lit 0)⟩
  , ⟨3, .bin .mul (.reg 3)
      (.bin .bxor
        (.bin .mul (.reg 12)
          (.bin .eq (.bin .sub (.reg 10) (.bin .mul (.reg 11) (.reg 9)))
            (.lit 0)))
        (.lit 1))⟩ ]

/-- The totient product and cofactor updates. -/
def blkBa2 : List Assign :=
  [ ⟨2, sel (.reg 12) (.bin .mul (.reg 2) (.bin .add (.reg 7) (.lit 1)))
      (.reg 2)⟩
  , ⟨1, sel (.reg 12) (.reg 10) (.reg 1)⟩ ]

/-- One peel of `d` and the repeated-factor test. -/
def blkBa : List Assign := blkBa1 ++ blkBa2

/-- The totient decode and the term numerator. -/
def blkBb : List Assign :=
  [ ⟨20, sel (.bin .gt (.reg 1) (.lit 1))
      (.bin .mul (.reg 2) (.bin .sub (.reg 1) (.lit 1))) (.reg 2)⟩
  , ⟨21, .bin .sub (.bin .add (.lit (2 ^ 44)) (.reg 20)) (.lit 1)⟩ ]

/-- One peel of `d`, the repeated-factor test, and the term numerator. -/
def blkB : List Assign := blkBa ++ blkBb

/-- Masked accumulation and the mantissa high half-word. -/
def blkCa1a : List Assign :=
  [ ⟨4, .bin .add (.reg 4) (.bin .mul (.reg 18) (.bin .mul (.reg 3) (.reg 22)))⟩
  , ⟨24, .bin .lshr (.reg 13) (.lit 47)⟩ ]

/-- The mantissa low half-word and the high partial product. -/
def blkCa1b : List Assign :=
  [ ⟨25, .bin .sub (.reg 13) (.bin .shl (.reg 24) (.lit 47))⟩
  , ⟨26, .bin .mul (.reg 24) (.reg 8)⟩ ]

/-- Masked accumulation and the mantissa half-word split. -/
def blkCa1 : List Assign := blkCa1a ++ blkCa1b

/-- The low partial product. -/
def blkCa2a : List Assign :=
  [ ⟨27, .bin .mul (.reg 25) (.reg 8)⟩ ]

/-- The shifted product. -/
def blkCa2b : List Assign :=
  [ ⟨28, .bin .add
      (.bin .add
        (.bin .mul (.reg 8) (.bin .shl (.lit 1) (.bin .sub (.lit 62) (.reg 15))))
        (.bin .mul (.reg 26) (.bin .shl (.lit 1) (.bin .sub (.lit 45) (.reg 15)))))
      (.bin .lshr (.reg 27) (.bin .add (.reg 15) (.lit 2)))⟩ ]

/-- The renormalisation case bit. -/
def blkCa2c : List Assign :=
  [ ⟨29, .bin .ge (.reg 28) (.lit (2 ^ 63))⟩ ]

/-- The shifted product and the renormalisation case bit. -/
def blkCa2 : List Assign := blkCa2a ++ blkCa2b ++ blkCa2c

/-- `2⁶³` and `2⁶²`, def-wrapped so `simp` keeps them opaque. -/
def L63 : Nat := 2 ^ 63
/-- See `L63`. -/
def L62 : Nat := 2 ^ 62

/-- The doubled advance. -/
def blkCa3w1 : List Assign :=
  [ ⟨54, .bin .mul (.bin .sub (.reg 28) (.lit L63)) (.lit 2)⟩ ]

/-- The quadrupled advance. -/
def blkCa3w2 : List Assign :=
  [ ⟨55, .bin .mul (.bin .sub (.reg 28) (.lit L62)) (.lit 4)⟩ ]

/-- The renormalisation select (register-leaf branches). -/
def blkCa3x1 : List Assign :=
  [ ⟨30, sel (.reg 29) (.reg 54) (.reg 55)⟩ ]

/-- The init value. -/
def blkCa3x2 : List Assign :=
  [ ⟨31, .bin .shl (.bin .sub (.reg 8) (.reg 16)) (.bin .sub (.lit 64) (.reg 15))⟩ ]

/-- The two normalised advances and the init value. -/
def blkCa3x : List Assign := blkCa3w1 ++ blkCa3w2 ++ blkCa3x1 ++ blkCa3x2

/-- The mantissa select. -/
def blkCa3y : List Assign :=
  [ ⟨13, sel (.reg 19) (sel (.reg 18) (.reg 31) (.reg 30)) (.reg 13)⟩ ]

/-- The two normalised advances, the init value, and the mantissa select. -/
def blkCa3 : List Assign := blkCa3x ++ blkCa3y

/-- The unclamped exponent update. -/
def blkCa4x : List Assign :=
  [ ⟨48, .bin .add (.bin .add (.reg 14) (.reg 15)) (.reg 29)⟩ ]

/-- The exponent select. -/
def blkCa4y : List Assign :=
  [ ⟨14, sel (.reg 19)
      (sel (.reg 18) (.reg 15)
        (sel (.bin .le (.reg 48) (.lit KCAP)) (.reg 48) (.lit KCAP)))
      (.reg 14)⟩ ]

/-- The mantissa exponent update. -/
def blkCa4 : List Assign := blkCa4x ++ blkCa4y

/-- Masked accumulation and the mantissa init/advance. -/
def blkCa : List Assign := blkCa1 ++ blkCa2 ++ blkCa3 ++ blkCa4

/-- The truncated 25-bit mantissa. -/
def blkCb1x : List Assign :=
  [ ⟨32, .bin .add (.bin .lshr (.reg 13) (.lit 40)) (.lit (2 ^ 24))⟩ ]

/-- The Padé numerator. -/
def blkCb1y : List Assign :=
  [ ⟨33, .bin .mul (.bin .sub (.bin .mul (.reg 32) (.reg 32)) (.lit (2 ^ 48)))
      (.lit 3)⟩ ]

/-- The truncated 25-bit mantissa and the Padé numerator. -/
def blkCb1 : List Assign := blkCb1x ++ blkCb1y

/-- The Padé denominator and the shifted numerator. -/
def blkCb2 : List Assign :=
  [ ⟨34, .bin .add
      (.bin .add (.bin .mul (.reg 32) (.reg 32)) (.bin .shl (.reg 32) (.lit 26)))
      (.lit (2 ^ 48))⟩
  , ⟨35, .bin .shl (.reg 33) (.lit 12)⟩ ]

/-- The Padé operands. -/
def blkCb : List Assign := blkCb1 ++ blkCb2

/-- Masked accumulation, the mantissa init/advance, and the Padé operands. -/
def blkC : List Assign := blkCa ++ blkCb

/-- The Padé remainder step. -/
def blkD : List Assign :=
  [ ⟨37, .bin .shl (.bin .sub (.reg 35) (.bin .mul (.reg 36) (.reg 34)))
      (.lit 12)⟩ ]

/-- The Padé recombination. -/
def blkE1 : List Assign :=
  [ ⟨39, .bin .add (.bin .shl (.reg 36) (.lit 20)) (.bin .shl (.reg 38) (.lit 8))⟩ ]

/-- Candidate `A` and the sinh numerator. -/
def blkE2 : List Assign :=
  [ ⟨40, .bin .add (.bin .mul (.reg 14) (.lit CL)) (.reg 39)⟩
  , ⟨41, .bin .sub
      (.bin .add
        (.bin .shl (.bin .sub (.lit (2 ^ 50)) (.bin .mul (.reg 32) (.reg 32)))
          (.lit 6))
        (.reg 32))
      (.lit 1)⟩ ]

/-- The Padé recombination, candidate `A`, and the sinh numerator. -/
def blkE : List Assign := blkE1 ++ blkE2

/-- Candidate `B`, the pair index, and the gates. -/
def blkF1 (c : Params) : List Assign :=
  [ ⟨43, .bin .sub (.bin .mul (.bin .add (.reg 14) (.lit 1)) (.lit CL)) (.reg 42)⟩
  , ⟨44, .bin .add (.bin .sub (.reg 7) (.lit c.tdiv)) (.lit 1)⟩
  , ⟨45, .bin .bor (.reg 18) (.bin .le (.reg 8) (.lit c.split))⟩
  , ⟨46, .bin .le (.reg 4) (.lit ACAP)⟩ ]

/-- The two threshold comparisons and the mantissa guard. -/
def blkF2 : List Assign :=
  [ ⟨50, .bin .le (.bin .mul (.reg 4) (.reg 44))
      (.bin .add (.bin .shl (.reg 40) (.lit 12)) (.bin .mul (.lit CC) (.reg 44)))⟩
  , ⟨51, .bin .le (.bin .mul (.reg 4) (.reg 44))
      (.bin .add (.bin .shl (.reg 43) (.lit 12)) (.bin .mul (.lit CC) (.reg 44)))⟩
  , ⟨52, .bin .le (.reg 13) (.lit (2 ^ 64 - 2 ^ 50))⟩ ]

/-- The hit. -/
def blkF3a : List Assign :=
  [ ⟨53, .bin .mul (.reg 46)
      (.bin .mul (.reg 45) (.bin .bor (.reg 50) (.bin .mul (.reg 52) (.reg 51))))⟩ ]

/-- The pass accumulation. -/
def blkF3b : List Assign :=
  [ ⟨5, sel (.reg 19) (.bin .bor (.reg 5) (.reg 53)) (.reg 5)⟩ ]

/-- The verdict. -/
def blkF3c : List Assign :=
  [ ⟨0, sel (.reg 17) (.bin .mul (.reg 0) (.reg 5)) (.reg 0)⟩ ]

/-- The hit, the pass accumulation, and the verdict. -/
def blkF3 : List Assign := blkF3a ++ blkF3b ++ blkF3c

/-- Candidate `B`, the two checks, and the verdicts. -/
def blkF (c : Params) : List Assign := blkF1 c ++ blkF2 ++ blkF3

/-- The loop body. -/
def gfBody (c : Params) : List Instr :=
  [ .binop 6 .udiv .idx (.lit c.R)
  , .binop 7 .urem .idx (.lit c.R) ] ++
  block cursor (blkA c) ++
  [ .binop 10 .udiv (.reg 1) (.reg 9)
  , .binop 11 .udiv (.reg 10) (.reg 9) ] ++
  block cursor blkB ++
  [ .binop 22 .udiv (.reg 21) (.reg 20) ] ++
  block cursor blkC ++
  [ .binop 36 .udiv (.reg 35) (.reg 34) ] ++
  block cursor blkD ++
  [ .binop 38 .udiv (.reg 37) (.reg 34) ] ++
  block cursor blkE ++
  [ .binop 42 .udiv (.reg 41) (.reg 32) ] ++
  block cursor (blkF c)

/-- After decode, reset and `⌊log₂⌋`: the peel divisions' divisor lives in
register `9`. -/
def st1 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (idxDivStep c.R k s) (blkA1 c)) blkA2

/-- After the two peel divisions. -/
def st2 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9 (st1 c k s))

/-- After the peel and the totient decode: the term division's divisor lives
in register `20`. -/
def st3 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (st2 c k s) blkBa1) blkBa2) blkBb

/-- After the term division. -/
def st4 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 22 .udiv 21 20 (st3 c k s)

/-- After the accumulator step, the mantissa update and the Padé operands:
the Padé divisions' divisor lives in register `34`. -/
def st5 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (run k (run k (run k (run k (run k (run k (run k
    (st4 c k s)
    blkCa1a) blkCa1b) blkCa2) blkCa3x) blkCa3y) blkCa4x) blkCa4y)
    blkCb1x) blkCb1y) blkCb2

/-- After the first Padé division. -/
def st6 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 36 .udiv 35 34 (st5 c k s)

/-- After the remainder step. -/
def st7 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st6 c k s) blkD

/-- After the second Padé division. -/
def st8 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 38 .udiv 37 34 (st7 c k s)

/-- After candidate `A` and the sinh numerator: the sinh division's divisor
lives in register `32`. -/
def st9 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st8 c k s) blkE

/-- After the sinh division. -/
def st10 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 42 .udiv 41 32 (st9 c k s)

/-- The `Nat`-level meaning of one flat round. -/
def gfRun (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (st10 c k s) (blkF1 c)) blkF2) blkF3

/-- Initialisation: the good flag, cofactor, totient product and mantissa
exponent start at `1`; the accumulator starts at the seed. -/
def gfInit (c : Params) : List Instr :=
  [ .mov 0 (.lit 1), .mov 1 (.lit 1), .mov 2 (.lit 1), .mov 14 (.lit 1)
  , .mov 4 (.lit c.m0) ]

/-- The whole program: the output is the good flag itself. -/
def gfProgram (c : Params) : Program := {
  regCount := 128
  loopCount := c.len * c.R
  init := gfInit c
  body := gfBody c
  epilogue := []
  output := 0
}

/-! ## §3 Well-formedness -/

theorem blkA_wf (c : Params) : ∀ a ∈ blkA c, a.WF cursor := by
  intro a ha
  simp only [blkA, blkA1, blkA2, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl) <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, aLoExpr, aHiExpr,
      geBit, cursor], rfl⟩

theorem blkA_room (c : Params) :
    ∀ a ∈ blkA c, cursor + depth a.expr ≤ 128 := by
  intro a ha
  simp only [blkA, blkA1, blkA2, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl) <;>
    simp [depth, sel, aLoExpr, aHiExpr, geBit, cursor]

theorem blkB_wf : ∀ a ∈ blkB, a.WF cursor := by
  intro a ha
  simp only [blkB, blkBa, blkBa1, blkBa2, blkBb, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl) <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkB_room : ∀ a ∈ blkB, cursor + depth a.expr ≤ 128 := by
  intro a ha
  simp only [blkB, blkBa, blkBa1, blkBa2, blkBb, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ((rfl|rfl)|(rfl|rfl))|(rfl|rfl) <;> simp [depth, sel, cursor]

theorem blkC_pieces : ∀ a ∈ blkC,
    a.WF cursor ∧ cursor + depth a.expr ≤ 128 := by
  intro a ha
  have ha' : a ∈ (blkCa1a ++ blkCa1b) ++
      (blkCa2 ++ ((blkCa3x ++ blkCa3y) ++ (blkCa4x ++ blkCa4y))) ++
      ((blkCb1x ++ blkCb1y) ++ blkCb2) := ha
  rcases List.mem_append.mp ha' with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [blkCa1a, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
      · simp only [blkCa1b, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp (show a ∈ blkCa2a ++ blkCa2b ++ blkCa2c
        from h) with h | h
      · rcases List.mem_append.mp h with h | h
        · simp only [blkCa2a, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl <;>
            exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor],
              rfl⟩, by simp [depth, sel, cursor]⟩
        · simp only [blkCa2b, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl <;>
            exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor],
              rfl⟩, by simp [depth, sel, cursor]⟩
      · simp only [blkCa2c, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor],
            rfl⟩, by simp [depth, sel, cursor]⟩
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp
          (show a ∈ blkCa3w1 ++ blkCa3w2 ++ blkCa3x1 ++ blkCa3x2 from h)
          with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · simp only [blkCa3w1, List.mem_cons, List.not_mem_nil,
                or_false] at h
              rcases h with rfl <;>
                exact ⟨⟨by simp [cursor],
                  by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
                  by simp [depth, sel, cursor]⟩
            · simp only [blkCa3w2, List.mem_cons, List.not_mem_nil,
                or_false] at h
              rcases h with rfl <;>
                exact ⟨⟨by simp [cursor],
                  by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
                  by simp [depth, sel, cursor]⟩
          · simp only [blkCa3x1, List.mem_cons, List.not_mem_nil,
              or_false] at h
            rcases h with rfl <;>
              exact ⟨⟨by simp [cursor],
                by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
                by simp [depth, sel, cursor]⟩
        · simp only [blkCa3x2, List.mem_cons, List.not_mem_nil,
            or_false] at h
          rcases h with rfl <;>
            exact ⟨⟨by simp [cursor],
              by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
              by simp [depth, sel, cursor]⟩
      · simp only [blkCa3y, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
    · rcases List.mem_append.mp h with h | h
      · simp only [blkCa4x, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
      · simp only [blkCa4y, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [blkCb1x, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
      · simp only [blkCb1y, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl <;>
          exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
            by simp [depth, sel, cursor]⟩
    · simp only [blkCb2, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
          by simp [depth, sel, cursor]⟩

theorem blkC_wf : ∀ a ∈ blkC, a.WF cursor :=
  fun a ha => (blkC_pieces a ha).1

theorem blkC_room :
    ∀ a ∈ blkC, cursor + depth a.expr ≤ 128 :=
  fun a ha => (blkC_pieces a ha).2

theorem blkD_wf : ∀ a ∈ blkD, a.WF cursor := by
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkD_room : ∀ a ∈ blkD, cursor + depth a.expr ≤ 128 := by
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  simp [depth, cursor]

theorem blkE_wf : ∀ a ∈ blkE, a.WF cursor := by
  intro a ha
  rcases List.mem_append.mp (show a ∈ blkE1 ++ blkE2 from ha) with h | h
  · simp only [blkE1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩
  · simp only [blkE2, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
      exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkE_room : ∀ a ∈ blkE, cursor + depth a.expr ≤ 128 := by
  intro a ha
  rcases List.mem_append.mp (show a ∈ blkE1 ++ blkE2 from ha) with h | h
  · simp only [blkE1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    simp [depth, cursor]
  · simp only [blkE2, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [depth, cursor]

theorem blkF_pieces (c : Params) : ∀ a ∈ blkF c,
    a.WF cursor ∧ cursor + depth a.expr ≤ 128 := by
  intro a ha
  have ha' : a ∈ blkF1 c ++ (blkF2 ++ blkF3) := ha
  rcases List.mem_append.mp ha' with h | h
  · simp only [blkF1, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;>
      exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
        by simp [depth, sel, cursor]⟩
  rcases List.mem_append.mp h with h | h
  · simp only [blkF2, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;>
      exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
        by simp [depth, sel, cursor]⟩
  · rcases List.mem_append.mp (show a ∈ blkF3a ++ blkF3b ++ blkF3c from h)
      with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [blkF3a, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl
        exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
          by simp [depth, sel, cursor]⟩
      · simp only [blkF3b, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl
        exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
          by simp [depth, sel, cursor]⟩
    · simp only [blkF3c, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl
      exact ⟨⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩,
        by simp [depth, sel, cursor]⟩

theorem blkF_wf (c : Params) : ∀ a ∈ blkF c, a.WF cursor :=
  fun a ha => (blkF_pieces c a ha).1

theorem blkF_room (c : Params) :
    ∀ a ∈ blkF c, cursor + depth a.expr ≤ 128 :=
  fun a ha => (blkF_pieces c a ha).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem gfBody_wf (c : Params) : ∀ i ∈ gfBody c, i.WF 128 := by
  intro i hi
  have hcur : cursor ≤ 128 := by simp [cursor]
  have hi' : i ∈
      ([ Instr.binop 6 .udiv .idx (.lit c.R)
       , Instr.binop 7 .urem .idx (.lit c.R) ] ++
        (block cursor (blkA c) ++
          ([ Instr.binop 10 .udiv (.reg 1) (.reg 9)
           , Instr.binop 11 .udiv (.reg 10) (.reg 9) ] ++
            (block cursor blkB ++
              ([Instr.binop 22 .udiv (.reg 21) (.reg 20)] ++
                (block cursor blkC ++
                  ([Instr.binop 36 .udiv (.reg 35) (.reg 34)] ++
                    (block cursor blkD ++
                      ([Instr.binop 38 .udiv (.reg 37) (.reg 34)] ++
                        (block cursor blkE ++
                          ([Instr.binop 42 .udiv (.reg 41) (.reg 32)] ++
                            block cursor (blkF c)))))))))))) := hi
  rcases List.mem_append.mp hi' with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨by simp, trivial, trivial⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 128 (blkA c) (blkA_wf c) hcur (blkA_room c) i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
      exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 128 blkB blkB_wf hcur blkB_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 128 blkC blkC_wf hcur blkC_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 128 blkD blkD_wf hcur blkD_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 128 blkE blkE_wf hcur blkE_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  · exact block_wf cursor 128 (blkF c) (blkF_wf c) hcur (blkF_room c) i h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem gfProgram_wf (c : Params) : (gfProgram c).WF := by
  refine ⟨by simp [gfProgram], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ gfInit c := hi
    simp only [gfInit, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [gfProgram], trivial⟩
  · exact gfBody_wf c
  · intro i hi
    exact absurd hi (by simp [gfProgram])

/-! ## §4 The `Nat`-level round -/

/-- `if v ≤ n then 1 else 0`. -/
def ind (v n : Nat) : Nat := if v ≤ n then 1 else 0

/-- `⌊log₂ n⌋` for `2 ≤ n < 2¹⁷`, as the machine computes it: sixteen
threshold indicators. -/
def aOf (n : Nat) : Nat :=
  (ind 2 n + ind 4 n + (ind 8 n + ind 16 n) +
    (ind 32 n + ind 64 n + (ind 128 n + ind 256 n))) +
  (ind 512 n + ind 1024 n + (ind 2048 n + ind 4096 n) +
    (ind 8192 n + ind 16384 n + (ind 32768 n + ind 65536 n)))

theorem aOf_eq_log2 {n : Nat} (h2 : 2 ≤ n) (h17 : n < 2 ^ 17) :
    aOf n = Nat.log2 n := by
  have hn0 : n ≠ 0 := by omega
  have hL1 : 1 ≤ Nat.log2 n := (Nat.le_log2 hn0).mpr (by simpa using h2)
  have hL16 : Nat.log2 n < 17 := (Nat.log2_lt hn0).mpr h17
  have g : ∀ v i : Nat, v = 2 ^ i →
      (if v ≤ n then (1:Nat) else 0) = (if i ≤ Nat.log2 n then 1 else 0) := by
    intro v i hv
    subst hv
    by_cases h : 2 ^ i ≤ n
    · rw [if_pos h, if_pos ((Nat.le_log2 hn0).mpr h)]
    · rw [if_neg h, if_neg (fun hc => h ((Nat.le_log2 hn0).mp hc))]
  unfold aOf ind
  rw [g 2 1 (by decide), g 4 2 (by decide), g 8 3 (by decide),
    g 16 4 (by decide), g 32 5 (by decide), g 64 6 (by decide),
    g 128 7 (by decide), g 256 8 (by decide), g 512 9 (by decide),
    g 1024 10 (by decide), g 2048 11 (by decide), g 4096 12 (by decide),
    g 8192 13 (by decide), g 16384 14 (by decide), g 32768 15 (by decide),
    g 65536 16 (by decide)]
  rcases (show Nat.log2 n = 1 ∨ Nat.log2 n = 2 ∨ Nat.log2 n = 3 ∨
      Nat.log2 n = 4 ∨ Nat.log2 n = 5 ∨ Nat.log2 n = 6 ∨ Nat.log2 n = 7 ∨
      Nat.log2 n = 8 ∨ Nat.log2 n = 9 ∨ Nat.log2 n = 10 ∨ Nat.log2 n = 11 ∨
      Nat.log2 n = 12 ∨ Nat.log2 n = 13 ∨ Nat.log2 n = 14 ∨
      Nat.log2 n = 15 ∨ Nat.log2 n = 16 from by omega) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide

theorem aOf_bounds {n : Nat} (h2 : 2 ≤ n) (h17 : n < 2 ^ 17) :
    1 ≤ aOf n ∧ aOf n ≤ 16 ∧ 2 ^ aOf n ≤ n ∧ n < 2 ^ (aOf n + 1) := by
  have hn0 : n ≠ 0 := by omega
  rw [aOf_eq_log2 h2 h17]
  refine ⟨(Nat.le_log2 hn0).mpr (by simpa using h2), ?_,
    (Nat.le_log2 hn0).mp (Nat.le_refl _), (Nat.log2_lt hn0).mp (Nat.lt_succ_self _)⟩
  have := (Nat.log2_lt hn0).mpr h17
  omega

/-- The mantissa advance: `⌊X·n / 2^{a+2}⌋` from `xlo = X − 2⁶⁴`, by the
half-word split the machine performs. -/
def advX (n a xlo : Nat) : Nat :=
  n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a) +
    (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n / 2 ^ (a + 2)

/-- One per-candidate exponent-pair check, in exact `Nat` arithmetic (the
`% M` on `acc · b` is the machine's own, and is removed downstream by the
cap). -/
def hitOf (c : Params) (n b acc xlo kk : Nat) : Nat :=
  let y := xlo / 2 ^ 40 + 2 ^ 24
  let pnum := (y * y - 2 ^ 48) * 3
  let pden := y * y + y * 2 ^ 26 + 2 ^ 48
  let c1 := pnum * 2 ^ 12 / pden
  let c2 := (pnum * 2 ^ 12 - c1 * pden) * 2 ^ 12 / pden
  let pade := c1 * 2 ^ 20 + c2 * 2 ^ 8
  let vA := kk * CL + pade
  let sinh := ((2 ^ 50 - y * y) * 2 ^ 6 + y - 1) / y
  let vB := (kk + 1) * CL - sinh
  let ballow := if b = 1 ∨ n ≤ c.split then 1 else 0
  let capOK := if acc ≤ ACAP then 1 else 0
  let hA := if acc * b % M ≤ vA * 2 ^ 12 + CC * b then 1 else 0
  let hB := if acc * b % M ≤ vB * 2 ^ 12 + CC * b then 1 else 0
  let gd := if xlo ≤ 2 ^ 64 - 2 ^ 50 then 1 else 0
  capOK * (ballow * (hA ||| gd * hB))

/-- The eight carried registers. -/
structure Vals where
  /-- Register `0`. -/
  good : Nat
  /-- Register `1`. -/
  m : Nat
  /-- Register `2`. -/
  phi : Nat
  /-- Register `3`. -/
  sq : Nat
  /-- Register `4`. -/
  acc : Nat
  /-- Register `5`. -/
  pass : Nat
  /-- Register `13`. -/
  xlo : Nat
  /-- Register `14`. -/
  kk : Nat
  deriving DecidableEq, Repr

/-- Read the carried registers out of a machine state. -/
def valsOf (s : RegState) : Vals := ⟨s 0, s 1, s 2, s 3, s 4, s 5, s 13, s 14⟩

/-- The `Nat`-level round: what one flat iteration does to the carried
registers. -/
def gfRound (c : Params) (k : Nat) (v : Vals) : Vals :=
  let q := k % c.R
  let n := c.lo + k / c.R
  let d := q + 2
  let m0 := if q = 0 then n else v.m
  let phi0 := if q = 0 then 1 else v.phi
  let sq0 := if q = 0 then 1 else v.sq
  let pass0 := if q = 0 then 0 else v.pass
  let m1 := if m0 % d = 0 then m0 / d else m0
  let phi1 := if m0 % d = 0 then phi0 * (d - 1) else phi0
  let sq1 := if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0
  let phiF := if 1 < m1 then phi1 * (m1 - 1) else phi1
  let tq := (2 ^ 44 + phiF - 1) / phiF
  let acc1 := (v.acc + (if q = c.tdiv then sq1 * tq else 0)) % M
  let a := aOf n
  let x2 := advX n a v.xlo
  let g := if 2 ^ 63 ≤ x2 then 1 else 0
  let xloA := if 2 ^ 63 ≤ x2 then (x2 - 2 ^ 63) * 2 else (x2 - 2 ^ 62) * 4
  let xloI := (n - 2 ^ a) * 2 ^ (64 - a)
  let xlo1 := if q < c.tdiv then v.xlo else if q = c.tdiv then xloI else xloA
  let kkN := v.kk + a + g
  let kk1 := if q < c.tdiv then v.kk
             else if q = c.tdiv then a
             else if kkN ≤ KCAP then kkN else KCAP
  let pass1 := if q < c.tdiv then pass0
               else pass0 ||| hitOf c n (q - c.tdiv + 1) acc1 xlo1 kk1
  let good1 := if q = c.R - 1 then v.good * pass1 else v.good
  ⟨good1, m1, phi1, sq1, acc1, pass1, xlo1, kk1⟩

/-- The state invariant. -/
structure Inv (c : Params) (s : RegState) : Prop where
  /-- Every register holds a word. -/
  word : ∀ i, s i < M
  /-- The cofactor is positive. -/
  mPos : 0 < s 1
  /-- The totient product is positive. -/
  phiPos : 0 < s 2
  /-- Their product never grows past the scan ceiling. -/
  prod : s 1 * s 2 ≤ c.lo + c.len
  /-- The squarefree flag is a bit. -/
  sqLe : s 3 ≤ 1
  /-- The pass flag is a bit. -/
  passLe : s 5 ≤ 1
  /-- The good flag is a bit. -/
  goodLe : s 0 ≤ 1
  /-- The mantissa exponent is positive. -/
  kkPos : 1 ≤ s 14
  /-- The mantissa exponent is clamped. -/
  kkLe : s 14 ≤ KCAP

/-! ## §5 Word-sized literals and sizing consequences -/

private theorem lit0 : (0 : Nat) % M = 0 := by decide
private theorem lit1 : (1 : Nat) % M = 1 := by decide
private theorem lit2 : (2 : Nat) % M = 2 := by decide
private theorem lit3 : (3 : Nat) % M = 3 := by decide
private theorem lit4 : (4 : Nat) % M = 4 := by decide
private theorem litKCAP : KCAP % M = KCAP := by decide
private theorem litACAP : ACAP % M = ACAP := by decide
private theorem litCL : CL % M = CL := by decide
private theorem litCC : CC % M = CC := by decide
private theorem lit44 : (2 ^ 44 : Nat) % M = 2 ^ 44 := by decide
private theorem lit24 : (2 ^ 24 : Nat) % M = 2 ^ 24 := by decide
private theorem lit48' : (2 ^ 48 : Nat) % M = 2 ^ 48 := by decide
private theorem lit50 : (2 ^ 50 : Nat) % M = 2 ^ 50 := by decide
private theorem lit62 : (2 ^ 62 : Nat) % M = 2 ^ 62 := by decide
private theorem lit63 : (2 ^ 63 : Nat) % M = 2 ^ 63 := by decide
private theorem litGuard : (2 ^ 64 - 2 ^ 50 : Nat) % M = 2 ^ 64 - 2 ^ 50 := by
  decide
private theorem lit6 : (6 : Nat) % M = 6 := by decide
private theorem lit8 : (8 : Nat) % M = 8 := by decide
private theorem lit12 : (12 : Nat) % M = 12 := by decide
private theorem lit20 : (20 : Nat) % M = 20 := by decide
private theorem lit26 : (26 : Nat) % M = 26 := by decide
private theorem lit40 : (40 : Nat) % M = 40 := by decide
private theorem lit45 : (45 : Nat) % M = 45 := by decide
private theorem lit47 : (47 : Nat) % M = 47 := by decide
private theorem lit62' : (62 : Nat) % M = 62 := by decide
private theorem lit64 : (64 : Nat) % M = 64 := by decide
private theorem lit24n : (16777216 : Nat) % M = 16777216 := by decide
private theorem lit44n :
    (17592186044416 : Nat) % M = 17592186044416 := by decide
private theorem lit48n :
    (281474976710656 : Nat) % M = 281474976710656 := by decide
private theorem lit50n :
    (1125899906842624 : Nat) % M = 1125899906842624 := by decide
private theorem lit56n :
    (72057594037927936 : Nat) % M = 72057594037927936 := by decide
private theorem lit62n :
    (4611686018427387904 : Nat) % M = 4611686018427387904 := by decide
private theorem lit63n :
    (9223372036854775808 : Nat) % M = 9223372036854775808 := by decide
private theorem litGuardn :
    (18445618173802708992 : Nat) % M = 18445618173802708992 := by decide

private theorem two31_lt_M : (2 : Nat) ^ 31 < M := by decide

theorem Params.Sane.RPos {c : Params} (hc : c.Sane) : 0 < c.R := by
  have := hc.tdivPos; have := hc.bmaxPos; unfold Params.R; omega

theorem Params.Sane.RLtM {c : Params} (hc : c.Sane) : c.R < M := by
  have := hc.roundsSmall
  have : c.R < 2 ^ 31 := hc.roundsSmall
  exact Nat.lt_trans this two31_lt_M

theorem Params.Sane.RModM {c : Params} (hc : c.Sane) : c.R % M = c.R :=
  Nat.mod_eq_of_lt hc.RLtM

theorem Params.Sane.loopLtM {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : k < M := by
  have h1 : c.len * c.R < 2 ^ 48 := hc.loopSmall
  have h2 : (2:Nat) ^ 48 < M := by decide
  omega

theorem Params.Sane.qLt {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : k / c.R < c.len :=
  (Nat.div_lt_iff_lt_mul hc.RPos).mpr hk

/-- The candidate at a visited index. -/
theorem Params.Sane.candLt {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : c.lo + k / c.R < c.lo + c.len := by
  have := hc.qLt hk; omega

theorem Params.Sane.candGe {c : Params} (hc : c.Sane) {k : Nat} :
    2 ≤ c.lo + k / c.R :=
  Nat.le_trans hc.loPos (Nat.le_add_right _ _)

/-! ## §6 Arithmetic helpers -/

private theorem modId {a : Nat} (h : a < M) : a % M = a := Nat.mod_eq_of_lt h

/-- `a − b` computed in `u64`, for `b ≤ a < 2⁶⁴`. -/
private theorem subExact (a b : Nat) (hba : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hM : 0 < M := M_pos
  have hbM : b < M := by omega
  rw [show a + (M - b) = M + (a - b) by omega, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- `a − (a / b)·b` computed in `u64` is `a % b`. -/
private theorem peelSub (a b : Nat) (hb : 0 < b) (ha : a < M) :
    (a + (M - a / b * b % M)) % M = a % b := by
  have h : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hlt : a % b < b := Nat.mod_lt a hb
  have hc : a / b * b = b * (a / b) := Nat.mul_comm _ _
  rw [hc, Nat.mod_eq_of_lt (show b * (a / b) < M by omega),
    show a + (M - b * (a / b)) = M + a % b by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a % b < M by omega)]

private theorem bitLe (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) ≤ 1 := by split <;> omega

private theorem bit_or_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    x ||| y ≤ 1 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
    rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

private theorem or_mod (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    (x ||| y) % M = x ||| y := by
  refine Nat.mod_eq_of_lt ?_
  have h1 := bit_or_le x y hx hy
  have h2 : (2:Nat) ≤ M := by decide
  omega

/-- The mantissa advance is the exact shifted product. -/
theorem advX_eq (n a xlo : Nat) (ha : a ≤ 45) :
    advX n a xlo = (2 ^ 64 + xlo) * n / 2 ^ (a + 2) := by
  unfold advX
  have hsplit : xlo = xlo / 2 ^ 47 * 2 ^ 47 + (xlo - xlo / 2 ^ 47 * 2 ^ 47) := by
    have := Nat.div_mul_le_self xlo (2 ^ 47)
    omega
  have hp64 : (2 : Nat) ^ (62 - a) * 2 ^ (a + 2) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hp47 : (2 : Nat) ^ (45 - a) * 2 ^ (a + 2) = 2 ^ 47 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hpos : 0 < (2 : Nat) ^ (a + 2) := Nat.two_pow_pos _
  have hq1 : 2 ^ (a + 2) * (n * 2 ^ (62 - a)) = 2 ^ 64 * n := by
    rw [Nat.mul_comm n (2 ^ (62 - a)), ← Nat.mul_assoc,
      Nat.mul_comm (2 ^ (a + 2)) (2 ^ (62 - a)), hp64]
  have hq2 : 2 ^ (a + 2) * (xlo / 2 ^ 47 * n * 2 ^ (45 - a))
      = xlo / 2 ^ 47 * 2 ^ 47 * n := by
    rw [Nat.mul_comm (xlo / 2 ^ 47 * n) (2 ^ (45 - a)), ← Nat.mul_assoc,
      Nat.mul_comm (2 ^ (a + 2)) (2 ^ (45 - a)), hp47,
      Nat.mul_comm (2 ^ 47) (xlo / 2 ^ 47 * n),
      Nat.mul_assoc (xlo / 2 ^ 47) n (2 ^ 47),
      Nat.mul_comm n (2 ^ 47), ← Nat.mul_assoc]
  have hexp : (2 ^ 64 + xlo) * n
      = 2 ^ (a + 2) * (n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a))
        + (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n := by
    rw [Nat.mul_add, hq1, hq2]
    conv => lhs; rw [hsplit]
    rw [Nat.add_mul, Nat.add_mul]
    omega
  rw [hexp, Nat.mul_add_div hpos]

/-- The advance stays inside a word. -/
theorem advX_lt (n a xlo : Nat) (hn : n < 2 ^ (a + 1)) (hx : xlo < 2 ^ 64)
    (ha : a ≤ 45) : advX n a xlo < 2 ^ 64 := by
  rw [advX_eq n a xlo ha]
  refine Nat.div_lt_of_lt_mul ?_
  have h1 : 2 ^ 64 + xlo < 2 ^ 65 := by
    have : (2:Nat) ^ 65 = 2 ^ 64 + 2 ^ 64 := by omega
    omega
  have h2 : (2 ^ 64 + xlo) * n < 2 ^ 65 * 2 ^ (a + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt h1 hn
  have h3 : (2:Nat) ^ 65 * 2 ^ (a + 1) = 2 ^ 64 * 2 ^ (a + 2) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  omega

/-- The advance is at least `2⁶²` when the mantissa is live. -/
theorem advX_ge (n a xlo : Nat) (hna : 2 ^ a ≤ n) (ha : a ≤ 62) :
    2 ^ 62 ≤ advX n a xlo := by
  have h1 : (2:Nat) ^ a * 2 ^ (62 - a) ≤ n * 2 ^ (62 - a) :=
    Nat.mul_le_mul_right _ hna
  have h2 : (2:Nat) ^ a * 2 ^ (62 - a) = 2 ^ (a + (62 - a)) := by
    rw [Nat.pow_add]
  have h3 : a + (62 - a) = 62 := by omega
  rw [h3] at h2
  have h4 : n * 2 ^ (62 - a) ≤ advX n a xlo :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  omega

/-! ## §7 Stage specifications

Each block's effect, from an abstract incoming state, with every `% M`
truncation discharged here. -/

/-- **Stage A1**: decode, reset, masks. -/
theorem blkA1_spec (c : Params) (k : Nat) (t : RegState) (qd q : Nat)
    (h6 : t 6 = qd) (h7 : t 7 = q)
    (hloM : c.lo % M = c.lo)
    (hnM : (qd + c.lo) % M = c.lo + qd)
    (hnM' : (c.lo + qd) % M = c.lo + qd)
    (hdM : (q + 2) % M = q + 2)
    (hR1M : (c.R - 1) % M = c.R - 1)
    (htdM : c.tdiv % M = c.tdiv)
    (h1M : t 1 % M = t 1) (h2M : t 2 % M = t 2) (h3M : t 3 % M = t 3)
    (h5M : t 5 % M = t 5) :
    run k t (blkA1 c) 0 = t 0 ∧
    run k t (blkA1 c) 4 = t 4 ∧
    run k t (blkA1 c) 13 = t 13 ∧
    run k t (blkA1 c) 14 = t 14 ∧
    run k t (blkA1 c) 6 = qd ∧
    run k t (blkA1 c) 7 = q ∧
    run k t (blkA1 c) 8 = c.lo + qd ∧
    run k t (blkA1 c) 9 = q + 2 ∧
    run k t (blkA1 c) 17 = (if q = c.R - 1 then 1 else 0) ∧
    run k t (blkA1 c) 18 = (if q = c.tdiv then 1 else 0) ∧
    run k t (blkA1 c) 19 = (if c.tdiv ≤ q then 1 else 0) ∧
    run k t (blkA1 c) 1 = (if q = 0 then c.lo + qd else t 1) ∧
    run k t (blkA1 c) 2 = (if q = 0 then 1 else t 2) ∧
    run k t (blkA1 c) 3 = (if q = 0 then 1 else t 3) ∧
    run k t (blkA1 c) 5 = (if q = 0 then 0 else t 5) := by
  by_cases hz : q = 0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA1, evalExpr, denoteOp, RegState.set, sel, h6, h7, hz,
        hloM, hnM, hnM', hdM, hR1M, htdM, h1M, h2M, h3M, h5M, lit0, lit1, lit2,
        ge_iff_le]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA1, evalExpr, denoteOp, RegState.set, sel, h6, h7, hz,
        hloM, hnM, hnM', hdM, hR1M, htdM, h1M, h2M, h3M, h5M, lit0, lit1, lit2,
        ge_iff_le]

/-- **Stage A2**: `⌊log₂ n⌋` and its power. -/
theorem blkA2_spec (k : Nat) (t : RegState) (n : Nat) (h8 : t 8 = n)
    (h2n : 2 ≤ n) (h17 : n < 2 ^ 17) :
    (∀ j, j ≠ 15 → j ≠ 16 → run k t blkA2 j = t j) ∧
    run k t blkA2 15 = aOf n ∧
    run k t blkA2 16 = 2 ^ aOf n := by
  obtain ⟨ha1, ha16, hpow, hpow'⟩ := aOf_bounds h2n h17
  have hb : ∀ v : Nat, (if v ≤ n then (1:Nat) else 0) ≤ 1 := fun v => bitLe _
  have haOfLt : aOf n < M := by
    have : (16:Nat) < M := by decide
    omega
  have hsum15 : run k t blkA2 15 = aOf n := by
    have b2 := hb 2; have b4 := hb 4; have b8 := hb 8; have b16 := hb 16
    have b32 := hb 32; have b64 := hb 64; have b128 := hb 128
    have b256 := hb 256; have b512 := hb 512; have b1024 := hb 1024
    have b2048 := hb 2048; have b4096 := hb 4096; have b8192 := hb 8192
    have b16384 := hb 16384; have b32768 := hb 32768; have b65536 := hb 65536
    simp [run, blkA2, aLoExpr, aHiExpr, geBit, evalExpr, denoteOp,
      RegState.set, ge_iff_le, h8, M]
    unfold aOf ind
    omega
  refine ⟨?_, hsum15, ?_⟩
  · intro j hj15 hj16
    simp [run, blkA2, RegState.set, hj15, hj16]
  · have h16v : run k t blkA2 16
        = (1 <<< (run k t blkA2 15)) % M := by
      simp [run, blkA2, RegState.set, evalExpr, denoteOp, lit1]
    rw [h16v, hsum15, Nat.shiftLeft_eq, Nat.one_mul]
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ aOf n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) ha16
    have h2 : (2:Nat) ^ 16 < M := by decide
    omega

/-- **Stage Ba1**: the divisibility flag and the squarefree update. -/
theorem blkBa1_spec (k : Nat) (t : RegState) (m0 sq0 d : Nat)
    (h1 : t 1 = m0) (h3 : t 3 = sq0)
    (h9 : t 9 = d) (h10 : t 10 = m0 / d) (h11 : t 11 = m0 / d / d)
    (hd0 : 0 < d)
    (hm0M : m0 < M) (hsq0M : sq0 ≤ 1) :
    run k t blkBa1 0 = t 0 ∧ run k t blkBa1 1 = t 1 ∧
    run k t blkBa1 2 = t 2 ∧ run k t blkBa1 4 = t 4 ∧
    run k t blkBa1 5 = t 5 ∧ run k t blkBa1 7 = t 7 ∧
    run k t blkBa1 8 = t 8 ∧ run k t blkBa1 9 = t 9 ∧
    run k t blkBa1 10 = t 10 ∧
    run k t blkBa1 13 = t 13 ∧ run k t blkBa1 14 = t 14 ∧
    run k t blkBa1 15 = t 15 ∧ run k t blkBa1 16 = t 16 ∧
    run k t blkBa1 17 = t 17 ∧ run k t blkBa1 18 = t 18 ∧
    run k t blkBa1 19 = t 19 ∧ run k t blkBa1 22 = t 22 ∧
    run k t blkBa1 12 = (if m0 % d = 0 then 1 else 0) ∧
    run k t blkBa1 3 = (if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0) := by
  have hm0dM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  have p1 := peelSub m0 d hd0 hm0M
  have p2 := peelSub (m0 / d) d hd0 hm0dM
  have hsq0M' : sq0 < M := by
    have : (2:Nat) ≤ M := by decide
    omega
  by_cases hdvd : m0 % d = 0 <;> by_cases hdvd2 : m0 / d % d = 0 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ <;>
    simp [run, blkBa1, evalExpr, denoteOp, RegState.set,
      h1, h3, h9, h10, h11, hdvd, hdvd2, p1, p2, lit0, lit1,
      Nat.mod_eq_of_lt hm0M, Nat.mod_eq_of_lt hm0dM,
      Nat.mod_eq_of_lt hsq0M']

/-- **Stage Ba2**: the totient product and cofactor updates. -/
theorem blkBa2_spec (k : Nat) (t : RegState) (m0 phi0 q d fl : Nat)
    (h1 : t 1 = m0) (h2 : t 2 = phi0) (h7 : t 7 = q)
    (h10 : t 10 = m0 / d)
    (h12 : t 12 = fl) (efl : fl = if m0 % d = 0 then 1 else 0)
    (hd1 : d - 1 = q + 1)
    (hm0M : m0 < M) (hphi0M : phi0 < M)
    (hphi1M : phi0 * (q + 1) < M) :
    run k t blkBa2 0 = t 0 ∧ run k t blkBa2 3 = t 3 ∧
    run k t blkBa2 4 = t 4 ∧ run k t blkBa2 5 = t 5 ∧
    run k t blkBa2 7 = t 7 ∧ run k t blkBa2 8 = t 8 ∧
    run k t blkBa2 13 = t 13 ∧ run k t blkBa2 14 = t 14 ∧
    run k t blkBa2 15 = t 15 ∧ run k t blkBa2 16 = t 16 ∧
    run k t blkBa2 17 = t 17 ∧ run k t blkBa2 18 = t 18 ∧
    run k t blkBa2 19 = t 19 ∧ run k t blkBa2 22 = t 22 ∧
    run k t blkBa2 1 = (if m0 % d = 0 then m0 / d else m0) ∧
    run k t blkBa2 2 = (if m0 % d = 0 then phi0 * (d - 1) else phi0) := by
  have hm0dM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  by_cases hdvd : m0 % d = 0
  · rw [if_pos hdvd] at efl
    subst efl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkBa2, evalExpr, denoteOp, RegState.set, sel,
        h1, h2, h7, h10, h12, hd1, hdvd, lit0, lit1,
        Nat.mod_eq_of_lt hm0M, Nat.mod_eq_of_lt hm0dM,
        Nat.mod_eq_of_lt hphi0M, Nat.mod_eq_of_lt hphi1M]
  · rw [if_neg hdvd] at efl
    subst efl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkBa2, evalExpr, denoteOp, RegState.set, sel,
        h1, h2, h7, h10, h12, hd1, hdvd, lit0, lit1,
        Nat.mod_eq_of_lt hm0M, Nat.mod_eq_of_lt hm0dM,
        Nat.mod_eq_of_lt hphi0M, Nat.mod_eq_of_lt hphi1M]

/-- **Stage Bb**: the totient decode and the term numerator. -/
theorem blkBb_spec (k : Nat) (t : RegState) (m1 phi1 phiF : Nat)
    (h1 : t 1 = m1) (h2 : t 2 = phi1)
    (ephiF : phiF = if 1 < m1 then phi1 * (m1 - 1) else phi1)
    (hm1pos : 0 < m1) (hm1M : m1 < M) (hphi1M : phi1 < M)
    (hphiFM : phi1 * (m1 - 1) < M)
    (hsumM : 2 ^ 44 + phiF < M) :
    run k t blkBb 0 = t 0 ∧ run k t blkBb 1 = t 1 ∧ run k t blkBb 2 = t 2 ∧
    run k t blkBb 3 = t 3 ∧ run k t blkBb 4 = t 4 ∧ run k t blkBb 5 = t 5 ∧
    run k t blkBb 7 = t 7 ∧ run k t blkBb 8 = t 8 ∧
    run k t blkBb 13 = t 13 ∧ run k t blkBb 14 = t 14 ∧
    run k t blkBb 15 = t 15 ∧ run k t blkBb 16 = t 16 ∧
    run k t blkBb 17 = t 17 ∧ run k t blkBb 18 = t 18 ∧
    run k t blkBb 19 = t 19 ∧ run k t blkBb 22 = t 22 ∧
    run k t blkBb 20 = phiF ∧
    run k t blkBb 21 = 2 ^ 44 + phiF - 1 := by
  have hphiFM' : phiF < M := by
    rw [ephiF]; split
    · exact hphiFM
    · exact hphi1M
  have hs1 := subExact m1 1 hm1pos hm1M
  have hs2 := subExact (2 ^ 44 + phiF) 1 (by omega) hsumM
  by_cases hgt : 1 < m1
  · have ephiF' : phiF = phi1 * (m1 - 1) := by rw [ephiF, if_pos hgt]
    rw [ephiF'] at hs2 hsumM hphiFM'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;>
      simp [run, blkBb, evalExpr, denoteOp, RegState.set, sel,
        h1, h2, hgt, hs1, hs2, ephiF', lit1, lit44,
        Nat.mod_eq_of_lt hm1M, Nat.mod_eq_of_lt hphi1M,
        Nat.mod_eq_of_lt hphiFM, Nat.mod_eq_of_lt hphiFM',
        Nat.mod_eq_of_lt hsumM, ge_iff_le]
  · have ephiF' : phiF = phi1 := by rw [ephiF, if_neg hgt]
    rw [ephiF'] at hs2 hsumM hphiFM'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;>
      simp [run, blkBb, evalExpr, denoteOp, RegState.set, sel,
        h1, h2, hgt, hs1, hs2, ephiF', lit1, lit44,
        Nat.mod_eq_of_lt hm1M, Nat.mod_eq_of_lt hphi1M,
        Nat.mod_eq_of_lt hphiFM, Nat.mod_eq_of_lt hphiFM',
        Nat.mod_eq_of_lt hsumM, ge_iff_le]

/-- **Stage Ca1a**: the masked accumulator step and the mantissa high
half-word. -/
theorem blkCa1a_spec (k : Nat) (t : RegState) (acc t0m sq tq22 xlo : Nat)
    (h4 : t 4 = acc) (h18 : t 18 = t0m) (h3 : t 3 = sq) (h22 : t 22 = tq22)
    (h13 : t 13 = xlo)
    (hacc : acc < M) (ht0 : t0m ≤ 1) (hsq : sq ≤ 1) (htq : tq22 ≤ 2 ^ 44)
    (hxlo : xlo < M) :
    run k t blkCa1a 0 = t 0 ∧ run k t blkCa1a 1 = t 1 ∧
    run k t blkCa1a 2 = t 2 ∧ run k t blkCa1a 3 = t 3 ∧
    run k t blkCa1a 5 = t 5 ∧ run k t blkCa1a 7 = t 7 ∧
    run k t blkCa1a 8 = t 8 ∧ run k t blkCa1a 13 = t 13 ∧
    run k t blkCa1a 14 = t 14 ∧ run k t blkCa1a 15 = t 15 ∧
    run k t blkCa1a 16 = t 16 ∧ run k t blkCa1a 17 = t 17 ∧
    run k t blkCa1a 18 = t 18 ∧ run k t blkCa1a 19 = t 19 ∧
    run k t blkCa1a 22 = t 22 ∧
    run k t blkCa1a 4 = (acc + t0m * (sq * tq22)) % M ∧
    run k t blkCa1a 24 = xlo / 2 ^ 47 := by
  have e1 : (sq * tq22) % M = sq * tq22 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : sq * tq22 ≤ 1 * tq22 := Nat.mul_le_mul_right _ hsq
    have h2 : (2:Nat) ^ 44 < M := by decide
    omega
  have e2 : (t0m * (sq * tq22)) % M = t0m * (sq * tq22) := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : sq * tq22 ≤ 1 * tq22 := Nat.mul_le_mul_right _ hsq
    have h2 : t0m * (sq * tq22) ≤ 1 * (sq * tq22) := Nat.mul_le_mul_right _ ht0
    have h3 : (2:Nat) ^ 44 < M := by decide
    omega
  have e3 : xlo / 2 ^ 47 % M = xlo / 2 ^ 47 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxlo)
  refine ⟨run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, ?_, ?_⟩ <;>
    simp [run, blkCa1a, evalExpr, denoteOp, RegState.set,
      h4, h18, h3, h22, h13, e1, e2, e3, lit47,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hacc,
      Nat.mod_eq_of_lt hxlo]

/-- **Stage Ca1b**: the mantissa low half-word and the high partial
product. -/
theorem blkCa1b_spec (k : Nat) (t : RegState) (xlo n : Nat)
    (h24 : t 24 = xlo / 2 ^ 47) (h13 : t 13 = xlo) (h8 : t 8 = n)
    (hxlo : xlo < M) (hn17 : n < 2 ^ 17) :
    run k t blkCa1b 0 = t 0 ∧ run k t blkCa1b 1 = t 1 ∧
    run k t blkCa1b 2 = t 2 ∧ run k t blkCa1b 3 = t 3 ∧
    run k t blkCa1b 4 = t 4 ∧ run k t blkCa1b 5 = t 5 ∧
    run k t blkCa1b 7 = t 7 ∧ run k t blkCa1b 8 = t 8 ∧
    run k t blkCa1b 13 = t 13 ∧ run k t blkCa1b 14 = t 14 ∧
    run k t blkCa1b 15 = t 15 ∧ run k t blkCa1b 16 = t 16 ∧
    run k t blkCa1b 17 = t 17 ∧ run k t blkCa1b 18 = t 18 ∧
    run k t blkCa1b 19 = t 19 ∧ run k t blkCa1b 22 = t 22 ∧
    run k t blkCa1b 25 = xlo - xlo / 2 ^ 47 * 2 ^ 47 ∧
    run k t blkCa1b 26 = xlo / 2 ^ 47 * n := by
  have hshl : (xlo / 2 ^ 47) <<< 47 = xlo / 2 ^ 47 * 2 ^ 47 :=
    Nat.shiftLeft_eq _ _
  have hle : xlo / 2 ^ 47 * 2 ^ 47 ≤ xlo := Nat.div_mul_le_self _ _
  have e4 : xlo / 2 ^ 47 * 2 ^ 47 % M = xlo / 2 ^ 47 * 2 ^ 47 :=
    Nat.mod_eq_of_lt (by omega)
  have e5 := subExact xlo (xlo / 2 ^ 47 * 2 ^ 47) hle hxlo
  have hdivlt : xlo / 2 ^ 47 < 2 ^ 17 := by
    refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
    have : (2:Nat) ^ 17 * 2 ^ 47 = 2 ^ 64 := by decide
    have hM : M = 2 ^ 64 := rfl
    omega
  have e6 : xlo / 2 ^ 47 * n % M = xlo / 2 ^ 47 * n := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : xlo / 2 ^ 47 * n < 2 ^ 17 * 2 ^ 17 :=
      Nat.mul_lt_mul_of_lt_of_lt hdivlt hn17
    have h2 : (2:Nat) ^ 17 * 2 ^ 17 < M := by decide
    omega
  refine ⟨run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    run_untouched _ _ _ (by decide) _, run_untouched _ _ _ (by decide) _,
    ?_, ?_⟩
  · have hgoal : run k t blkCa1b 25
        = (t 13 + (M - t 24 <<< (47 % M) % M)) % M := by
      simp [run, blkCa1b, evalExpr, denoteOp, RegState.set]
    rw [hgoal, lit47, h24, h13, hshl, e4]
    exact e5
  · have hgoal : run k t blkCa1b 26 = t 24 * t 8 % M := by
      simp [run, blkCa1b, evalExpr, denoteOp, RegState.set]
    rw [hgoal, h24, h8]
    exact e6

/-- **Stage Ca2**: the shifted product and the renormalisation case bit. -/
theorem blkCa2_spec (k : Nat) (t : RegState) (xlo n a : Nat)
    (h25 : t 25 = xlo - xlo / 2 ^ 47 * 2 ^ 47) (h26 : t 26 = xlo / 2 ^ 47 * n)
    (h8 : t 8 = n) (h15 : t 15 = a)
    (hxlo : xlo < M) (hn17 : n < 2 ^ 17) (hna : 2 ^ a ≤ n)
    (hna' : n < 2 ^ (a + 1)) (ha : a ≤ 16) :
    run k t blkCa2 0 = t 0 ∧ run k t blkCa2 1 = t 1 ∧
    run k t blkCa2 2 = t 2 ∧ run k t blkCa2 3 = t 3 ∧
    run k t blkCa2 4 = t 4 ∧ run k t blkCa2 5 = t 5 ∧
    run k t blkCa2 7 = t 7 ∧ run k t blkCa2 8 = t 8 ∧
    run k t blkCa2 13 = t 13 ∧ run k t blkCa2 14 = t 14 ∧
    run k t blkCa2 15 = t 15 ∧ run k t blkCa2 16 = t 16 ∧
    run k t blkCa2 17 = t 17 ∧ run k t blkCa2 18 = t 18 ∧
    run k t blkCa2 19 = t 19 ∧ run k t blkCa2 22 = t 22 ∧
    run k t blkCa2 28 = advX n a xlo ∧
    run k t blkCa2 29 = (if 2 ^ 63 ≤ advX n a xlo then 1 else 0) := by
  have ha45 : a ≤ 45 := by omega
  have hAdv := advX_lt n a xlo hna' (by
    have hM : M = 2 ^ 64 := rfl
    omega) ha45
  have hMeq : M = 2 ^ 64 := rfl
  have hdm := Nat.div_add_mod xlo (2 ^ 47)
  have hmodlt : xlo % 2 ^ 47 < 2 ^ 47 := Nat.mod_lt _ (by decide)
  have hlo47 : xlo - xlo / 2 ^ 47 * 2 ^ 47 = xlo % 2 ^ 47 := by omega
  have hlo47lt : xlo - xlo / 2 ^ 47 * 2 ^ 47 < 2 ^ 47 := by omega
  have hBlt : (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n < M := by
    have h1 : (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n < 2 ^ 47 * 2 ^ 17 :=
      Nat.mul_lt_mul_of_lt_of_lt hlo47lt hn17
    have h2 : (2:Nat) ^ 47 * 2 ^ 17 = 2 ^ 64 := by decide
    omega
  have eB : (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n % M
      = (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n := Nat.mod_eq_of_lt hBlt
  have e62 := subExact 62 a (by omega) (by decide)
  have e45 := subExact 45 a (by omega) (by decide)
  have hp62lt : (2:Nat) ^ (62 - a) < M := by
    have h1 : (2:Nat) ^ (62 - a) ≤ 2 ^ 62 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (2:Nat) ^ 62 < M := by decide
    omega
  have hp45lt : (2:Nat) ^ (45 - a) < M := by
    have h1 : (2:Nat) ^ (45 - a) ≤ 2 ^ 45 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (2:Nat) ^ 45 < M := by decide
    omega
  have hshl62 : 1 <<< (62 - a) % M = 2 ^ (62 - a) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp62lt
  have hshl45 : 1 <<< (45 - a) % M = 2 ^ (45 - a) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp45lt
  have hpow63 : (2:Nat) ^ (a + 1) * 2 ^ (62 - a) = 2 ^ 63 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have ht1lt : n * 2 ^ (62 - a) < 2 ^ 63 := by
    have h1 : n * 2 ^ (62 - a) < 2 ^ (a + 1) * 2 ^ (62 - a) :=
      Nat.mul_lt_mul_of_lt_of_le hna' (Nat.le_refl _) (Nat.two_pow_pos _)
    omega
  have et1 : n * 2 ^ (62 - a) % M = n * 2 ^ (62 - a) := by
    refine Nat.mod_eq_of_lt ?_
    have : (2:Nat) ^ 63 < M := by decide
    omega
  have hpow63' : (2:Nat) ^ 17 * (2 ^ (a + 1) * 2 ^ (45 - a)) = 2 ^ 63 := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have ht2lt : xlo / 2 ^ 47 * n * 2 ^ (45 - a) < 2 ^ 63 := by
    have hdivlt : xlo / 2 ^ 47 < 2 ^ 17 := by
      refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
      have : (2:Nat) ^ 17 * 2 ^ 47 = 2 ^ 64 := by decide
      omega
    have h1 : xlo / 2 ^ 47 * n < 2 ^ 17 * 2 ^ (a + 1) :=
      Nat.mul_lt_mul_of_lt_of_lt hdivlt hna'
    have h2 : xlo / 2 ^ 47 * n * 2 ^ (45 - a)
        < 2 ^ 17 * 2 ^ (a + 1) * 2 ^ (45 - a) :=
      Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_refl _) (Nat.two_pow_pos _)
    rw [Nat.mul_assoc (2 ^ 17) (2 ^ (a + 1)) (2 ^ (45 - a))] at h2
    omega
  have et2 : xlo / 2 ^ 47 * n * 2 ^ (45 - a) % M
      = xlo / 2 ^ 47 * n * 2 ^ (45 - a) := by
    refine Nat.mod_eq_of_lt ?_
    have : (2:Nat) ^ 63 < M := by decide
    omega
  have ea2 : (a + 2) % M = a + 2 := Nat.mod_eq_of_lt (by
    have : (17:Nat) < M := by decide
    omega)
  have et3 : (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n / 2 ^ (a + 2) % M
      = (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n / 2 ^ (a + 2) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hBlt)
  have hsplit12 : n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a)
      ≤ advX n a xlo := Nat.le_add_right _ _
  have es12 : (n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a)) % M
      = n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a) := by
    refine Nat.mod_eq_of_lt ?_
    have := hAdv
    omega
  have esT : advX n a xlo % M = advX n a xlo := by
    refine Nat.mod_eq_of_lt ?_
    omega
  have hAdvUnfold : n * 2 ^ (62 - a) + xlo / 2 ^ 47 * n * 2 ^ (45 - a)
      + (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n / 2 ^ (a + 2) = advX n a xlo := rfl
  have hsplit : run k t blkCa2 = run k (run k (run k t blkCa2a) blkCa2b) blkCa2c := by
    show run k t (blkCa2a ++ blkCa2b ++ blkCa2c) = _
    rw [run_append, run_append]
  have lit47' : (47 : Nat) % M = 47 := by decide
  have lit2' : (2 : Nat) % M = 2 := by decide
  have V27 : run k t blkCa2a 27 = (xlo - xlo / 2 ^ 47 * 2 ^ 47) * n := by
    have hgoal : run k t blkCa2a 27 = t 25 * t 8 % M := by
      simp [run, blkCa2a, evalExpr, denoteOp, RegState.set]
    rw [hgoal, h25, h8]
    exact eB
  have t2f : ∀ j, j ≠ 27 → run k t blkCa2a j = t j := by
    intro j hj
    refine run_untouched _ _ _ ?_ _
    intro a ha
    simp only [blkCa2a, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    simp only []
    omega
  have V28 : run k (run k t blkCa2a) blkCa2b 28 = advX n a xlo := by
    have hgoal : ∀ u : RegState, run k u blkCa2b 28
        = (u 8 * (1 % M) <<< ((62 + (M - u 15)) % M)
           + u 26 * (1 % M) <<< ((45 + (M - u 15)) % M)
           + u 27 >>> ((u 15 + 2) % M)) % M := by
      intro u
      simp [run, blkCa2b, evalExpr, denoteOp, RegState.set]
    have hshl62' : (1:Nat) <<< (62 - a) = 2 ^ (62 - a) := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hshl45' : (1:Nat) <<< (45 - a) = 2 ^ (45 - a) := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hgoal, t2f 8 (by decide), t2f 15 (by decide), t2f 26 (by decide), V27,
      h8, h15, h26, (by decide : (1:Nat) % M = 1), e62, e45, hshl62', hshl45',
      ea2, Nat.shiftRight_eq_div_pow, hAdvUnfold]
    exact esT
  have V29 : run k (run k (run k t blkCa2a) blkCa2b) blkCa2c 29
      = (if 2 ^ 63 ≤ advX n a xlo then 1 else 0) := by
    have hgoal : ∀ u : RegState, run k u blkCa2c 29
        = (if u 28 ≥ 9223372036854775808 % M then 1 else 0) := by
      intro u
      simp [run, blkCa2c, evalExpr, denoteOp, RegState.set]
    rw [hgoal]
    have h28v : run k (run k t blkCa2a) blkCa2b 28 = advX n a xlo := V28
    simp only [h28v, (by decide : (9223372036854775808 : Nat) % M
      = 9223372036854775808), ge_iff_le]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    first
      | (rw [hsplit, run_untouched _ _ _ (by decide),
          run_untouched _ _ _ (by decide), run_untouched _ _ _ (by decide)])
      | (rw [hsplit]
         exact V28)
      | (rw [hsplit]
         exact V29)

private theorem blkCa3w1_val54 (k : Nat) (t : RegState) (x2 : Nat)
    (h28 : t 28 = x2) (hg : 2 ^ 63 ≤ x2) (hx2lt : x2 < M) :
    run k t blkCa3w1 54 = (x2 - 2 ^ 63) * 2 := by
  have hgoal : run k t blkCa3w1 54
      = ((t 28 + (M - L63 % M)) * 2) % M := by
    simp [run, blkCa3w1, evalExpr, denoteOp, RegState.set]
  have hg' : L63 ≤ x2 := hg
  have es63 := subExact x2 L63 hg' hx2lt
  have e30 : (x2 - L63) * 2 % M = (x2 - L63) * 2 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : L63 = 2 ^ 63 := rfl
    have h2 : M = 2 ^ 64 := rfl
    omega
  rw [hgoal, h28, (by decide : L63 % M = L63), Nat.mul_mod, es63,
    (by decide : (2 : Nat) % M = 2), e30]
  rfl

private theorem blkCa3w2_val55 (k : Nat) (t : RegState) (x2 : Nat)
    (h28 : t 28 = x2) (hx2ge : 2 ^ 62 ≤ x2) (hlt : x2 < 2 ^ 63) :
    run k t blkCa3w2 55 = (x2 - 2 ^ 62) * 4 := by
  have hgoal : run k t blkCa3w2 55
      = ((t 28 + (M - L62 % M)) * 4) % M := by
    simp [run, blkCa3w2, evalExpr, denoteOp, RegState.set]
  have hg2 : L62 ≤ x2 := hx2ge
  have es62 := subExact x2 L62 hg2 (by
    have h1 : M = 2 ^ 64 := rfl
    omega)
  have e30 : (x2 - L62) * 4 % M = (x2 - L62) * 4 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : L62 = 2 ^ 62 := rfl
    have h2 : M = 2 ^ 64 := rfl
    omega
  rw [hgoal, h28, (by decide : L62 % M = L62), Nat.mul_mod, es62,
    (by decide : (4 : Nat) % M = 4), e30]
  rfl

private theorem blkCa3x1_val30 (k : Nat) (t : RegState) (v54 v55 g : Nat)
    (h54 : t 54 = v54) (h55 : t 55 = v55) (h29 : t 29 = g) (hg : g ≤ 1)
    (h54M : v54 < M) (h55M : v55 < M) :
    run k t blkCa3x1 30 = (if g = 1 then v54 else v55) := by
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl <;>
    simp [run, blkCa3x1, sel, evalExpr, denoteOp, RegState.set,
      h54, h55, h29, Nat.mod_eq_of_lt h54M, Nat.mod_eq_of_lt h55M]

private theorem blkCa3x_val30 (k : Nat) (t : RegState) (x2 : Nat)
    (h28 : t 28 = x2) (h29 : t 29 = (if 2 ^ 63 ≤ x2 then 1 else 0))
    (hword : ∀ i, t i < M) (hx2lt : x2 < M) (hx2ge : 2 ^ 62 ≤ x2) :
    run k (run k (run k t blkCa3w1) blkCa3w2) blkCa3x1 30
      = (if 2 ^ 63 ≤ x2 then (x2 - 2 ^ 63) * 2 else (x2 - 2 ^ 62) * 4) := by
  have hMeq : M = 2 ^ 64 := rfl
  have w1wf : ∀ a ∈ blkCa3w1, a.WF cursor := by
    intro a ha
    simp only [blkCa3w1, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩
  have w2wf : ∀ a ∈ blkCa3w2, a.WF cursor := by
    intro a ha
    simp only [blkCa3w2, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩
  have hword1 : ∀ i, run k t blkCa3w1 i < M :=
    run_lt k cursor blkCa3w1 w1wf _ hword
  have hword2 : ∀ i, run k (run k t blkCa3w1) blkCa3w2 i < M :=
    run_lt k cursor blkCa3w2 w2wf _ hword1
  have w2f28 : run k (run k t blkCa3w1) blkCa3w2 28 = x2 := by
    rw [run_untouched _ _ _ (by
      intro a ha
      simp only [blkCa3w2, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only []
      omega),
      run_untouched _ _ _ (by
      intro a ha
      simp only [blkCa3w1, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only []
      omega)]
    exact h28
  have w2f29 : run k (run k t blkCa3w1) blkCa3w2 29
      = (if 2 ^ 63 ≤ x2 then 1 else 0) := by
    rw [run_untouched _ _ _ (by
      intro a ha
      simp only [blkCa3w2, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only []
      omega),
      run_untouched _ _ _ (by
      intro a ha
      simp only [blkCa3w1, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only []
      omega)]
    exact h29
  by_cases hg : 2 ^ 63 ≤ x2
  · have V54 : run k (run k t blkCa3w1) blkCa3w2 54 = (x2 - 2 ^ 63) * 2 := by
      rw [run_untouched _ _ _ (by
        intro a ha
        simp only [blkCa3w2, List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        simp only []
        omega)]
      exact blkCa3w1_val54 k t x2 h28 hg hx2lt
    have h29b : run k (run k t blkCa3w1) blkCa3w2 29 = 1 := by
      rw [w2f29, if_pos hg]
    have hval := blkCa3x1_val30 k (run k (run k t blkCa3w1) blkCa3w2)
      ((x2 - 2 ^ 63) * 2) (run k (run k t blkCa3w1) blkCa3w2 55) 1
      V54 rfl h29b (by omega) (by omega) (hword2 55)
    rw [hval, if_pos rfl, if_pos hg]
  · have hlt63 : x2 < 2 ^ 63 := by omega
    have V55 : run k (run k t blkCa3w1) blkCa3w2 55 = (x2 - 2 ^ 62) * 4 :=
      blkCa3w2_val55 k (run k t blkCa3w1) x2
        (by
          rw [run_untouched _ _ _ (by
            intro a ha
            simp only [blkCa3w1, List.mem_cons, List.not_mem_nil,
              or_false] at ha
            subst ha
            simp only []
            omega)]
          exact h28)
        hx2ge hlt63
    have h29b : run k (run k t blkCa3w1) blkCa3w2 29 = 0 := by
      rw [w2f29, if_neg hg]
    have hval := blkCa3x1_val30 k (run k (run k t blkCa3w1) blkCa3w2)
      (run k (run k t blkCa3w1) blkCa3w2 54) ((x2 - 2 ^ 62) * 4) 0
      rfl V55 h29b (by omega) (hword2 54) (by omega)
    rw [hval, if_neg (by omega), if_neg hg]

/-- **Stage Ca3x**: the renormalised advance and the init value. -/
theorem blkCa3x_spec (k : Nat) (t : RegState) (x2 n a : Nat)
    (h28 : t 28 = x2) (h29 : t 29 = (if 2 ^ 63 ≤ x2 then 1 else 0))
    (h8 : t 8 = n) (h16 : t 16 = 2 ^ a) (h15 : t 15 = a)
    (hword : ∀ i, t i < M)
    (hx2lt : x2 < M) (hx2ge : 2 ^ 62 ≤ x2)
    (hna : 2 ^ a ≤ n) (hna' : n < 2 ^ (a + 1)) (ha : a ≤ 16)
    (hn17 : n < 2 ^ 17) :
    run k t blkCa3x 0 = t 0 ∧ run k t blkCa3x 1 = t 1 ∧
    run k t blkCa3x 2 = t 2 ∧ run k t blkCa3x 3 = t 3 ∧
    run k t blkCa3x 4 = t 4 ∧ run k t blkCa3x 5 = t 5 ∧
    run k t blkCa3x 7 = t 7 ∧ run k t blkCa3x 8 = t 8 ∧
    run k t blkCa3x 13 = t 13 ∧
    run k t blkCa3x 14 = t 14 ∧ run k t blkCa3x 15 = t 15 ∧
    run k t blkCa3x 16 = t 16 ∧ run k t blkCa3x 17 = t 17 ∧
    run k t blkCa3x 18 = t 18 ∧ run k t blkCa3x 19 = t 19 ∧
    run k t blkCa3x 22 = t 22 ∧ run k t blkCa3x 29 = t 29 ∧
    run k t blkCa3x 30 =
      (if 2 ^ 63 ≤ x2 then (x2 - 2 ^ 63) * 2 else (x2 - 2 ^ 62) * 4) ∧
    run k t blkCa3x 31 = (n - 2 ^ a) * 2 ^ (64 - a) := by
  have hsplit : run k t blkCa3x
      = run k (run k (run k (run k t blkCa3w1) blkCa3w2) blkCa3x1)
          blkCa3x2 := by
    show run k t (blkCa3w1 ++ blkCa3w2 ++ blkCa3x1 ++ blkCa3x2) = _
    rw [run_append, run_append, run_append]
  have V30 := blkCa3x_val30 k t x2 h28 h29 hword hx2lt hx2ge
  have hx1f : ∀ j, j ≠ 30 →
      run k (run k (run k t blkCa3w1) blkCa3w2) blkCa3x1 j
        = run k (run k t blkCa3w1) blkCa3w2 j := by
    intro j hj
    refine run_untouched _ _ _ ?_ _
    intro a' ha'
    simp only [blkCa3x1, List.mem_cons, List.not_mem_nil, or_false] at ha'
    subst ha'
    simp only []
    omega
  have hw12f : ∀ j, j ≠ 54 → j ≠ 55 →
      run k (run k t blkCa3w1) blkCa3w2 j = t j := by
    intro j hj54 hj55
    rw [run_untouched _ _ _ (by
      intro a' ha'
      simp only [blkCa3w2, List.mem_cons, List.not_mem_nil, or_false] at ha'
      subst ha'
      simp only []
      omega),
      run_untouched _ _ _ (by
      intro a' ha'
      simp only [blkCa3w1, List.mem_cons, List.not_mem_nil, or_false] at ha'
      subst ha'
      simp only []
      omega)]
  have V31 : run k (run k (run k (run k t blkCa3w1) blkCa3w2) blkCa3x1)
      blkCa3x2 31 = (n - 2 ^ a) * 2 ^ (64 - a) :=
    blkCa3x2_val31 k
      (run k (run k (run k t blkCa3w1) blkCa3w2) blkCa3x1) n a
      (by rw [hx1f 8 (by decide), hw12f 8 (by decide) (by decide)]; exact h8)
      (by rw [hx1f 16 (by decide), hw12f 16 (by decide) (by decide)]
          exact h16)
      (by rw [hx1f 15 (by decide), hw12f 15 (by decide) (by decide)]
          exact h15)
      hna hna' ha hn17
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;>
    first
      | (rw [hsplit, run_untouched _ _ _ (by decide),
          run_untouched _ _ _ (by decide), run_untouched _ _ _ (by decide),
          run_untouched _ _ _ (by decide)])
      | (rw [hsplit, run_untouched _ _ _ (by decide)]
         exact V30)
      | (rw [hsplit]
         exact V31)

/-- **Stage Ca3y**: the mantissa select. -/
theorem blkCa3y_spec (k : Nat) (t : RegState) (xloI xloA xlo tqm t0m : Nat)
    (h31 : t 31 = xloI) (h30 : t 30 = xloA) (h13 : t 13 = xlo)
    (h19 : t 19 = tqm) (h18 : t 18 = t0m)
    (hI : xloI < M) (hA : xloA < M) (hxlo : xlo < M)
    (htqm : tqm ≤ 1) (ht0m : t0m ≤ 1) :
    run k t blkCa3y 0 = t 0 ∧ run k t blkCa3y 1 = t 1 ∧
    run k t blkCa3y 2 = t 2 ∧ run k t blkCa3y 3 = t 3 ∧
    run k t blkCa3y 4 = t 4 ∧ run k t blkCa3y 5 = t 5 ∧
    run k t blkCa3y 7 = t 7 ∧ run k t blkCa3y 8 = t 8 ∧
    run k t blkCa3y 14 = t 14 ∧ run k t blkCa3y 15 = t 15 ∧
    run k t blkCa3y 16 = t 16 ∧ run k t blkCa3y 17 = t 17 ∧
    run k t blkCa3y 18 = t 18 ∧ run k t blkCa3y 19 = t 19 ∧
    run k t blkCa3y 22 = t 22 ∧ run k t blkCa3y 29 = t 29 ∧
    run k t blkCa3y 13 =
      (if tqm = 1 then (if t0m = 1 then xloI else xloA) else xlo) := by
  rcases (show tqm = 0 ∨ tqm = 1 by omega) with rfl | rfl <;>
    rcases (show t0m = 0 ∨ t0m = 1 by omega) with rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    simp [run, blkCa3y, evalExpr, denoteOp, RegState.set, sel,
      h31, h30, h13, h19, h18, lit1,
      Nat.mod_eq_of_lt hI, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hxlo]

/-- **Stage Ca4x**: the unclamped exponent update. -/
theorem blkCa4x_spec (k : Nat) (t : RegState) (kk a g : Nat)
    (h14 : t 14 = kk) (h15 : t 15 = a) (h29 : t 29 = g)
    (hkk : kk ≤ KCAP) (ha : a ≤ 16) (hgle : g ≤ 1) :
    run k t blkCa4x 0 = t 0 ∧ run k t blkCa4x 1 = t 1 ∧
    run k t blkCa4x 2 = t 2 ∧ run k t blkCa4x 3 = t 3 ∧
    run k t blkCa4x 4 = t 4 ∧ run k t blkCa4x 5 = t 5 ∧
    run k t blkCa4x 7 = t 7 ∧ run k t blkCa4x 8 = t 8 ∧
    run k t blkCa4x 13 = t 13 ∧ run k t blkCa4x 14 = t 14 ∧
    run k t blkCa4x 15 = t 15 ∧ run k t blkCa4x 16 = t 16 ∧
    run k t blkCa4x 17 = t 17 ∧ run k t blkCa4x 18 = t 18 ∧
    run k t blkCa4x 19 = t 19 ∧ run k t blkCa4x 22 = t 22 ∧
    run k t blkCa4x 48 = kk + a + g := by
  have e1 : (kk + a) % M = kk + a := Nat.mod_eq_of_lt (by
    have : KCAP + 17 < M := by decide
    omega)
  have e2 : (kk + a + g) % M = kk + a + g := Nat.mod_eq_of_lt (by
    have : KCAP + 18 < M := by decide
    omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp [run, blkCa4x, evalExpr, denoteOp, RegState.set,
      h14, h15, h29, e1, e2,
      Nat.mod_eq_of_lt (show kk < M from by
        have : KCAP < M := by decide
        omega),
      Nat.mod_eq_of_lt (show a < M from by
        have : (17:Nat) < M := by decide
        omega)]

/-- **Stage Ca4y**: the exponent select. -/
theorem blkCa4y_spec (k : Nat) (t : RegState) (kk a kkN tqm t0m : Nat)
    (h14 : t 14 = kk) (h15 : t 15 = a) (h48 : t 48 = kkN)
    (h19 : t 19 = tqm) (h18 : t 18 = t0m)
    (hkk : kk ≤ KCAP) (ha : a ≤ 16) (hkkN : kkN ≤ KCAP + 17)
    (htqm : tqm ≤ 1) (ht0m : t0m ≤ 1) :
    run k t blkCa4y 0 = t 0 ∧ run k t blkCa4y 1 = t 1 ∧
    run k t blkCa4y 2 = t 2 ∧ run k t blkCa4y 3 = t 3 ∧
    run k t blkCa4y 4 = t 4 ∧ run k t blkCa4y 5 = t 5 ∧
    run k t blkCa4y 7 = t 7 ∧ run k t blkCa4y 8 = t 8 ∧
    run k t blkCa4y 13 = t 13 ∧ run k t blkCa4y 15 = t 15 ∧
    run k t blkCa4y 16 = t 16 ∧ run k t blkCa4y 17 = t 17 ∧
    run k t blkCa4y 18 = t 18 ∧ run k t blkCa4y 19 = t 19 ∧
    run k t blkCa4y 22 = t 22 ∧ run k t blkCa4y 29 = t 29 ∧
    run k t blkCa4y 14 =
      (if tqm = 1 then
        (if t0m = 1 then a else if kkN ≤ KCAP then kkN else KCAP)
       else kk) := by
  have hkkM : kk < M := by
    have : KCAP < M := by decide
    omega
  have haM : a < M := by
    have : (17:Nat) < M := by decide
    omega
  have hkkNM : kkN < M := by
    have : KCAP + 17 < M := by decide
    omega
  by_cases hcl : kkN ≤ KCAP <;>
    rcases (show tqm = 0 ∨ tqm = 1 by omega) with rfl | rfl <;>
    rcases (show t0m = 0 ∨ t0m = 1 by omega) with rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    simp [run, blkCa4y, evalExpr, denoteOp, RegState.set, sel,
      h14, h15, h48, h19, h18, hcl, lit1, litKCAP,
      Nat.mod_eq_of_lt hkkM, Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hkkNM]

/-- **Stage Cb1x**: the truncated 25-bit mantissa. -/
theorem blkCb1x_spec (k : Nat) (t : RegState) (x : Nat)
    (h13 : t 13 = x) (hx : x < M) :
    run k t blkCb1x 0 = t 0 ∧ run k t blkCb1x 1 = t 1 ∧
    run k t blkCb1x 2 = t 2 ∧ run k t blkCb1x 3 = t 3 ∧
    run k t blkCb1x 4 = t 4 ∧ run k t blkCb1x 5 = t 5 ∧
    run k t blkCb1x 7 = t 7 ∧ run k t blkCb1x 8 = t 8 ∧
    run k t blkCb1x 13 = t 13 ∧ run k t blkCb1x 14 = t 14 ∧
    run k t blkCb1x 17 = t 17 ∧ run k t blkCb1x 18 = t 18 ∧
    run k t blkCb1x 19 = t 19 ∧
    run k t blkCb1x 32 = x / 2 ^ 40 + 2 ^ 24 := by
  have hdivlt : x / 2 ^ 40 < 2 ^ 24 := by
    refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
    have h1 : (2:Nat) ^ 24 * 2 ^ 40 = 2 ^ 64 := by decide
    have h2 : M = 2 ^ 64 := rfl
    omega
  have e1 : x / 1099511627776 % M = x / 1099511627776 := Nat.mod_eq_of_lt (by
    have h1 : x / 1099511627776 ≤ x := Nat.div_le_self _ _
    omega)
  have e2 : (x / 1099511627776 + 16777216) % M
      = x / 1099511627776 + 16777216 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : x / 2 ^ 40 < 2 ^ 24 := hdivlt
    have h2 : (33554432:Nat) < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkCb1x, evalExpr, denoteOp, RegState.set,
      h13, e1, e2, lit24n, lit40,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]

/-- **Stage Cb1y**: the Padé numerator. -/
theorem blkCb1y_spec (k : Nat) (t : RegState) (y : Nat)
    (h32 : t 32 = y) (hyge : 2 ^ 24 ≤ y) (hylt : y < 2 ^ 25) :
    run k t blkCb1y 0 = t 0 ∧ run k t blkCb1y 1 = t 1 ∧
    run k t blkCb1y 2 = t 2 ∧ run k t blkCb1y 3 = t 3 ∧
    run k t blkCb1y 4 = t 4 ∧ run k t blkCb1y 5 = t 5 ∧
    run k t blkCb1y 7 = t 7 ∧ run k t blkCb1y 8 = t 8 ∧
    run k t blkCb1y 13 = t 13 ∧ run k t blkCb1y 14 = t 14 ∧
    run k t blkCb1y 17 = t 17 ∧ run k t blkCb1y 18 = t 18 ∧
    run k t blkCb1y 19 = t 19 ∧ run k t blkCb1y 32 = t 32 ∧
    run k t blkCb1y 33 = (y * y - 2 ^ 48) * 3 := by
  have hy2lt : y * y < 2 ^ 50 := by
    have h1 : y * y < 2 ^ 25 * 2 ^ 25 := Nat.mul_lt_mul_of_lt_of_lt hylt hylt
    have h2 : (2:Nat) ^ 25 * 2 ^ 25 = 2 ^ 50 := by decide
    omega
  have hy2ge : 2 ^ 48 ≤ y * y := by
    have h1 : (2:Nat) ^ 24 * 2 ^ 24 ≤ y * y := Nat.mul_le_mul hyge hyge
    have h2 : (2:Nat) ^ 24 * 2 ^ 24 = 2 ^ 48 := by decide
    omega
  have e3 : y * y % M = y * y := Nat.mod_eq_of_lt (by
    have : (2:Nat) ^ 50 < M := by decide
    omega)
  have e4 := subExact (y * y) (2 ^ 48) hy2ge (by
    have : (2:Nat) ^ 50 < M := by decide
    omega)
  have e4' : (y * y + (M - 281474976710656)) % M
      = y * y - 281474976710656 := e4
  have e5 : (y * y - 281474976710656) * 3 % M
      = (y * y - 281474976710656) * 3 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (y * y - 281474976710656) * 3 ≤ 2 ^ 50 * 3 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2:Nat) ^ 50 * 3 < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkCb1y, evalExpr, denoteOp, RegState.set,
      h32, e3, e4', e5, lit3, lit48n,
      Nat.mod_eq_of_lt (show y < M from by
        have : (2:Nat) ^ 25 < M := by decide
        omega)]

/-- **Stage Cb2**: the Padé denominator and the shifted numerator. -/
theorem blkCb2_spec (k : Nat) (t : RegState) (y pnum : Nat)
    (h32 : t 32 = y) (h33 : t 33 = pnum)
    (hyge : 2 ^ 24 ≤ y) (hylt : y < 2 ^ 25) (hpn : pnum ≤ 3 * 2 ^ 50) :
    run k t blkCb2 0 = t 0 ∧ run k t blkCb2 1 = t 1 ∧
    run k t blkCb2 2 = t 2 ∧ run k t blkCb2 3 = t 3 ∧
    run k t blkCb2 4 = t 4 ∧ run k t blkCb2 5 = t 5 ∧
    run k t blkCb2 7 = t 7 ∧ run k t blkCb2 8 = t 8 ∧
    run k t blkCb2 13 = t 13 ∧ run k t blkCb2 14 = t 14 ∧
    run k t blkCb2 17 = t 17 ∧ run k t blkCb2 18 = t 18 ∧
    run k t blkCb2 19 = t 19 ∧ run k t blkCb2 32 = t 32 ∧
    run k t blkCb2 34 = y * y + y * 2 ^ 26 + 2 ^ 48 ∧
    run k t blkCb2 35 = pnum * 2 ^ 12 := by
  have hy2lt : y * y < 2 ^ 50 := by
    have h1 : y * y < 2 ^ 25 * 2 ^ 25 := Nat.mul_lt_mul_of_lt_of_lt hylt hylt
    have h2 : (2:Nat) ^ 25 * 2 ^ 25 = 2 ^ 50 := by decide
    omega
  have e1 : y * y % M = y * y := Nat.mod_eq_of_lt (by
    have : (2:Nat) ^ 50 < M := by decide
    omega)
  have hshl26 : y <<< 26 = y * 2 ^ 26 := Nat.shiftLeft_eq _ _
  have hy26lt : y * 2 ^ 26 < 2 ^ 51 := by
    have h1 : y * 2 ^ 26 < 2 ^ 25 * 2 ^ 26 :=
      Nat.mul_lt_mul_of_lt_of_le hylt (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 25 * 2 ^ 26 = 2 ^ 51 := by decide
    omega
  have e2 : y * 2 ^ 26 % M = y * 2 ^ 26 := Nat.mod_eq_of_lt (by
    have : (2:Nat) ^ 51 < M := by decide
    omega)
  have e3 : (y * y + y * 2 ^ 26) % M = y * y + y * 2 ^ 26 :=
    Nat.mod_eq_of_lt (by
      have : (2:Nat) ^ 50 + 2 ^ 51 < M := by decide
      omega)
  have e4 : (y * y + y * 2 ^ 26 + 2 ^ 48) % M = y * y + y * 2 ^ 26 + 2 ^ 48 :=
    Nat.mod_eq_of_lt (by
      have : (2:Nat) ^ 50 + 2 ^ 51 + 2 ^ 48 < M := by decide
      omega)
  have hshl12 : pnum <<< 12 = pnum * 2 ^ 12 := Nat.shiftLeft_eq _ _
  have e5 : pnum * 2 ^ 12 % M = pnum * 2 ^ 12 := Nat.mod_eq_of_lt (by
    have h1 : pnum * 2 ^ 12 ≤ 3 * 2 ^ 50 * 2 ^ 12 :=
      Nat.mul_le_mul_right _ hpn
    have h2 : (3:Nat) * 2 ^ 50 * 2 ^ 12 < M := by decide
    omega)
  have hshl26' : y <<< 26 = y * 67108864 := hshl26
  have e2' : y * 67108864 % M = y * 67108864 := e2
  have e3' : (y * y + y * 67108864) % M = y * y + y * 67108864 := e3
  have e4' : (y * y + y * 67108864 + 281474976710656) % M
      = y * y + y * 67108864 + 281474976710656 := e4
  have hshl12' : pnum <<< 12 = pnum * 4096 := hshl12
  have e5' : pnum * 4096 % M = pnum * 4096 := e5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkCb2, evalExpr, denoteOp, RegState.set,
      h32, h33, hshl26', hshl12', e1, e2', e3', e4', e5', lit12, lit26,
      lit48n,
      Nat.mod_eq_of_lt (show y < M from by
        have : (2:Nat) ^ 25 < M := by decide
        omega),
      Nat.mod_eq_of_lt (show pnum < M from by
        have : (3:Nat) * 2 ^ 50 < M := by decide
        omega)]

/-- **Stage D**: the Padé remainder step. -/
theorem blkD_spec (k : Nat) (t : RegState) (p12 pden : Nat)
    (h35 : t 35 = p12) (h36 : t 36 = p12 / pden) (h34 : t 34 = pden)
    (hp12 : p12 < M) (hpden : 0 < pden) (hpdenlt : pden < 2 ^ 52) :
    run k t blkD 0 = t 0 ∧ run k t blkD 1 = t 1 ∧
    run k t blkD 2 = t 2 ∧ run k t blkD 3 = t 3 ∧
    run k t blkD 4 = t 4 ∧ run k t blkD 5 = t 5 ∧
    run k t blkD 7 = t 7 ∧ run k t blkD 8 = t 8 ∧
    run k t blkD 13 = t 13 ∧ run k t blkD 14 = t 14 ∧
    run k t blkD 17 = t 17 ∧ run k t blkD 18 = t 18 ∧
    run k t blkD 19 = t 19 ∧ run k t blkD 32 = t 32 ∧
    run k t blkD 34 = t 34 ∧ run k t blkD 36 = t 36 ∧
    run k t blkD 37 = (p12 - p12 / pden * pden) * 2 ^ 12 := by
  have hle : p12 / pden * pden ≤ p12 := Nat.div_mul_le_self _ _
  have e1 : p12 / pden % M = p12 / pden :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp12)
  have e2 : p12 / pden * pden % M = p12 / pden * pden :=
    Nat.mod_eq_of_lt (by omega)
  have e3 := subExact p12 (p12 / pden * pden) hle hp12
  have hdm := Nat.div_add_mod p12 pden
  have hcomm : p12 / pden * pden = pden * (p12 / pden) := Nat.mul_comm _ _
  have hrem : p12 - p12 / pden * pden < pden := by
    have := Nat.mod_lt p12 hpden
    omega
  have hshl : (p12 - p12 / pden * pden) <<< 12
      = (p12 - p12 / pden * pden) * 4096 := Nat.shiftLeft_eq _ _
  have e4 : (p12 - p12 / pden * pden) * 4096 % M
      = (p12 - p12 / pden * pden) * 4096 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (p12 - p12 / pden * pden) * 2 ^ 12 < 2 ^ 52 * 2 ^ 12 :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 52 * 2 ^ 12 = 2 ^ 64 := by decide
    have h3 : M = 2 ^ 64 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkD, evalExpr, denoteOp, RegState.set,
      h35, h36, h34, e1, e2, e3, e4, hshl, lit12,
      Nat.mod_eq_of_lt hp12,
      Nat.mod_eq_of_lt (show pden < M from by
        have : (2:Nat) ^ 52 < M := by decide
        omega)]

private theorem blkE1_val39 (k : Nat) (t : RegState) (c1 c2 : Nat)
    (h36 : t 36 = c1) (h38 : t 38 = c2)
    (hc1 : c1 < 2 ^ 12) (hc2 : c2 < 2 ^ 12) :
    run k t blkE1 39 = c1 * 2 ^ 20 + c2 * 2 ^ 8 := by
  have hgoal : run k t blkE1 39
      = (t 36 <<< (20 % M) % M + t 38 <<< (8 % M) % M) % M := by
    simp [run, blkE1, evalExpr, denoteOp, RegState.set]
  have hshl20 : c1 <<< 20 = c1 * 2 ^ 20 := Nat.shiftLeft_eq _ _
  have hshl8 : c2 <<< 8 = c2 * 2 ^ 8 := Nat.shiftLeft_eq _ _
  have e1 : c1 * 2 ^ 20 % M = c1 * 2 ^ 20 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : c1 * 2 ^ 20 < 2 ^ 12 * 2 ^ 20 :=
      Nat.mul_lt_mul_of_lt_of_le hc1 (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 12 * 2 ^ 20 < M := by decide
    omega
  have e2 : c2 * 2 ^ 8 % M = c2 * 2 ^ 8 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : c2 * 2 ^ 8 < 2 ^ 12 * 2 ^ 8 :=
      Nat.mul_lt_mul_of_lt_of_le hc2 (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 12 * 2 ^ 8 < M := by decide
    omega
  have e3 : (c1 * 2 ^ 20 + c2 * 2 ^ 8) % M = c1 * 2 ^ 20 + c2 * 2 ^ 8 := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 32 + 2 ^ 20 < M := by decide
    have h2 : c1 * 2 ^ 20 < 2 ^ 12 * 2 ^ 20 :=
      Nat.mul_lt_mul_of_lt_of_le hc1 (Nat.le_refl _) (by decide)
    have h3 : c2 * 2 ^ 8 < 2 ^ 12 * 2 ^ 8 :=
      Nat.mul_lt_mul_of_lt_of_le hc2 (Nat.le_refl _) (by decide)
    have h4 : (2:Nat) ^ 12 * 2 ^ 20 = 2 ^ 32 := by decide
    have h5 : (2:Nat) ^ 12 * 2 ^ 8 = 2 ^ 20 := by decide
    omega
  rw [hgoal, (by decide : (20:Nat) % M = 20), (by decide : (8:Nat) % M = 8),
    h36, h38, hshl20, hshl8, e1, e2, e3]

private theorem blkE2_val40 (k : Nat) (u : RegState) (kk1 pade : Nat)
    (h14 : u 14 = kk1) (h39 : u 39 = pade)
    (hkk1 : kk1 ≤ KCAP) (hpade : pade < 2 ^ 33) :
    run k u blkE2 40 = kk1 * CL + pade := by
  have hgoal : run k u blkE2 40 = (u 14 * (CL % M) + u 39) % M := by
    simp [run, blkE2, evalExpr, denoteOp, RegState.set]
  have e1 : kk1 * CL % M = kk1 * CL := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : kk1 * CL ≤ KCAP * CL := Nat.mul_le_mul_right _ hkk1
    have h2 : KCAP * CL < M := by decide
    omega
  have e2 : (kk1 * CL + pade) % M = kk1 * CL + pade := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : kk1 * CL ≤ KCAP * CL := Nat.mul_le_mul_right _ hkk1
    have h2 : KCAP * CL + 2 ^ 33 < M := by decide
    omega
  rw [hgoal, litCL, h14, h39, Nat.mul_mod, e1]
  sorry

private theorem blkE2_val41 (k : Nat) (u : RegState) (y : Nat)
    (h32 : u 32 = y) (hyge : 2 ^ 24 ≤ y) (hylt : y < 2 ^ 25) :
    run k u blkE2 41 = (2 ^ 50 - y * y) * 2 ^ 6 + y - 1 := by
  sorry

/-- **Stage E**: the Padé recombination, candidate `A`, and the sinh
numerator. -/
theorem blkE_spec (k : Nat) (t : RegState) (c1 c2 kk1 y : Nat)
    (h36 : t 36 = c1) (h38 : t 38 = c2) (h14 : t 14 = kk1) (h32 : t 32 = y)
    (hc1 : c1 < 2 ^ 12) (hc2 : c2 < 2 ^ 12) (hkk1 : kk1 ≤ KCAP)
    (hyge : 2 ^ 24 ≤ y) (hylt : y < 2 ^ 25) :
    run k t blkE 0 = t 0 ∧ run k t blkE 3 = t 3 ∧
    run k t blkE 4 = t 4 ∧ run k t blkE 5 = t 5 ∧
    run k t blkE 7 = t 7 ∧ run k t blkE 8 = t 8 ∧
    run k t blkE 13 = t 13 ∧ run k t blkE 14 = t 14 ∧
    run k t blkE 17 = t 17 ∧ run k t blkE 18 = t 18 ∧
    run k t blkE 19 = t 19 ∧ run k t blkE 32 = t 32 ∧
    run k t blkE 40 = kk1 * CL + (c1 * 2 ^ 20 + c2 * 2 ^ 8) ∧
    run k t blkE 41 = (2 ^ 50 - y * y) * 2 ^ 6 + y - 1 := by
  have hsplit : run k t blkE = run k (run k t blkE1) blkE2 := by
    show run k t (blkE1 ++ blkE2) = _
    rw [run_append]
  have t1f : ∀ j, j ≠ 39 → run k t blkE1 j = t j := by
    intro j hj
    refine run_untouched _ _ _ ?_ _
    intro a ha
    simp only [blkE1, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    simp only []
    omega
  have hpade : c1 * 2 ^ 20 + c2 * 2 ^ 8 < 2 ^ 33 := by
    have h1 : c1 * 2 ^ 20 < 2 ^ 12 * 2 ^ 20 :=
      Nat.mul_lt_mul_of_lt_of_le hc1 (Nat.le_refl _) (by decide)
    have h2 : c2 * 2 ^ 8 < 2 ^ 12 * 2 ^ 8 :=
      Nat.mul_lt_mul_of_lt_of_le hc2 (Nat.le_refl _) (by decide)
    have h3 : (2:Nat) ^ 12 * 2 ^ 20 = 2 ^ 32 := by decide
    have h4 : (2:Nat) ^ 12 * 2 ^ 8 = 2 ^ 20 := by decide
    have h5 : (2:Nat) ^ 32 + 2 ^ 20 < 2 ^ 33 := by decide
    omega
  have V39 : run k t blkE1 39 = c1 * 2 ^ 20 + c2 * 2 ^ 8 :=
    blkE1_val39 k t c1 c2 h36 h38 hc1 hc2
  have V40 : run k (run k t blkE1) blkE2 40
      = kk1 * CL + (c1 * 2 ^ 20 + c2 * 2 ^ 8) :=
    blkE2_val40 k (run k t blkE1) kk1 (c1 * 2 ^ 20 + c2 * 2 ^ 8)
      (by rw [t1f 14 (by decide)]; exact h14) V39 hkk1 hpade
  have V41 : run k (run k t blkE1) blkE2 41
      = (2 ^ 50 - y * y) * 2 ^ 6 + y - 1 :=
    blkE2_val41 k (run k t blkE1) y
      (by rw [t1f 32 (by decide)]; exact h32) hyge hylt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [hsplit, run_untouched _ _ _ (by decide)]
         exact t1f _ (by decide))
      | (rw [hsplit]
         exact V40)
      | (rw [hsplit]
         exact V41)

/-- **Stage F1**: candidate `B`, the pair index, and the gates. -/
theorem blkF1_spec (c : Params) (k : Nat) (t : RegState)
    (kk1 sinh t0m n acc1 : Nat)
    (h14 : t 14 = kk1) (h42 : t 42 = sinh) (h18 : t 18 = t0m)
    (h8 : t 8 = n) (h4 : t 4 = acc1)
    (hkk1pos : 1 ≤ kk1) (hkk1 : kk1 ≤ KCAP) (hsinh : sinh ≤ 3 * 2 ^ 30 + 2)
    (ht0m : t0m ≤ 1) (hn17 : n < 2 ^ 17) (hacc : acc1 < M)
    (hsplit : c.split < 2 ^ 17) :
    run k t (blkF1 c) 0 = t 0 ∧ run k t (blkF1 c) 1 = t 1 ∧
    run k t (blkF1 c) 2 = t 2 ∧ run k t (blkF1 c) 3 = t 3 ∧
    run k t (blkF1 c) 4 = t 4 ∧ run k t (blkF1 c) 5 = t 5 ∧
    run k t (blkF1 c) 7 = t 7 ∧ run k t (blkF1 c) 13 = t 13 ∧
    run k t (blkF1 c) 14 = t 14 ∧ run k t (blkF1 c) 17 = t 17 ∧
    run k t (blkF1 c) 19 = t 19 ∧ run k t (blkF1 c) 40 = t 40 ∧
    run k t (blkF1 c) 43 = (kk1 + 1) * CL - sinh ∧
    run k t (blkF1 c) 45 = (t0m ||| (if n ≤ c.split then 1 else 0)) ∧
    run k t (blkF1 c) 46 = (if acc1 ≤ ACAP then 1 else 0) := by
  have hCL : (kk1 + 1) * CL < M := by
    have h1 : (kk1 + 1) * CL ≤ (KCAP + 1) * CL :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (KCAP + 1) * CL < M := by decide
    omega
  have e1 : (kk1 + 1) % M = kk1 + 1 := Nat.mod_eq_of_lt (by
    have : KCAP + 1 < M := by decide
    omega)
  have e2 : (kk1 + 1) * CL % M = (kk1 + 1) * CL := Nat.mod_eq_of_lt hCL
  have hsle : sinh ≤ (kk1 + 1) * CL := by
    have h1 : 2 * CL ≤ (kk1 + 1) * CL := Nat.mul_le_mul_right _ (by omega)
    have h2 : (3:Nat) * 2 ^ 30 + 2 ≤ 2 * CL := by decide
    omega
  have e3 := subExact ((kk1 + 1) * CL) sinh hsle hCL
  have hor : ∀ P : Prop, ∀ _ : Decidable P,
      (t0m ||| (if P then (1:Nat) else 0)) % M
        = t0m ||| (if P then 1 else 0) := by
    intro P inst
    exact or_mod _ _ ht0m (bitLe _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkF1, evalExpr, denoteOp, RegState.set,
      h14, h42, h18, h8, h4, e1, e2, e3, hor, lit1, litCL, litACAP,
      Nat.mod_eq_of_lt hacc,
      Nat.mod_eq_of_lt (show sinh < M from by
        have : (3:Nat) * 2 ^ 30 + 2 < M := by decide
        omega),
      Nat.mod_eq_of_lt (show c.split < M from by
        have : (2:Nat) ^ 17 < M := by decide
        omega)]

/-- **Stage F1, the pair index**: exact only in the exponent rounds. -/
theorem blkF1_spec44 (c : Params) (k : Nat) (t : RegState) (q : Nat)
    (h7 : t 7 = q) (hq : c.tdiv ≤ q) (hqM : q + 1 < M)
    (htd : c.tdiv < M) :
    run k t (blkF1 c) 44 = q - c.tdiv + 1 := by
  have e1 := subExact q c.tdiv hq (by omega)
  have e2 : (q - c.tdiv + 1) % M = q - c.tdiv + 1 :=
    Nat.mod_eq_of_lt (by omega)
  simp [run, blkF1, evalExpr, denoteOp, RegState.set, h7, e1, e2, lit1,
    Nat.mod_eq_of_lt htd]

/-- **Stage F2, always**: the comparison registers are bits. -/
theorem blkF2_bits (k : Nat) (t : RegState) :
    run k t blkF2 0 = t 0 ∧ run k t blkF2 1 = t 1 ∧
    run k t blkF2 2 = t 2 ∧ run k t blkF2 3 = t 3 ∧
    run k t blkF2 4 = t 4 ∧ run k t blkF2 5 = t 5 ∧
    run k t blkF2 13 = t 13 ∧ run k t blkF2 14 = t 14 ∧
    run k t blkF2 17 = t 17 ∧ run k t blkF2 19 = t 19 ∧
    run k t blkF2 45 = t 45 ∧ run k t blkF2 46 = t 46 ∧
    run k t blkF2 50 ≤ 1 ∧ run k t blkF2 51 ≤ 1 ∧ run k t blkF2 52 ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkF2, evalExpr, denoteOp, RegState.set] <;>
    split <;> simp

/-- **Stage F2, exponent rounds**: the two threshold comparisons and the
mantissa guard, exactly. -/
theorem blkF2_spec (k : Nat) (t : RegState) (acc1 b vA vB xlo1 : Nat)
    (h4 : t 4 = acc1) (h44 : t 44 = b) (h40 : t 40 = vA) (h43 : t 43 = vB)
    (h13 : t 13 = xlo1)
    (hacc : acc1 < M) (hb : b ≤ 48) (hvA : vA < 2 ^ 43) (hvB : vB < 2 ^ 43)
    (hx : xlo1 < M) :
    run k t blkF2 0 = t 0 ∧ run k t blkF2 1 = t 1 ∧
    run k t blkF2 2 = t 2 ∧ run k t blkF2 3 = t 3 ∧
    run k t blkF2 4 = t 4 ∧ run k t blkF2 5 = t 5 ∧
    run k t blkF2 13 = t 13 ∧ run k t blkF2 14 = t 14 ∧
    run k t blkF2 17 = t 17 ∧ run k t blkF2 19 = t 19 ∧
    run k t blkF2 45 = t 45 ∧ run k t blkF2 46 = t 46 ∧
    run k t blkF2 50 = (if acc1 * b % M ≤ vA * 2 ^ 12 + CC * b then 1 else 0) ∧
    run k t blkF2 51 = (if acc1 * b % M ≤ vB * 2 ^ 12 + CC * b then 1 else 0) ∧
    run k t blkF2 52 = (if xlo1 ≤ 2 ^ 64 - 2 ^ 50 then 1 else 0) := by
  have hshlA : vA <<< 12 = vA * 2 ^ 12 := Nat.shiftLeft_eq _ _
  have hshlB : vB <<< 12 = vB * 2 ^ 12 := Nat.shiftLeft_eq _ _
  have eA : vA * 2 ^ 12 % M = vA * 2 ^ 12 := Nat.mod_eq_of_lt (by
    have h1 : vA * 2 ^ 12 < 2 ^ 43 * 2 ^ 12 :=
      Nat.mul_lt_mul_of_lt_of_le hvA (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 43 * 2 ^ 12 < M := by decide
    omega)
  have eB' : vB * 2 ^ 12 % M = vB * 2 ^ 12 := Nat.mod_eq_of_lt (by
    have h1 : vB * 2 ^ 12 < 2 ^ 43 * 2 ^ 12 :=
      Nat.mul_lt_mul_of_lt_of_le hvB (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 43 * 2 ^ 12 < M := by decide
    omega)
  have eCC : CC * b % M = CC * b := Nat.mod_eq_of_lt (by
    have h1 : CC * b ≤ CC * 48 := Nat.mul_le_mul_left _ hb
    have h2 : CC * 48 < M := by decide
    omega)
  have eSA : (vA * 2 ^ 12 + CC * b) % M = vA * 2 ^ 12 + CC * b :=
    Nat.mod_eq_of_lt (by
      have h1 : vA * 2 ^ 12 < 2 ^ 43 * 2 ^ 12 :=
        Nat.mul_lt_mul_of_lt_of_le hvA (Nat.le_refl _) (by decide)
      have h2 : CC * b ≤ CC * 48 := Nat.mul_le_mul_left _ hb
      have h3 : (2:Nat) ^ 43 * 2 ^ 12 + CC * 48 < M := by decide
      omega)
  have eSB : (vB * 2 ^ 12 + CC * b) % M = vB * 2 ^ 12 + CC * b :=
    Nat.mod_eq_of_lt (by
      have h1 : vB * 2 ^ 12 < 2 ^ 43 * 2 ^ 12 :=
        Nat.mul_lt_mul_of_lt_of_le hvB (Nat.le_refl _) (by decide)
      have h2 : CC * b ≤ CC * 48 := Nat.mul_le_mul_left _ hb
      have h3 : (2:Nat) ^ 43 * 2 ^ 12 + CC * 48 < M := by decide
      omega)
  have hshlA' : vA <<< 12 = vA * 4096 := hshlA
  have hshlB' : vB <<< 12 = vB * 4096 := hshlB
  have eA' : vA * 4096 % M = vA * 4096 := eA
  have eB'' : vB * 4096 % M = vB * 4096 := eB'
  have eSA' : (vA * 4096 + CC * b) % M = vA * 4096 + CC * b := eSA
  have eSB' : (vB * 4096 + CC * b) % M = vB * 4096 + CC * b := eSB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkF2, evalExpr, denoteOp, RegState.set,
      h4, h44, h40, h43, h13, hshlA', hshlB', eA', eB'', eCC, eSA', eSB',
      lit12, litCC, litGuardn,
      Nat.mod_eq_of_lt hacc, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show b < M from by
        have : (49:Nat) < M := by decide
        omega)]

private theorem blkF3a_val53 (k : Nat) (t : RegState)
    (cap bal hA hB gd : Nat)
    (h46 : t 46 = cap) (h45 : t 45 = bal) (h50 : t 50 = hA)
    (h51 : t 51 = hB) (h52 : t 52 = gd)
    (hcap : cap ≤ 1) (hbal : bal ≤ 1) (hhA : hA ≤ 1) (hhB : hB ≤ 1)
    (hgd : gd ≤ 1) :
    run k t blkF3a 53 = cap * (bal * (hA ||| gd * hB)) := by
  have hgh : gd * hB ≤ 1 := by
    rcases (show gd = 0 ∨ gd = 1 by omega) with rfl | rfl <;> omega
  have hor : hA ||| gd * hB ≤ 1 := by
    rcases (show hA = 0 ∨ hA = 1 by omega) with rfl | rfl <;>
      rcases (show gd * hB = 0 ∨ gd * hB = 1 by omega) with h | h <;>
      rw [h] <;> decide
  have hbo : bal * (hA ||| gd * hB) ≤ 1 := by
    rcases (show bal = 0 ∨ bal = 1 by omega) with rfl | rfl <;> omega
  have hM2 : (2:Nat) ≤ M := by decide
  have e1 : gd * hB % M = gd * hB := Nat.mod_eq_of_lt (by omega)
  have e2 : (hA ||| gd * hB) % M = hA ||| gd * hB :=
    Nat.mod_eq_of_lt (by omega)
  have e3 : bal * (hA ||| gd * hB) % M = bal * (hA ||| gd * hB) :=
    Nat.mod_eq_of_lt (by omega)
  have e4 : cap * (bal * (hA ||| gd * hB)) % M
      = cap * (bal * (hA ||| gd * hB)) := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : cap * (bal * (hA ||| gd * hB)) ≤ 1 := by
      rcases (show cap = 0 ∨ cap = 1 by omega) with rfl | rfl <;> omega
    omega
  have hgoal : run k t blkF3a 53
      = (t 46 * (t 45 * (t 50 ||| t 52 * t 51 % M) % M)) % M := by
    simp [run, blkF3a, evalExpr, denoteOp, RegState.set]
  rw [hgoal, h46, h45, h50, h51, h52, e1, e2, e3, e4]

private theorem blkF3b_val5 (k : Nat) (t : RegState) (tqm pass0 hit : Nat)
    (h19 : t 19 = tqm) (h5 : t 5 = pass0) (h53 : t 53 = hit)
    (htqm : tqm ≤ 1) (hpass : pass0 ≤ 1) (hhit : hit ≤ 1) :
    run k t blkF3b 5 = (if tqm = 1 then pass0 ||| hit else pass0) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have hor : pass0 ||| hit ≤ 1 := by
    rcases (show pass0 = 0 ∨ pass0 = 1 by omega) with rfl | rfl <;>
      rcases (show hit = 0 ∨ hit = 1 by omega) with rfl | rfl <;> decide
  rcases (show tqm = 0 ∨ tqm = 1 by omega) with rfl | rfl <;>
    simp [run, blkF3b, sel, evalExpr, denoteOp, RegState.set,
      h19, h5, h53, Nat.mod_eq_of_lt (show pass0 < M by omega),
      Nat.mod_eq_of_lt (show pass0 ||| hit < M by omega)]

private theorem blkF3c_val0 (k : Nat) (t : RegState) (lastm good pass1 : Nat)
    (h17 : t 17 = lastm) (h0 : t 0 = good) (h5 : t 5 = pass1)
    (hlastm : lastm ≤ 1) (hgood : good ≤ 1) (hpass : pass1 ≤ 1) :
    run k t blkF3c 0 = (if lastm = 1 then good * pass1 else good) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have hgp : good * pass1 ≤ 1 := by
    rcases (show good = 0 ∨ good = 1 by omega) with rfl | rfl <;> omega
  rcases (show lastm = 0 ∨ lastm = 1 by omega) with rfl | rfl <;>
    simp [run, blkF3c, sel, evalExpr, denoteOp, RegState.set,
      h17, h0, h5, Nat.mod_eq_of_lt (show good < M by omega),
      Nat.mod_eq_of_lt (show good * pass1 < M by omega)]

/-- **Stage F3**: the hit, the pass accumulation, and the verdict. -/
theorem blkF3_spec (k : Nat) (t : RegState)
    (cap bal hA hB gd tqm lastm pass0 good : Nat)
    (h46 : t 46 = cap) (h45 : t 45 = bal) (h50 : t 50 = hA) (h51 : t 51 = hB)
    (h52 : t 52 = gd) (h19 : t 19 = tqm) (h17 : t 17 = lastm)
    (h5 : t 5 = pass0) (h0 : t 0 = good)
    (hcap : cap ≤ 1) (hbal : bal ≤ 1) (hhA : hA ≤ 1) (hhB : hB ≤ 1)
    (hgd : gd ≤ 1) (htqm : tqm ≤ 1) (hlastm : lastm ≤ 1)
    (hpass : pass0 ≤ 1) (hgood : good ≤ 1) :
    run k t blkF3 1 = t 1 ∧ run k t blkF3 2 = t 2 ∧
    run k t blkF3 3 = t 3 ∧ run k t blkF3 4 = t 4 ∧
    run k t blkF3 13 = t 13 ∧ run k t blkF3 14 = t 14 ∧
    run k t blkF3 5 =
      (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB)) else pass0) ∧
    run k t blkF3 0 =
      (if lastm = 1 then
        good * (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB))
                else pass0)
       else good) := by
  have hsplit : run k t blkF3
      = run k (run k (run k t blkF3a) blkF3b) blkF3c := by
    show run k t (blkF3a ++ blkF3b ++ blkF3c) = _
    rw [run_append, run_append]
  have haf : ∀ j, j ≠ 53 → run k t blkF3a j = t j := by
    intro j hj
    refine run_untouched _ _ _ ?_ _
    intro a' ha'
    simp only [blkF3a, List.mem_cons, List.not_mem_nil, or_false] at ha'
    subst ha'
    simp only []
    omega
  have hbf : ∀ j, j ≠ 53 → j ≠ 5 →
      run k (run k t blkF3a) blkF3b j = t j := by
    intro j hj53 hj5
    rw [run_untouched _ _ _ (by
      intro a' ha'
      simp only [blkF3b, List.mem_cons, List.not_mem_nil, or_false] at ha'
      subst ha'
      simp only []
      omega), haf j hj53]
  have hhit : run k t blkF3a 53 = cap * (bal * (hA ||| gd * hB)) :=
    blkF3a_val53 k t cap bal hA hB gd h46 h45 h50 h51 h52 hcap hbal hhA
      hhB hgd
  have hhitle : cap * (bal * (hA ||| gd * hB)) ≤ 1 := by
    have hgh : gd * hB ≤ 1 := by
      rcases (show gd = 0 ∨ gd = 1 by omega) with rfl | rfl <;> omega
    have hor : hA ||| gd * hB ≤ 1 := by
      rcases (show hA = 0 ∨ hA = 1 by omega) with rfl | rfl <;>
        rcases (show gd * hB = 0 ∨ gd * hB = 1 by omega) with h | h <;>
        rw [h] <;> decide
    have hbo : bal * (hA ||| gd * hB) ≤ 1 := by
      rcases (show bal = 0 ∨ bal = 1 by omega) with rfl | rfl <;> omega
    rcases (show cap = 0 ∨ cap = 1 by omega) with rfl | rfl <;> omega
  have V5 : run k (run k t blkF3a) blkF3b 5
      = (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB))
         else pass0) :=
    blkF3b_val5 k (run k t blkF3a) tqm pass0
      (cap * (bal * (hA ||| gd * hB)))
      (by rw [haf 19 (by decide)]; exact h19)
      (by rw [haf 5 (by decide)]; exact h5)
      hhit htqm hpass hhitle
  have hp1le : (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB))
      else pass0) ≤ 1 := by
    split
    · rcases (show pass0 = 0 ∨ pass0 = 1 by omega) with rfl | rfl <;>
        rcases (show cap * (bal * (hA ||| gd * hB)) = 0 ∨
          cap * (bal * (hA ||| gd * hB)) = 1 from by omega) with h | h <;>
        rw [h] <;> decide
    · exact hpass
  have V0 : run k (run k (run k t blkF3a) blkF3b) blkF3c 0
      = (if lastm = 1 then
          good * (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB))
                  else pass0)
         else good) :=
    blkF3c_val0 k (run k (run k t blkF3a) blkF3b) lastm good
      (if tqm = 1 then pass0 ||| cap * (bal * (hA ||| gd * hB)) else pass0)
      (by rw [hbf 17 (by decide) (by decide)]; exact h17)
      (by rw [hbf 0 (by decide) (by decide)]; exact h0)
      V5 hlastm hgood hp1le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [hsplit, run_untouched _ _ _ (by decide),
          run_untouched _ _ _ (by decide), run_untouched _ _ _ (by decide)])
      | (rw [hsplit, run_untouched _ _ _ (by decide)]
         exact V5)
      | (rw [hsplit]
         exact V0)

end LeanCompCert.Ports.GFoldCheck
