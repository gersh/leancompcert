import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Ports.TrialDivisionBlockSpec
import LeanCompCert.Verified.Straight

/-!
# The two-sided Helfgott (12.15) running check `log R + 1.312 ≤ G(R) ≤ log R + 1.354`

The consumer's certificate (`AnalyticNT.LargeSieve.g1215_cert`) is a running
fold over `n = 1 … 10⁷` that maintains **two** fixed-point sums

```text
S⁺(n) = ∑_{r ≤ n} μ²(r)·⌈2⁴⁴/φ(r)⌉      S⁻(n) = ∑_{r ≤ n} μ²(r)·⌊2⁴⁴/φ(r)⌋
```

and tests, per `n`, the two-sided pair

```text
n ≥ 120 → S⁺(n) ≤ 2⁴⁴·(logQL e n     + 1.354)
n ≥ 182 → 2⁴⁴·(logQU e (n+1) + 1.312) ≤ S⁻(n)          e = e(n) = 16 or 2
```

where `logQL e m` / `logQU e m` are the certificate's own exact-`ℚ` dyadic
Padé brackets for `log m`, evaluated at the mantissa of `m^e`.  At `e = 16`
and `m < 10⁵` that mantissa is a `266`-bit number, which is why the ordinary
kernel cannot reach the fold.

This module is the register-program replacement.  Its shape follows
`Ports/GFoldCheck.lean` — the flat loop index carries both the candidate and
the round, trial division peels the factorisation, and a truncated mantissa
tracks `m^b` without ever materialising it — with three differences forced by
the two-sidedness:

* **two** mantissa tracks are carried, one for `n` (feeding the upper check)
  and one for `n+1` (feeding the lower check);
* the mantissa is **40 bits**, not 65.  With `X < 2⁴⁰` and every candidate
  below `2²⁴`, the advance `X' = ⌊X·n/2^a⌋` stays inside a word, so there is
  no half-word split at all: one multiply, one variable shift.  The relative
  loss is `i/2³⁹ < 2⁻³⁵` after `i` steps, four orders of magnitude below the
  binding margin (`1.8·10⁻⁴` at `n = 231`);
* the lower check needs an *upper* bound for `log`, so its Padé is rounded
  **up** at an up-rounded mantissa, and it is guarded by `xL ≤ 2³⁹ − 32`,
  which forces the machine's mantissa exponent to be exactly
  `⌊log₂ (n+1)^b⌋`.  The upper check needs no guard: an undershooting
  exponent is paid for by `qPadeLo ≤ qL2LB`.

Both Padé evaluations are single divisions at a `17`-bit mantissa, which the
width budget `N·2²⁸ < 2⁶⁴` allows and the margin does not notice.

The design was replayed, bit for bit, against the exact-`ℚ` certificate over
the dense prefix `[1, 120000]` before anything here was proved
(`ext/analytic_nt/scripts/g1215_machine_replay.py` in the consumer
repository): zero soundness violations, zero guard failures, and the machine's
own slack is `3.209·10⁹` against the certificate's `3.216·10⁹` margin.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated: the program is well-formed; its
denotation is the flat fold of a transparent `Nat` round function
(`gProgram_denote`); the flat fold re-blocks per candidate; and acceptance
yields, for every candidate, the two exact accumulators and a passing
per-candidate check (`rows_of_denote`, in `Ports/G1215CheckSpec.lean`).

Left to the consumer (which has Mathlib): that the trial-division block
computes `Nat.totient`, and that the passing `u64` checks imply the
certificate's own `ℚ` comparisons against `logQL` / `logQU`.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 4000

/-! ## §1 Parameters -/

/-- One instance of the family: candidates `n ∈ [lo, lo + len)`, `tdiv + 1`
trial divisors `2 … tdiv + 2` per candidate, `bmax` exponent rounds per
candidate, the `e = 16` regime below `esplit`, and the two final sums. -/
structure Params where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial rounds; divisors are `2 … tdiv + 2`. -/
  tdiv : Nat
  /-- Exponent rounds per candidate (`b = 1 … bmax`). -/
  bmax : Nat
  /-- Candidates below this use `e = 16`; the others use `e = 2`. -/
  esplit : Nat
  /-- The final upper bound the running `S⁺` is re-tested against. -/
  finU : Nat
  /-- The final lower bound the running `S⁻` is re-tested against. -/
  finL : Nat
  deriving Repr, DecidableEq

/-- Rounds per candidate. -/
def Params.R (c : Params) : Nat := c.tdiv + c.bmax

/-- The sizing side conditions; all decidable, discharged by `decide` at each
concrete instance. -/
structure Params.Sane (c : Params) : Prop where
  /-- Candidates start at `1`. -/
  loPos : 1 ≤ c.lo
  /-- At least one candidate. -/
  lenPos : 0 < c.len
  /-- At least one trial round. -/
  tdivPos : 0 < c.tdiv
  /-- The exponent phase runs exactly the `16` rounds the check needs. -/
  bmaxEq : c.bmax = 16
  /-- Every candidate, and its successor, is below `2²⁴` (the mantissa
  advance's width budget). -/
  topSmall : c.lo + c.len ≤ 2 ^ 24
  /-- The flat index is a word. -/
  loopSmall : c.len * (c.tdiv + c.bmax) < 2 ^ 48
  /-- The per-round literals are words. -/
  roundsSmall : c.tdiv + c.bmax < 2 ^ 31
  /-- The `e = 16` threshold is a word. -/
  esplitLt : c.esplit < 2 ^ 24
  /-- The final bounds are words. -/
  finLt : c.finU < 2 ^ 56 ∧ c.finL < 2 ^ 56

/-- `⌊2³²·0.6931471803⌋`, the fixed-point image of the certificate's
`qL2LB = 6931471803/10¹⁰` **lower** bound for `log 2`. -/
def CL : Nat := 2977044470

/-- `⌈2³²·0.6931471808⌉`, the fixed-point image of the certificate's
`qL2UB = 6931471808/10¹⁰` **upper** bound for `log 2`. -/
def CU2 : Nat := 2977044473

/-- `⌊2⁴⁴·1.354⌋`, the certificate's upper additive constant. -/
def CU : Nat := 23819819904139

/-- `⌈2⁴⁴·1.312⌉`, the certificate's lower additive constant. -/
def CD : Nat := 23080948090274

/-- The kk-register clamp; the reference recurrence stays `≤ 24·16 = 384`, so
the clamp is inert on every real run and only serves the state invariant. -/
def KCAP : Nat := 1024

/-- The accumulator cap a passing check re-tests; keeps `acc · b` exact. -/
def ACAP : Nat := 2 ^ 56

/-- The mantissa's implicit leading bit: `X = 2³⁹ + x`. -/
def MB : Nat := 2 ^ 39

/-- The mantissa guard for the lower check: `2³⁹ − 32`.  An undershooting
exponent would force `x` above this, so the guard makes the exponent exact. -/
def MGUARD : Nat := 2 ^ 39 - 32

/-! ## §2 Register layout

Carried across rounds (the `Vals` below):

| reg | meaning | | reg | meaning |
| --- | --- | --- | --- | --- |
| `0` | good flag (output) | | `5` | `S⁻` accumulator |
| `1` | `m`, the cofactor | | `6` | candidate pass flag |
| `2` | `φ` product | | `7` | mantissa `xU = X − 2³⁹` for `n` |
| `3` | squarefree flag | | `8` | mantissa exponent `kU` |
| `4` | `S⁺` accumulator | | `9` | mantissa `xL` for `n+1` |
| | | | `10` | mantissa exponent `kL` |

Scratch, recomputed every round: `11`–`63`.  Temporaries of the expression
compiler start at `cursor = 72`. -/

def cursor : Nat := 72

/-- Branchless select for a `0/1` condition: `c * a + (c ^^^ 1) * b`. -/
def sel (c a b : Expr) : Expr :=
  .bin .add (.bin .mul c a) (.bin .mul (.bin .bxor c (.lit 1)) b)

/-- One `udiv` instruction's `Nat`-level effect. -/
def divStep (dest : Nat) (op : Op) (a b : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp op (s a) (s b)).getD 0)

/-- A `udiv` whose dividend is a literal. -/
def litDivStep (dest : Nat) (v : Nat) (b : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp .udiv (v % M) (s b)).getD 0)

/-- The two index-decoding divisions, whose divisor is a literal. -/
def idxDivStep (R : Nat) (k : Nat) (s : RegState) : RegState :=
  (s.set 11 ((denoteOp .udiv (k % M) (R % M)).getD 0)).set 12
    ((denoteOp .urem (k % M) (R % M)).getD 0)

/-- `n ≥ v`, as a `0/1` expression on register `13`. -/
def geBit (v : Nat) : Expr := .bin .ge (.reg 13) (.lit v)

/-- Bits `2¹ … 2⁸` of the `⌊log₂ n⌋` indicator sum. -/
def aLoExpr : Expr :=
  .bin .add
    (.bin .add (.bin .add (geBit 2) (geBit 4)) (.bin .add (geBit 8) (geBit 16)))
    (.bin .add (.bin .add (geBit 32) (geBit 64))
      (.bin .add (geBit 128) (geBit 256)))

/-- Bits `2⁹ … 2¹⁶`. -/
def aMdExpr : Expr :=
  .bin .add
    (.bin .add (.bin .add (geBit 512) (geBit 1024))
      (.bin .add (geBit 2048) (geBit 4096)))
    (.bin .add (.bin .add (geBit 8192) (geBit 16384))
      (.bin .add (geBit 32768) (geBit 65536)))

/-- Bits `2¹⁷ … 2²⁴`. -/
def aHiExpr : Expr :=
  .bin .add
    (.bin .add (.bin .add (geBit 131072) (geBit 262144))
      (.bin .add (geBit 524288) (geBit 1048576)))
    (.bin .add (.bin .add (geBit 2097152) (geBit 4194304))
      (.bin .add (geBit 8388608) (geBit 16777216)))

/-! ### Block A — decode, per-candidate reset, and the two exponents -/

/-- Decode, per-candidate reset and the round masks. -/
def blkA1 (c : Params) : List Assign :=
  [ ⟨13, .bin .add (.lit c.lo) (.reg 11)⟩
  , ⟨14, .bin .add (.reg 12) (.lit 2)⟩
  , ⟨15, .bin .eq (.reg 12) (.lit 0)⟩
  , ⟨16, .bin .eq (.reg 12) (.lit (c.R - 1))⟩
  , ⟨17, .bin .eq (.reg 12) (.lit c.tdiv)⟩
  , ⟨18, .bin .ge (.reg 12) (.lit c.tdiv)⟩
  , ⟨1, sel (.reg 15) (.reg 13) (.reg 1)⟩
  , ⟨2, sel (.reg 15) (.lit 1) (.reg 2)⟩
  , ⟨3, sel (.reg 15) (.lit 1) (.reg 3)⟩
  , ⟨6, sel (.reg 15) (.lit 0) (.reg 6)⟩ ]

/-- `⌊log₂ n⌋`, `2^{⌊log₂ n⌋}`, and the same pair for `n + 1` — the latter
by one comparison, since `⌊log₂ (n+1)⌋ − ⌊log₂ n⌋ ∈ {0, 1}`. -/
def blkA2 : List Assign :=
  [ ⟨27, aLoExpr⟩
  , ⟨27, .bin .add (.reg 27) aMdExpr⟩
  , ⟨27, .bin .add (.reg 27) aHiExpr⟩
  , ⟨28, .bin .shl (.lit 1) (.reg 27)⟩
  , ⟨29, .bin .add (.reg 27)
      (.bin .ge (.bin .add (.reg 13) (.lit 1)) (.bin .mul (.lit 2) (.reg 28)))⟩
  , ⟨30, .bin .shl (.lit 1) (.reg 29)⟩ ]

/-- Decode, reset, masks and the two exponents. -/
def blkA (c : Params) : List Assign := blkA1 c ++ blkA2

/-! ### Block B — one trial-division peel -/

/-- The divisibility flag and the squarefree update. -/
def blkB1 : List Assign :=
  [ ⟨21, .bin .eq (.bin .sub (.reg 1) (.bin .mul (.reg 19) (.reg 14))) (.lit 0)⟩
  , ⟨3, .bin .mul (.reg 3)
      (.bin .bxor
        (.bin .mul (.reg 21)
          (.bin .eq (.bin .sub (.reg 19) (.bin .mul (.reg 20) (.reg 14)))
            (.lit 0)))
        (.lit 1))⟩ ]

/-- The totient product and cofactor updates. -/
def blkB2 : List Assign :=
  [ ⟨2, sel (.reg 21) (.bin .mul (.reg 2) (.bin .add (.reg 12) (.lit 1)))
      (.reg 2)⟩
  , ⟨1, sel (.reg 21) (.reg 19) (.reg 1)⟩ ]

/-- The totient decode. -/
def blkB3 : List Assign :=
  [ ⟨22, sel (.bin .gt (.reg 1) (.lit 1))
      (.bin .mul (.reg 2) (.bin .sub (.reg 1) (.lit 1))) (.reg 2)⟩ ]

/-- One peel of `d`, the repeated-factor test, and the totient decode. -/
def blkB : List Assign := blkB1 ++ blkB2 ++ blkB3

/-! ### Block C — the two terms, the two accumulators, the two mantissae

Every literal above a few million is written on the **left** of its `add` /
`mul`.  This is not cosmetic: the kernel's `Nat.add`/`Nat.mul` recurse on
their *second* argument, so a stuck `symbolic ⊕ big-literal` term forces a
unary unfolding of the literal during defeq, while `big-literal ⊕ symbolic`
is stuck immediately and costs nothing.  `+` and `*` commute on `Nat` and
`denoteOp` reduces both modulo `M`, so every such placement is
value-preserving on the nose. -/

/-- The exactness bit of `2⁴⁴/φ`, and the two masked terms: the ceiling one
for `S⁺` and the floor one for `S⁻`.  One division serves both. -/
def blkC1a : List Assign :=
  [ ⟨24, .bin .eq (.bin .sub (.lit (2 ^ 44)) (.bin .mul (.reg 23) (.reg 22)))
      (.lit 0)⟩ ]

/-- The two masked terms: the ceiling one for `S⁺`, the floor one for `S⁻`. -/
def blkC1b : List Assign :=
  [ ⟨25, .bin .mul (.reg 3)
      (.bin .add (.reg 23) (.bin .bxor (.reg 24) (.lit 1)))⟩
  , ⟨26, .bin .mul (.reg 3) (.reg 23)⟩ ]

/-- The two accumulator steps, masked to the single round `q = tdiv`. -/
def blkC2 : List Assign :=
  [ ⟨4, .bin .add (.reg 4) (.bin .mul (.reg 17) (.reg 25))⟩
  , ⟨5, .bin .add (.reg 5) (.bin .mul (.reg 17) (.reg 26))⟩ ]

/-- Track `U`: the advance `⌊X·n/2^a⌋` and its renormalisation bit. -/
def blkC3a : List Assign :=
  [ ⟨31, .bin .lshr (.bin .mul (.bin .add (.lit (2 ^ 39)) (.reg 7)) (.reg 13))
      (.reg 27)⟩ ]

/-- Track `U`: the renormalisation bit. -/
def blkC3b : List Assign :=
  [ ⟨32, .bin .ge (.reg 31) (.lit (2 ^ 40))⟩ ]

/-- Track `U`: the renormalised advance and the round-`tdiv` init. -/
def blkC4 : List Assign :=
  [ ⟨33, .bin .sub (.bin .lshr (.reg 31) (.reg 32)) (.lit (2 ^ 39))⟩
  , ⟨34, .bin .shl (.bin .sub (.reg 13) (.reg 28))
      (.bin .sub (.lit 39) (.reg 27))⟩ ]

/-- Track `U`: the mantissa select. -/
def blkC5 : List Assign :=
  [ ⟨7, sel (.reg 18) (sel (.reg 17) (.reg 34) (.reg 33)) (.reg 7)⟩ ]

/-- Track `U`: the unclamped exponent. -/
def blkC6 : List Assign :=
  [ ⟨35, .bin .add (.bin .add (.reg 8) (.reg 27)) (.reg 32)⟩ ]

/-- Track `U`: the exponent select. -/
def blkC7 : List Assign :=
  [ ⟨8, sel (.reg 18)
      (sel (.reg 17) (.reg 27)
        (sel (.bin .le (.reg 35) (.lit KCAP)) (.reg 35) (.lit KCAP)))
      (.reg 8)⟩ ]

/-- Track `L`: the advance and its renormalisation bit. -/
def blkC8a : List Assign :=
  [ ⟨36, .bin .lshr
      (.bin .mul (.bin .add (.lit (2 ^ 39)) (.reg 9))
        (.bin .add (.reg 13) (.lit 1)))
      (.reg 29)⟩ ]

/-- Track `L`: the renormalisation bit. -/
def blkC8b : List Assign :=
  [ ⟨37, .bin .ge (.reg 36) (.lit (2 ^ 40))⟩ ]

/-- Track `L`: the renormalised advance and the round-`tdiv` init. -/
def blkC9 : List Assign :=
  [ ⟨38, .bin .sub (.bin .lshr (.reg 36) (.reg 37)) (.lit (2 ^ 39))⟩
  , ⟨39, .bin .shl (.bin .sub (.bin .add (.reg 13) (.lit 1)) (.reg 30))
      (.bin .sub (.lit 39) (.reg 29))⟩ ]

/-- Track `L`: the mantissa select. -/
def blkC10 : List Assign :=
  [ ⟨9, sel (.reg 18) (sel (.reg 17) (.reg 39) (.reg 38)) (.reg 9)⟩ ]

/-- Track `L`: the unclamped exponent. -/
def blkC11 : List Assign :=
  [ ⟨40, .bin .add (.bin .add (.reg 10) (.reg 29)) (.reg 37)⟩ ]

/-- Track `L`: the exponent select. -/
def blkC12 : List Assign :=
  [ ⟨10, sel (.reg 18)
      (sel (.reg 17) (.reg 29)
        (sel (.bin .le (.reg 40) (.lit KCAP)) (.reg 40) (.lit KCAP)))
      (.reg 10)⟩ ]

/-- The `17`-bit truncated mantissa of track `U` and the Padé-lower
operands.  `y = 2¹⁶ + u` with `u = ⌊x/2²³⌋`, and the numerator
`3(y² − 2³²) = 3(u² + 2¹⁷u)` is formed subtraction-free. -/
def blkC13a : List Assign :=
  [ ⟨41, .bin .lshr (.reg 7) (.lit 23)⟩ ]

/-- Track `U`: the `17`-bit mantissa itself. -/
def blkC13b : List Assign :=
  [ ⟨42, .bin .add (.lit (2 ^ 16)) (.reg 41)⟩ ]

/-- Track `U`: the Padé-lower numerator (already shifted) and denominator. -/
def blkC13c : List Assign :=
  [ ⟨43, .bin .shl
      (.bin .mul (.lit 3)
        (.bin .add (.bin .mul (.reg 41) (.reg 41)) (.bin .shl (.reg 41) (.lit 17))))
      (.lit 28)⟩
  , ⟨44, .bin .add (.lit (2 ^ 32))
      (.bin .add (.bin .mul (.reg 42) (.reg 42)) (.bin .shl (.reg 42) (.lit 18)))⟩ ]

/-- The up-rounded `17`-bit mantissa of track `L` and the Padé-upper
operands, with the dividend already carrying the `+ D − 1` of the ceiling. -/
def blkC14a : List Assign :=
  [ ⟨47, .bin .add (.lit 2) (.bin .lshr (.reg 9) (.lit 23))⟩ ]

/-- Track `L`: the Padé-upper denominator. -/
def blkC14b : List Assign :=
  [ ⟨49, .bin .add (.lit 393216) (.bin .mul (.lit 4) (.reg 47))⟩ ]

/-- Track `L`: the Padé-upper dividend, carrying the `+ D − 1` of the
ceiling. -/
def blkC14c : List Assign :=
  [ ⟨48, .bin .add
      (.bin .shl (.bin .mul (.reg 47) (.bin .add (.lit 393216) (.reg 47)))
        (.lit 16))
      (.bin .sub (.reg 49) (.lit 1))⟩ ]

/-- The terms, the accumulators, the two mantissae and the two Padé
operand pairs. -/
def blkC : List Assign :=
  blkC1a ++ blkC1b ++ blkC2 ++ blkC3a ++ blkC3b ++ blkC4 ++ blkC5 ++
  blkC6 ++ blkC7 ++ blkC8a ++ blkC8b ++ blkC9 ++ blkC10 ++ blkC11 ++
  blkC12 ++ blkC13a ++ blkC13b ++ blkC13c ++ blkC14a ++ blkC14b ++ blkC14c

/-! ### Block D — the lower candidate, from the first Padé division -/

/-- `padeLo = c·2⁴` and the lower log bound `vL = kU·CL + padeLo`. -/
def blkD1 : List Assign :=
  [ ⟨46, .bin .shl (.reg 45) (.lit 4)⟩ ]

/-- The lower log bound `vL = kU·CL + padeLo`. -/
def blkD2 : List Assign :=
  [ ⟨51, .bin .add (.bin .mul (.lit CL) (.reg 8)) (.reg 46)⟩ ]

/-- The lower candidate. -/
def blkD : List Assign := blkD1 ++ blkD2

/-! ### Block F — the two comparisons and the verdicts -/

/-- The upper log bound, the exponent `b`, the certificate's `e(n)`, and the
gates. -/
def blkF1a (c : Params) : List Assign :=
  [ ⟨52, .bin .add (.bin .mul (.lit CU2) (.reg 10)) (.reg 50)⟩
  , ⟨60, .bin .add (.bin .sub (.reg 12) (.lit c.tdiv)) (.lit 1)⟩
  , ⟨59, .bin .add (.lit 2)
      (.bin .mul (.lit 14) (.bin .lt (.reg 13) (.lit c.esplit)))⟩ ]

/-- The allowed-exponent bit, the accumulator cap, and the mantissa guard. -/
def blkF1b : List Assign :=
  [ ⟨53, .bin .eq (.reg 60) (.reg 59)⟩
  , ⟨54, .bin .mul (.bin .le (.reg 4) (.lit ACAP))
      (.bin .le (.reg 5) (.lit ACAP))⟩
  , ⟨55, .bin .le (.reg 9) (.lit MGUARD)⟩ ]

/-- The upper bound, `b`, `e(n)`, and the gates. -/
def blkF1 (c : Params) : List Assign := blkF1a c ++ blkF1b

/-- The two threshold comparisons, each behind its own range gate. -/
def blkF2 : List Assign :=
  [ ⟨56, .bin .bor (.bin .lt (.reg 13) (.lit 120))
      (.bin .le (.bin .mul (.reg 4) (.reg 60))
        (.bin .add (.bin .shl (.reg 51) (.lit 12)) (.bin .mul (.lit CU) (.reg 60))))⟩
  , ⟨57, .bin .bor (.bin .lt (.reg 13) (.lit 182))
      (.bin .mul (.reg 55)
        (.bin .le (.bin .add (.bin .shl (.reg 52) (.lit 12))
            (.bin .mul (.lit CD) (.reg 60)))
          (.bin .mul (.reg 5) (.reg 60))))⟩ ]

/-- The hit, the pass accumulation, and the verdict. -/
def blkF3a : List Assign :=
  [ ⟨58, .bin .mul (.reg 54) (.bin .mul (.reg 53) (.bin .mul (.reg 56) (.reg 57)))⟩ ]

/-- The pass accumulation. -/
def blkF3b : List Assign :=
  [ ⟨6, sel (.reg 18) (.bin .bor (.reg 6) (.reg 58)) (.reg 6)⟩ ]

/-- The verdict. -/
def blkF3c : List Assign :=
  [ ⟨0, sel (.reg 16) (.bin .mul (.reg 0) (.reg 6)) (.reg 0)⟩ ]

/-- The hit, the pass accumulation, and the verdict. -/
def blkF3 : List Assign := blkF3a ++ blkF3b ++ blkF3c

/-- The upper bound, the gates, the two comparisons and the verdicts. -/
def blkF (c : Params) : List Assign := blkF1 c ++ blkF2 ++ blkF3

/-! ### The epilogue — the two exact final sums -/

/-- The good flag is multiplied by the two final-sum tests. -/
def blkEp (c : Params) : List Assign :=
  [ ⟨0, .bin .mul (.reg 0)
      (.bin .mul (.bin .le (.reg 4) (.lit c.finU))
        (.bin .le (.lit c.finL) (.reg 5)))⟩ ]

/-- The loop body. -/
def gBody (c : Params) : List Instr :=
  [ .binop 11 .udiv .idx (.lit c.R)
  , .binop 12 .urem .idx (.lit c.R) ] ++
  block cursor (blkA c) ++
  [ .binop 19 .udiv (.reg 1) (.reg 14)
  , .binop 20 .udiv (.reg 19) (.reg 14) ] ++
  block cursor blkB ++
  [ .binop 23 .udiv (.lit (2 ^ 44)) (.reg 22) ] ++
  block cursor blkC ++
  [ .binop 45 .udiv (.reg 43) (.reg 44) ] ++
  block cursor blkD ++
  [ .binop 50 .udiv (.reg 48) (.reg 49) ] ++
  block cursor (blkF c)

/-- After decode, reset and the two `⌊log₂⌋`s: the peel divisions' divisor
lives in register `14`. -/
def st1 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (idxDivStep c.R k s) (blkA1 c)) blkA2

/-- After the two peel divisions. -/
def st2 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 20 .udiv 19 14 (divStep 19 .udiv 1 14 (st1 c k s))

/-- After the peel and the totient decode: the term division's divisor lives
in register `22`. -/
def st3 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (st2 c k s) blkB1) blkB2) blkB3

/-- After the term division. -/
def st4 (c : Params) (k : Nat) (s : RegState) : RegState :=
  litDivStep 23 (2 ^ 44) 22 (st3 c k s)

/-- After the accumulator steps, the two mantissa updates and the two Padé
operand pairs. -/
def st5 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (run k (run k (run k (run k (run k (run k (run k (run k
    (run k (run k (run k (run k (run k (run k (run k (run k (run k (run k
    (st4 c k s)
    blkC1a) blkC1b) blkC2) blkC3a) blkC3b) blkC4) blkC5) blkC6) blkC7)
    blkC8a) blkC8b) blkC9) blkC10) blkC11) blkC12)
    blkC13a) blkC13b) blkC13c) blkC14a) blkC14b) blkC14c

/-- After the Padé-lower division. -/
def st6 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 45 .udiv 43 44 (st5 c k s)

/-- After the lower candidate. -/
def st7 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (st6 c k s) blkD1) blkD2

/-- After the Padé-upper division. -/
def st8 (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 50 .udiv 48 49 (st7 c k s)

/-- The `Nat`-level meaning of one flat round. -/
def gRun (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (run k (run k (run k (run k (st8 c k s) (blkF1a c)) blkF1b) blkF2)
    blkF3a) (blkF3b ++ blkF3c)

/-- Initialisation: the good flag, cofactor and totient product start at `1`;
both accumulators start at `0`. -/
def gInit : List Instr :=
  [ .mov 0 (.lit 1), .mov 1 (.lit 1), .mov 2 (.lit 1) ]

/-- The whole program: the output is the good flag itself, after the two
final-sum tests. -/
def gProgram (c : Params) : Program := {
  regCount := 128
  loopCount := c.len * c.R
  init := gInit
  body := gBody c
  epilogue := block cursor (blkEp c)
  output := 0
}


/-! ## §3 Well-formedness

`Assign.WF` is a `Prop` with no `Decidable` instance, so the 60-odd
assignments are checked through a Boolean mirror instead of a 60-way `rcases`:
`regsBelowB` decides `Expr.RegsBelow`, and `assignOK` bundles the three
`Assign.WF` conjuncts with the temporary-budget bound.  Every block's check is
then one `decide` over a closed list — and it touches no numeral, because
`depth`, `NoDiv` and `RegsBelow` all ignore a `.lit`'s value. -/

/-- Boolean mirror of `Expr.RegsBelow`. -/
def regsBelowB (cur : Nat) : Expr → Bool
  | .reg i => decide (i < cur)
  | .lit _ => true
  | .idx => true
  | .bin _ l r => regsBelowB cur l && regsBelowB cur r

theorem regsBelowB_sound (cur : Nat) :
    ∀ e : Expr, regsBelowB cur e = true → e.RegsBelow cur := by
  intro e
  induction e with
  | reg i =>
      intro h
      have h' : decide (i < cur) = true := h
      show i < cur
      exact of_decide_eq_true h'
  | lit v => intro _; exact True.intro
  | «idx» => intro _; exact True.intro
  | bin op l r ihl ihr =>
      intro h
      rw [regsBelowB, Bool.and_eq_true] at h
      exact ⟨ihl h.1, ihr h.2⟩

/-- Everything one assignment owes: it writes below the cursor, reads below
the cursor, is division-free, and fits the temporary budget. -/
def assignOK (a : Assign) : Bool :=
  decide (a.dest < cursor) && regsBelowB cursor a.expr && NoDiv a.expr &&
    decide (cursor + depth a.expr ≤ 128)

theorem wf_of_assignOK {as : List Assign} (h : as.all assignOK = true) :
    (∀ a ∈ as, a.WF cursor) ∧ (∀ a ∈ as, cursor + depth a.expr ≤ 128) := by
  rw [List.all_eq_true] at h
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h1 := h a ha
    rw [assignOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
    exact ⟨of_decide_eq_true h1.1.1.1, regsBelowB_sound _ _ h1.1.1.2, h1.1.2⟩
  · have h1 := h a ha
    rw [assignOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
    exact of_decide_eq_true h1.2

theorem blkA_ok (c : Params) : (blkA c).all assignOK = true := rfl

theorem blkA_wf (c : Params) : ∀ a ∈ blkA c, a.WF cursor :=
  (wf_of_assignOK (blkA_ok c)).1

theorem blkA_room (c : Params) : ∀ a ∈ blkA c, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK (blkA_ok c)).2

theorem blkB_ok : blkB.all assignOK = true := rfl

theorem blkB_wf : ∀ a ∈ blkB, a.WF cursor := (wf_of_assignOK blkB_ok).1

theorem blkB_room : ∀ a ∈ blkB, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK blkB_ok).2

theorem blkC_ok : blkC.all assignOK = true := rfl

theorem blkC_wf : ∀ a ∈ blkC, a.WF cursor := (wf_of_assignOK blkC_ok).1

theorem blkC_room : ∀ a ∈ blkC, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK blkC_ok).2

theorem blkD_ok : blkD.all assignOK = true := rfl

theorem blkD_wf : ∀ a ∈ blkD, a.WF cursor := (wf_of_assignOK blkD_ok).1

theorem blkD_room : ∀ a ∈ blkD, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK blkD_ok).2

theorem blkF_ok (c : Params) : (blkF c).all assignOK = true := rfl

theorem blkF_wf (c : Params) : ∀ a ∈ blkF c, a.WF cursor :=
  (wf_of_assignOK (blkF_ok c)).1

theorem blkF_room (c : Params) : ∀ a ∈ blkF c, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK (blkF_ok c)).2

theorem blkEp_ok (c : Params) : (blkEp c).all assignOK = true := rfl

theorem blkEp_wf (c : Params) : ∀ a ∈ blkEp c, a.WF cursor :=
  (wf_of_assignOK (blkEp_ok c)).1

theorem blkEp_room (c : Params) : ∀ a ∈ blkEp c, cursor + depth a.expr ≤ 128 :=
  (wf_of_assignOK (blkEp_ok c)).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem gBody_wf (c : Params) : ∀ i ∈ gBody c, i.WF 128 := by
  intro i hi
  have hcur : cursor ≤ 128 := by simp [cursor]
  have hi' : i ∈
      ([ Instr.binop 11 .udiv .idx (.lit c.R)
       , Instr.binop 12 .urem .idx (.lit c.R) ] ++
        (block cursor (blkA c) ++
          ([ Instr.binop 19 .udiv (.reg 1) (.reg 14)
           , Instr.binop 20 .udiv (.reg 19) (.reg 14) ] ++
            (block cursor blkB ++
              ([Instr.binop 23 .udiv (.lit (2 ^ 44)) (.reg 22)] ++
                (block cursor blkC ++
                  ([Instr.binop 45 .udiv (.reg 43) (.reg 44)] ++
                    (block cursor blkD ++
                      ([Instr.binop 50 .udiv (.reg 48) (.reg 49)] ++
                        block cursor (blkF c)))))))))) := hi
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
  · exact block_wf cursor 128 (blkF c) (blkF_wf c) hcur (blkF_room c) i h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem gProgram_wf (c : Params) : (gProgram c).WF := by
  refine ⟨by simp [gProgram], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ gInit := hi
    simp only [gInit, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl <;> exact ⟨by simp [gProgram], trivial⟩
  · exact gBody_wf c
  · intro i hi
    exact block_wf cursor 128 (blkEp c) (blkEp_wf c) (by simp [cursor])
      (blkEp_room c) i hi

/-! ## §4 The `Nat`-level round -/

/-- `if v ≤ n then 1 else 0`. -/
def ind (v n : Nat) : Nat := if v ≤ n then 1 else 0

/-- `⌊log₂ n⌋` for `1 ≤ n < 2²⁵`, as the machine computes it: twenty-four
threshold indicators, in the same association as `aLoExpr`/`aMdExpr`/
`aHiExpr`. -/
def aOf (n : Nat) : Nat :=
  ((ind 2 n + ind 4 n + (ind 8 n + ind 16 n) +
      (ind 32 n + ind 64 n + (ind 128 n + ind 256 n))) +
    (ind 512 n + ind 1024 n + (ind 2048 n + ind 4096 n) +
      (ind 8192 n + ind 16384 n + (ind 32768 n + ind 65536 n)))) +
  (ind 131072 n + ind 262144 n + (ind 524288 n + ind 1048576 n) +
    (ind 2097152 n + ind 4194304 n + (ind 8388608 n + ind 16777216 n)))

theorem aOf_eq_log2 {n : Nat} (h1 : 1 ≤ n) (h25 : n < 2 ^ 25) :
    aOf n = Nat.log2 n := by
  have hn0 : n ≠ 0 := by omega
  have hL25 : Nat.log2 n < 25 := (Nat.log2_lt hn0).mpr h25
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
    g 65536 16 (by decide), g 131072 17 (by decide), g 262144 18 (by decide),
    g 524288 19 (by decide), g 1048576 20 (by decide),
    g 2097152 21 (by decide), g 4194304 22 (by decide),
    g 8388608 23 (by decide), g 16777216 24 (by decide)]
  rcases (show Nat.log2 n = 0 ∨ Nat.log2 n = 1 ∨ Nat.log2 n = 2 ∨
      Nat.log2 n = 3 ∨ Nat.log2 n = 4 ∨ Nat.log2 n = 5 ∨ Nat.log2 n = 6 ∨
      Nat.log2 n = 7 ∨ Nat.log2 n = 8 ∨ Nat.log2 n = 9 ∨ Nat.log2 n = 10 ∨
      Nat.log2 n = 11 ∨ Nat.log2 n = 12 ∨ Nat.log2 n = 13 ∨
      Nat.log2 n = 14 ∨ Nat.log2 n = 15 ∨ Nat.log2 n = 16 ∨
      Nat.log2 n = 17 ∨ Nat.log2 n = 18 ∨ Nat.log2 n = 19 ∨
      Nat.log2 n = 20 ∨ Nat.log2 n = 21 ∨ Nat.log2 n = 22 ∨
      Nat.log2 n = 23 ∨ Nat.log2 n = 24 from by omega) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide

theorem aOf_bounds {n : Nat} (h1 : 1 ≤ n) (h25 : n < 2 ^ 25) :
    aOf n ≤ 24 ∧ 2 ^ aOf n ≤ n ∧ n < 2 ^ (aOf n + 1) := by
  have hn0 : n ≠ 0 := by omega
  rw [aOf_eq_log2 h1 h25]
  have hlt := (Nat.log2_lt hn0).mpr h25
  exact ⟨by omega, (Nat.le_log2 hn0).mp (Nat.le_refl _),
    (Nat.log2_lt hn0).mp (Nat.lt_succ_self _)⟩

/-- The mantissa advance: `⌊X·n / 2^a⌋` from `x = X − 2³⁹`.  `X < 2⁴⁰` and
`n < 2²⁴` keep the product inside a word, so there is no half-word split. -/
def advX (n a x : Nat) : Nat := (MB + x) * n / 2 ^ a

/-- The Padé **lower** value at the down-rounded `17`-bit mantissa
`y = 2¹⁶ + ⌊x/2²³⌋`, at scale `2³²`, rounded down. -/
def padeLoOf (x : Nat) : Nat :=
  let u := x / 2 ^ 23
  let y := 2 ^ 16 + u
  3 * (u * u + u * 2 ^ 17) * 2 ^ 28 / (2 ^ 32 + (y * y + y * 2 ^ 18)) * 2 ^ 4

/-- The Padé **upper** value at the up-rounded `17`-bit mantissa
`y = 2¹⁶ + ⌊x/2²³⌋ + 2`, at scale `2³²`, rounded up. -/
def padeUpOf (x : Nat) : Nat :=
  let u := x / 2 ^ 23 + 2
  let den := 393216 + 4 * u
  (u * (393216 + u) * 2 ^ 16 + (den - 1)) / den

/-- The certificate's exponent regime, as the machine forms it. -/
def eOf (c : Params) (n : Nat) : Nat :=
  2 + 14 * (if n < c.esplit then 1 else 0)

/-- One per-candidate two-sided check, in exact `Nat` arithmetic (the `% M` on
`acc · b` is the machine's own, and is removed downstream by the cap). -/
def hitOf (c : Params) (n b accU accL xU kU xL kL : Nat) : Nat :=
  let vL := CL * kU + padeLoOf xU
  let vU := CU2 * kL + padeUpOf xL
  let ballow := if b = eOf c n then 1 else 0
  let capOK := (if accU ≤ ACAP then 1 else 0) * (if accL ≤ ACAP then 1 else 0)
  let hU := (if n < 120 then 1 else 0) |||
    (if accU * b % M ≤ vL * 2 ^ 12 + CU * b then 1 else 0)
  let gd := if xL ≤ MGUARD then 1 else 0
  let hL := (if n < 182 then 1 else 0) |||
    gd * (if vU * 2 ^ 12 + CD * b ≤ accL * b % M then 1 else 0)
  capOK * (ballow * (hU * hL))

/-- The eleven carried registers. -/
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
  accU : Nat
  /-- Register `5`. -/
  accL : Nat
  /-- Register `6`. -/
  pass : Nat
  /-- Register `7`. -/
  xU : Nat
  /-- Register `8`. -/
  kU : Nat
  /-- Register `9`. -/
  xL : Nat
  /-- Register `10`. -/
  kL : Nat
  deriving DecidableEq, Repr

/-- Read the carried registers out of a machine state. -/
def valsOf (s : RegState) : Vals :=
  ⟨s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7, s 8, s 9, s 10⟩

/-- The `Nat`-level round: what one flat iteration does to the carried
registers. -/
def gRound (c : Params) (k : Nat) (v : Vals) : Vals :=
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
  let tq := 2 ^ 44 / phiF
  let tU := sq1 * (tq + (if 2 ^ 44 % phiF = 0 then 0 else 1))
  let tL := sq1 * tq
  let accU1 := (v.accU + (if q = c.tdiv then tU else 0)) % M
  let accL1 := (v.accL + (if q = c.tdiv then tL else 0)) % M
  let aU := aOf n
  let aL := aOf (n + 1)
  let x2U := advX n aU v.xU
  let gU := if 2 ^ 40 ≤ x2U then 1 else 0
  let xUA := x2U / 2 ^ gU - MB
  let xUI := (n - 2 ^ aU) * 2 ^ (39 - aU)
  let xU1 := if q < c.tdiv then v.xU else if q = c.tdiv then xUI else xUA
  let kUN := v.kU + aU + gU
  let kU1 := if q < c.tdiv then v.kU
             else if q = c.tdiv then aU
             else if kUN ≤ KCAP then kUN else KCAP
  let x2L := advX (n + 1) aL v.xL
  let gL := if 2 ^ 40 ≤ x2L then 1 else 0
  let xLA := x2L / 2 ^ gL - MB
  let xLI := (n + 1 - 2 ^ aL) * 2 ^ (39 - aL)
  let xL1 := if q < c.tdiv then v.xL else if q = c.tdiv then xLI else xLA
  let kLN := v.kL + aL + gL
  let kL1 := if q < c.tdiv then v.kL
             else if q = c.tdiv then aL
             else if kLN ≤ KCAP then kLN else KCAP
  let pass1 := if q < c.tdiv then pass0
               else pass0 ||| hitOf c n (q - c.tdiv + 1) accU1 accL1 xU1 kU1 xL1 kL1
  let good1 := if q = c.R - 1 then v.good * pass1 else v.good
  ⟨good1, m1, phi1, sq1, accU1, accL1, pass1, xU1, kU1, xL1, kL1⟩

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
  passLe : s 6 ≤ 1
  /-- The good flag is a bit. -/
  goodLe : s 0 ≤ 1
  /-- Track `U`'s mantissa stays in its band. -/
  xULt : s 7 < MB
  /-- Track `U`'s exponent is clamped. -/
  kULe : s 8 ≤ KCAP
  /-- Track `L`'s mantissa stays in its band. -/
  xLLt : s 9 < MB
  /-- Track `L`'s exponent is clamped. -/
  kLLe : s 10 ≤ KCAP

end LeanCompCert.Ports.G1215Check
