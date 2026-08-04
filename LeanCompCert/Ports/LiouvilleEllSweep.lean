import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold

/-!
# The Liouville little-sum sweep in the scalar fragment

Ramaré, Acta Arith. 165 (2014), Lemma 2.4(3) needs `|ℓ(N)|·log (N+1) ≤ 99/1000`
on the finite head `N ∈ [8918, 4·10⁶)`, where `ℓ(N) = ∑_{n≤N} λ(n)/n`.  The Lean
certificate turns that into an integer sweep at scale `P = 2⁵⁰`,

```text
  ellLval N = ∑_{n=1}^{N} λ(n)·⌊P/n⌋ ,      |ellLval N| + N ≤ T_j
```

with `T_j` read from a 65-entry band table.  This module is the register-program
replacement for the `native_decide` that discharged it.

## Why the band table does not have to be data

The scalar `Reflect.Program` has no array, and the atom's own statement is a
Boolean about that table, so the table cannot simply be dropped.  It does not
have to be carried either: the 65 rows are the orbit of a two-line integer
recurrence.  With `B` the band's first candidate,

```text
  w   = min (B/10 + 1) (NHI − B)              (the next band starts at B + w)
  L'  = L + ⌈2²⁰·w / B⌉                       (the chain `log (B+w) ≤ log B + w/B`)
```

reproduces every `(w_j, L_j)` of `ellBands` exactly from the seed
`(B, L) = (9442, 9603098)`, and `T_j = ⌊99·2⁷⁰/(1000·L_j)⌋`.  So the machine
carries the band's own `L_j` in a register, one division per candidate, and the
bridge to the table is a 65-step kernel check rather than an inequality.

⚠ An earlier design tested the *tableless* per-candidate bound
`(|ellLval N|+N)·L(N+1)·1000 ≤ 99·2^(50+SC)` with `L(n+1) = L(n) + ⌈2^SC/n⌉` and
proposed to reach the band thresholds through `L(N+1)·2²⁰ ≤ L_j·2^SC`.  That
inequality points the wrong way: it says the per-candidate bound is *sharper*
than the band's, so the tableless threshold `⌊99·2^(50+SC)/(1000·L(N+1))⌋`
**exceeds** `T_j` — at all 3 991 082 candidates, by up to 2.6 %.  It yields
`(B) ⟹ (A)`, not `(A) ⟹ (B)`.  See `bench/ref_liouville.c`.

## What the machine does, per candidate `n`

`λ` is completely multiplicative, so the machine needs `Ω(n) mod 2`, i.e. prime
*multiplicities*.  It strips them by a two-phase flat-index trial division:

```text
  phase B  rounds q < ex·dsm      d = q/ex + 2   -- each d ∈ [2, dsm+1] held
                                                 -- `ex` CONSECUTIVE rounds
  phase A  rounds q ≥ ex·dsm      d = (q − ex·dsm) + dsm + 2   -- one pass
```

The consecutive hold is load-bearing: cycling the divisors instead breaks the
invariant that a composite `d` never divides the residual (at `n = 8` the
residual `4` is then divided by `d = 4` and counted once, giving parity `0`
where `Ω(8) = 3`).  A residual `≠ 1` at the end contributes one more factor.

The signed partial sum is carried biased at `2⁶²`; `|ellLval N| + N` is tested
against the band in the shifted form

```text
  ⌈A/2²⁰⌉ · L_j · 1000 ≤ 99·2⁵⁰ ,
```

sound because `⌈x/2²⁰⌉ ≥ x/2²⁰`, and inside a word because `⌈A/2²⁰⌉` and `L_j`
are each clamped below `2²⁵`.  Every clamp is paired with a gate, so a run that
returns `0` proves the clamps were inactive and the model below is exact.

## What is proved here

```text
  lProgram_denote     : lOK c = true → (lProgram c).denote = some (value c)
  value_eq_zero_rows  : lOK c = true → value c = 0 → SweepRows c
```

`SweepRows` is a statement about `Nat`-valued per-candidate sequences: the
accumulator recurrence, the band ladder, and the two gates.  Identifying the
strip's parity with `Ω(n) mod 2`, and the ladder with `ellBands`, is the
consumer's obligation and lives where Mathlib lives.
-/

namespace LeanCompCert.Ports.LiouvilleEllSweep

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## Design constants (fixed by the margin audit; not sizing) -/

/-- Fixed-point scale of the little sum. -/
def plScale : Nat := 1125899906842624
/-- Bias of the signed accumulator. -/
def biasV : Nat := 4611686018427387904
/-- Unconditional clamp on the accumulator; wider than the gate. -/
def accLo : Nat := 4539628424389459968
def accHi : Nat := 4683743612465315840
/-- The accumulator gate; `|ellLval| ≤ 2⁵⁰` in fact, so this is loose. -/
def gateLo : Nat := 4575657221408423936
def gateHi : Nat := 4647714815446351872
/-- The shift the band product is tested under. -/
def shBits : Nat := 20
def shMask : Nat := 1048575
/-- Clamps on the two factors of the band product. -/
def ashCap : Nat := 33554432
def lbCap : Nat := 33554432
/-- `99·2⁵⁰`: the shifted right-hand side. -/
def rhsCap : Nat := 111464090777419776
/-- Scale of the band log numerators. -/
def lgScale : Nat := 1048576

/-! ## The configuration -/

/-- The sizing.  Every field appears as a literal in the emitted C, and every
field is re-tested by `lOK`. -/
structure Cfg where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Consecutive rounds each small divisor is held. -/
  ex : Nat
  /-- Small divisors are `2 … dsm + 1`. -/
  dsm : Nat
  /-- All divisors are `2 … dbg + 1`. -/
  dbg : Nat
  /-- Rounds per candidate; `ex·dsm + (dbg − dsm)`. -/
  rounds : Nat
  /-- First candidate the band test applies to. -/
  nlo : Nat
  /-- One past the last candidate the bands cover. -/
  nhi : Nat
  /-- First candidate of the second band. -/
  e0 : Nat
  /-- The first band's log numerator, at scale `2²⁰`. -/
  lb0 : Nat
  deriving Repr

/-- The arithmetic side conditions of the denotation, as one decidable test. -/
def lOK (c : Cfg) : Bool :=
  decide (0 < c.lo) && decide (0 < c.ex) && decide (c.dsm < c.dbg) &&
  decide (c.rounds = c.ex * c.dsm + (c.dbg - c.dsm)) &&
  decide (0 < c.rounds) &&
  decide (c.lo + c.len ≤ c.nhi) && decide (c.nhi ≤ 2 ^ 32) &&
  decide (c.len * c.rounds ≤ M) && decide (c.dbg + 2 ≤ 2 ^ 32) &&
  decide (0 < c.e0) && decide (c.e0 ≤ c.nhi) && decide (c.lb0 ≤ lbCap)

/-- The side conditions of the denotation, unpacked. -/
theorem lFacts_of_ok {c : Cfg} (h : lOK c = true) :
    0 < c.lo ∧ 0 < c.ex ∧ c.dsm < c.dbg ∧
      c.rounds = c.ex * c.dsm + (c.dbg - c.dsm) ∧ 0 < c.rounds ∧
      c.lo + c.len ≤ c.nhi ∧ c.nhi ≤ 2 ^ 32 ∧ c.len * c.rounds ≤ M ∧
      c.dbg + 2 ≤ 2 ^ 32 ∧ 0 < c.e0 ∧ c.e0 ≤ c.nhi ∧ c.lb0 ≤ lbCap := by
  rw [lOK] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## The reference computation, in ordinary arithmetic -/

/-- The divisor tried at round `q`: two phases on the flat round index. -/
def divOfR (EX EDS DS2 q : Nat) : Nat :=
  if q < EDS then 2 + q / EX else DS2 + (q - EDS)

def divOf (c : Cfg) (q : Nat) : Nat :=
  divOfR c.ex (c.ex * c.dsm) (c.dsm + 2) q

/-- Exclusive-or of two bits, in the form the machine's `.ne` produces. -/
def xorBit (a b : Nat) : Nat := if a = b then 0 else 1

/-- One trial-division round on `(residual, parity)`. -/
def stripStep (d : Nat) (rp : Nat × Nat) : Nat × Nat :=
  let r := rp.1
  let qd := r / d
  if r - qd * d = 0 then (qd, xorBit rp.2 1) else (r, xorBit rp.2 0)

/-- The strip state of candidate `n` after `j` rounds. -/
def stripPre (c : Cfg) (n : Nat) : Nat → Nat × Nat
  | 0 => (n, 0)
  | j + 1 => stripStep (divOf c j) (stripPre c n j)

/-- The completely-multiplicative sign the machine reads off the strip:
`0` for `λ = +1`, `1` for `λ = −1`. -/
def signOf (rp : Nat × Nat) : Nat := xorBit rp.2 (xorBit rp.1 1)

/-- One accumulator step at scale `PL`, biased at `2⁶²`. -/
def accApplyR (PL a sgn n : Nat) : Nat :=
  a + (1 - sgn) * (PL / n) - sgn * (PL / n)

def accApply (a sgn n : Nat) : Nat := accApplyR plScale a sgn n

/-- The width clamp the accumulator is stored under. -/
def accClamp (x : Nat) : Nat := min (max x accLo) accHi

/-- `|x − 2⁶²|`, as the machine computes it. -/
def absBias (x : Nat) : Nat := max x biasV - min x biasV

/-- The shifted left-hand side of the band test. -/
def ashOf (bigA : Nat) : Nat := (shMask + bigA) / 2 ^ shBits

/-- The band ladder's width step. -/
def bandWR (NHI e : Nat) : Nat := min (1 + e / 10) (NHI - e)

def bandW (c : Cfg) (e : Nat) : Nat := bandWR c.nhi e

/-- The band ladder's log step, `⌈2²⁰·w/e⌉`. -/
def bandIncR (NHI LG e : Nat) : Nat := (LG * bandWR NHI e + e - 1) / e

def bandInc (c : Cfg) (e : Nat) : Nat := bandIncR c.nhi lgScale e

/-! ## The abstract state and the abstract step -/

/-- What survives one round of the loop. -/
structure Abs where
  /-- `1` once some candidate failed a gate. -/
  bad : Nat
  /-- The biased accumulator. -/
  acc : Nat
  /-- The current candidate's strip residual. -/
  res : Nat
  /-- The current candidate's strip parity. -/
  par : Nat
  /-- The current band's log numerator, at scale `2²⁰`. -/
  lb : Nat
  /-- The next band's first candidate. -/
  ee : Nat
  deriving Repr, DecidableEq

theorem Abs.eq_of {x y : Abs} (h0 : x.bad = y.bad) (h1 : x.acc = y.acc)
    (h2 : x.res = y.res) (h3 : x.par = y.par) (h4 : x.lb = y.lb)
    (h5 : x.ee = y.ee) : x = y := by
  cases x; cases y; simp_all

def obs (s : RegState) : Abs := ⟨s 0, s 1, s 2, s 3, s 4, s 5⟩

/-- How the machine combines the row's six bits. -/
def rowVerdict (gaccLo gaccHi glb post gash gok : Nat) : Nat :=
  gaccLo * gaccHi * glb * (1 - post * (1 - gash * gok))

/-- The band log the row is tested against: the ladder value after the
advance, if this candidate opens a band. -/
def lbRawOf (c : Cfg) (n lb ee : Nat) : Nat :=
  lb + (if n = ee then 1 else 0) * bandInc c ee

/-- The row's verdict at candidate `n` with incoming accumulator `a`, sign
`sgn`, band log `lb` and band cursor `ee`.  `1` means the row passed. -/
def rowOKOf (c : Cfg) (a sgn n lb ee : Nat) : Nat :=
  let accS := accApply a sgn n
  let ash := ashOf (absBias (accClamp accS) + n)
  let lbRaw := lbRawOf c n lb ee
  rowVerdict (if gateLo ≤ accS then 1 else 0) (if accS ≤ gateHi then 1 else 0)
    (if lbRaw ≤ lbCap then 1 else 0) (if c.nlo ≤ n then 1 else 0)
    (if ash ≤ ashCap then 1 else 0)
    (if 1000 * (min ash ashCap * min lbRaw lbCap) ≤ rhsCap then 1 else 0)

/-- The abstract step at flat index `idx`.  Written exactly as the machine
computes it: every quantity the row test reads is the *gated* one, so no
case analysis is needed to line the two up. -/
def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let q := idx % c.rounds
  let n := c.lo + idx / c.rounds
  let rp' := stripStep (divOf c q) (if q = 0 then (n, 0) else (a.res, a.par))
  let sgn := signOf rp'
  let lastB := if q = c.rounds - 1 then 1 else 0
  let accS := if lastB = 1 then accApply a.acc sgn n else a.acc
  let ash := ashOf (absBias (accClamp accS) + n)
  let adv := lastB * (if n = a.ee then 1 else 0)
  let lbRaw := a.lb + adv * bandInc c a.ee
  ⟨a.bad ||| lastB * (1 - rowVerdict (if gateLo ≤ accS then 1 else 0)
      (if accS ≤ gateHi then 1 else 0) (if lbRaw ≤ lbCap then 1 else 0)
      (if c.nlo ≤ n then 1 else 0) (if ash ≤ ashCap then 1 else 0)
      (if 1000 * (min ash ashCap * min lbRaw lbCap) ≤ rhsCap then 1 else 0)),
    accClamp accS, rp'.1, rp'.2, min lbRaw lbCap, a.ee + adv * bandW c a.ee⟩

/-! ## The register program

| reg | meaning                                     |
| --- | ------------------------------------------- |
| `0` | violation flag (the output)                 |
| `1` | biased accumulator                          |
| `2` | strip residual                              |
| `3` | strip parity                                |
| `4` | band log numerator, scale `2²⁰`             |
| `5` | next band's first candidate                 |
| `6–10` | index decode: `i, q, n, first, last`     |
| `11–15` | divisor decode                          |
| `16–24` | strip round and sign                    |
| `25–28` | accumulator                             |
| `29–35` | `|S|`, `A`, `⌈A/2²⁰⌉`                   |
| `36–45` | band ladder                             |
| `46–51`, `59` | the row test                      |
| `52–58` | scratch, rewritten every round          |
-/

def regCount : Nat := 60

/-- Index decode. -/
def blkAP (R RM1 LO : Nat) : List Instr :=
  [ .binop 6 .udiv .idx (.lit R)
  , .binop 52 .mul (.lit R) (.reg 6)
  , .binop 7 .sub .idx (.reg 52)
  , .binop 8 .add (.lit LO) (.reg 6)
  , .binop 9 .eq (.reg 7) (.lit 0)
  , .binop 10 .eq (.reg 7) (.lit RM1) ]

def blkA (c : Cfg) : List Instr := blkAP c.rounds (c.rounds - 1) c.lo

/-- Divisor decode: two phases on the flat round index. -/
def blkBP (EX EDS DS2 : Nat) : List Instr :=
  [ .binop 11 .udiv (.reg 7) (.lit EX)
  , .binop 12 .add (.lit 2) (.reg 11)
  , .binop 14 .lt (.reg 7) (.lit EDS)
  , .binop 52 .mul (.lit EDS) (.reg 14)
  , .binop 53 .sub (.lit 1) (.reg 14)
  , .binop 54 .mul (.reg 53) (.reg 7)
  , .binop 58 .add (.reg 52) (.reg 54)
  , .binop 13 .sub (.reg 58) (.lit EDS)
  , .binop 13 .add (.lit DS2) (.reg 13)
  , .binop 52 .mul (.reg 14) (.reg 12)
  , .binop 54 .mul (.reg 53) (.reg 13)
  , .binop 15 .add (.reg 52) (.reg 54) ]

def blkB (c : Cfg) : List Instr := blkBP c.ex (c.ex * c.dsm) (c.dsm + 2)

/-- Select the round's incoming `(residual, parity)`. -/
def blkC1 : List Instr :=
  [ .binop 52 .mul (.reg 9) (.reg 8)
  , .binop 53 .sub (.lit 1) (.reg 9)
  , .binop 54 .mul (.reg 53) (.reg 2)
  , .binop 16 .add (.reg 52) (.reg 54)
  , .binop 17 .mul (.reg 53) (.reg 3) ]

/-- One trial-division round, and the completely-multiplicative sign. -/
def blkC2 : List Instr :=
  [ .binop 18 .udiv (.reg 16) (.reg 15)
  , .binop 52 .mul (.reg 18) (.reg 15)
  , .binop 19 .sub (.reg 16) (.reg 52)
  , .binop 20 .eq (.reg 19) (.lit 0)
  , .binop 52 .mul (.reg 20) (.reg 18)
  , .binop 53 .sub (.lit 1) (.reg 20)
  , .binop 54 .mul (.reg 53) (.reg 16)
  , .binop 21 .add (.reg 52) (.reg 54)
  , .binop 22 .ne (.reg 17) (.reg 20)
  , .mov 2 (.reg 21)
  , .mov 3 (.reg 22)
  , .binop 23 .ne (.reg 21) (.lit 1)
  , .binop 24 .ne (.reg 22) (.reg 23) ]

/-- The accumulator: one signed step, then the `last`-gated store. -/
def blkD1P (PL : Nat) : List Instr :=
  [ .binop 25 .udiv (.lit PL) (.reg 8)
  , .binop 52 .sub (.lit 1) (.reg 24)
  , .binop 52 .mul (.reg 52) (.reg 25)
  , .binop 53 .add (.reg 1) (.reg 52)
  , .binop 54 .mul (.reg 24) (.reg 25)
  , .binop 26 .sub (.reg 53) (.reg 54)
  , .binop 52 .mul (.reg 10) (.reg 26)
  , .binop 53 .sub (.lit 1) (.reg 10)
  , .binop 54 .mul (.reg 53) (.reg 1)
  , .binop 27 .add (.reg 52) (.reg 54) ]

def blkD1 : List Instr := blkD1P plScale

/-- The accumulator's unconditional width clamp. -/
def blkD2P (ALO AHI : Nat) : List Instr :=
  [ .binop 52 .lt (.reg 27) (.lit ALO)
  , .binop 53 .mul (.lit ALO) (.reg 52)
  , .binop 54 .sub (.lit 1) (.reg 52)
  , .binop 54 .mul (.reg 54) (.reg 27)
  , .binop 28 .add (.reg 53) (.reg 54)
  , .binop 52 .gt (.reg 28) (.lit AHI)
  , .binop 53 .mul (.lit AHI) (.reg 52)
  , .binop 54 .sub (.lit 1) (.reg 52)
  , .binop 54 .mul (.reg 54) (.reg 28)
  , .binop 28 .add (.reg 53) (.reg 54)
  , .mov 1 (.reg 28) ]

def blkD2 : List Instr := blkD2P accLo accHi

/-- `|S| = |acc − 2⁶²|`. -/
def blkE1P (BI : Nat) : List Instr :=
  [ .binop 52 .lt (.reg 28) (.lit BI)
  , .binop 53 .mul (.lit BI) (.reg 52)
  , .binop 54 .sub (.lit 1) (.reg 52)
  , .binop 55 .mul (.reg 54) (.reg 28)
  , .binop 29 .add (.reg 53) (.reg 55)
  , .binop 53 .mul (.reg 52) (.reg 28)
  , .binop 55 .mul (.lit BI) (.reg 54)
  , .binop 30 .add (.reg 53) (.reg 55)
  , .binop 31 .sub (.reg 29) (.reg 30) ]

def blkE1 : List Instr := blkE1P biasV

/-- `A = |S| + n` and the shifted `⌈A/2²⁰⌉` with its clamp. -/
def blkE2P (SM SB AC : Nat) : List Instr :=
  [ .binop 32 .add (.reg 31) (.reg 8)
  , .binop 52 .add (.lit SM) (.reg 32)
  , .binop 33 .lshr (.reg 52) (.lit SB)
  , .binop 35 .le (.reg 33) (.lit AC)
  , .binop 52 .sub (.lit 1) (.reg 35)
  , .binop 53 .mul (.lit AC) (.reg 52)
  , .binop 54 .mul (.reg 35) (.reg 33)
  , .binop 34 .add (.reg 53) (.reg 54) ]

def blkE2 : List Instr := blkE2P shMask shBits ashCap

/-- The band ladder's width step. -/
def blkF1aP (NHI : Nat) : List Instr :=
  [ .binop 36 .udiv (.reg 5) (.lit 10)
  , .binop 36 .add (.lit 1) (.reg 36)
  , .binop 37 .sub (.lit NHI) (.reg 5)
  , .binop 52 .gt (.reg 36) (.reg 37)
  , .binop 53 .mul (.reg 52) (.reg 37)
  , .binop 54 .sub (.lit 1) (.reg 52)
  , .binop 55 .mul (.reg 54) (.reg 36)
  , .binop 38 .add (.reg 53) (.reg 55) ]

def blkF1a (c : Cfg) : List Instr := blkF1aP c.nhi

/-- The band ladder's log step, `⌈2²⁰·w/e⌉`. -/
def blkF1bP (LG : Nat) : List Instr :=
  [ .binop 52 .mul (.lit LG) (.reg 38)
  , .binop 53 .add (.reg 52) (.reg 5)
  , .binop 39 .sub (.reg 53) (.lit 1)
  , .binop 40 .udiv (.reg 39) (.reg 5) ]

def blkF1b : List Instr := blkF1bP lgScale

/-- The band advance decision and the raw ladder value. -/
def blkF2a : List Instr :=
  [ .binop 41 .eq (.reg 8) (.reg 5)
  , .binop 42 .mul (.reg 10) (.reg 41)
  , .binop 52 .mul (.reg 42) (.reg 40)
  , .binop 43 .add (.reg 4) (.reg 52) ]

/-- The ladder's clamp and the cursor update. -/
def blkF2bP (LC : Nat) : List Instr :=
  [ .binop 44 .le (.reg 43) (.lit LC)
  , .binop 52 .sub (.lit 1) (.reg 44)
  , .binop 53 .mul (.lit LC) (.reg 52)
  , .binop 54 .mul (.reg 44) (.reg 43)
  , .binop 45 .add (.reg 53) (.reg 54)
  , .mov 4 (.reg 45)
  , .binop 52 .mul (.reg 42) (.reg 38)
  , .binop 5 .add (.reg 5) (.reg 52) ]

def blkF2b : List Instr := blkF2bP lbCap

/-- The row test and the violation flag. -/
def blkGP (NLO RC GL GH : Nat) : List Instr :=
  [ .binop 46 .ge (.reg 8) (.lit NLO)
  , .binop 47 .mul (.reg 34) (.reg 45)
  , .binop 48 .mul (.lit 1000) (.reg 47)
  , .binop 49 .le (.reg 48) (.lit RC)
  , .binop 52 .ge (.reg 27) (.lit GL)
  , .binop 53 .le (.reg 27) (.lit GH)
  , .binop 50 .mul (.reg 52) (.reg 53)
  , .binop 52 .mul (.reg 35) (.reg 49)
  , .binop 53 .sub (.lit 1) (.reg 52)
  , .binop 53 .mul (.reg 46) (.reg 53)
  , .binop 53 .sub (.lit 1) (.reg 53)
  , .binop 52 .mul (.reg 50) (.reg 44)
  , .binop 51 .mul (.reg 52) (.reg 53)
  , .binop 52 .sub (.lit 1) (.reg 51)
  , .binop 59 .mul (.reg 10) (.reg 52)
  , .binop 0 .bor (.reg 0) (.reg 59) ]

def blkG (c : Cfg) : List Instr := blkGP c.nlo rhsCap gateLo gateHi

def body (c : Cfg) : List Instr :=
  blkA c ++ blkB c ++ blkC1 ++ blkC2 ++ blkD1 ++ blkD2 ++ blkE1 ++ blkE2 ++
    blkF1a c ++ blkF1b ++ blkF2a ++ blkF2b ++ blkG c

/-- Seed the accumulator and the band ladder; every other register starts `0`. -/
def initBlock (c : Cfg) : List Instr :=
  [ .mov 1 (.lit biasV), .mov 4 (.lit c.lb0), .mov 5 (.lit c.e0) ]

def lProgram (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := body c
  , epilogue := []
  , output := 0 }

/-- The value the loop computes, as a fold in ordinary arithmetic. -/
def value (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    ⟨0, biasV, 0, 0, c.lb0, c.e0⟩).bad

/-! ## Machine helpers -/

private theorem msub_bit (x : Nat) (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by decide)
  · have h : 1 + (M - 1) = M := by decide
    rw [h, Nat.mod_self]

private theorem msub_general (x y : Nat) (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hyM : y ≤ M := by omega
  have h : x + (M - y) = (x - y) + M := by omega
  rw [h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem or_lt (x y : Nat) (hx : x < M) (hy : y < M) : x ||| y < M := by
  have hM : M = 2 ^ 64 := rfl
  exact hM ▸ Nat.or_lt_two_pow (hM ▸ hx) (hM ▸ hy)

private theorem or_mod (x y : Nat) (hx : x < M) (hy : y < M) :
    (x ||| y) % M = x ||| y :=
  Nat.mod_eq_of_lt (or_lt x y hx hy)

private theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

private theorem bit_or_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

private theorem M_gt_one : (1 : Nat) < M := by decide

private theorem modM_of_le_one {x : Nat} (hx : x ≤ 1) : x % M = x :=
  Nat.mod_eq_of_lt (by have := M_gt_one; omega)

/-! The `simp` set every block spec runs with. -/
private theorem one_modM : (1 : Nat) % M = 1 := by decide
private theorem zero_modM : (0 : Nat) % M = 0 := by decide
private theorem two_modM : (2 : Nat) % M = 2 := by decide
private theorem modM_idem (x : Nat) : x % M % M = x % M :=
  Nat.mod_eq_of_lt (Nat.mod_lt _ M_pos)
private theorem one_add_M_modM : (1 + M) % M = 1 := by
  rw [Nat.add_mod_right]; exact one_modM

/-! ## Block specifications

Each block's literals are abstracted to variables, so no spec proof's defeq
ever sees a numeral; the concrete blocks are recovered by `rfl` equations. -/

set_option maxHeartbeats 1000000 in
/-- **Index decode.** -/
theorem blkAP_spec (k R RM1 LO : Nat) (s : RegState)
    (hR : 0 < R) (hRM : R < M) (hRM1 : RM1 < M) (hLO : LO < M)
    (hk : k < M) (hn : LO + k / R < M) :
    let s' := srun k s (blkAP R RM1 LO)
    s' 6 = k / R ∧ s' 7 = k % R ∧ s' 8 = LO + k / R ∧
      s' 9 = (if k % R = 0 then 1 else 0) ∧
      s' 10 = (if k % R = RM1 then 1 else 0) ∧
      ∀ j, j ≠ 6 → j ≠ 52 → j ≠ 7 → j ≠ 8 → j ≠ 9 → j ≠ 10 → s' j = s j := by
  have hkM : k % M = k := Nat.mod_eq_of_lt hk
  have hRMM : R % M = R := Nat.mod_eq_of_lt hRM
  have hR0 : ¬ (R = 0) := by omega
  have hdle : k / R ≤ k := Nat.div_le_self _ _
  have hdivM : (k / R) % M = k / R := Nat.mod_eq_of_lt (by omega)
  have hmulle : R * (k / R) ≤ k := Nat.mul_div_le k R
  have hmulM : (R * (k / R)) % M = R * (k / R) := Nat.mod_eq_of_lt (by omega)
  have hdm : R * (k / R) + k % R = k := Nat.div_add_mod k R
  have hsubM : (k + (M - R * (k / R))) % M = k % R := by
    rw [msub_general k (R * (k / R)) hmulle hk]; omega
  have hnM : (LO + k / R) % M = LO + k / R := Nat.mod_eq_of_lt hn
  have hLOM : LO % M = LO := Nat.mod_eq_of_lt hLO
  have hRM1M : RM1 % M = RM1 := Nat.mod_eq_of_lt hRM1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show srun k s (blkAP R RM1 LO) 6 = k / R
    simp only [blkAP, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hR0, reduceIte, reduceCtorEq, Nat.reduceEqDiff, hkM,
      hRMM, hdivM, hmulM, hsubM, hnM, hLOM, hRM1M, zero_modM, two_modM,
      modM_idem, if_true, if_false]
  · show srun k s (blkAP R RM1 LO) 7 = k % R
    simp only [blkAP, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hR0, reduceIte, reduceCtorEq, Nat.reduceEqDiff, hkM,
      hRMM, hdivM, hmulM, hsubM, hnM, hLOM, hRM1M, zero_modM, two_modM,
      modM_idem, if_true, if_false]
  · show srun k s (blkAP R RM1 LO) 8 = LO + k / R
    simp only [blkAP, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hR0, reduceIte, reduceCtorEq, Nat.reduceEqDiff, hkM,
      hRMM, hdivM, hmulM, hsubM, hnM, hLOM, hRM1M, zero_modM, two_modM,
      modM_idem, if_true, if_false]
  · show srun k s (blkAP R RM1 LO) 9 = (if k % R = 0 then 1 else 0)
    simp only [blkAP, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hR0, reduceIte, reduceCtorEq, Nat.reduceEqDiff, hkM,
      hRMM, hdivM, hmulM, hsubM, hnM, hLOM, hRM1M, zero_modM, two_modM,
      modM_idem, if_true, if_false]
  · show srun k s (blkAP R RM1 LO) 10 = (if k % R = RM1 then 1 else 0)
    simp only [blkAP, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hR0, reduceIte, reduceCtorEq, Nat.reduceEqDiff, hkM,
      hRMM, hdivM, hmulM, hsubM, hnM, hLOM, hRM1M, zero_modM, two_modM,
      modM_idem, if_true, if_false]
  · intro j h6 h52 h7 h8 h9 h10
    refine srun_untouched k j (blkAP R RM1 LO) ?_ s
    intro i hi
    simp only [blkAP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **Divisor decode**, both phases. -/
theorem blkBP_spec (k EX EDS DS2 q : Nat) (s : RegState)
    (h7 : s 7 = q) (hEX : 0 < EX) (hEXM : EX < M) (hEDS : EDS < M)
    (hDS2 : DS2 < M) (hq : q < M) (hd1 : 2 + q / EX < M)
    (hd2 : DS2 + (q - EDS) < M) :
    let s' := srun k s (blkBP EX EDS DS2)
    s' 14 = (if q < EDS then 1 else 0) ∧ s' 15 = divOfR EX EDS DS2 q ∧
      ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 14 → j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 58 →
        j ≠ 13 → j ≠ 15 → s' j = s j := by
  have hEXM' : EX % M = EX := Nat.mod_eq_of_lt hEXM
  have hEX0 : ¬ (EX = 0) := by omega
  have hqM : q % M = q := Nat.mod_eq_of_lt hq
  have hdivM : (q / EX) % M = q / EX :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hq)
  have hd1M : (2 + q / EX) % M = 2 + q / EX := Nat.mod_eq_of_lt hd1
  have hEDSM : EDS % M = EDS := Nat.mod_eq_of_lt hEDS
  have hDS2M : DS2 % M = DS2 := Nat.mod_eq_of_lt hDS2
  have hd2M : (DS2 + (q - EDS)) % M = DS2 + (q - EDS) := Nat.mod_eq_of_lt hd2
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  have hb0 : (1 + (M - 0)) % M = 1 := by rw [msub_bit 0 (by omega)]
  have key : ∀ r, r = 14 ∨ r = 15 →
      srun k s (blkBP EX EDS DS2) r =
        (if r = 14 then (if q < EDS then 1 else 0) else divOfR EX EDS DS2 q) := by
    intro r hr
    by_cases hlt : q < EDS
    · have hz : (EDS + (M - EDS)) % M = 0 := by
        rw [msub_general EDS EDS (Nat.le_refl _) hEDS, Nat.sub_self]
      rcases hr with rfl | rfl <;>
        simp only [blkBP, divOfR, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, hEX0, reduceCtorEq, Nat.reduceEqDiff,
          h7, hqM, hEXM', hdivM, hd1M, hb1, hb0, one_add_M_modM, two_modM, modM_idem,
          hEDSM, hDS2M, hd2M, hlt, hz, one_modM, zero_modM, reduceIte, if_true,
          if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero]
    · have hsubq : (q + (M - EDS)) % M = q - EDS :=
        msub_general q EDS (by omega) hq
      rcases hr with rfl | rfl <;>
        simp only [blkBP, divOfR, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, hEX0, reduceCtorEq, Nat.reduceEqDiff,
          h7, hqM, hEXM', hdivM, hd1M, hb1, hb0, one_add_M_modM, two_modM, modM_idem,
          hEDSM, hDS2M, hd2M, hlt, hsubq, one_modM, zero_modM, reduceIte,
          if_true, if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one,
          Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero]
  refine ⟨by simpa using key 14 (Or.inl rfl), by simpa using key 15 (Or.inr rfl), ?_⟩
  intro j h11 h12 h14 h52 h53 h54 h58 h13 h15
  refine srun_untouched k j (blkBP EX EDS DS2) ?_ s
  intro i hi
  simp only [blkBP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-! ### Shape lemmas for the machine's `min`/`max`/select idioms -/

private theorem ite_lt_max (x L : Nat) : (if x < L then L else x) = max x L := by
  by_cases h : x < L
  · rw [if_pos h, Nat.max_def, if_pos (Nat.le_of_lt h)]
  · rw [if_neg h, Nat.max_def]
    by_cases h2 : x ≤ L
    · rw [if_pos h2]; omega
    · rw [if_neg h2]

private theorem ite_lt_min (x L : Nat) : (if x < L then x else L) = min x L := by
  by_cases h : x < L
  · rw [if_pos h, Nat.min_def, if_pos (Nat.le_of_lt h)]
  · rw [if_neg h, Nat.min_def]
    by_cases h2 : x ≤ L
    · rw [if_pos h2]; omega
    · rw [if_neg h2]

private theorem ite_gt_min (x L : Nat) : (if L < x then L else x) = min x L := by
  by_cases h : L < x
  · rw [if_pos h, Nat.min_def, if_neg (by omega)]
  · rw [if_neg h, Nat.min_def, if_pos (by omega)]

private theorem ite_le_min (x L : Nat) : (if x ≤ L then x else L) = min x L := by
  rw [Nat.min_def]

private theorem ne_xorBit (a b : Nat) :
    (if ¬ (a = b) then (1:Nat) else 0) = xorBit a b := by
  unfold xorBit
  by_cases h : a = b
  · rw [if_neg (not_not_intro h), if_pos h]
  · rw [if_pos h, if_neg h]

private theorem add_M_modM (x : Nat) (hx : x < M) : (x + M) % M = x := by
  rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hx

private theorem mul_bit_le (x b : Nat) (hb : b ≤ 1) : b * x ≤ x := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega

set_option maxHeartbeats 1000000 in
/-- **Round input select.** -/
theorem blkC1_spec (k n r0 p0 fb : Nat) (s : RegState)
    (h9 : s 9 = fb) (h8 : s 8 = n) (h2 : s 2 = r0) (h3 : s 3 = p0)
    (hfb : fb ≤ 1) (hn : n < M) (hr0 : r0 < M) (hp0 : p0 < M) :
    let s' := srun k s blkC1
    s' 16 = (if fb = 1 then n else r0) ∧ s' 17 = (if fb = 1 then 0 else p0) ∧
      ∀ j, j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 16 → j ≠ 17 → s' j = s j := by
  have hnM : n % M = n := Nat.mod_eq_of_lt hn
  have hr0M : r0 % M = r0 := Nat.mod_eq_of_lt hr0
  have hp0M : p0 % M = p0 := Nat.mod_eq_of_lt hp0
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rcases (by omega : fb = 0 ∨ fb = 1) with rfl | rfl <;>
      show srun k s blkC1 16 = _ <;>
      simp only [blkC1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, h9, h8, h2, h3, hnM, hr0M, hp0M, hb1, one_modM,
        zero_modM, one_add_M_modM, modM_idem, reduceIte, reduceCtorEq,
        Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
        Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  · rcases (by omega : fb = 0 ∨ fb = 1) with rfl | rfl <;>
      show srun k s blkC1 17 = _ <;>
      simp only [blkC1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, h9, h8, h2, h3, hnM, hr0M, hp0M, hb1, one_modM,
        zero_modM, one_add_M_modM, modM_idem, reduceIte, reduceCtorEq,
        Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
        Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  · intro j h52 h53 h54 h16 h17
    refine srun_untouched k j blkC1 ?_ s
    intro i hi
    simp only [blkC1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **One trial-division round**, and the completely-multiplicative sign. -/
theorem blkC2_spec (k rin pin d : Nat) (s : RegState)
    (h16 : s 16 = rin) (h17 : s 17 = pin) (h15 : s 15 = d)
    (hd : 0 < d) (hrin : rin < M) (hpin : pin ≤ 1) :
    let s' := srun k s blkC2
    s' 2 = (stripStep d (rin, pin)).1 ∧ s' 3 = (stripStep d (rin, pin)).2 ∧
      s' 24 = signOf (stripStep d (rin, pin)) ∧
      ∀ j, j ≠ 18 → j ≠ 52 → j ≠ 19 → j ≠ 20 → j ≠ 53 → j ≠ 54 → j ≠ 21 →
        j ≠ 22 → j ≠ 2 → j ≠ 3 → j ≠ 23 → j ≠ 24 → s' j = s j := by
  have hd0 : ¬ (d = 0) := by omega
  have hrinM : rin % M = rin := Nat.mod_eq_of_lt hrin
  have hqdle : rin / d ≤ rin := Nat.div_le_self _ _
  have hqdM : (rin / d) % M = rin / d := Nat.mod_eq_of_lt (by omega)
  have hmulle : rin / d * d ≤ rin := Nat.div_mul_le_self rin d
  have hmulM : (rin / d * d) % M = rin / d * d := Nat.mod_eq_of_lt (by omega)
  have hsubM : (rin + (M - rin / d * d)) % M = rin - rin / d * d :=
    msub_general rin (rin / d * d) hmulle hrin
  have hpinM : pin % M = pin := modM_of_le_one hpin
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  have key : ∀ r, r = 2 ∨ r = 3 ∨ r = 24 →
      srun k s blkC2 r =
        (if r = 2 then (stripStep d (rin, pin)).1
         else if r = 3 then (stripStep d (rin, pin)).2
         else signOf (stripStep d (rin, pin))) := by
    intro r hr
    by_cases hhit : rin - rin / d * d = 0
    · rcases hr with rfl | rfl | rfl <;>
        simp only [blkC2, stripStep, signOf, srun, sdest, sval, denoteOperand,
          denoteOp, RegState.set, Option.getD_some, hd0, h16, h17, h15, hrinM,
          hqdM, hmulM, hsubM, hpinM, hhit, hb1, one_modM, zero_modM,
          one_add_M_modM, modM_idem, ne_xorBit, reduceIte, reduceCtorEq,
          Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
          Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    · rcases hr with rfl | rfl | rfl <;>
        simp only [blkC2, stripStep, signOf, srun, sdest, sval, denoteOperand,
          denoteOp, RegState.set, Option.getD_some, hd0, h16, h17, h15, hrinM,
          hqdM, hmulM, hsubM, hpinM, hhit, hb1, one_modM, zero_modM,
          one_add_M_modM, modM_idem, ne_xorBit, reduceIte, reduceCtorEq,
          Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
          Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  refine ⟨by simpa using key 2 (Or.inl rfl), by simpa using key 3 (Or.inr (Or.inl rfl)),
    by simpa using key 24 (Or.inr (Or.inr rfl)), ?_⟩
  intro j h18 h52 h19 h20 h53 h54 h21 h22 h2' h3' h23 h24
  refine srun_untouched k j blkC2 ?_ s
  intro i hi
  simp only [blkC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The signed accumulator step**, gated by `last`. -/
theorem blkD1P_spec (k PL n sgn lastb a : Nat) (s : RegState)
    (h8 : s 8 = n) (h24 : s 24 = sgn) (h10 : s 10 = lastb) (h1 : s 1 = a)
    (hn : 0 < n) (hPL : PL < M) (hsgn : sgn ≤ 1) (hlastb : lastb ≤ 1)
    (hpa : PL / n ≤ a) (haM : a + PL / n < M) :
    let s' := srun k s (blkD1P PL)
    s' 26 = accApplyR PL a sgn n ∧
      s' 27 = (if lastb = 1 then accApplyR PL a sgn n else a) ∧
      ∀ j, j ≠ 25 → j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 26 → j ≠ 27 → s' j = s j := by
  have hn0 : ¬ (n = 0) := by omega
  have hPLM : PL % M = PL := Nat.mod_eq_of_lt hPL
  have hpnM : (PL / n) % M = PL / n :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hPL)
  have haM' : a % M = a := Nat.mod_eq_of_lt (by omega)
  have hsub1 : (1 + (M - sgn)) % M = 1 - sgn := msub_bit sgn hsgn
  have hsub1' : (1 + (M - lastb)) % M = 1 - lastb := msub_bit lastb hlastb
  have hm1 : ((1 - sgn) * (PL / n)) % M = (1 - sgn) * (PL / n) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (mul_bit_le _ _ (by omega)) (by omega))
  have hm2 : (sgn * (PL / n)) % M = sgn * (PL / n) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (mul_bit_le _ _ hsgn) (by omega))
  have hadd : (a + (1 - sgn) * (PL / n)) % M = a + (1 - sgn) * (PL / n) := by
    refine Nat.mod_eq_of_lt ?_
    have := mul_bit_le (PL / n) (1 - sgn) (by omega)
    omega
  have hle : sgn * (PL / n) ≤ a + (1 - sgn) * (PL / n) := by
    have := mul_bit_le (PL / n) sgn hsgn
    omega
  have hstep : (a + (1 - sgn) * (PL / n) + (M - sgn * (PL / n))) % M
      = accApplyR PL a sgn n := by
    rw [msub_general _ _ hle (by
      have := mul_bit_le (PL / n) (1 - sgn) (by omega); omega)]
    rfl
  have haccM : (accApplyR PL a sgn n) % M = accApplyR PL a sgn n := by
    refine Nat.mod_eq_of_lt ?_
    have := mul_bit_le (PL / n) (1 - sgn) (by omega)
    unfold accApplyR
    omega
  refine ⟨?_, ?_, ?_⟩
  · show srun k s (blkD1P PL) 26 = _
    simp only [blkD1P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hn0, h8, h24, h10, h1, hPLM, hpnM, haM', hsub1, hsub1',
      hm1, hm2, hadd, hstep, one_modM, zero_modM, modM_idem, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, if_false]
  · rcases (by omega : lastb = 0 ∨ lastb = 1) with rfl | rfl <;>
      show srun k s (blkD1P PL) 27 = _ <;>
      simp only [blkD1P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, hn0, h8, h24, h10, h1, hPLM, hpnM, haM', hsub1, hsub1',
        hm1, hm2, hadd, hstep, haccM, one_modM, zero_modM, one_add_M_modM,
        modM_idem, reduceIte,
        reduceCtorEq, Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero,
        Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        Nat.sub_zero, Nat.sub_self]
  · intro j h25 h52 h53 h54 h26 h27
    refine srun_untouched k j (blkD1P PL) ?_ s
    intro i hi
    simp only [blkD1P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The accumulator's width clamp.** -/
theorem blkD2P_spec (k ALO AHI x : Nat) (s : RegState)
    (h27 : s 27 = x) (hALO : ALO < M) (hAHI : AHI < M) (hx : x < M) :
    let s' := srun k s (blkD2P ALO AHI)
    s' 28 = min (max x ALO) AHI ∧ s' 1 = min (max x ALO) AHI ∧
      ∀ j, j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 28 → j ≠ 1 → s' j = s j := by
  have hALOM : ALO % M = ALO := Nat.mod_eq_of_lt hALO
  have hAHIM : AHI % M = AHI := Nat.mod_eq_of_lt hAHI
  have hxM : x % M = x := Nat.mod_eq_of_lt hx
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  have key : ∀ r, r = 28 ∨ r = 1 →
      srun k s (blkD2P ALO AHI) r = min (max x ALO) AHI := by
    intro r hr
    by_cases h1 : x < ALO
    · have hmax : max x ALO = ALO := by rw [← ite_lt_max, if_pos h1]
      by_cases h2 : AHI < ALO
      · have : min (max x ALO) AHI = AHI := by
          rw [hmax, Nat.min_def, if_neg (by omega)]
        rcases hr with rfl | rfl <;>
          simp only [blkD2P, srun, sdest, sval, denoteOperand, denoteOp,
            RegState.set, Option.getD_some, h27, hALOM, hAHIM, hxM, h1, h2, hb1,
            this, one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte,
            reduceCtorEq, Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero,
            Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
            Nat.sub_zero]
      · have : min (max x ALO) AHI = ALO := by
          rw [hmax, Nat.min_def, if_pos (by omega)]
        rcases hr with rfl | rfl <;>
          simp only [blkD2P, srun, sdest, sval, denoteOperand, denoteOp,
            RegState.set, Option.getD_some, h27, hALOM, hAHIM, hxM, h1, h2, hb1,
            this, one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte,
            reduceCtorEq, Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero,
            Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
            Nat.sub_zero]
    · have hmax : max x ALO = x := by rw [← ite_lt_max, if_neg h1]
      by_cases h2 : AHI < x
      · have : min (max x ALO) AHI = AHI := by
          rw [hmax, Nat.min_def, if_neg (by omega)]
        rcases hr with rfl | rfl <;>
          simp only [blkD2P, srun, sdest, sval, denoteOperand, denoteOp,
            RegState.set, Option.getD_some, h27, hALOM, hAHIM, hxM, h1, h2, hb1,
            this, one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte,
            reduceCtorEq, Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero,
            Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
            Nat.sub_zero]
      · have : min (max x ALO) AHI = x := by
          rw [hmax, Nat.min_def, if_pos (by omega)]
        rcases hr with rfl | rfl <;>
          simp only [blkD2P, srun, sdest, sval, denoteOperand, denoteOp,
            RegState.set, Option.getD_some, h27, hALOM, hAHIM, hxM, h1, h2, hb1,
            this, one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte,
            reduceCtorEq, Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero,
            Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
            Nat.sub_zero]
  refine ⟨by simpa using key 28 (Or.inl rfl), by simpa using key 1 (Or.inr rfl), ?_⟩
  intro j h52 h53 h54 h28 h1'
  refine srun_untouched k j (blkD2P ALO AHI) ?_ s
  intro i hi
  simp only [blkD2P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **`|S| = |acc − 2⁶²|`.** -/
theorem blkE1P_spec (k BI x : Nat) (s : RegState)
    (h28 : s 28 = x) (hBI : BI < M) (hx : x < M) :
    let s' := srun k s (blkE1P BI)
    s' 31 = max x BI - min x BI ∧
      ∀ j, j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 55 → j ≠ 29 → j ≠ 30 → j ≠ 31 →
        s' j = s j := by
  have hBIM : BI % M = BI := Nat.mod_eq_of_lt hBI
  have hxM : x % M = x := Nat.mod_eq_of_lt hx
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  refine ⟨?_, ?_⟩
  · by_cases h : x < BI
    · have hmx : max x BI = BI := by rw [← ite_lt_max, if_pos h]
      have hmn : min x BI = x := by rw [← ite_lt_min, if_pos h]
      have hsb : (BI + (M - x)) % M = BI - x := msub_general BI x (by omega) hBI
      show srun k s (blkE1P BI) 31 = _
      simp only [blkE1P, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, h28, hBIM, hxM, h, hb1, hmx, hmn, hsb,
        one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte, reduceCtorEq,
        Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
        Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    · have hmx : max x BI = x := by rw [← ite_lt_max, if_neg h]
      have hmn : min x BI = BI := by rw [← ite_lt_min, if_neg h]
      have hsb : (x + (M - BI)) % M = x - BI := msub_general x BI (by omega) hx
      show srun k s (blkE1P BI) 31 = _
      simp only [blkE1P, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, h28, hBIM, hxM, h, hb1, hmx, hmn, hsb,
        one_modM, zero_modM, one_add_M_modM, modM_idem, reduceIte, reduceCtorEq,
        Nat.reduceEqDiff, if_true, if_false, Nat.mul_zero, Nat.zero_mul,
        Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  · intro j h52 h53 h54 h55 h29 h30 h31
    refine srun_untouched k j (blkE1P BI) ?_ s
    intro i hi
    simp only [blkE1P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **`A = |S| + n`, its shift, and the shift's clamp.** -/
theorem blkE2P_spec (k SM SB AC ab n : Nat) (s : RegState)
    (h31 : s 31 = ab) (h8 : s 8 = n) (hSM : SM < M) (hSB : SB < M) (hAC : AC < M)
    (hsm : SM + (ab + n) < M) :
    let s' := srun k s (blkE2P SM SB AC)
    s' 33 = (SM + (ab + n)) / 2 ^ SB ∧
      s' 35 = (if (SM + (ab + n)) / 2 ^ SB ≤ AC then 1 else 0) ∧
      s' 34 = min ((SM + (ab + n)) / 2 ^ SB) AC ∧
      ∀ j, j ≠ 32 → j ≠ 52 → j ≠ 33 → j ≠ 35 → j ≠ 53 → j ≠ 54 → j ≠ 34 →
        s' j = s j := by
  have hSMM : SM % M = SM := Nat.mod_eq_of_lt hSM
  have hSBM : SB % M = SB := Nat.mod_eq_of_lt hSB
  have hACM : AC % M = AC := Nat.mod_eq_of_lt hAC
  have habn : (ab + n) % M = ab + n := Nat.mod_eq_of_lt (by omega)
  have hsmM : (SM + (ab + n)) % M = SM + (ab + n) := Nat.mod_eq_of_lt hsm
  have hshift : ((SM + (ab + n)) >>> SB) % M = (SM + (ab + n)) / 2 ^ SB := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsm)
  have hdivM : ((SM + (ab + n)) / 2 ^ SB) % M = (SM + (ab + n)) / 2 ^ SB :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsm)
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  have key : ∀ r, r = 33 ∨ r = 35 ∨ r = 34 →
      srun k s (blkE2P SM SB AC) r =
        (if r = 33 then (SM + (ab + n)) / 2 ^ SB
         else if r = 35 then (if (SM + (ab + n)) / 2 ^ SB ≤ AC then 1 else 0)
         else min ((SM + (ab + n)) / 2 ^ SB) AC) := by
    intro r hr
    by_cases hle : (SM + (ab + n)) / 2 ^ SB ≤ AC
    · have hmin : min ((SM + (ab + n)) / 2 ^ SB) AC = (SM + (ab + n)) / 2 ^ SB := by
        rw [← ite_le_min, if_pos hle]
      rcases hr with rfl | rfl | rfl <;>
        simp only [blkE2P, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, h31, h8, hSMM, hSBM, hACM, habn, hsmM,
          hshift, hdivM, hle, hmin, hb1, one_modM, zero_modM, one_add_M_modM,
          modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
          if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    · have hmin : min ((SM + (ab + n)) / 2 ^ SB) AC = AC := by
        rw [← ite_le_min, if_neg hle]
      rcases hr with rfl | rfl | rfl <;>
        simp only [blkE2P, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, h31, h8, hSMM, hSBM, hACM, habn, hsmM,
          hshift, hdivM, hle, hmin, hb1, one_modM, zero_modM, one_add_M_modM,
          modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
          if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  refine ⟨by simpa using key 33 (Or.inl rfl),
    by simpa using key 35 (Or.inr (Or.inl rfl)),
    by simpa using key 34 (Or.inr (Or.inr rfl)), ?_⟩
  intro j h32 h52 h33 h35 h53 h54 h34
  refine srun_untouched k j (blkE2P SM SB AC) ?_ s
  intro i hi
  simp only [blkE2P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The band ladder's width step.** -/
theorem blkF1aP_spec (k NHI e : Nat) (s : RegState)
    (h5 : s 5 = e) (he : 0 < e) (heN : e ≤ NHI) (hNHI : NHI < M) :
    let s' := srun k s (blkF1aP NHI)
    s' 38 = bandWR NHI e ∧
      ∀ j, j ≠ 36 → j ≠ 37 → j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 55 → j ≠ 38 →
        s' j = s j := by
  have heM : e % M = e := Nat.mod_eq_of_lt (by omega)
  have hNHIM : NHI % M = NHI := Nat.mod_eq_of_lt hNHI
  have hten : (10 : Nat) % M = 10 := by decide
  have hten0 : ¬ ((10 : Nat) = 0) := by decide
  have hdle : e / 10 ≤ e := Nat.div_le_self _ _
  have hdivM : (e / 10) % M = e / 10 := Nat.mod_eq_of_lt (by omega)
  have hwrM : (1 + e / 10) % M = 1 + e / 10 := Nat.mod_eq_of_lt (by omega)
  have hremM : (NHI + (M - e)) % M = NHI - e := msub_general NHI e heN hNHI
  have hremM' : (NHI - e) % M = NHI - e := Nat.mod_eq_of_lt (by omega)
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  refine ⟨?_, ?_⟩
  · by_cases hgt : NHI - e < 1 + e / 10
    · have hbw : bandWR NHI e = NHI - e := by
        show min (1 + e / 10) (NHI - e) = NHI - e
        rw [← ite_gt_min, if_pos hgt]
      show srun k s (blkF1aP NHI) 38 = _
      simp only [blkF1aP, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, hten0, h5, heM, hNHIM, hten, hdivM,
        hwrM, hremM, hremM', hgt, hbw, hb1, one_modM, zero_modM, one_add_M_modM,
        modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true, if_false,
        Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero,
        Nat.zero_add, Nat.sub_zero, Nat.sub_self]
    · have hbw : bandWR NHI e = 1 + e / 10 := by
        show min (1 + e / 10) (NHI - e) = 1 + e / 10
        rw [← ite_gt_min, if_neg hgt]
      show srun k s (blkF1aP NHI) 38 = _
      simp only [blkF1aP, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, hten0, h5, heM, hNHIM, hten, hdivM,
        hwrM, hremM, hremM', hgt, hbw, hb1, one_modM, zero_modM, one_add_M_modM,
        modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true, if_false,
        Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero,
        Nat.zero_add, Nat.sub_zero, Nat.sub_self]
  · intro j h36 h37 h52 h53 h54 h55 h38
    refine srun_untouched k j (blkF1aP NHI) ?_ s
    intro i hi
    simp only [blkF1aP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The band ladder's log step**, `⌈LG·w/e⌉`. -/
theorem blkF1bP_spec (k LG e W : Nat) (s : RegState)
    (h38 : s 38 = W) (h5 : s 5 = e) (he : 0 < e) (hLG : LG < M)
    (hw : LG * W + e < M) :
    let s' := srun k s (blkF1bP LG)
    s' 40 = (LG * W + e - 1) / e ∧
      ∀ j, j ≠ 52 → j ≠ 53 → j ≠ 39 → j ≠ 40 → s' j = s j := by
  have he0 : ¬ (e = 0) := by omega
  have heM : e % M = e := Nat.mod_eq_of_lt (by omega)
  have hLGM : LG % M = LG := Nat.mod_eq_of_lt hLG
  have hlgw : (LG * W) % M = LG * W := Nat.mod_eq_of_lt (by omega)
  have hnum : (LG * W + e) % M = LG * W + e := Nat.mod_eq_of_lt hw
  have hnum1 : (LG * W + e + (M - 1)) % M = LG * W + e - 1 :=
    msub_general _ 1 (by omega) hw
  have hq : ((LG * W + e - 1) / e) % M = (LG * W + e - 1) / e :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  refine ⟨?_, ?_⟩
  · show srun k s (blkF1bP LG) 40 = _
    simp only [blkF1bP, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, he0, h38, h5, heM, hLGM, hlgw, hnum,
      hnum1, hq, one_modM, zero_modM, modM_idem, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, if_false]
  · intro j h52 h53 h39 h40
    refine srun_untouched k j (blkF1bP LG) ?_ s
    intro i hi
    simp only [blkF1bP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The band advance decision and the raw ladder value.** -/
theorem blkF2a_spec (k n e lb inc lastb : Nat) (s : RegState)
    (h8 : s 8 = n) (h5 : s 5 = e) (h4 : s 4 = lb) (h10 : s 10 = lastb)
    (h40 : s 40 = inc) (hlastb : lastb ≤ 1) (hlbinc : lb + inc < M) :
    let s' := srun k s blkF2a
    s' 42 = lastb * (if n = e then 1 else 0) ∧
      s' 43 = lb + lastb * (if n = e then 1 else 0) * inc ∧
      ∀ j, j ≠ 41 → j ≠ 42 → j ≠ 52 → j ≠ 43 → s' j = s j := by
  have hadvle : lastb * (if n = e then 1 else 0) ≤ 1 := by
    have := bitLe (n = e)
    exact Nat.le_trans (Nat.mul_le_mul hlastb this) (by omega)
  have hbitM : ((if n = e then (1:Nat) else 0)) % M = (if n = e then 1 else 0) :=
    modM_of_le_one (bitLe _)
  have hadvM' : (lastb * (if n = e then 1 else 0)) % M
      = lastb * (if n = e then 1 else 0) := modM_of_le_one hadvle
  have hmulle : lastb * (if n = e then 1 else 0) * inc ≤ inc :=
    mul_bit_le inc _ hadvle
  have hmulM : (lastb * (if n = e then 1 else 0) * inc) % M
      = lastb * (if n = e then 1 else 0) * inc :=
    Nat.mod_eq_of_lt (by omega)
  have haddM : (lb + lastb * (if n = e then 1 else 0) * inc) % M
      = lb + lastb * (if n = e then 1 else 0) * inc := Nat.mod_eq_of_lt (by omega)
  have hlbM : lb % M = lb := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · show srun k s blkF2a 42 = _
    simp only [blkF2a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, h8, h5, h4, h10, h40, hbitM, hadvM', hmulM, haddM, hlbM,
      one_modM, zero_modM, modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false]
  · show srun k s blkF2a 43 = _
    simp only [blkF2a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, h8, h5, h4, h10, h40, hbitM, hadvM', hmulM, haddM, hlbM,
      one_modM, zero_modM, modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false]
  · intro j h41 h42 h52 h43
    refine srun_untouched k j blkF2a ?_ s
    intro i hi
    simp only [blkF2a, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The ladder's clamp and the cursor update.** -/
theorem blkF2bP_spec (k LC lr adv w e : Nat) (s : RegState)
    (h43 : s 43 = lr) (h42 : s 42 = adv) (h38 : s 38 = w) (h5 : s 5 = e)
    (hadv : adv ≤ 1) (hLC : LC < M) (hlr : lr < M) (hew : e + w < M) :
    let s' := srun k s (blkF2bP LC)
    s' 44 = (if lr ≤ LC then 1 else 0) ∧ s' 45 = min lr LC ∧
      s' 4 = min lr LC ∧ s' 5 = e + adv * w ∧
      ∀ j, j ≠ 44 → j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 45 → j ≠ 4 → j ≠ 5 →
        s' j = s j := by
  have hLCM : LC % M = LC := Nat.mod_eq_of_lt hLC
  have hlrM : lr % M = lr := Nat.mod_eq_of_lt hlr
  have hwM : w % M = w := Nat.mod_eq_of_lt (by omega)
  have heM : e % M = e := Nat.mod_eq_of_lt (by omega)
  have hmw : (adv * w) % M = adv * w :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (mul_bit_le w adv hadv) (by omega))
  have hew' : (e + adv * w) % M = e + adv * w := by
    refine Nat.mod_eq_of_lt ?_
    have := mul_bit_le w adv hadv
    omega
  have hb1 : (1 + (M - 1)) % M = 0 := by rw [msub_bit 1 (by omega)]
  have key : ∀ r, r = 44 ∨ r = 45 ∨ r = 4 ∨ r = 5 →
      srun k s (blkF2bP LC) r =
        (if r = 44 then (if lr ≤ LC then 1 else 0)
         else if r = 5 then e + adv * w else min lr LC) := by
    intro r hr
    by_cases hle : lr ≤ LC
    · have hmin : min lr LC = lr := by rw [← ite_le_min, if_pos hle]
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [blkF2bP, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, h43, h42, h38, h5, hLCM, hlrM, hwM,
          heM, hmw, hew', hle, hmin, hb1, one_modM, zero_modM, one_add_M_modM,
          modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
          if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, Nat.sub_zero, Nat.sub_self]
    · have hmin : min lr LC = LC := by rw [← ite_le_min, if_neg hle]
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [blkF2bP, srun, sdest, sval, denoteOperand, denoteOp,
          RegState.set, Option.getD_some, h43, h42, h38, h5, hLCM, hlrM, hwM,
          heM, hmw, hew', hle, hmin, hb1, one_modM, zero_modM, one_add_M_modM,
          modM_idem, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
          if_false, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, Nat.sub_zero, Nat.sub_self]
  refine ⟨by simpa using key 44 (Or.inl rfl),
    by simpa using key 45 (Or.inr (Or.inl rfl)),
    by simpa using key 4 (Or.inr (Or.inr (Or.inl rfl))),
    by simpa using key 5 (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
  intro j h44 h52 h53 h54 h45 h4' h5'
  refine srun_untouched k j (blkF2bP LC) ?_ s
  intro i hi
  simp only [blkF2bP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 2000000 in
/-- **The row test and the violation flag.** -/
theorem blkGP_spec (k NLO RC GL GH n ashC lbC gash glb accS lastb bd : Nat)
    (s : RegState)
    (h8 : s 8 = n) (h34 : s 34 = ashC) (h45 : s 45 = lbC) (h35 : s 35 = gash)
    (h44 : s 44 = glb) (h27 : s 27 = accS) (h10 : s 10 = lastb) (h0 : s 0 = bd)
    (hgash : gash ≤ 1) (hglb : glb ≤ 1) (hlastb : lastb ≤ 1) (hbd : bd ≤ 1)
    (hNLO : NLO < M) (hRC : RC < M) (hGL : GL < M) (hGH : GH < M)
    (hn : n < M) (haccS : accS < M) (hprod : 1000 * (ashC * lbC) < M) :
    let s' := srun k s (blkGP NLO RC GL GH)
    s' 0 = bd ||| lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
        (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
        (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) ∧
      ∀ j, j ≠ 46 → j ≠ 47 → j ≠ 48 → j ≠ 49 → j ≠ 52 → j ≠ 53 → j ≠ 50 →
        j ≠ 51 → j ≠ 59 → j ≠ 0 → s' j = s j := by
  have hnM : n % M = n := Nat.mod_eq_of_lt hn
  have haccM : accS % M = accS := Nat.mod_eq_of_lt haccS
  have hNLOM : NLO % M = NLO := Nat.mod_eq_of_lt hNLO
  have hRCM : RC % M = RC := Nat.mod_eq_of_lt hRC
  have hGLM : GL % M = GL := Nat.mod_eq_of_lt hGL
  have hGHM : GH % M = GH := Nat.mod_eq_of_lt hGH
  have h1000 : (1000 : Nat) % M = 1000 := by decide
  have hac : ashC * lbC < M := by omega
  have hacM : (ashC * lbC) % M = ashC * lbC := Nat.mod_eq_of_lt hac
  have hlhsM : (1000 * (ashC * lbC)) % M = 1000 * (ashC * lbC) :=
    Nat.mod_eq_of_lt hprod
  have hpostM : ((if NLO ≤ n then (1:Nat) else 0)) % M = (if NLO ≤ n then 1 else 0) :=
    modM_of_le_one (bitLe _)
  have hgokM : ((if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0)) % M
      = (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) := modM_of_le_one (bitLe _)
  have hgloM : ((if GL ≤ accS then (1:Nat) else 0)) % M = (if GL ≤ accS then 1 else 0) :=
    modM_of_le_one (bitLe _)
  have hghiM : ((if accS ≤ GH then (1:Nat) else 0)) % M = (if accS ≤ GH then 1 else 0) :=
    modM_of_le_one (bitLe _)
  have hgaccLe : (if GL ≤ accS then (1:Nat) else 0) * (if accS ≤ GH then 1 else 0) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul (bitLe _) (bitLe _)) (by omega)
  have hgaccM : ((if GL ≤ accS then (1:Nat) else 0) * (if accS ≤ GH then 1 else 0)) % M
      = (if GL ≤ accS then 1 else 0) * (if accS ≤ GH then 1 else 0) :=
    modM_of_le_one hgaccLe
  have hggLe : gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul hgash (bitLe _)) (by omega)
  have hggM : (gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0)) % M
      = gash * (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) := modM_of_le_one hggLe
  have hs1 : (1 + (M - gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0))) % M
      = 1 - gash * (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) := msub_bit _ hggLe
  have hpgLe : (if NLO ≤ n then (1:Nat) else 0) *
      (1 - gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0)) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul (bitLe _) (Nat.sub_le _ _)) (by omega)
  have hpgM : ((if NLO ≤ n then (1:Nat) else 0) *
      (1 - gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0))) % M
      = (if NLO ≤ n then 1 else 0) *
        (1 - gash * (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) := modM_of_le_one hpgLe
  have hs2 : (1 + (M - (if NLO ≤ n then (1:Nat) else 0) *
      (1 - gash * (if 1000 * (ashC * lbC) ≤ RC then (1:Nat) else 0)))) % M
      = 1 - (if NLO ≤ n then 1 else 0) *
        (1 - gash * (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) := msub_bit _ hpgLe
  have hglLe : (if GL ≤ accS then (1:Nat) else 0) * (if accS ≤ GH then 1 else 0) * glb ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul hgaccLe hglb) (by omega)
  have hglM : ((if GL ≤ accS then (1:Nat) else 0) * (if accS ≤ GH then 1 else 0) * glb) % M
      = (if GL ≤ accS then 1 else 0) * (if accS ≤ GH then 1 else 0) * glb :=
    modM_of_le_one hglLe
  have hrvLe : rowVerdict (if GL ≤ accS then 1 else 0) (if accS ≤ GH then 1 else 0)
      glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) ≤ 1 := by
    unfold rowVerdict
    exact Nat.le_trans (Nat.mul_le_mul hglLe (Nat.sub_le _ _)) (by omega)
  have hrvM : (rowVerdict (if GL ≤ accS then 1 else 0) (if accS ≤ GH then 1 else 0)
      glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) % M
      = rowVerdict (if GL ≤ accS then 1 else 0) (if accS ≤ GH then 1 else 0)
        glb (if NLO ≤ n then 1 else 0) gash
        (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) := modM_of_le_one hrvLe
  have hs3 : (1 + (M - rowVerdict (if GL ≤ accS then 1 else 0)
      (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0))) % M
      = 1 - rowVerdict (if GL ≤ accS then 1 else 0) (if accS ≤ GH then 1 else 0)
        glb (if NLO ≤ n then 1 else 0) gash
        (if 1000 * (ashC * lbC) ≤ RC then 1 else 0) := msub_bit _ hrvLe
  have hviolLe : lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
      (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul hlastb (Nat.sub_le _ _)) (by omega)
  have hviolM : (lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
      (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0))) % M
      = lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
        (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
        (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) := modM_of_le_one hviolLe
  have horM : (bd ||| lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
      (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
      (if 1000 * (ashC * lbC) ≤ RC then 1 else 0))) % M
      = bd ||| lastb * (1 - rowVerdict (if GL ≤ accS then 1 else 0)
        (if accS ≤ GH then 1 else 0) glb (if NLO ≤ n then 1 else 0) gash
        (if 1000 * (ashC * lbC) ≤ RC then 1 else 0)) :=
    or_mod _ _ (by have := M_gt_one; omega) (by have := M_gt_one; omega)
  unfold rowVerdict at hrvLe hrvM hs3 hviolLe hviolM horM
  refine ⟨?_, ?_⟩
  · show srun k s (blkGP NLO RC GL GH) 0 = _
    simp only [blkGP, rowVerdict, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, h8, h34, h45, h35, h44, h27, h10, h0,
      hnM, haccM, hNLOM, hRCM, hGLM, hGHM, h1000, hacM, hlhsM, hpostM, hgokM,
      hgloM, hghiM, hgaccM, hggM, hs1, hpgM, hs2, hglM, hrvM, hs3, hviolM,
      horM, one_modM, zero_modM, modM_idem, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, if_false]
  · intro j h46 h47 h48 h49 h52 h53 h50 h51 h59 h0'
    refine srun_untouched k j (blkGP NLO RC GL GH) ?_ s
    intro i hi
    simp only [blkGP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp only [sdest] <;> omega

/-! ## Width bounds on the model, all unconditional -/

private theorem pos_add (a b : Nat) (h : 0 < a) : 0 < a + b := by omega

theorem divOf_pos (c : Cfg) (q : Nat) : 0 < divOf c q := by
  unfold divOf divOfR
  by_cases h : q < c.ex * c.dsm
  · rw [if_pos h]; exact pos_add 2 _ (by decide)
  · rw [if_neg h]; exact pos_add (c.dsm + 2) _ (by omega)

theorem divOf_le (c : Cfg) (q : Nat) (hex : 0 < c.ex) (hd : c.dsm < c.dbg)
    (hq : q < c.ex * c.dsm + (c.dbg - c.dsm)) : divOf c q ≤ c.dbg + 1 := by
  unfold divOf divOfR
  by_cases h : q < c.ex * c.dsm
  · rw [if_pos h]
    have hcomm : c.ex * c.dsm = c.dsm * c.ex := Nat.mul_comm _ _
    have h1 : q / c.ex < c.dsm := Nat.div_lt_of_lt_mul (hcomm ▸ h)
    have h2 : ∀ x : Nat, x < c.dsm → 2 + x ≤ c.dbg + 1 := by
      intro x hx; omega
    exact h2 _ h1
  · rw [if_neg h]
    have h3 : ∀ E : Nat, ¬ (q < E) → q < E + (c.dbg - c.dsm) →
        c.dsm + 2 + (q - E) ≤ c.dbg + 1 := by
      intro E hE hq2; omega
    exact h3 _ h hq

theorem accClamp_le (x : Nat) : accClamp x ≤ accHi := Nat.min_le_right _ _

theorem accClamp_ge (x : Nat) : accLo ≤ accClamp x := by
  have h1 : accLo ≤ max x accLo := by
    rw [Nat.max_def]
    by_cases h : x ≤ accLo
    · rw [if_pos h]; exact Nat.le_refl accLo
    · rw [if_neg h]; omega
  have h2 : accLo ≤ accHi := by decide
  unfold accClamp
  rw [Nat.min_def]
  by_cases h : max x accLo ≤ accHi
  · rw [if_pos h]; exact h1
  · rw [if_neg h]; exact h2

theorem absBias_le (x : Nat) (h1 : accLo ≤ x) (h2 : x ≤ accHi) :
    absBias x ≤ 72057594037927936 := by
  unfold accLo at h1
  unfold accHi at h2
  unfold absBias biasV
  rw [Nat.max_def, Nat.min_def]
  by_cases h : x ≤ 4611686018427387904
  · rw [if_pos h, if_pos h]; omega
  · rw [if_neg h, if_neg h]; omega

theorem bandWR_le (NHI e : Nat) : bandWR NHI e ≤ NHI - e := Nat.min_le_right _ _

theorem bandWR_le' (NHI e : Nat) : bandWR NHI e ≤ 1 + e / 10 := Nat.min_le_left _ _

theorem bandIncR_le (NHI LG e : Nat) :
    bandIncR NHI LG e ≤ LG * bandWR NHI e + e := by
  unfold bandIncR
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
/-! ## Well-formedness -/

theorem blkA_wf (c : Cfg) : ∀ i ∈ blkA c, i.WF regCount := by
  intro i hi
  simp only [blkA, blkAP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkB_wf (c : Cfg) : ∀ i ∈ blkB c, i.WF regCount := by
  intro i hi
  simp only [blkB, blkBP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkC1_wf : ∀ i ∈ blkC1, i.WF regCount := by
  intro i hi
  simp only [blkC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkC2_wf : ∀ i ∈ blkC2, i.WF regCount := by
  intro i hi
  simp only [blkC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkD1_wf : ∀ i ∈ blkD1, i.WF regCount := by
  intro i hi
  simp only [blkD1, blkD1P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkD2_wf : ∀ i ∈ blkD2, i.WF regCount := by
  intro i hi
  simp only [blkD2, blkD2P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkE1_wf : ∀ i ∈ blkE1, i.WF regCount := by
  intro i hi
  simp only [blkE1, blkE1P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkE2_wf : ∀ i ∈ blkE2, i.WF regCount := by
  intro i hi
  simp only [blkE2, blkE2P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkF1a_wf (c : Cfg) : ∀ i ∈ blkF1a c, i.WF regCount := by
  intro i hi
  simp only [blkF1a, blkF1aP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkF1b_wf : ∀ i ∈ blkF1b, i.WF regCount := by
  intro i hi
  simp only [blkF1b, blkF1bP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkF2a_wf : ∀ i ∈ blkF2a, i.WF regCount := by
  intro i hi
  simp only [blkF2a, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkF2b_wf : ∀ i ∈ blkF2b, i.WF regCount := by
  intro i hi
  simp only [blkF2b, blkF2bP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem blkG_wf (c : Cfg) : ∀ i ∈ blkG c, i.WF regCount := by
  intro i hi
  simp only [blkG, blkGP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [body] at hi
  simp only [List.mem_append] at hi
  rcases hi with ((((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)
  · exact blkA_wf c i h
  · exact blkB_wf c i h
  · exact blkC1_wf i h
  · exact blkC2_wf i h
  · exact blkD1_wf i h
  · exact blkD2_wf i h
  · exact blkE1_wf i h
  · exact blkE2_wf i h
  · exact blkF1a_wf c i h
  · exact blkF1b_wf i h
  · exact blkF2a_wf i h
  · exact blkF2b_wf i h
  · exact blkG_wf c i h

theorem initBlock_wf (c : Cfg) : ∀ i ∈ initBlock c, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF]

theorem lProgram_wf (c : Cfg) : (lProgram c).WF :=
  ⟨by show (0 : Nat) < regCount; decide, initBlock_wf c, body_wf c,
    by intro i hi; cases hi⟩

end LeanCompCert.Ports.LiouvilleEllSweep
