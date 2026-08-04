import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.Rolled
import LeanCompCert.Verified.RegFrame
import LeanCompCert.Verified.BlockDefined
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
  decide (0 < c.e0) && decide (c.e0 ≤ c.nhi) && decide (c.lb0 ≤ lbCap) &&
  decide (c.rounds ≤ 4294967296) && decide (c.ex ≤ 4294967296) &&
  decide (c.nlo ≤ 4294967296)

/-- The side conditions of the denotation, unpacked. -/
theorem lFacts_of_ok {c : Cfg} (h : lOK c = true) :
    0 < c.lo ∧ 0 < c.ex ∧ c.dsm < c.dbg ∧
      c.rounds = c.ex * c.dsm + (c.dbg - c.dsm) ∧ 0 < c.rounds ∧
      c.lo + c.len ≤ c.nhi ∧ c.nhi ≤ 2 ^ 32 ∧ c.len * c.rounds ≤ M ∧
      c.dbg + 2 ≤ 2 ^ 32 ∧ 0 < c.e0 ∧ c.e0 ≤ c.nhi ∧ c.lb0 ≤ lbCap ∧
      c.rounds ≤ 4294967296 ∧ c.ex ≤ 4294967296 ∧ c.nlo ≤ 4294967296 := by
  rw [lOK] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

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

theorem obs_bad (s : RegState) : (obs s).bad = s 0 := rfl
theorem obs_acc (s : RegState) : (obs s).acc = s 1 := rfl
theorem obs_res (s : RegState) : (obs s).res = s 2 := rfl
theorem obs_par (s : RegState) : (obs s).par = s 3 := rfl
theorem obs_lb (s : RegState) : (obs s).lb = s 4 := rfl
theorem obs_ee (s : RegState) : (obs s).ee = s 5 := rfl

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


/-! ## The loop invariant, and the bits the model carries -/

/-- What the loop carries between rounds: every register a word, the violation
flag and the parity a bit, the accumulator inside its unconditional clamp, the
ladder inside its cap, and the band cursor a positive candidate at most `nhi`.
Every clause is structural — no gate is assumed. -/
def Inv (c : Cfg) (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 0 ≤ 1 ∧ accLo ≤ s 1 ∧ s 1 ≤ accHi ∧ s 3 ≤ 1 ∧
    s 4 ≤ lbCap ∧ 0 < s 5 ∧ s 5 ≤ c.nhi

theorem xorBit_le (a b : Nat) : xorBit a b ≤ 1 := by
  unfold xorBit
  by_cases h : a = b
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem stripStep_par_le (d : Nat) (rp : Nat × Nat) : (stripStep d rp).2 ≤ 1 := by
  show (if rp.1 - rp.1 / d * d = 0 then ((rp.1 / d : Nat), xorBit rp.2 1)
      else (rp.1, xorBit rp.2 0)).2 ≤ 1
  by_cases h : rp.1 - rp.1 / d * d = 0
  · rw [if_pos h]; exact xorBit_le _ _
  · rw [if_neg h]; exact xorBit_le _ _

theorem stripStep_res_le (d : Nat) (rp : Nat × Nat) : (stripStep d rp).1 ≤ rp.1 := by
  show (if rp.1 - rp.1 / d * d = 0 then ((rp.1 / d : Nat), xorBit rp.2 1)
      else (rp.1, xorBit rp.2 0)).1 ≤ rp.1
  by_cases h : rp.1 - rp.1 / d * d = 0
  · rw [if_pos h]; exact Nat.div_le_self _ _
  · rw [if_neg h]; exact Nat.le_refl _

theorem signOf_le (rp : Nat × Nat) : signOf rp ≤ 1 := xorBit_le _ _

private theorem sel_bridge (P : Prop) [Decidable P] (x y : Nat) :
    (if (if P then (1:Nat) else 0) = 1 then x else y) = (if P then x else y) := by
  by_cases h : P <;> simp [h]

private theorem ite_pair (P : Prop) [Decidable P] (a b x y : Nat) :
    (if P then ((a : Nat), (b : Nat)) else ((x : Nat), (y : Nat)))
      = ((if P then a else x), (if P then b else y)) := by
  by_cases h : P <;> simp [h]

/-! ### Numeric facts about the design constants -/

private theorem accLo_le_accHi' : accLo ≤ accHi := by decide
private theorem plScale_le_accLo : plScale ≤ accLo := by decide
private theorem accHi_add_lt : accHi + plScale < M := by decide
private theorem biasV_lt : biasV < M := by decide
private theorem accLo_lt_M : accLo < M := by decide
private theorem accHi_lt_M : accHi < M := by decide
private theorem shMask_lt : shMask < M := by decide
private theorem shBits_lt : shBits < M := by decide
private theorem ashCap_lt : ashCap < M := by decide
private theorem lbCap_lt : lbCap < M := by decide
private theorem rhsCap_lt : rhsCap < M := by decide
private theorem gateLo_lt : gateLo < M := by decide
private theorem gateHi_lt : gateHi < M := by decide
private theorem plScale_lt : plScale < M := by decide
private theorem lgScale_lt : lgScale < M := by decide
private theorem two32_val : (2:Nat) ^ 32 = 4294967296 := by decide
private theorem two32_lt_M : (4294967296 : Nat) < M := by decide
private theorem prodCap_lt : 1000 * (ashCap * lbCap) < M := by decide
private theorem lgw_lt : lgScale * 4294967296 + 4294967296 < M := by decide
private theorem lbCap_add_lt : lbCap + (lgScale * 4294967296 + 4294967296) < M := by decide
private theorem absCap_add : shMask + (72057594037927936 + 4294967296) < M := by decide
private theorem biasV_in : accLo ≤ biasV ∧ biasV ≤ accHi := by decide


private theorem widthW (NHI e : Nat) (h : NHI ≤ 4294967296) :
    bandWR NHI e ≤ 4294967296 :=
  Nat.le_trans (bandWR_le NHI e) (Nat.le_trans (Nat.sub_le _ _) h)

private theorem widthLGW (NHI e : Nat) (h : NHI ≤ 4294967296)
    (he : e ≤ 4294967296) : lgScale * bandWR NHI e + e < M := by
  have h1 : lgScale * bandWR NHI e ≤ lgScale * 4294967296 :=
    Nat.mul_le_mul (Nat.le_refl _) (widthW NHI e h)
  have h2 := lgw_lt
  omega

private theorem widthInc (NHI e : Nat) (h : NHI ≤ 4294967296) :
    bandIncR NHI lgScale e ≤ lgScale * 4294967296 + e := by
  have h1 := bandIncR_le NHI lgScale e
  have h2 : lgScale * bandWR NHI e ≤ lgScale * 4294967296 :=
    Nat.mul_le_mul (Nat.le_refl _) (widthW NHI e h)
  omega

private theorem widthLbInc (a b : Nat) (h1 : a ≤ lbCap)
    (h2 : b ≤ lgScale * 4294967296 + 4294967296) : a + b < M :=
  Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) lbCap_add_lt

private theorem widthEW (NHI e : Nat) (h : NHI ≤ 4294967296) (he : e ≤ NHI) :
    e + bandWR NHI e < M := by
  have h1 := bandWR_le NHI e
  have h2 := two32_lt_M
  omega

private theorem widthProd (a b : Nat) (h1 : a ≤ ashCap) (h2 : b ≤ lbCap) :
    1000 * (a * b) < M := by
  have h3 : a * b ≤ ashCap * lbCap := Nat.mul_le_mul h1 h2
  have h4 : 1000 * (a * b) ≤ 1000 * (ashCap * lbCap) :=
    Nat.mul_le_mul (Nat.le_refl 1000) h3
  have h5 := prodCap_lt
  omega

private theorem widthAbs (ab n : Nat) (h1 : ab ≤ 72057594037927936)
    (h2 : n ≤ 4294967296) : shMask + (ab + n) < M := by
  have := absCap_add
  omega

private theorem widthAccLe (a pn : Nat) (h1 : accLo ≤ a) (h2 : pn ≤ plScale) :
    pn ≤ a := by
  have := plScale_le_accLo
  omega

private theorem widthAccAdd (a pn : Nat) (h1 : a ≤ accHi) (h2 : pn ≤ plScale) :
    a + pn < M := by
  have := accHi_add_lt
  omega

/-! ## The whole body simulates `gstep` -/

set_option maxHeartbeats 4000000 in
/-- **The body simulates the abstract step**, observed on the six carried
registers. -/
theorem body_obs (c : Cfg) (idx : Nat) (s : RegState) (hOK : lOK c = true)
    (hidx : idx < c.len * c.rounds) (hI : Inv c s) :
    obs (srun idx s (body c)) = gstep c idx (obs s) := by
  obtain ⟨hlo, hex, hdsm, hrd, hR, hlolen, hnhi32, hlenR, hdbg, he0p, he0n, hlb0,
    hRc, hEXc, hNLOc⟩ := lFacts_of_ok hOK
  obtain ⟨hsw, hbd, haclo, hachi, hp3, hlb4, hee5p, hee5n⟩ := hI
  rw [two32_val] at hnhi32 hdbg
  have hMbig : (4294967296 : Nat) < M := two32_lt_M
  have hidxM : idx < M := Nat.lt_of_lt_of_le hidx hlenR
  have hlenpos : 0 < c.len := by
    rcases Nat.eq_zero_or_pos c.len with h | h
    · rw [h, Nat.zero_mul] at hidx; omega
    · exact h
  have hdivlt : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hnlt : c.lo + idx / c.rounds < c.nhi := by omega
  have hnM : c.lo + idx / c.rounds < M := by omega
  have hnpos : 0 < c.lo + idx / c.rounds :=
    Nat.lt_of_lt_of_le hlo (Nat.le_add_right _ _)
  have hqM32 : idx % c.rounds < 4294967296 := Nat.lt_of_lt_of_le hqlt hRc
  have hqM : idx % c.rounds < M := Nat.lt_trans hqM32 hMbig
  have hee5c : s 5 ≤ 4294967296 := Nat.le_trans hee5n hnhi32
  have hnc : c.lo + idx / c.rounds ≤ 4294967296 :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le hnlt hnhi32)
  have hnhiM : c.nhi < M := Nat.lt_of_le_of_lt hnhi32 hMbig
  have hNLOM : c.nlo < M := Nat.lt_of_le_of_lt hNLOc hMbig
  have hloM : c.lo < M := by omega
  have hRM : c.rounds < M := by omega
  have hRM1 : c.rounds - 1 < M := by omega
  have hEXM : c.ex < M := by omega
  have hEDSle : c.ex * c.dsm ≤ c.rounds := by omega
  have hEDSM : c.ex * c.dsm < M := by omega
  have hDS2M : c.dsm + 2 < M := by omega
  -- the block split
  have hassoc : body c = blkAP c.rounds (c.rounds - 1) c.lo ++
      (blkBP c.ex (c.ex * c.dsm) (c.dsm + 2) ++ (blkC1 ++ (blkC2 ++
        (blkD1P plScale ++ (blkD2P accLo accHi ++ (blkE1P biasV ++
          (blkE2P shMask shBits ashCap ++ (blkF1aP c.nhi ++ (blkF1bP lgScale ++
            (blkF2a ++ (blkF2bP lbCap ++
              blkGP c.nlo rhsCap gateLo gateHi))))))))))) := by
    show blkAP c.rounds (c.rounds - 1) c.lo ++ blkBP c.ex (c.ex * c.dsm) (c.dsm + 2)
        ++ blkC1 ++ blkC2 ++ blkD1P plScale ++ blkD2P accLo accHi ++ blkE1P biasV
        ++ blkE2P shMask shBits ashCap ++ blkF1aP c.nhi ++ blkF1bP lgScale
        ++ blkF2a ++ blkF2bP lbCap ++ blkGP c.nlo rhsCap gateLo gateHi = _
    simp only [List.append_assoc]
  obtain ⟨sA, hgA⟩ : ∃ t, srun idx s (blkAP c.rounds (c.rounds - 1) c.lo) = t :=
    ⟨_, rfl⟩
  obtain ⟨sB, hgB⟩ : ∃ t, srun idx sA (blkBP c.ex (c.ex * c.dsm) (c.dsm + 2)) = t :=
    ⟨_, rfl⟩
  obtain ⟨sC1, hgC1⟩ : ∃ t, srun idx sB blkC1 = t := ⟨_, rfl⟩
  obtain ⟨sC2, hgC2⟩ : ∃ t, srun idx sC1 blkC2 = t := ⟨_, rfl⟩
  obtain ⟨sD1, hgD1⟩ : ∃ t, srun idx sC2 (blkD1P plScale) = t := ⟨_, rfl⟩
  obtain ⟨sD2, hgD2⟩ : ∃ t, srun idx sD1 (blkD2P accLo accHi) = t := ⟨_, rfl⟩
  obtain ⟨sE1, hgE1⟩ : ∃ t, srun idx sD2 (blkE1P biasV) = t := ⟨_, rfl⟩
  obtain ⟨sE2, hgE2⟩ : ∃ t, srun idx sE1 (blkE2P shMask shBits ashCap) = t := ⟨_, rfl⟩
  obtain ⟨sFa, hgFa⟩ : ∃ t, srun idx sE2 (blkF1aP c.nhi) = t := ⟨_, rfl⟩
  obtain ⟨sFb, hgFb⟩ : ∃ t, srun idx sFa (blkF1bP lgScale) = t := ⟨_, rfl⟩
  obtain ⟨sG1, hgG1⟩ : ∃ t, srun idx sFb blkF2a = t := ⟨_, rfl⟩
  obtain ⟨sG2, hgG2⟩ : ∃ t, srun idx sG1 (blkF2bP lbCap) = t := ⟨_, rfl⟩
  have hsplit : srun idx s (body c) = srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) := by
    rw [hassoc, srun_append, srun_append, srun_append, srun_append, srun_append,
      srun_append, srun_append, srun_append, srun_append, srun_append, srun_append,
      srun_append, hgA, hgB, hgC1, hgC2, hgD1, hgD2, hgE1, hgE2, hgFa, hgFb, hgG1,
      hgG2]
  -- word bounds, stage by stage
  have hsA : ∀ j, sA j < M := by
    intro j; rw [← hgA]; exact srun_lt_of_lt idx _ s hsw j
  have hsB : ∀ j, sB j < M := by
    intro j; rw [← hgB]; exact srun_lt_of_lt idx _ sA hsA j
  have hsC1 : ∀ j, sC1 j < M := by
    intro j; rw [← hgC1]; exact srun_lt_of_lt idx _ sB hsB j
  have hsC2 : ∀ j, sC2 j < M := by
    intro j; rw [← hgC2]; exact srun_lt_of_lt idx _ sC1 hsC1 j
  have hsD1 : ∀ j, sD1 j < M := by
    intro j; rw [← hgD1]; exact srun_lt_of_lt idx _ sC2 hsC2 j
  have hsD2 : ∀ j, sD2 j < M := by
    intro j; rw [← hgD2]; exact srun_lt_of_lt idx _ sD1 hsD1 j
  have hsE1 : ∀ j, sE1 j < M := by
    intro j; rw [← hgE1]; exact srun_lt_of_lt idx _ sD2 hsD2 j
  have hsE2 : ∀ j, sE2 j < M := by
    intro j; rw [← hgE2]; exact srun_lt_of_lt idx _ sE1 hsE1 j
  have hsFa : ∀ j, sFa j < M := by
    intro j; rw [← hgFa]; exact srun_lt_of_lt idx _ sE2 hsE2 j
  have hsFb : ∀ j, sFb j < M := by
    intro j; rw [← hgFb]; exact srun_lt_of_lt idx _ sFa hsFa j
  have hsG1 : ∀ j, sG1 j < M := by
    intro j; rw [← hgG1]; exact srun_lt_of_lt idx _ sFb hsFb j
  have hsG2 : ∀ j, sG2 j < M := by
    intro j; rw [← hgG2]; exact srun_lt_of_lt idx _ sG1 hsG1 j
  -- stage A
  obtain ⟨hA6, hA7, hA8, hA9, hA10, _⟩ :=
    blkAP_spec idx c.rounds (c.rounds - 1) c.lo s hR hRM hRM1 hloM hidxM hnM
  rw [hgA] at hA6 hA7 hA8 hA9 hA10
  -- stage B
  obtain ⟨_, hB15, _⟩ := blkBP_spec idx c.ex (c.ex * c.dsm) (c.dsm + 2)
    (idx % c.rounds) sA hA7 hex hEXM hEDSM hDS2M hqM
    (by have h1 : idx % c.rounds / c.ex ≤ idx % c.rounds := Nat.div_le_self _ _
        have h2 : (4294967298 : Nat) < M := by decide
        omega)
    (by have h1 : idx % c.rounds - c.ex * c.dsm ≤ idx % c.rounds := Nat.sub_le _ _
        have h2 : (8589934592 : Nat) < M := by decide
        omega)
  rw [hgB] at hB15
  have hdOf : sB 15 = divOf c (idx % c.rounds) := hB15
  have hdpos : 0 < divOf c (idx % c.rounds) := divOf_pos c _
  -- carry the A-stage reads through B
  have hB8 : sB 8 = c.lo + idx / c.rounds := by
    rw [← hA8, ← hgB]; exact RegFrame.srun_frame idx 8 _ (by rfl) sA
  have hB9 : sB 9 = (if idx % c.rounds = 0 then 1 else 0) := by
    rw [← hA9, ← hgB]; exact RegFrame.srun_frame idx 9 _ (by rfl) sA
  have hB10 : sB 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hA10, ← hgB]; exact RegFrame.srun_frame idx 10 _ (by rfl) sA
  have hA2 : sA 2 = s 2 := by rw [← hgA]; exact RegFrame.srun_frame idx 2 _ (by rfl) s
  have hA3 : sA 3 = s 3 := by rw [← hgA]; exact RegFrame.srun_frame idx 3 _ (by rfl) s
  have hA1 : sA 1 = s 1 := by rw [← hgA]; exact RegFrame.srun_frame idx 1 _ (by rfl) s
  have hA0 : sA 0 = s 0 := by rw [← hgA]; exact RegFrame.srun_frame idx 0 _ (by rfl) s
  have hA4 : sA 4 = s 4 := by rw [← hgA]; exact RegFrame.srun_frame idx 4 _ (by rfl) s
  have hA5 : sA 5 = s 5 := by rw [← hgA]; exact RegFrame.srun_frame idx 5 _ (by rfl) s
  have hB2 : sB 2 = s 2 := by
    rw [← hA2, ← hgB]; exact RegFrame.srun_frame idx 2 _ (by rfl) sA
  have hB3 : sB 3 = s 3 := by
    rw [← hA3, ← hgB]; exact RegFrame.srun_frame idx 3 _ (by rfl) sA
  have hB1 : sB 1 = s 1 := by
    rw [← hA1, ← hgB]; exact RegFrame.srun_frame idx 1 _ (by rfl) sA
  have hB0 : sB 0 = s 0 := by
    rw [← hA0, ← hgB]; exact RegFrame.srun_frame idx 0 _ (by rfl) sA
  have hB4 : sB 4 = s 4 := by
    rw [← hA4, ← hgB]; exact RegFrame.srun_frame idx 4 _ (by rfl) sA
  have hB5 : sB 5 = s 5 := by
    rw [← hA5, ← hgB]; exact RegFrame.srun_frame idx 5 _ (by rfl) sA
  -- stage C1
  obtain ⟨hC116, hC117, _⟩ := blkC1_spec idx (c.lo + idx / c.rounds) (s 2) (s 3)
    (if idx % c.rounds = 0 then 1 else 0) sB hB9 hB8 hB2 hB3 (bitLe _) hnM
    (hsw 2) (hsw 3)
  rw [hgC1, sel_bridge] at hC116
  rw [hgC1, sel_bridge] at hC117
  have hC115 : sC1 15 = divOf c (idx % c.rounds) := by
    rw [← hdOf, ← hgC1]; exact RegFrame.srun_frame idx 15 _ (by rfl) sB
  have hC18 : sC1 8 = c.lo + idx / c.rounds := by
    rw [← hB8, ← hgC1]; exact RegFrame.srun_frame idx 8 _ (by rfl) sB
  have hC110 : sC1 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hB10, ← hgC1]; exact RegFrame.srun_frame idx 10 _ (by rfl) sB
  have hC11 : sC1 1 = s 1 := by
    rw [← hB1, ← hgC1]; exact RegFrame.srun_frame idx 1 _ (by rfl) sB
  have hC10 : sC1 0 = s 0 := by
    rw [← hB0, ← hgC1]; exact RegFrame.srun_frame idx 0 _ (by rfl) sB
  have hC14 : sC1 4 = s 4 := by
    rw [← hB4, ← hgC1]; exact RegFrame.srun_frame idx 4 _ (by rfl) sB
  have hC15 : sC1 5 = s 5 := by
    rw [← hB5, ← hgC1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sB
  -- the round's incoming pair, in the model's shape
  have hpairIn :
      ((if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2),
        (if idx % c.rounds = 0 then (0:Nat) else s 3))
        = (if idx % c.rounds = 0 then ((c.lo + idx / c.rounds : Nat), (0:Nat))
           else (s 2, s 3)) := (ite_pair _ _ _ _ _).symm
  obtain ⟨hC22, hC23, hC224, _⟩ := blkC2_spec idx
    (if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2)
    (if idx % c.rounds = 0 then 0 else s 3) (divOf c (idx % c.rounds)) sC1
    hC116 hC117 hC115 hdpos
    (by by_cases h : idx % c.rounds = 0
        · rw [if_pos h]; exact hnM
        · rw [if_neg h]; exact hsw 2)
    (by by_cases h : idx % c.rounds = 0
        · rw [if_pos h]; omega
        · rw [if_neg h]; exact hp3)
  rw [hgC2, hpairIn] at hC22 hC23 hC224
  have hC28 : sC2 8 = c.lo + idx / c.rounds := by
    rw [← hC18, ← hgC2]; exact RegFrame.srun_frame idx 8 _ (by rfl) sC1
  have hC210 : sC2 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hC110, ← hgC2]; exact RegFrame.srun_frame idx 10 _ (by rfl) sC1
  have hC21 : sC2 1 = s 1 := by
    rw [← hC11, ← hgC2]; exact RegFrame.srun_frame idx 1 _ (by rfl) sC1
  have hC20 : sC2 0 = s 0 := by
    rw [← hC10, ← hgC2]; exact RegFrame.srun_frame idx 0 _ (by rfl) sC1
  have hC24 : sC2 4 = s 4 := by
    rw [← hC14, ← hgC2]; exact RegFrame.srun_frame idx 4 _ (by rfl) sC1
  have hC25 : sC2 5 = s 5 := by
    rw [← hC15, ← hgC2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sC1
  -- stage D1: the signed accumulator
  have hpn : plScale / (c.lo + idx / c.rounds) ≤ plScale := Nat.div_le_self _ _
  obtain ⟨_, hD127, _⟩ := blkD1P_spec idx plScale (c.lo + idx / c.rounds)
    (signOf (stripStep (divOf c (idx % c.rounds))
      (if idx % c.rounds = 0 then ((c.lo + idx / c.rounds : Nat), (0:Nat))
       else (s 2, s 3))))
    (if idx % c.rounds = c.rounds - 1 then 1 else 0) (s 1) sC2
    hC28 hC224 hC210 hC21 hnpos plScale_lt (signOf_le _) (bitLe _)
    (widthAccLe _ _ haclo hpn) (widthAccAdd _ _ hachi hpn)
  rw [hgD1] at hD127
  have hD18 : sD1 8 = c.lo + idx / c.rounds := by
    rw [← hC28, ← hgD1]; exact RegFrame.srun_frame idx 8 _ (by rfl) sC2
  have hD110 : sD1 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hC210, ← hgD1]; exact RegFrame.srun_frame idx 10 _ (by rfl) sC2
  have hD10 : sD1 0 = s 0 := by
    rw [← hC20, ← hgD1]; exact RegFrame.srun_frame idx 0 _ (by rfl) sC2
  have hD12 : sD1 2 = sC2 2 := by
    rw [← hgD1]; exact RegFrame.srun_frame idx 2 _ (by rfl) sC2
  have hD13 : sD1 3 = sC2 3 := by
    rw [← hgD1]; exact RegFrame.srun_frame idx 3 _ (by rfl) sC2
  have hD14 : sD1 4 = s 4 := by
    rw [← hC24, ← hgD1]; exact RegFrame.srun_frame idx 4 _ (by rfl) sC2
  have hD15 : sD1 5 = s 5 := by
    rw [← hC25, ← hgD1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sC2
  -- stage D2: the clamp
  obtain ⟨hD228, hD21, _⟩ := blkD2P_spec idx accLo accHi (sD1 27) sD1 rfl
    accLo_lt_M accHi_lt_M (hsD1 27)
  rw [hgD2] at hD228 hD21
  have hD227 : sD2 27 = sD1 27 := by
    rw [← hgD2]; exact RegFrame.srun_frame idx 27 _ (by rfl) sD1
  have hD28 : sD2 8 = c.lo + idx / c.rounds := by
    rw [← hD18, ← hgD2]; exact RegFrame.srun_frame idx 8 _ (by rfl) sD1
  have hD210 : sD2 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hD110, ← hgD2]; exact RegFrame.srun_frame idx 10 _ (by rfl) sD1
  have hD20 : sD2 0 = s 0 := by
    rw [← hD10, ← hgD2]; exact RegFrame.srun_frame idx 0 _ (by rfl) sD1
  have hD22 : sD2 2 = sC2 2 := by
    rw [← hD12, ← hgD2]; exact RegFrame.srun_frame idx 2 _ (by rfl) sD1
  have hD23 : sD2 3 = sC2 3 := by
    rw [← hD13, ← hgD2]; exact RegFrame.srun_frame idx 3 _ (by rfl) sD1
  have hD24 : sD2 4 = s 4 := by
    rw [← hD14, ← hgD2]; exact RegFrame.srun_frame idx 4 _ (by rfl) sD1
  have hD25 : sD2 5 = s 5 := by
    rw [← hD15, ← hgD2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sD1
  -- stage E1: |acc − 2⁶²|
  obtain ⟨hE131, _⟩ := blkE1P_spec idx biasV (sD2 28) sD2 rfl biasV_lt (hsD2 28)
  rw [hgE1] at hE131
  have habsle : max (sD2 28) biasV - min (sD2 28) biasV ≤ 72057594037927936 := by
    have h1 : accLo ≤ sD2 28 := by rw [hD228]; exact accClamp_ge _
    have h2 : sD2 28 ≤ accHi := by rw [hD228]; exact accClamp_le _
    exact absBias_le _ h1 h2
  have hE18 : sE1 8 = c.lo + idx / c.rounds := by
    rw [← hD28, ← hgE1]; exact RegFrame.srun_frame idx 8 _ (by rfl) sD2
  have hE110 : sE1 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hD210, ← hgE1]; exact RegFrame.srun_frame idx 10 _ (by rfl) sD2
  have hE127 : sE1 27 = sD1 27 := by
    rw [← hD227, ← hgE1]; exact RegFrame.srun_frame idx 27 _ (by rfl) sD2
  have hE10 : sE1 0 = s 0 := by
    rw [← hD20, ← hgE1]; exact RegFrame.srun_frame idx 0 _ (by rfl) sD2
  have hE11 : sE1 1 = sD2 1 := by
    rw [← hgE1]; exact RegFrame.srun_frame idx 1 _ (by rfl) sD2
  have hE12 : sE1 2 = sC2 2 := by
    rw [← hD22, ← hgE1]; exact RegFrame.srun_frame idx 2 _ (by rfl) sD2
  have hE13 : sE1 3 = sC2 3 := by
    rw [← hD23, ← hgE1]; exact RegFrame.srun_frame idx 3 _ (by rfl) sD2
  have hE14 : sE1 4 = s 4 := by
    rw [← hD24, ← hgE1]; exact RegFrame.srun_frame idx 4 _ (by rfl) sD2
  have hE15 : sE1 5 = s 5 := by
    rw [← hD25, ← hgE1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sD2
  -- stage E2: the shifted left-hand side
  obtain ⟨_, hE235, hE234, _⟩ := blkE2P_spec idx shMask shBits ashCap
    (max (sD2 28) biasV - min (sD2 28) biasV) (c.lo + idx / c.rounds) sE1
    hE131 hE18 shMask_lt shBits_lt ashCap_lt (widthAbs _ _ habsle hnc)
  rw [hgE2] at hE235 hE234
  have hE28 : sE2 8 = c.lo + idx / c.rounds := by
    rw [← hE18, ← hgE2]; exact RegFrame.srun_frame idx 8 _ (by rfl) sE1
  have hE210 : sE2 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hE110, ← hgE2]; exact RegFrame.srun_frame idx 10 _ (by rfl) sE1
  have hE227 : sE2 27 = sD1 27 := by
    rw [← hE127, ← hgE2]; exact RegFrame.srun_frame idx 27 _ (by rfl) sE1
  have hE20 : sE2 0 = s 0 := by
    rw [← hE10, ← hgE2]; exact RegFrame.srun_frame idx 0 _ (by rfl) sE1
  have hE21 : sE2 1 = sD2 1 := by
    rw [← hE11, ← hgE2]; exact RegFrame.srun_frame idx 1 _ (by rfl) sE1
  have hE22 : sE2 2 = sC2 2 := by
    rw [← hE12, ← hgE2]; exact RegFrame.srun_frame idx 2 _ (by rfl) sE1
  have hE23 : sE2 3 = sC2 3 := by
    rw [← hE13, ← hgE2]; exact RegFrame.srun_frame idx 3 _ (by rfl) sE1
  have hE24 : sE2 4 = s 4 := by
    rw [← hE14, ← hgE2]; exact RegFrame.srun_frame idx 4 _ (by rfl) sE1
  have hE25 : sE2 5 = s 5 := by
    rw [← hE15, ← hgE2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sE1
  -- stage F1a: the band width step
  obtain ⟨hFa38, _⟩ := blkF1aP_spec idx c.nhi (s 5) sE2 hE25 hee5p hee5n hnhiM
  rw [hgFa] at hFa38
  have hwle : bandWR c.nhi (s 5) ≤ 4294967296 := widthW c.nhi (s 5) hnhi32
  have hFa5 : sFa 5 = s 5 := by
    rw [← hE25, ← hgFa]; exact RegFrame.srun_frame idx 5 _ (by rfl) sE2
  have hFa8 : sFa 8 = c.lo + idx / c.rounds := by
    rw [← hE28, ← hgFa]; exact RegFrame.srun_frame idx 8 _ (by rfl) sE2
  have hFa10 : sFa 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hE210, ← hgFa]; exact RegFrame.srun_frame idx 10 _ (by rfl) sE2
  have hFa27 : sFa 27 = sD1 27 := by
    rw [← hE227, ← hgFa]; exact RegFrame.srun_frame idx 27 _ (by rfl) sE2
  have hFa0 : sFa 0 = s 0 := by
    rw [← hE20, ← hgFa]; exact RegFrame.srun_frame idx 0 _ (by rfl) sE2
  have hFa1 : sFa 1 = sD2 1 := by
    rw [← hE21, ← hgFa]; exact RegFrame.srun_frame idx 1 _ (by rfl) sE2
  have hFa2 : sFa 2 = sC2 2 := by
    rw [← hE22, ← hgFa]; exact RegFrame.srun_frame idx 2 _ (by rfl) sE2
  have hFa3 : sFa 3 = sC2 3 := by
    rw [← hE23, ← hgFa]; exact RegFrame.srun_frame idx 3 _ (by rfl) sE2
  have hFa4 : sFa 4 = s 4 := by
    rw [← hE24, ← hgFa]; exact RegFrame.srun_frame idx 4 _ (by rfl) sE2
  have hFa34 : sFa 34 = sE2 34 := by
    rw [← hgFa]; exact RegFrame.srun_frame idx 34 _ (by rfl) sE2
  have hFa35 : sFa 35 = sE2 35 := by
    rw [← hgFa]; exact RegFrame.srun_frame idx 35 _ (by rfl) sE2
  -- stage F1b: the band log step
  obtain ⟨hFb40, _⟩ := blkF1bP_spec idx lgScale (s 5) (bandWR c.nhi (s 5)) sFa
    hFa38 hFa5 hee5p lgScale_lt (widthLGW c.nhi (s 5) hnhi32 hee5c)
  rw [hgFb] at hFb40
  have hincle : bandIncR c.nhi lgScale (s 5) ≤ lgScale * 4294967296 + 4294967296 :=
    Nat.le_trans (widthInc c.nhi (s 5) hnhi32) (Nat.add_le_add_left hee5c _)
  have hFb5 : sFb 5 = s 5 := by
    rw [← hFa5, ← hgFb]; exact RegFrame.srun_frame idx 5 _ (by rfl) sFa
  have hFb38 : sFb 38 = bandWR c.nhi (s 5) := by
    rw [← hFa38, ← hgFb]; exact RegFrame.srun_frame idx 38 _ (by rfl) sFa
  have hFb8 : sFb 8 = c.lo + idx / c.rounds := by
    rw [← hFa8, ← hgFb]; exact RegFrame.srun_frame idx 8 _ (by rfl) sFa
  have hFb10 : sFb 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hFa10, ← hgFb]; exact RegFrame.srun_frame idx 10 _ (by rfl) sFa
  have hFb27 : sFb 27 = sD1 27 := by
    rw [← hFa27, ← hgFb]; exact RegFrame.srun_frame idx 27 _ (by rfl) sFa
  have hFb0 : sFb 0 = s 0 := by
    rw [← hFa0, ← hgFb]; exact RegFrame.srun_frame idx 0 _ (by rfl) sFa
  have hFb1 : sFb 1 = sD2 1 := by
    rw [← hFa1, ← hgFb]; exact RegFrame.srun_frame idx 1 _ (by rfl) sFa
  have hFb2 : sFb 2 = sC2 2 := by
    rw [← hFa2, ← hgFb]; exact RegFrame.srun_frame idx 2 _ (by rfl) sFa
  have hFb3 : sFb 3 = sC2 3 := by
    rw [← hFa3, ← hgFb]; exact RegFrame.srun_frame idx 3 _ (by rfl) sFa
  have hFb4 : sFb 4 = s 4 := by
    rw [← hFa4, ← hgFb]; exact RegFrame.srun_frame idx 4 _ (by rfl) sFa
  have hFb34 : sFb 34 = sE2 34 := by
    rw [← hFa34, ← hgFb]; exact RegFrame.srun_frame idx 34 _ (by rfl) sFa
  have hFb35 : sFb 35 = sE2 35 := by
    rw [← hFa35, ← hgFb]; exact RegFrame.srun_frame idx 35 _ (by rfl) sFa
  -- stage F2a: the advance decision
  obtain ⟨hG142, hG143, _⟩ := blkF2a_spec idx (c.lo + idx / c.rounds) (s 5) (s 4)
    (bandIncR c.nhi lgScale (s 5))
    (if idx % c.rounds = c.rounds - 1 then 1 else 0) sFb
    hFb8 hFb5 hFb4 hFb10 hFb40 (bitLe _) (widthLbInc _ _ hlb4 hincle)
  rw [hgG1] at hG142 hG143
  have hG138 : sG1 38 = bandWR c.nhi (s 5) := by
    rw [← hFb38, ← hgG1]; exact RegFrame.srun_frame idx 38 _ (by rfl) sFb
  have hG15 : sG1 5 = s 5 := by
    rw [← hFb5, ← hgG1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sFb
  have hG18 : sG1 8 = c.lo + idx / c.rounds := by
    rw [← hFb8, ← hgG1]; exact RegFrame.srun_frame idx 8 _ (by rfl) sFb
  have hG110 : sG1 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hFb10, ← hgG1]; exact RegFrame.srun_frame idx 10 _ (by rfl) sFb
  have hG127 : sG1 27 = sD1 27 := by
    rw [← hFb27, ← hgG1]; exact RegFrame.srun_frame idx 27 _ (by rfl) sFb
  have hG10 : sG1 0 = s 0 := by
    rw [← hFb0, ← hgG1]; exact RegFrame.srun_frame idx 0 _ (by rfl) sFb
  have hG11 : sG1 1 = sD2 1 := by
    rw [← hFb1, ← hgG1]; exact RegFrame.srun_frame idx 1 _ (by rfl) sFb
  have hG12 : sG1 2 = sC2 2 := by
    rw [← hFb2, ← hgG1]; exact RegFrame.srun_frame idx 2 _ (by rfl) sFb
  have hG13 : sG1 3 = sC2 3 := by
    rw [← hFb3, ← hgG1]; exact RegFrame.srun_frame idx 3 _ (by rfl) sFb
  have hG134 : sG1 34 = sE2 34 := by
    rw [← hFb34, ← hgG1]; exact RegFrame.srun_frame idx 34 _ (by rfl) sFb
  have hG135 : sG1 35 = sE2 35 := by
    rw [← hFb35, ← hgG1]; exact RegFrame.srun_frame idx 35 _ (by rfl) sFb
  -- stage F2b: the clamp and the cursor
  have hadvle : (if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0) *
      (if c.lo + idx / c.rounds = s 5 then (1:Nat) else 0) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul (bitLe _) (bitLe _)) (by omega)
  obtain ⟨hG244, hG245, hG24, hG25, _⟩ := blkF2bP_spec idx lbCap
    (s 4 + (if idx % c.rounds = c.rounds - 1 then 1 else 0) *
      (if c.lo + idx / c.rounds = s 5 then 1 else 0) *
      bandIncR c.nhi lgScale (s 5))
    ((if idx % c.rounds = c.rounds - 1 then 1 else 0) *
      (if c.lo + idx / c.rounds = s 5 then 1 else 0))
    (bandWR c.nhi (s 5)) (s 5) sG1 hG143 hG142 hG138 hG15 hadvle lbCap_lt
    (widthLbInc _ _ hlb4 (Nat.le_trans (mul_bit_le _ _ hadvle) hincle))
    (widthEW c.nhi (s 5) hnhi32 hee5n)
  rw [hgG2] at hG244 hG245 hG24 hG25
  have hG28 : sG2 8 = c.lo + idx / c.rounds := by
    rw [← hG18, ← hgG2]; exact RegFrame.srun_frame idx 8 _ (by rfl) sG1
  have hG210 : sG2 10 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [← hG110, ← hgG2]; exact RegFrame.srun_frame idx 10 _ (by rfl) sG1
  have hG227 : sG2 27 = sD1 27 := by
    rw [← hG127, ← hgG2]; exact RegFrame.srun_frame idx 27 _ (by rfl) sG1
  have hG20 : sG2 0 = s 0 := by
    rw [← hG10, ← hgG2]; exact RegFrame.srun_frame idx 0 _ (by rfl) sG1
  have hG21 : sG2 1 = sD2 1 := by
    rw [← hG11, ← hgG2]; exact RegFrame.srun_frame idx 1 _ (by rfl) sG1
  have hG22 : sG2 2 = sC2 2 := by
    rw [← hG12, ← hgG2]; exact RegFrame.srun_frame idx 2 _ (by rfl) sG1
  have hG23 : sG2 3 = sC2 3 := by
    rw [← hG13, ← hgG2]; exact RegFrame.srun_frame idx 3 _ (by rfl) sG1
  have hG234 : sG2 34 = sE2 34 := by
    rw [← hG134, ← hgG2]; exact RegFrame.srun_frame idx 34 _ (by rfl) sG1
  have hG235 : sG2 35 = sE2 35 := by
    rw [← hG135, ← hgG2]; exact RegFrame.srun_frame idx 35 _ (by rfl) sG1
  -- stage G: the row test
  have hashle : sE2 34 ≤ ashCap := by rw [hE234]; exact Nat.min_le_right _ _
  have hlbCle : sG2 45 ≤ lbCap := by rw [hG245]; exact Nat.min_le_right _ _
  obtain ⟨hGout, _⟩ := blkGP_spec idx c.nlo rhsCap gateLo gateHi
    (c.lo + idx / c.rounds) (sE2 34) (sG2 45) (sE2 35) (sG2 44) (sD1 27)
    (if idx % c.rounds = c.rounds - 1 then 1 else 0) (s 0) sG2
    hG28 hG234 rfl hG235 rfl hG227 hG210 hG20
    (by rw [hE235]; exact bitLe _) (by rw [hG244]; exact bitLe _) (bitLe _) hbd
    hNLOM rhsCap_lt gateLo_lt gateHi_lt hnM (hsD1 27)
    (widthProd _ _ hashle hlbCle)
  rw [hE234, hE235, hG244, hG245, hD228, hD127] at hGout
  -- assemble
  rw [hsplit]
  refine Abs.eq_of ?_ ?_ ?_ ?_ ?_ ?_
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 0 = _
    rw [hGout]
    rfl
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 1 = _
    rw [RegFrame.srun_frame idx 1 _ (by rfl) sG2, hG21, hD21, hD127]
    rfl
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 2 = _
    rw [RegFrame.srun_frame idx 2 _ (by rfl) sG2, hG22, hC22]
    rfl
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 3 = _
    rw [RegFrame.srun_frame idx 3 _ (by rfl) sG2, hG23, hC23]
    rfl
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 4 = _
    rw [RegFrame.srun_frame idx 4 _ (by rfl) sG2, hG24]
    rfl
  · show srun idx sG2 (blkGP c.nlo rhsCap gateLo gateHi) 5 = _
    rw [RegFrame.srun_frame idx 5 _ (by rfl) sG2, hG25]
    rfl


/-! ## Definedness

Every division in the body is by a nonzero literal or by a register the block
containing it never writes.  Two generic shapes cover all six. -/

/-- A block whose only divisions are by one register the block never writes. -/
theorem divReg_defined (k r : Nat) : ∀ (l : List Instr),
    (∀ i ∈ l, sdest i ≠ r) →
    (∀ i ∈ l, NoDivI i = true ∨
      ∃ d op a, i = .binop d op a (.reg r) ∧ (op = Op.udiv ∨ op = Op.urem)) →
    ∀ s : RegState, ¬ (s r = 0) → SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro _ _ s _; exact trivial
  | cons i rest ih =>
      intro hdest hshape s hr
      have hhead : SDefined k s i := by
        rcases hshape i (by simp) with hnd | ⟨d, op, a, rfl, hop⟩
        · exact BlockDefined.sDefined_of_noDiv hnd
        · rcases hop with rfl | rfl
          · exact BlockDefined.sDefined_udiv (by show ¬ (s r = 0); exact hr)
          · exact BlockDefined.sDefined_urem (by show ¬ (s r = 0); exact hr)
      refine ⟨hhead, ?_⟩
      refine ih (fun j hj => hdest j (by simp [hj]))
        (fun j hj => hshape j (by simp [hj])) _ ?_
      have hkeep : (s.set (sdest i) (sval k s i)) r = s r := by
        show (if r = sdest i then sval k s i else s r) = s r
        rw [if_neg (fun h => (hdest i (by simp)) h.symm)]
      rw [hkeep]
      exact hr

/-- A block whose only divisions are by nonzero literals. -/
theorem divLit_defined (k : Nat) : ∀ (l : List Instr),
    (∀ i ∈ l, NoDivI i = true ∨
      ∃ d op a L, i = .binop d op a (.lit L) ∧ (op = Op.udiv ∨ op = Op.urem) ∧
        ¬ (L % M = 0)) →
    ∀ s : RegState, SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro _ s; exact trivial
  | cons i rest ih =>
      intro hshape s
      have hhead : SDefined k s i := by
        rcases hshape i (by simp) with hnd | ⟨d, op, a, L, rfl, hop, hL⟩
        · exact BlockDefined.sDefined_of_noDiv hnd
        · rcases hop with rfl | rfl
          · exact BlockDefined.sDefined_udiv (by show ¬ (L % M = 0); exact hL)
          · exact BlockDefined.sDefined_urem (by show ¬ (L % M = 0); exact hL)
      exact ⟨hhead, ih (fun j hj => hshape j (by simp [hj])) _⟩

theorem blkAP_defined (k R RM1 LO : Nat) (s : RegState) (hR : ¬ (R % M = 0)) :
    SAllDefined k s (blkAP R RM1 LO) := by
  refine divLit_defined k (blkAP R RM1 LO) ?_ s
  intro i hi
  simp only [blkAP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h <;> subst h
  · exact Or.inr ⟨6, .udiv, .idx, R, rfl, Or.inl rfl, hR⟩
  all_goals exact Or.inl rfl

theorem blkBP_defined (k EX EDS DS2 : Nat) (s : RegState) (hEX : ¬ (EX % M = 0)) :
    SAllDefined k s (blkBP EX EDS DS2) := by
  refine divLit_defined k (blkBP EX EDS DS2) ?_ s
  intro i hi
  simp only [blkBP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact Or.inr ⟨11, .udiv, .reg 7, EX, rfl, Or.inl rfl, hEX⟩
  all_goals exact Or.inl rfl

theorem blkC2_defined (k : Nat) (s : RegState) (h15 : ¬ (s 15 = 0)) :
    SAllDefined k s blkC2 := by
  refine divReg_defined k 15 blkC2 ?_ ?_ s h15
  · intro i hi
    simp only [blkC2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [blkC2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
    · exact Or.inr ⟨18, .udiv, .reg 16, rfl, Or.inl rfl⟩
    all_goals exact Or.inl rfl

theorem blkD1P_defined (k PL : Nat) (s : RegState) (h8 : ¬ (s 8 = 0)) :
    SAllDefined k s (blkD1P PL) := by
  refine divReg_defined k 8 (blkD1P PL) ?_ ?_ s h8
  · intro i hi
    simp only [blkD1P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [blkD1P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h
    · exact Or.inr ⟨25, .udiv, .lit PL, rfl, Or.inl rfl⟩
    all_goals exact Or.inl rfl

theorem blkF1aP_defined (k NHI : Nat) (s : RegState) :
    SAllDefined k s (blkF1aP NHI) := by
  refine divLit_defined k (blkF1aP NHI) ?_ s
  intro i hi
  simp only [blkF1aP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h
  · exact Or.inr ⟨36, .udiv, .reg 5, 10, rfl, Or.inl rfl, by decide⟩
  all_goals exact Or.inl rfl

theorem blkF1bP_defined (k LG : Nat) (s : RegState) (h5 : ¬ (s 5 = 0)) :
    SAllDefined k s (blkF1bP LG) := by
  refine divReg_defined k 5 (blkF1bP LG) ?_ ?_ s h5
  · intro i hi
    simp only [blkF1bP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [blkF1bP, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨40, .udiv, .reg 39, rfl, Or.inl rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The body always steps.** -/
theorem body_denote (c : Cfg) (idx : Nat) (s : RegState) (hOK : lOK c = true)
    (hidx : idx < c.len * c.rounds) (hI : Inv c s) :
    denoteInstrs idx s (body c) = some (srun idx s (body c)) := by
  obtain ⟨hlo, hex, hdsm, hrd, hR, hlolen, hnhi32, hlenR, hdbg, he0p, he0n, hlb0,
    hRc, hEXc, hNLOc⟩ := lFacts_of_ok hOK
  obtain ⟨hsw, hbd, haclo, hachi, hp3, hlb4, hee5p, hee5n⟩ := hI
  rw [two32_val] at hnhi32 hdbg
  have hMbig : (4294967296 : Nat) < M := two32_lt_M
  have hidxM : idx < M := Nat.lt_of_lt_of_le hidx hlenR
  have hlenpos : 0 < c.len := by
    rcases Nat.eq_zero_or_pos c.len with h | h
    · rw [h, Nat.zero_mul] at hidx; omega
    · exact h
  have hdivlt : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hnlt : c.lo + idx / c.rounds < c.nhi := by omega
  have hnM : c.lo + idx / c.rounds < M := by omega
  have hnpos : 0 < c.lo + idx / c.rounds :=
    Nat.lt_of_lt_of_le hlo (Nat.le_add_right _ _)
  have hqM32 : idx % c.rounds < 4294967296 := Nat.lt_of_lt_of_le hqlt hRc
  have hqM : idx % c.rounds < M := Nat.lt_trans hqM32 hMbig
  have hloM : c.lo < M := by omega
  have hRM : c.rounds < M := by omega
  have hRM1 : c.rounds - 1 < M := by omega
  have hEXM : c.ex < M := by omega
  have hEDSle : c.ex * c.dsm ≤ c.rounds := by omega
  have hEDSM : c.ex * c.dsm < M := by omega
  have hDS2M : c.dsm + 2 < M := by omega
  have hRne : ¬ (c.rounds % M = 0) := by
    rw [Nat.mod_eq_of_lt hRM]; omega
  have hEXne : ¬ (c.ex % M = 0) := by
    rw [Nat.mod_eq_of_lt hEXM]; omega
  have hassoc : body c = blkAP c.rounds (c.rounds - 1) c.lo ++
      (blkBP c.ex (c.ex * c.dsm) (c.dsm + 2) ++ (blkC1 ++ (blkC2 ++
        (blkD1P plScale ++ (blkD2P accLo accHi ++ (blkE1P biasV ++
          (blkE2P shMask shBits ashCap ++ (blkF1aP c.nhi ++ (blkF1bP lgScale ++
            (blkF2a ++ (blkF2bP lbCap ++
              blkGP c.nlo rhsCap gateLo gateHi))))))))))) := by
    show blkAP c.rounds (c.rounds - 1) c.lo ++ blkBP c.ex (c.ex * c.dsm) (c.dsm + 2)
        ++ blkC1 ++ blkC2 ++ blkD1P plScale ++ blkD2P accLo accHi ++ blkE1P biasV
        ++ blkE2P shMask shBits ashCap ++ blkF1aP c.nhi ++ blkF1bP lgScale
        ++ blkF2a ++ blkF2bP lbCap ++ blkGP c.nlo rhsCap gateLo gateHi = _
    simp only [List.append_assoc]
  obtain ⟨sA, hgA⟩ : ∃ t, srun idx s (blkAP c.rounds (c.rounds - 1) c.lo) = t :=
    ⟨_, rfl⟩
  obtain ⟨sB, hgB⟩ : ∃ t, srun idx sA (blkBP c.ex (c.ex * c.dsm) (c.dsm + 2)) = t :=
    ⟨_, rfl⟩
  obtain ⟨sC1, hgC1⟩ : ∃ t, srun idx sB blkC1 = t := ⟨_, rfl⟩
  obtain ⟨sC2, hgC2⟩ : ∃ t, srun idx sC1 blkC2 = t := ⟨_, rfl⟩
  obtain ⟨sD1, hgD1⟩ : ∃ t, srun idx sC2 (blkD1P plScale) = t := ⟨_, rfl⟩
  obtain ⟨sD2, hgD2⟩ : ∃ t, srun idx sD1 (blkD2P accLo accHi) = t := ⟨_, rfl⟩
  obtain ⟨sE1, hgE1⟩ : ∃ t, srun idx sD2 (blkE1P biasV) = t := ⟨_, rfl⟩
  obtain ⟨sE2, hgE2⟩ : ∃ t, srun idx sE1 (blkE2P shMask shBits ashCap) = t := ⟨_, rfl⟩
  obtain ⟨sFa, hgFa⟩ : ∃ t, srun idx sE2 (blkF1aP c.nhi) = t := ⟨_, rfl⟩
  obtain ⟨sFb, hgFb⟩ : ∃ t, srun idx sFa (blkF1bP lgScale) = t := ⟨_, rfl⟩
  obtain ⟨sG1, hgG1⟩ : ∃ t, srun idx sFb blkF2a = t := ⟨_, rfl⟩
  obtain ⟨sG2, hgG2⟩ : ∃ t, srun idx sG1 (blkF2bP lbCap) = t := ⟨_, rfl⟩
  -- the divisor facts
  obtain ⟨_, hA7, hA8, _, _, _⟩ :=
    blkAP_spec idx c.rounds (c.rounds - 1) c.lo s hR hRM hRM1 hloM hidxM hnM
  rw [hgA] at hA7 hA8
  obtain ⟨_, hB15, _⟩ := blkBP_spec idx c.ex (c.ex * c.dsm) (c.dsm + 2)
    (idx % c.rounds) sA hA7 hex hEXM hEDSM hDS2M hqM
    (by have h1 : idx % c.rounds / c.ex ≤ idx % c.rounds := Nat.div_le_self _ _
        have h2 : (4294967298 : Nat) < M := by decide
        omega)
    (by have h1 : idx % c.rounds - c.ex * c.dsm ≤ idx % c.rounds := Nat.sub_le _ _
        have h2 : (8589934592 : Nat) < M := by decide
        omega)
  rw [hgB] at hB15
  have hC115 : ¬ (sC1 15 = 0) := by
    have h : sC1 15 = sB 15 := by
      rw [← hgC1]; exact RegFrame.srun_frame idx 15 _ (by rfl) sB
    rw [h, hB15]
    show ¬ (divOf c (idx % c.rounds) = 0)
    have := divOf_pos c (idx % c.rounds)
    omega
  have h8B : sB 8 = sA 8 := by
    rw [← hgB]; exact RegFrame.srun_frame idx 8 _ (by rfl) sA
  have h8C1 : sC1 8 = sB 8 := by
    rw [← hgC1]; exact RegFrame.srun_frame idx 8 _ (by rfl) sB
  have h8C2 : sC2 8 = sC1 8 := by
    rw [← hgC2]; exact RegFrame.srun_frame idx 8 _ (by rfl) sC1
  have hC28 : ¬ (sC2 8 = 0) := by
    rw [h8C2, h8C1, h8B, hA8]; omega
  have h5A : sA 5 = s 5 := by
    rw [← hgA]; exact RegFrame.srun_frame idx 5 _ (by rfl) s
  have h5B : sB 5 = sA 5 := by
    rw [← hgB]; exact RegFrame.srun_frame idx 5 _ (by rfl) sA
  have h5C1 : sC1 5 = sB 5 := by
    rw [← hgC1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sB
  have h5C2 : sC2 5 = sC1 5 := by
    rw [← hgC2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sC1
  have h5D1 : sD1 5 = sC2 5 := by
    rw [← hgD1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sC2
  have h5D2 : sD2 5 = sD1 5 := by
    rw [← hgD2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sD1
  have h5E1 : sE1 5 = sD2 5 := by
    rw [← hgE1]; exact RegFrame.srun_frame idx 5 _ (by rfl) sD2
  have h5E2 : sE2 5 = sE1 5 := by
    rw [← hgE2]; exact RegFrame.srun_frame idx 5 _ (by rfl) sE1
  have h5Fa : sFa 5 = sE2 5 := by
    rw [← hgFa]; exact RegFrame.srun_frame idx 5 _ (by rfl) sE2
  have hFa5 : ¬ (sFa 5 = 0) := by
    rw [h5Fa, h5E2, h5E1, h5D2, h5D1, h5C2, h5C1, h5B, h5A]; omega
  refine denoteInstrs_eq_srun idx (body c) s ?_
  rw [hassoc, SAllDefined_append, hgA, SAllDefined_append, hgB, SAllDefined_append,
    hgC1, SAllDefined_append, hgC2, SAllDefined_append, hgD1, SAllDefined_append,
    hgD2, SAllDefined_append, hgE1, SAllDefined_append, hgE2, SAllDefined_append,
    hgFa, SAllDefined_append, hgFb, SAllDefined_append, hgG1, SAllDefined_append,
    hgG2]
  exact ⟨blkAP_defined idx _ _ _ s hRne, blkBP_defined idx _ _ _ sA hEXne,
    BlockDefined.sAllDefined_of_noDiv idx _ sB (by rfl),
    blkC2_defined idx sC1 hC115,
    blkD1P_defined idx plScale sC2 hC28,
    BlockDefined.sAllDefined_of_noDiv idx _ sD1 (by rfl),
    BlockDefined.sAllDefined_of_noDiv idx _ sD2 (by rfl),
    BlockDefined.sAllDefined_of_noDiv idx _ sE1 (by rfl),
    blkF1aP_defined idx c.nhi sE2,
    blkF1bP_defined idx lgScale sFa hFa5,
    BlockDefined.sAllDefined_of_noDiv idx _ sFb (by rfl),
    BlockDefined.sAllDefined_of_noDiv idx _ sG1 (by rfl),
    BlockDefined.sAllDefined_of_noDiv idx _ sG2 (by rfl)⟩

/-! ## The denotation -/

/-- The state the init block reaches. -/
def entry (c : Cfg) : RegState :=
  RegState.set (RegState.set (RegState.set initialState 1 (biasV % M)) 4
    (c.lb0 % M)) 5 (c.e0 % M)

theorem entry_init (c : Cfg) :
    denoteInstrs 0 initialState (initBlock c) = some (entry c) := rfl

theorem obs_entry (c : Cfg) (hlb0 : c.lb0 ≤ lbCap) (he0 : c.e0 ≤ 4294967296) :
    obs (entry c) = ⟨0, biasV, 0, 0, c.lb0, c.e0⟩ := by
  have hlbM : c.lb0 < M := by
    have := lbCap_lt; omega
  have he0M : c.e0 < M := by
    have := two32_lt_M; omega
  refine Abs.eq_of ?_ ?_ ?_ ?_ ?_ ?_
  · show entry c 0 = 0; rfl
  · show entry c 1 = biasV
    show biasV % M = biasV
    exact Nat.mod_eq_of_lt biasV_lt
  · show entry c 2 = 0; rfl
  · show entry c 3 = 0; rfl
  · show entry c 4 = c.lb0
    show c.lb0 % M = c.lb0
    exact Nat.mod_eq_of_lt hlbM
  · show entry c 5 = c.e0
    show c.e0 % M = c.e0
    exact Nat.mod_eq_of_lt he0M

theorem entry_inv (c : Cfg) (hlb0 : c.lb0 ≤ lbCap) (he0p : 0 < c.e0)
    (he0n : c.e0 ≤ c.nhi) (hnhi : c.nhi ≤ 4294967296) : Inv c (entry c) := by
  have hobs := obs_entry c hlb0 (Nat.le_trans he0n hnhi)
  have h0 : entry c 0 = 0 := congrArg Abs.bad hobs
  have h1 : entry c 1 = biasV := congrArg Abs.acc hobs
  have h3 : entry c 3 = 0 := congrArg Abs.par hobs
  have h4 : entry c 4 = c.lb0 := congrArg Abs.lb hobs
  have h5 : entry c 5 = c.e0 := congrArg Abs.ee hobs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show (RegState.set (RegState.set (RegState.set initialState 1 (biasV % M)) 4
      (c.lb0 % M)) 5 (c.e0 % M)) j < M
    by_cases hj5 : j = 5
    · rw [hj5]; show (if (5:Nat) = 5 then c.e0 % M else _) < M
      rw [if_pos rfl]; exact Nat.mod_lt _ M_pos
    · show (if j = 5 then c.e0 % M else
        (RegState.set (RegState.set initialState 1 (biasV % M)) 4 (c.lb0 % M)) j) < M
      rw [if_neg hj5]
      by_cases hj4 : j = 4
      · rw [hj4]; show (if (4:Nat) = 4 then c.lb0 % M else _) < M
        rw [if_pos rfl]; exact Nat.mod_lt _ M_pos
      · show (if j = 4 then c.lb0 % M else
          (RegState.set initialState 1 (biasV % M)) j) < M
        rw [if_neg hj4]
        by_cases hj1 : j = 1
        · rw [hj1]; show (if (1:Nat) = 1 then biasV % M else _) < M
          rw [if_pos rfl]; exact Nat.mod_lt _ M_pos
        · show (if j = 1 then biasV % M else initialState j) < M
          rw [if_neg hj1]
          exact M_pos
  · rw [h0]; omega
  · rw [h1]; exact biasV_in.1
  · rw [h1]; exact biasV_in.2
  · rw [h3]; omega
  · rw [h4]; exact hlb0
  · rw [h5]; exact he0p
  · rw [h5]; exact he0n

/-- One step preserves the invariant, read on the abstract state. -/
theorem gstep_inv (c : Cfg) (idx : Nat) (a : Abs) (h0 : a.bad ≤ 1)
    (h1lo : accLo ≤ a.acc) (h1hi : a.acc ≤ accHi) (h3 : a.par ≤ 1)
    (h4 : a.lb ≤ lbCap) (h5p : 0 < a.ee) (h5n : a.ee ≤ c.nhi) :
    (gstep c idx a).bad ≤ 1 ∧ accLo ≤ (gstep c idx a).acc ∧
      (gstep c idx a).acc ≤ accHi ∧ (gstep c idx a).par ≤ 1 ∧
      (gstep c idx a).lb ≤ lbCap ∧ 0 < (gstep c idx a).ee ∧
      (gstep c idx a).ee ≤ c.nhi := by
  have hadv : (if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0) *
      (if c.lo + idx / c.rounds = a.ee then (1:Nat) else 0) ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul (bitLe _) (bitLe _)) (by omega)
  refine ⟨?_, accClamp_ge _, accClamp_le _, stripStep_par_le _ _,
    Nat.min_le_right _ _, ?_, ?_⟩
  · show a.bad ||| (if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0) *
        (1 - rowVerdict _ _ _ _ _ _) ≤ 1
    exact bit_or_le _ _ h0
      (Nat.le_trans (Nat.mul_le_mul (bitLe _) (Nat.sub_le _ _)) (by omega))
  · show 0 < a.ee + _
    omega
  · show a.ee + ((if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0) *
        (if c.lo + idx / c.rounds = a.ee then (1:Nat) else 0)) * bandW c a.ee ≤ c.nhi
    have hb := mul_bit_le (bandW c a.ee) _ hadv
    have hw : bandW c a.ee ≤ c.nhi - a.ee := bandWR_le c.nhi a.ee
    omega

set_option maxHeartbeats 1000000 in
/-- **The denotation theorem**: the sweep denotes the violation flag of the
`gstep` fold, with no fold evaluated in the proof. -/
theorem lProgram_denote (c : Cfg) (hOK : lOK c = true) :
    (lProgram c).denote = some (value c) := by
  obtain ⟨hlo, hex, hdsm, hrd, hR, hlolen, hnhi32, hlenR, hdbg, he0p, he0n, hlb0,
    hRc, hEXc, hNLOc⟩ := lFacts_of_ok hOK
  rw [two32_val] at hnhi32
  have hLoop : (lProgram c).loopCount = c.len * c.rounds := rfl
  have hval : value c = Abs.bad ((List.range (c.len * c.rounds)).foldl
      (fun a index => gstep c index a) (obs (entry c))) := by
    rw [obs_entry c hlb0 (Nat.le_trans he0n hnhi32)]
    rfl
  rw [hval]
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (lProgram c) (Inv c)
    (fun index t => srun index t (body c)) obs (fun index a => gstep c index a)
    Abs.bad (entry c) (entry_init c) (entry_inv c hlb0 he0p he0n hnhi32) ?_ ?_ ?_ ?_
  · intro index t hidx hInv
    exact body_denote c index t hOK (hLoop ▸ hidx) hInv
  · intro index t hidx hInv
    obtain ⟨hsw, hbd, haclo, hachi, hp3, hlb4, hee5p, hee5n⟩ := hInv
    have hobs := body_obs c index t hOK (hLoop ▸ hidx)
      ⟨hsw, hbd, haclo, hachi, hp3, hlb4, hee5p, hee5n⟩
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ :=
      gstep_inv c index (obs t) hbd haclo hachi hp3 hlb4 hee5p hee5n
    refine ⟨srun_lt_of_lt index (body c) t hsw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← obs_bad (srun index t (body c)), hobs]; exact g0
    · rw [← obs_acc (srun index t (body c)), hobs]; exact g1
    · rw [← obs_acc (srun index t (body c)), hobs]; exact g2
    · rw [← obs_par (srun index t (body c)), hobs]; exact g3
    · rw [← obs_lb (srun index t (body c)), hobs]; exact g4
    · rw [← obs_ee (srun index t (body c)), hobs]; exact g5
    · rw [← obs_ee (srun index t (body c)), hobs]; exact g6
  · intro index t hidx hInv
    exact body_obs c index t hOK (hLoop ▸ hidx) hInv
  · intro t _
    rfl

/-! ## From the flat index space to candidates -/

/-- The completely-multiplicative sign of candidate `n`, as the strip reads it. -/
def sgnOf (c : Cfg) (n : Nat) : Nat := signOf (stripPre c n c.rounds)

/-- The unclamped accumulator after candidate `n`, from incoming `acc`. -/
def accSA (c : Cfg) (n acc : Nat) : Nat := accApply acc (sgnOf c n) n

/-- Does candidate `n` open a new band? -/
def advA (n ee : Nat) : Nat := if n = ee then 1 else 0

/-- The unclamped ladder value candidate `n` is tested against. -/
def lbRawA (c : Cfg) (n lb ee : Nat) : Nat := lb + advA n ee * bandInc c ee

/-- The shifted left-hand side candidate `n` is tested with. -/
def ashA (c : Cfg) (n acc : Nat) : Nat :=
  ashOf (absBias (accClamp (accSA c n acc)) + n)

/-- The row's verdict at candidate `n`. -/
def rowBitA (c : Cfg) (n acc lb ee : Nat) : Nat :=
  rowVerdict (if gateLo ≤ accSA c n acc then 1 else 0)
    (if accSA c n acc ≤ gateHi then 1 else 0)
    (if lbRawA c n lb ee ≤ lbCap then 1 else 0) (if c.nlo ≤ n then 1 else 0)
    (if ashA c n acc ≤ ashCap then 1 else 0)
    (if 1000 * (min (ashA c n acc) ashCap * min (lbRawA c n lb ee) lbCap) ≤ rhsCap
     then 1 else 0)

/-- The band cursor, candidate by candidate. -/
def eeSeq (c : Cfg) : Nat → Nat
  | 0 => c.e0
  | i + 1 => eeSeq c i + advA (c.lo + i) (eeSeq c i) * bandW c (eeSeq c i)

/-- The ladder value, candidate by candidate. -/
def lbSeq (c : Cfg) : Nat → Nat
  | 0 => c.lb0
  | i + 1 => min (lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i)) lbCap

/-- The clamped accumulator, candidate by candidate. -/
def accSeq (c : Cfg) : Nat → Nat
  | 0 => biasV
  | i + 1 => accClamp (accSA c (c.lo + i) (accSeq c i))

/-- The violation flag, candidate by candidate. -/
def badSeq (c : Cfg) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      badSeq c i ||| (1 - rowBitA c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i))

theorem accSeq_range (c : Cfg) : ∀ i, accLo ≤ accSeq c i ∧ accSeq c i ≤ accHi
  | 0 => biasV_in
  | i + 1 => ⟨accClamp_ge _, accClamp_le _⟩

theorem lbSeq_le (c : Cfg) (h : c.lb0 ≤ lbCap) : ∀ i, lbSeq c i ≤ lbCap
  | 0 => h
  | _ + 1 => Nat.min_le_right _ _

/-- The flat index decodes to `(candidate, round)`. -/
theorem index_decode (c : Cfg) (q r : Nat) (hr : r < c.rounds) :
    (q * c.rounds + r) / c.rounds = q ∧ (q * c.rounds + r) % c.rounds = r := by
  have h0 : 0 < c.rounds := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-! ### The abstract step with the flat index already decoded

Every quantity gets a name, so a projection of `gstepAt` is a named term and no
proof about the loop ever forces the step's body open. -/

/-- The round's outgoing `(residual, parity)`. -/
def rpAt (c : Cfg) (q n : Nat) (a : Abs) : Nat × Nat :=
  stripStep (divOf c q) (if q = 0 then (n, 0) else (a.res, a.par))

/-- Is this the candidate's last round? -/
def lastAt (c : Cfg) (q : Nat) : Nat := if q = c.rounds - 1 then 1 else 0

/-- The accumulator the row test reads. -/
def accAt (c : Cfg) (q n : Nat) (a : Abs) : Nat :=
  if lastAt c q = 1 then accApply a.acc (signOf (rpAt c q n a)) n else a.acc

/-- The shifted left-hand side the row test reads. -/
def ashAt (c : Cfg) (q n : Nat) (a : Abs) : Nat :=
  ashOf (absBias (accClamp (accAt c q n a)) + n)

/-- Does this round open a new band? -/
def advAt (c : Cfg) (q n : Nat) (a : Abs) : Nat :=
  lastAt c q * (if n = a.ee then 1 else 0)

/-- The unclamped ladder value the row test reads. -/
def lbRawAt (c : Cfg) (q n : Nat) (a : Abs) : Nat :=
  a.lb + advAt c q n a * bandInc c a.ee

/-- The row's verdict, at a flat-decoded round. -/
def rowAt (c : Cfg) (q n : Nat) (a : Abs) : Nat :=
  rowVerdict (if gateLo ≤ accAt c q n a then 1 else 0)
    (if accAt c q n a ≤ gateHi then 1 else 0)
    (if lbRawAt c q n a ≤ lbCap then 1 else 0) (if c.nlo ≤ n then 1 else 0)
    (if ashAt c q n a ≤ ashCap then 1 else 0)
    (if 1000 * (min (ashAt c q n a) ashCap * min (lbRawAt c q n a) lbCap) ≤ rhsCap
     then 1 else 0)

/-- The abstract step, with the flat index already decoded. -/
def gstepAt (c : Cfg) (q n : Nat) (a : Abs) : Abs :=
  ⟨a.bad ||| lastAt c q * (1 - rowAt c q n a), accClamp (accAt c q n a),
    (rpAt c q n a).1, (rpAt c q n a).2, min (lbRawAt c q n a) lbCap,
    a.ee + advAt c q n a * bandW c a.ee⟩

theorem gstep_eq_at (c : Cfg) (idx : Nat) (a : Abs) :
    gstep c idx a = gstepAt c (idx % c.rounds) (c.lo + idx / c.rounds) a := rfl

/-- One round of one candidate, in ordinary arithmetic. -/
theorem gstep_round (c : Cfg) (q r : Nat) (hr : r < c.rounds) (a : Abs) :
    gstep c (q * c.rounds + r) a = gstepAt c r (c.lo + q) a := by
  obtain ⟨hdiv, hmod⟩ := index_decode c q r hr
  rw [gstep_eq_at, hdiv, hmod]


/-! ## One candidate's block -/

private theorem min_self_left (a b : Nat) (h : a ≤ b) : min a b = a := by
  rw [Nat.min_def, if_pos h]

private theorem max_self_left (a b : Nat) (h : b ≤ a) : max a b = a := by
  rw [Nat.max_def]
  by_cases hh : a ≤ b
  · rw [if_pos hh]; omega
  · rw [if_neg hh]

theorem accClamp_eq_self (x : Nat) (h1 : accLo ≤ x) (h2 : x ≤ accHi) :
    accClamp x = x := by
  unfold accClamp
  rw [max_self_left x accLo h1, min_self_left x accHi h2]

theorem gstepAt_bad (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).bad = a.bad ||| lastAt c q * (1 - rowAt c q n a) := rfl
theorem gstepAt_acc (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).acc = accClamp (accAt c q n a) := rfl
theorem gstepAt_res (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).res = (rpAt c q n a).1 := rfl
theorem gstepAt_par (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).par = (rpAt c q n a).2 := rfl
theorem gstepAt_lb (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).lb = min (lbRawAt c q n a) lbCap := rfl
theorem gstepAt_ee (c : Cfg) (q n : Nat) (a : Abs) :
    (gstepAt c q n a).ee = a.ee + advAt c q n a * bandW c a.ee := rfl

theorem rpAt_zero (c : Cfg) (n : Nat) (a : Abs) :
    rpAt c 0 n a = stripPre c n 1 := by
  unfold rpAt
  rw [if_pos rfl]
  rfl

theorem rpAt_succ (c : Cfg) (q n : Nat) (a : Abs) (hq : ¬ (q = 0))
    (hres : a.res = (stripPre c n q).1) (hpar : a.par = (stripPre c n q).2) :
    rpAt c q n a = stripPre c n (q + 1) := by
  unfold rpAt
  rw [if_neg hq, hres, hpar]
  rfl

theorem accAt_last (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 1)
    (hs : rpAt c q n a = stripPre c n c.rounds) :
    accAt c q n a = accSA c n a.acc := by
  unfold accAt
  rw [hq, if_pos rfl, hs]
  rfl

theorem accAt_mid (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 0) :
    accAt c q n a = a.acc := by
  unfold accAt
  rw [hq]
  exact if_neg (by omega)

theorem advAt_last (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 1) :
    advAt c q n a = advA n a.ee := by
  unfold advAt advA
  rw [hq, Nat.one_mul]

theorem advAt_mid (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 0) :
    advAt c q n a = 0 := by
  unfold advAt
  rw [hq, Nat.zero_mul]

theorem gstepAt_last (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 1)
    (hs : rpAt c q n a = stripPre c n c.rounds) :
    gstepAt c q n a =
      (⟨a.bad ||| (1 - rowBitA c n a.acc a.lb a.ee), accClamp (accSA c n a.acc),
        (stripPre c n c.rounds).1, (stripPre c n c.rounds).2,
        min (lbRawA c n a.lb a.ee) lbCap,
        a.ee + advA n a.ee * bandW c a.ee⟩ : Abs) := by
  have hacc := accAt_last c q n a hq hs
  have hadv := advAt_last c q n a hq
  have hlbr : lbRawAt c q n a = lbRawA c n a.lb a.ee := by
    unfold lbRawAt lbRawA
    rw [hadv]
  have hash : ashAt c q n a = ashA c n a.acc := by
    unfold ashAt ashA
    rw [hacc]
  have hrow : rowAt c q n a = rowBitA c n a.acc a.lb a.ee := by
    unfold rowAt rowBitA
    rw [hacc, hlbr, hash]
  refine Abs.eq_of ?_ ?_ ?_ ?_ ?_ ?_
  · rw [gstepAt_bad, hq, hrow, Nat.one_mul]
  · rw [gstepAt_acc, hacc]
  · rw [gstepAt_res, hs]
  · rw [gstepAt_par, hs]
  · rw [gstepAt_lb, hlbr]
  · rw [gstepAt_ee, hadv]

theorem gstepAt_mid (c : Cfg) (q n : Nat) (a : Abs) (hq : lastAt c q = 0)
    (haclo : accLo ≤ a.acc) (hachi : a.acc ≤ accHi) (hlb : a.lb ≤ lbCap) :
    gstepAt c q n a =
      (⟨a.bad, a.acc, (rpAt c q n a).1, (rpAt c q n a).2, a.lb, a.ee⟩ : Abs) := by
  have hacc := accAt_mid c q n a hq
  have hadv := advAt_mid c q n a hq
  have hlbr : lbRawAt c q n a = a.lb := by
    unfold lbRawAt
    rw [hadv, Nat.zero_mul, Nat.add_zero]
  refine Abs.eq_of ?_ ?_ ?_ ?_ ?_ ?_
  · rw [gstepAt_bad, hq, Nat.zero_mul, Nat.or_zero]
  · rw [gstepAt_acc, hacc, accClamp_eq_self a.acc haclo hachi]
  · rw [gstepAt_res]
  · rw [gstepAt_par]
  · rw [gstepAt_lb, hlbr, min_self_left _ _ hlb]
  · rw [gstepAt_ee, hadv, Nat.zero_mul, Nat.add_zero]

set_option maxHeartbeats 1000000 in
/-- The prefix of one candidate's block. -/
theorem block_prefix (c : Cfg) (hR : 0 < c.rounds) (qq : Nat) (a : Abs)
    (haclo : accLo ≤ a.acc) (hachi : a.acc ≤ accHi) (hlb : a.lb ≤ lbCap) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (qq * c.rounds + r) x) a =
        (⟨(if k + 1 = c.rounds then
              a.bad ||| (1 - rowBitA c (c.lo + qq) a.acc a.lb a.ee) else a.bad),
          (if k + 1 = c.rounds then accClamp (accSA c (c.lo + qq) a.acc) else a.acc),
          (stripPre c (c.lo + qq) (k + 1)).1,
          (stripPre c (c.lo + qq) (k + 1)).2,
          (if k + 1 = c.rounds then min (lbRawA c (c.lo + qq) a.lb a.ee) lbCap
           else a.lb),
          (if k + 1 = c.rounds then
             a.ee + advA (c.lo + qq) a.ee * bandW c a.ee else a.ee)⟩ : Abs) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp only [Nat.zero_add]
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstep_round c qq 0 hk a]
      by_cases h1 : (1:Nat) = c.rounds
      · have hl : lastAt c 0 = 1 := by
          unfold lastAt
          rw [if_pos (by omega)]
        have hs : rpAt c 0 (c.lo + qq) a = stripPre c (c.lo + qq) c.rounds := by
          rw [rpAt_zero, ← h1]
        rw [gstepAt_last c 0 (c.lo + qq) a hl hs, if_pos h1, if_pos h1, if_pos h1,
          if_pos h1, ← h1]
      · have hl : lastAt c 0 = 0 := by
          unfold lastAt
          rw [if_neg (by omega)]
        rw [gstepAt_mid c 0 (c.lo + qq) a hl haclo hachi hlb, if_neg h1, if_neg h1,
          if_neg h1, if_neg h1, rpAt_zero]
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt, if_neg hkne, if_neg hkne, if_neg hkne, if_neg hkne,
        gstep_round c qq (k + 1) hk _]
      have hrp : rpAt c (k + 1) (c.lo + qq)
          (⟨a.bad, a.acc, (stripPre c (c.lo + qq) (k + 1)).1,
            (stripPre c (c.lo + qq) (k + 1)).2, a.lb, a.ee⟩ : Abs)
          = stripPre c (c.lo + qq) (k + 1 + 1) :=
        rpAt_succ c (k + 1) (c.lo + qq) _ (by omega) rfl rfl
      by_cases h1 : k + 1 + 1 = c.rounds
      · have hl : lastAt c (k + 1) = 1 := by
          unfold lastAt
          rw [if_pos (by omega)]
        have hs : rpAt c (k + 1) (c.lo + qq)
            (⟨a.bad, a.acc, (stripPre c (c.lo + qq) (k + 1)).1,
              (stripPre c (c.lo + qq) (k + 1)).2, a.lb, a.ee⟩ : Abs)
            = stripPre c (c.lo + qq) c.rounds := by
          rw [hrp, h1]
        rw [gstepAt_last c (k + 1) (c.lo + qq)
            (⟨a.bad, a.acc, (stripPre c (c.lo + qq) (k + 1)).1,
              (stripPre c (c.lo + qq) (k + 1)).2, a.lb, a.ee⟩ : Abs) hl hs,
          if_pos h1, if_pos h1, if_pos h1, if_pos h1, ← h1]
      · have hl : lastAt c (k + 1) = 0 := by
          unfold lastAt
          rw [if_neg (by omega)]
        rw [gstepAt_mid c (k + 1) (c.lo + qq)
            (⟨a.bad, a.acc, (stripPre c (c.lo + qq) (k + 1)).1,
              (stripPre c (c.lo + qq) (k + 1)).2, a.lb, a.ee⟩ : Abs) hl haclo hachi
            hlb,
          if_neg h1, if_neg h1, if_neg h1, if_neg h1, hrp]

/-- One block: a whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (qq : Nat) (a : Abs)
    (haclo : accLo ≤ a.acc) (hachi : a.acc ≤ accHi) (hlb : a.lb ≤ lbCap) :
    BlockedFold.block c.rounds (fun x i => gstep c i x) a qq =
      (⟨a.bad ||| (1 - rowBitA c (c.lo + qq) a.acc a.lb a.ee),
        accClamp (accSA c (c.lo + qq) a.acc),
        (stripPre c (c.lo + qq) c.rounds).1, (stripPre c (c.lo + qq) c.rounds).2,
        min (lbRawA c (c.lo + qq) a.lb a.ee) lbCap,
        a.ee + advA (c.lo + qq) a.ee * bandW c a.ee⟩ : Abs) := by
  have h := block_prefix c hR qq a haclo hachi hlb (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [if_pos (rfl : c.rounds = c.rounds), if_pos (rfl : c.rounds = c.rounds),
    if_pos (rfl : c.rounds = c.rounds), if_pos (rfl : c.rounds = c.rounds)] at h
  rw [BlockedFold.block_eq_shift]
  show (List.range c.rounds).foldl (fun x r => gstep c (qq * c.rounds + r) x) a = _
  rw [h]

/-- The candidate fold. -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) (hlb0 : c.lb0 ≤ lbCap) : ∀ i,
    ((List.range i).foldl (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
      (⟨0, biasV, 0, 0, c.lb0, c.e0⟩ : Abs)).bad = badSeq c i ∧
    ((List.range i).foldl (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
      (⟨0, biasV, 0, 0, c.lb0, c.e0⟩ : Abs)).acc = accSeq c i ∧
    ((List.range i).foldl (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
      (⟨0, biasV, 0, 0, c.lb0, c.e0⟩ : Abs)).lb = lbSeq c i ∧
    ((List.range i).foldl (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
      (⟨0, biasV, 0, 0, c.lb0, c.e0⟩ : Abs)).ee = eeSeq c i := by
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ i ih =>
      obtain ⟨ih0, ih1, ih4, ih5⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        block_spec c hR i _ (by rw [ih1]; exact (accSeq_range c i).1)
          (by rw [ih1]; exact (accSeq_range c i).2)
          (by rw [ih4]; exact lbSeq_le c hlb0 i)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show _ ||| _ = badSeq c (i + 1)
        simp only [badSeq]
        rw [ih0, ih1, ih4, ih5]
      · show accClamp _ = accSeq c (i + 1)
        simp only [accSeq]
        rw [ih1]
      · show min _ lbCap = lbSeq c (i + 1)
        simp only [lbSeq]
        rw [ih4, ih5]
      · show _ + _ = eeSeq c (i + 1)
        simp only [eeSeq]
        rw [ih5]

/-- The denotation, candidate by candidate. -/
theorem value_eq_badSeq (c : Cfg) (hR : 0 < c.rounds) (hlb0 : c.lb0 ≤ lbCap) :
    value c = badSeq c c.len := by
  rw [value, BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstep c index a) (⟨0, biasV, 0, 0, c.lb0, c.e0⟩ : Abs)]
  exact (fold_blocks c hR hlb0 c.len).1

/-! ## What a run establishes -/

private theorem bit_eq_one (P : Prop) [Decidable P]
    (h : (if P then (1:Nat) else 0) = 1) : P := by
  by_cases hp : P
  · exact hp
  · rw [if_neg hp] at h; omega

theorem rowVerdict_le_one (g1 g2 g3 g4 g5 g6 : Nat) (h1 : g1 ≤ 1) (h2 : g2 ≤ 1)
    (h3 : g3 ≤ 1) : rowVerdict g1 g2 g3 g4 g5 g6 ≤ 1 := by
  have hp : g1 * g2 * g3 ≤ 1 := by
    rcases (show g1 = 0 ∨ g1 = 1 by omega) with rfl | rfl <;>
      rcases (show g2 = 0 ∨ g2 = 1 by omega) with rfl | rfl <;>
      rcases (show g3 = 0 ∨ g3 = 1 by omega) with rfl | rfl <;> decide
  show g1 * g2 * g3 * (1 - g4 * (1 - g5 * g6)) ≤ 1
  exact Nat.le_trans (Nat.mul_le_mul hp (Nat.sub_le 1 _)) (by omega)

theorem rowBitA_le_one (c : Cfg) (n acc lb ee : Nat) : rowBitA c n acc lb ee ≤ 1 :=
  rowVerdict_le_one _ _ _ _ _ _ (bitLe _) (bitLe _) (bitLe _)

theorem rowVerdict_one (g1 g2 g3 g4 g5 g6 : Nat)
    (h1 : g1 ≤ 1) (h2 : g2 ≤ 1) (h3 : g3 ≤ 1) (h4 : g4 ≤ 1) (h5 : g5 ≤ 1)
    (h6 : g6 ≤ 1) (h : rowVerdict g1 g2 g3 g4 g5 g6 = 1) :
    g1 = 1 ∧ g2 = 1 ∧ g3 = 1 ∧ (g4 = 1 → g5 = 1 ∧ g6 = 1) := by
  rcases (show g1 = 0 ∨ g1 = 1 by omega) with rfl | rfl <;>
    rcases (show g2 = 0 ∨ g2 = 1 by omega) with rfl | rfl <;>
    rcases (show g3 = 0 ∨ g3 = 1 by omega) with rfl | rfl <;>
    rcases (show g4 = 0 ∨ g4 = 1 by omega) with rfl | rfl <;>
    rcases (show g5 = 0 ∨ g5 = 1 by omega) with rfl | rfl <;>
    rcases (show g6 = 0 ∨ g6 = 1 by omega) with rfl | rfl <;>
    simp_all [rowVerdict]

theorem badSeq_le (c : Cfg) : ∀ i, badSeq c i ≤ 1
  | 0 => by rw [badSeq]; omega
  | i + 1 => by
      rw [badSeq]
      exact bit_or_le _ _ (badSeq_le c i) (Nat.sub_le _ _)

/-- A `bor` chain of bits vanishes exactly when every row passed. -/
theorem badSeq_eq_zero (c : Cfg) : ∀ i, badSeq c i = 0 →
    ∀ m, m < i → rowBitA c (c.lo + m) (accSeq c m) (lbSeq c m) (eeSeq c m) = 1 := by
  intro i
  induction i with
  | zero => intro _ m hm; omega
  | succ i ih =>
      intro h m hm
      rw [badSeq] at h
      have hb := badSeq_le c i
      have hr := rowBitA_le_one c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i)
      have hsplit : badSeq c i = 0 ∧
          1 - rowBitA c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i) = 0 := by
        have h1 : badSeq c i = 0 ∨ badSeq c i = 1 := by omega
        have h2 : 1 - rowBitA c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i) = 0 ∨
            1 - rowBitA c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i) = 1 := by
          omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          rw [h1, h2] at h <;> simp_all
      rcases Nat.lt_or_ge m i with hlt | hge
      · exact ih hsplit.1 m hlt
      · have hmi : m = i := by omega
        subst hmi
        omega

/-- **The sweep's rows**: every candidate cleared the accumulator gate and the
ladder cap, and every candidate at or above `nlo` cleared the band product. -/
def SweepRows (c : Cfg) : Prop :=
  ∀ i, i < c.len →
    gateLo ≤ accSA c (c.lo + i) (accSeq c i) ∧
    accSA c (c.lo + i) (accSeq c i) ≤ gateHi ∧
    lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i) ≤ lbCap ∧
    (c.nlo ≤ c.lo + i →
      ashA c (c.lo + i) (accSeq c i) ≤ ashCap ∧
      1000 * (ashA c (c.lo + i) (accSeq c i) *
        lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i)) ≤ rhsCap)

/-- **The certificate's meaning**: a zero violation flag is the rows. -/
theorem value_eq_zero_rows (c : Cfg) (hOK : lOK c = true) (hval : value c = 0) :
    SweepRows c := by
  obtain ⟨_, _, _, _, hR, _, _, _, _, _, _, hlb0, _, _, _⟩ := lFacts_of_ok hOK
  intro i hi
  have hrow : rowBitA c (c.lo + i) (accSeq c i) (lbSeq c i) (eeSeq c i) = 1 := by
    refine badSeq_eq_zero c c.len ?_ i hi
    rw [← value_eq_badSeq c hR hlb0]
    exact hval
  rw [rowBitA] at hrow
  obtain ⟨g1, g2, g3, g46⟩ := rowVerdict_one _ _ _ _ _ _ (bitLe _) (bitLe _)
    (bitLe _) (bitLe _) (bitLe _) (bitLe _) hrow
  have hlble : lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i) ≤ lbCap := bit_eq_one _ g3
  refine ⟨bit_eq_one _ g1, bit_eq_one _ g2, hlble, ?_⟩
  intro hnlo
  obtain ⟨g5, g6⟩ := g46 (by rw [if_pos hnlo])
  have hashle : ashA c (c.lo + i) (accSeq c i) ≤ ashCap := bit_eq_one _ g5
  have hprod : 1000 * (min (ashA c (c.lo + i) (accSeq c i)) ashCap *
      min (lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i)) lbCap) ≤ rhsCap :=
    bit_eq_one _ g6
  rw [min_self_left _ _ hashle, min_self_left _ _ hlble] at hprod
  exact ⟨hashle, hprod⟩

private theorem gateLo_ge : accLo ≤ gateLo := by decide
private theorem gateHi_le : gateHi ≤ accHi := by decide

/-- Under the rows, the accumulator clamp was inactive. -/
theorem accSeq_succ_of_rows (c : Cfg) (hrows : SweepRows c) (i : Nat)
    (hi : i < c.len) : accSeq c (i + 1) = accSA c (c.lo + i) (accSeq c i) := by
  obtain ⟨h1, h2, _, _⟩ := hrows i hi
  show accClamp (accSA c (c.lo + i) (accSeq c i)) = _
  refine accClamp_eq_self _ ?_ ?_
  · have := gateLo_ge; omega
  · have := gateHi_le; omega

/-- Under the rows, the ladder clamp was inactive. -/
theorem lbSeq_succ_of_rows (c : Cfg) (hrows : SweepRows c) (i : Nat)
    (hi : i < c.len) :
    lbSeq c (i + 1) = lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i) := by
  obtain ⟨_, _, h3, _⟩ := hrows i hi
  show min (lbRawA c (c.lo + i) (lbSeq c i) (eeSeq c i)) lbCap = _
  exact min_self_left _ _ h3

end LeanCompCert.Ports.LiouvilleEllSweep
