import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Verified.ScalarLift
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined

/-!
# The Helfgott (2.17) weighted-moment sweep as an array program

The `ternary-goldbach-lean` atom `check_weighted_moment_2_17_full` evaluates

```
checkWeightedMomentTable 1600000 19000000 = true
```

a Boolean that sieves a factor table over `[2, 1.9·10⁷]` and streams the exact
fixed-point accumulator `W(N) = Σ_{1<n≤N} n · Λub(n)` (units `2⁻⁴⁸`), checking
`2500·W(N) < 1251·N²·2⁴⁸` at every `N ≥ 1 600 000`.  Downstream,
`WeightedMoment217Sweep.lean` (in the goldbach tree) proves that Boolean
**equivalent** to the array-free row proposition `WM217Rows`, with the table
reads replaced by `Nat.minFac` — so what an artifact must establish is pure
arithmetic.

This file is the artifact: a flat candidate × round trial-division scan in the
array machine, `AProgram`, whose single array is a **read-only table of ladder
seeds** for the prime bases `p ≤ 4359` of proper prime powers.

## The dominance design

The exact accumulator `W(N)` reaches `≈ 5.1·10²⁸` in `2⁻⁴⁸` units — far beyond
one word.  The artifact therefore carries a **dominating rescaled**
accumulator at `2⁻⁴⁴` relative to the fixed-point unit:

* per candidate `n` with ladder value `lam < 2⁵³`, it adds
  `addend = ((n·(⌊lam/2²⁰⌋ + 1)) >>> 24) + 1 ≥ n·lam / 2⁴⁴`;
* a passing row test `2500·acc < 20016·n²` (`20016 = 1251·16`,
  `16 = 2⁴⁸⁻⁴⁴`) then implies the exact row
  `2500·W(n) < 1251·n²·2⁴⁸`, because `2⁴⁴·acc ≥ W(n)` termwise.

The per-term inflation (two `+1` ceilings and one low-bit truncation) totals
`< 10⁻⁸` relative against the row margin of `≈ 8.6·10⁻⁵` — three orders of
magnitude of slack.  Domination, not equality, is the invariant: wherever the
machine cannot reproduce a value exactly it must only stay `≥` the exact one.

* **primes** `n`: `lam` is the running RS62 upper ladder, advanced by
  `incUWord n` (`Ports/RS62Increments.lean`, exact and word-safe) from the
  compile-time seed `seedL = logUpper n0` — *equal* to the exact ladder, since
  above the LeanCert handoff (`10⁴`) the exact ladder is this same recursion;
* **proper prime powers** `n = p^k`: `lam = seeds[p]`, the array cell holding
  `directLogUBfp p` — *equal* to the exact value; the power test is a
  24-round multiplication chain `p, p², …` compared against `n`, which can
  only over-accept (mod-`2⁶⁴` collisions), and over-acceptance only inflates;
* **other composites**: `lam = 0`, exact.

The candidates below the handoff, `n ≤ 10⁴`, are *not* swept here: their
exact prefix `W(10⁴)` enters as the compile-time constant `acc0`
(rounded up), certified in the goldbach tree by one kernel evaluation
(measured `≈ 34 ms` per LeanCert log seed).

## Width budget and the accumulator cap

At the production sizing every live quantity fits `u64` with headroom:
`acc ≤ capA = 4·10¹⁵`, `2500·acc ≤ 10¹⁹ < 2⁶⁴`, `20016·n² ≤ 7.3·10¹⁸`,
`n·(⌊lam/2²⁰⌋+1) < 1.7·10¹⁷`, and every `incUWord` intermediate is below
`2⁵¹`.  Because a sweep that exits `0` must not be able to have wrapped
(the SegSieve accumulator-width lesson), the body **checks `acc ≤ capA` at
every commit and counts a violation otherwise**: a run that returns `0`
certifies both every row and that the accumulator stayed in range.

## What is proved here and what is not

Proved here:

* `wmProgram_wf` — well-formedness, for every configuration; so
  `AProgram.evalCC_compile` applies and the emitted C computes exactly
  `AProgram.denote`;
* **`wmBody_defined`** — the body is *defined* at every index the loop visits,
  on any state satisfying the cross-iteration invariant `Inv`.  Every one of
  the seven partial instructions in the 137 is discharged: the decode's `urem`
  and `udiv` by the literal `B`, the scan's `urem` by the decoded trial
  divisor, the seed-table `load`, and the ladder's three divisions by `n`,
  `2·n` and `n − 1`.  The supporting register specs — `decode_rR`,
  `decode_rN`, `decode_rD`, `scan_rS`, `select_rIsP`, `select_rP_of_ne`,
  `load_index_lt` — are the arithmetic half of the encoding obligation below,
  proved here and reusable there;
* two kernel smoke checks: at a tiny configuration the 135-instruction body
  denotes exactly the independently written candidate-level reference
  `wmRef`, run both in passing and in violating sizings.

* **`wmProgram_denote` / `wmEncoding`** — `denote = some (wmRef c)` for every
  configuration satisfying `wmOK`.  This is the encoding obligation, and it
  has three parts, all of them here:
  * definedness (above);
  * the **value** of the body — `wmPre_vals` and `wmPost_vals` give every
    register, not just the divisors, and `wmBody_obs` assembles them into
    `wmRound`, one flat round written in ordinary mathematics.  Every read is
    `RegFrame.srun_read_write` followed by one `denoteOp` value lemma on a
    state that stays a variable, so no `fpD`-scale literal enters any goal;
  * the **re-blocking** of the flat `len · B` loop into `len` candidates of
    `B` rounds, through `Ports/BlockedFold.lean`.  `block_eq_wmStep` is the
    per-block statement — its size does not grow with `len` — and
    `foldl_wmRound_eq_wmRef` is the assembled fold.  The commit gate `r = B−1`
    is what makes a block one candidate: the first `B−1` rounds only advance
    the trial scan, and the last one commits the addend, both violation tests
    and the ladder, then clears the scan.

  The truncations are mirrored, not assumed away: `wmRound` and `wmStep` carry
  the machine's `% 2⁶⁴` at every point the machine has one, and the only
  places a bound is needed are the ones where the *reference* has no `%`
  (the violation counter, which the invariant keeps below `2·len + 2`).

So a run of this artifact reads a **proved** denotation off
(`Verified/ArrayComputation.lean`'s `value_of_returns`), and
`wmRef c = 0` becomes `WM217Rows` in the goldbach tree through
`checkWeightedMomentTable_eq_true_iff`.
-/

namespace LeanCompCert.Ports.RamareWM217

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

/-! ## Configuration -/

/-- Every constant the artifact is compiled against.  All of them appear as
literals in the emitted C. -/
structure Cfg where
  /-- First candidate (production: `10001`, the LeanCert handoff + 1). -/
  n0 : Nat
  /-- Number of candidates (production: `18 990 000`). -/
  len : Nat
  /-- Trial rounds per candidate; must cover the square root
  (`n0 + len ≤ (B + 2)²`; production: `4358`). -/
  B : Nat
  /-- First checked row (production: `1 600 000`). -/
  lower : Nat
  /-- The ladder seed `logUpper n0` (certified in the goldbach tree). -/
  seedL : Nat
  /-- Dominating rescaled prefix `⌈W(n0 − 1)/2⁴⁴⌉ + 1`. -/
  acc0 : Nat
  /-- Accumulator cap (production: `4·10¹⁵`). -/
  capA : Nat
  /-- Static array length (production: `4360 > B + 1`). -/
  tableLen : Nat
  /-- Seed cells `(p, directLogUBfp p)` for the prime bases `p ≤ B + 1`. -/
  seeds : List (Nat × Nat)
  deriving Repr

/-- Structural sanity, all decidable: coverage of the square root, seed cells
in range, the power chain long enough, and the width budget. -/
def wmOK (c : Cfg) : Bool :=
  decide (2 ≤ c.n0) && decide (1 ≤ c.B) &&
  decide (c.n0 + c.len ≤ (c.B + 2) ^ 2) &&
  decide (c.B + 1 < c.tableLen) &&
  decide (c.n0 + c.len ≤ 2 ^ 25) &&
  decide (c.tableLen ≤ 2 ^ 20) &&
  decide (2500 * (c.capA + 2 ^ 35) < M) &&
  decide (20016 * (c.n0 + c.len) ^ 2 < M) &&
  decide (c.seedL < 2 ^ 53) && decide (c.acc0 ≤ c.capA) &&
  c.seeds.all (fun e => decide (e.1 < c.tableLen) && decide (e.2 < 2 ^ 53)) &&
  decide (c.lower ≤ c.n0 + c.len)

/-! ## Register conventions -/

/-- Violation counter; the output.  `0` is the passing verdict. -/
def rBad : Nat := 0
/-- The dominating rescaled accumulator. -/
def rAcc : Nat := 1
/-- The running upper-ladder value `logUpper n`. -/
def rL : Nat := 2
/-- The smallest-factor scan accumulator (0 = nothing found yet). -/
def rS : Nat := 3
/-- The candidate, recomputed from the loop index. -/
def rN : Nat := 4
/-- The round `i % B`. -/
def rR : Nat := 5
/-- The trial divisor `r + 2`. -/
def rD : Nat := 6
/-- Scan gate. -/
def rG : Nat := 7
/-- Scratch. -/
def rT1 : Nat := 8
/-- Scratch. -/
def rT2 : Nat := 9
/-- Power-chain value. -/
def rM : Nat := 10
/-- The committed smallest factor (or the candidate itself when prime). -/
def rP : Nat := 11
/-- Primality gate: the scan found nothing. -/
def rIsP : Nat := 12
/-- Prime-power gate. -/
def rPow : Nat := 13
/-- The ladder value charged to this candidate. -/
def rLam : Nat := 14
/-- The commit gate `r = B − 1`. -/
def rC : Nat := 15
/-- Scratch (seed-table read). -/
def rT3 : Nat := 16
/-- Row gate `n ≥ lower`. -/
def rLow : Nat := 17
/-- `incUWord n`. -/
def rIU : Nat := 18

/-- Registers used. -/
def wmRegCount : Nat := 19

/-- Rounds of the multiplicative power chain: covers `n < 2²⁵`. -/
def powerRounds : Nat := 24

/-- `3·fpD` as a plain numeral.  Left as closed arithmetic it would be
re-evaluated at every defeq check — one of the two ways the kernel recursion
guard is tripped; the value is unchanged, so the emitted C is unchanged. -/
def fpD3 : Nat := 844424930131968

theorem fpD3_eq : fpD3 = 3 * fpD := rfl

/-! ## The body, in blocks

Every block below is a list of **scalar** instructions.  The body has exactly
one array instruction — the seed-table `load` — so it is written as

```text
lift (wmPre c) ++ (.load rT3 rT2 :: lift (wmPost c))
```

and `Verified/ArrayScalarBlock.lean` reduces each scalar stage to the
ordinary scalar machine (`InstrBlock.srun`), carrying the array along
untouched.  That is what keeps the transcription's goals small: the array is
never pushed through a scalar `simp`.
-/

/-- Decode: `r = i % B`, `n = n0 + i / B`, `d = r + 2`. -/
def decodeBlock (c : Cfg) : List Instr :=
  [ .binop rR .urem .idx (.lit c.B)
  , .binop rN .udiv .idx (.lit c.B)
  , .binop rN .add (.reg rN) (.lit c.n0)
  , .binop rD .add (.reg rR) (.lit 2) ]

/-- One trial round:
`s := if s = 0 ∧ d·d ≤ n ∧ n % d = 0 then d else s`. -/
def scanBlock : List Instr :=
  [ .binop rG .eq (.reg rS) (.lit 0)
  , .binop rT1 .mul (.reg rD) (.reg rD)
  , .binop rT1 .le (.reg rT1) (.reg rN)
  , .binop rG .mul (.reg rG) (.reg rT1)
  , .binop rT2 .urem (.reg rN) (.reg rD)
  , .binop rT2 .eq (.reg rT2) (.lit 0)
  , .binop rG .mul (.reg rG) (.reg rT2)
  , .binop rT1 .sub (.lit 1) (.reg rG)
  , .binop rT1 .mul (.reg rT1) (.reg rS)
  , .binop rT2 .mul (.reg rG) (.reg rD)
  , .binop rS .add (.reg rT1) (.reg rT2) ]

/-- Commit gate and factor select: `isP = (s = 0)`, `p = isP ? n : s`. -/
def selectBlock (c : Cfg) : List Instr :=
  [ .binop rC .eq (.reg rR) (.lit (c.B - 1))
  , .binop rIsP .eq (.reg rS) (.lit 0)
  , .binop rT1 .sub (.lit 1) (.reg rIsP)
  , .binop rT2 .mul (.reg rT1) (.reg rS)
  , .binop rT1 .mul (.reg rIsP) (.reg rN)
  , .binop rP .add (.reg rT1) (.reg rT2) ]

/-- One power-chain round: `m := m·p`, `pow := pow ∨ (m = n)`. -/
def powerRound : List Instr :=
  [ .binop rM .mul (.reg rM) (.reg rP)
  , .binop rT1 .eq (.reg rM) (.reg rN)
  , .binop rPow .bor (.reg rPow) (.reg rT1) ]

/-- `pow = (∃ k ≤ powerRounds + 1, p^k = n)`, by a multiplication chain.
Over-acceptance through mod-`2⁶⁴` collisions is sound: it only inflates. -/
def powerBlock : List Instr :=
  [ .mov rM (.reg rP)
  , .binop rPow .eq (.reg rM) (.reg rN) ] ++
  (List.range powerRounds).flatMap (fun _ => powerRound)

/-- The seed-table index, clamped to `0` in the prime case so the read stays
in range: `t2 = (1 − isP)·p`. -/
def lambdaPre : List Instr :=
  [ .binop rT1 .sub (.lit 1) (.reg rIsP)
  , .binop rT2 .mul (.reg rT1) (.reg rP) ]

/-- After the load: `lam = isP ? L : (pow ? seeds[p] : 0)`. -/
def lambdaPost : List Instr :=
  [ .binop rT1 .mul (.reg rT1) (.reg rPow)
  , .binop rT3 .mul (.reg rT1) (.reg rT3)
  , .binop rT2 .mul (.reg rIsP) (.reg rL)
  , .binop rLam .add (.reg rT2) (.reg rT3) ]

/-- The dominating rescaled addend, gated by the commit:
`acc += C · ((n·(⌊lam/2²⁰⌋ + 1)) >>> 24 + 1)`. -/
def accBlock : List Instr :=
  [ .binop rT1 .lshr (.reg rLam) (.lit 20)
  , .binop rT1 .add (.reg rT1) (.lit 1)
  , .binop rT1 .mul (.reg rT1) (.reg rN)
  , .binop rT1 .lshr (.reg rT1) (.lit 24)
  , .binop rT1 .add (.reg rT1) (.lit 1)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rAcc .add (.reg rAcc) (.reg rT1) ]

/-- The cap test: a committed accumulator beyond `capA` is a violation, so a
`0` verdict certifies the width budget as well as the rows. -/
def capBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .gt (.reg rAcc) (.lit c.capA)
  , .binop rT1 .mul (.reg rT1) (.reg rC)
  , .binop rBad .add (.reg rBad) (.reg rT1) ]

/-- The row test, at commits with `n ≥ lower`:
violation unless `2500·acc < 20016·n²`. -/
def rowBlock (c : Cfg) : List Instr :=
  [ .binop rT1 .mul (.reg rN) (.reg rN)
  , .binop rT1 .mul (.reg rT1) (.lit 20016)
  , .binop rT2 .mul (.reg rAcc) (.lit 2500)
  , .binop rT2 .ge (.reg rT2) (.reg rT1)
  , .binop rLow .ge (.reg rN) (.lit c.lower)
  , .binop rT2 .mul (.reg rT2) (.reg rLow)
  , .binop rT2 .mul (.reg rT2) (.reg rC)
  , .binop rBad .add (.reg rBad) (.reg rT2) ]

/-- `incUWord n`, instruction for instruction
(`Ports/RS62Increments.lean`), then the gated ladder advance. -/
def ladderBlock : List Instr :=
  [ .binop rT1 .mul (.reg rN) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit fpD3)
  , .binop rT2 .add (.reg rN) (.lit fpD3)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT2 .udiv (.reg rT2) (.reg rN)
  , .binop rT1 .sub (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.reg rN) (.lit 2)
  , .binop rT1 .udiv (.reg rT1) (.reg rT2)
  , .binop rT2 .add (.reg rN) (.lit fpD)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT1 .sub (.reg rT2) (.reg rT1)
  , .binop rT2 .sub (.reg rN) (.lit 1)
  , .binop rIU .udiv (.reg rT1) (.reg rT2)
  , .binop rT1 .mul (.reg rC) (.reg rIU)
  , .binop rL .add (.reg rL) (.reg rT1) ]

/-- Clear the scan accumulator at the last round of each candidate. -/
def resetBlock : List Instr :=
  [ .binop rT1 .sub (.lit 1) (.reg rC)
  , .binop rS .mul (.reg rT1) (.reg rS) ]

/-- Everything before the seed-table read. -/
def wmPre (c : Cfg) : List Instr :=
  decodeBlock c ++ scanBlock ++ selectBlock c ++ powerBlock ++ lambdaPre

/-- Everything after it. -/
def wmPost (c : Cfg) : List Instr :=
  lambdaPost ++ accBlock ++ capBlock c ++ rowBlock c ++ ladderBlock ++
    resetBlock

/-- The loop body: 137 instructions, every one executed every iteration,
with the single array access in the middle. -/
def wmBody (c : Cfg) : List AInstr :=
  lift (wmPre c) ++ (.load rT3 rT2 :: lift (wmPost c))

/-- Initialization: the two carried registers, then the seed table. -/
def wmInit (c : Cfg) : List AInstr :=
  lift [ .mov rAcc (.lit c.acc0), .mov rL (.lit c.seedL) ] ++
  c.seeds.flatMap (fun e =>
    [ .scalar (.mov rT1 (.lit e.1))
    , .scalar (.mov rT2 (.lit e.2))
    , .store rT1 rT2 ])

/-- **The artifact.**  One flat loop of `len · B` iterations over one
read-only array of `tableLen` cells; output is the violation counter. -/
def wmProgram (c : Cfg) : AProgram :=
  { regCount := wmRegCount
  , arrayLen := c.tableLen
  , loopCount := c.len * c.B
  , init := wmInit c
  , body := wmBody c
  , epilogue := []
  , output := rBad }

/-! ## Well-formedness -/

/-- Register bounds for one operand, as a Boolean. -/
def operandOK : Operand → Bool
  | .reg j => decide (j < wmRegCount)
  | _ => true

/-- Register bounds for a scalar instruction, as a Boolean. -/
def instrOK : Instr → Bool
  | .mov d src => decide (d < wmRegCount) && operandOK src
  | .binop d _ l r => decide (d < wmRegCount) && operandOK l && operandOK r

theorem operand_wf_of_ok {o : Operand} (h : operandOK o = true) :
    o.WF wmRegCount := by
  cases o with
  | reg j => simpa [operandOK, Operand.WF] using h
  | lit v => exact trivial
  | idx => exact trivial

theorem wf_of_instrOK {i : Instr} (h : instrOK i = true) : i.WF wmRegCount := by
  cases i with
  | mov d src =>
      simp only [instrOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, operand_wf_of_ok h.2⟩
  | binop d op l r =>
      simp only [instrOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, operand_wf_of_ok h.1.2, operand_wf_of_ok h.2⟩

theorem lift_wf {xs : List Instr} (h : xs.all instrOK = true) :
    ∀ a ∈ lift xs, a.WF wmRegCount := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_lift ha
  exact wf_of_instrOK ((List.all_eq_true.mp h) i hi)

private theorem powerBlock_ok : powerBlock.all instrOK = true := by
  simp only [powerBlock, List.all_append, List.all_cons, List.all_nil,
    List.all_flatMap, Bool.and_eq_true]
  refine ⟨⟨?_, ?_, trivial⟩, ?_⟩
  · simp +decide [instrOK, operandOK, wmRegCount, rM, rP]
  · simp +decide [instrOK, operandOK, wmRegCount, rPow, rM, rN]
  · rw [List.all_eq_true]
    intro x _
    simp +decide [powerRound, instrOK, operandOK, wmRegCount, rM, rP, rN,
      rT1, rPow]

theorem wmPre_ok (c : Cfg) : (wmPre c).all instrOK = true := by
  simp only [wmPre, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, powerBlock_ok⟩, ?_⟩ <;>
    simp +decide [decodeBlock, scanBlock, selectBlock, lambdaPre, instrOK,
      operandOK, wmRegCount, rBad, rAcc, rL, rS, rN, rR, rD, rG, rT1, rT2,
      rM, rP, rIsP, rPow, rLam, rC, rT3, rLow, rIU]

theorem wmPost_ok (c : Cfg) : (wmPost c).all instrOK = true := by
  simp +decide [wmPost, lambdaPost, accBlock, capBlock, rowBlock,
    ladderBlock, resetBlock, List.all_append, instrOK, operandOK,
    wmRegCount, rBad, rAcc, rL, rS, rN, rR, rD, rG, rT1, rT2, rM, rP,
    rIsP, rPow, rLam, rC, rT3, rLow, rIU]

theorem wmBody_wf (c : Cfg) : ∀ a ∈ wmBody c, a.WF wmRegCount := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact lift_wf (wmPre_ok c) a h
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by simp [wmRegCount, rT3], by simp [wmRegCount, rT2]⟩
    · exact lift_wf (wmPost_ok c) a h

theorem wmInit_wf (c : Cfg) : ∀ a ∈ wmInit c, a.WF wmRegCount := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · refine lift_wf ?_ a h
    simp +decide [instrOK, operandOK, wmRegCount, rAcc, rL]
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨by simp [wmRegCount, rT1], trivial⟩
    · exact ⟨by simp [wmRegCount, rT2], trivial⟩
    · exact ⟨by simp [wmRegCount, rT1], by simp [wmRegCount, rT2]⟩

/-- **The program is well formed** at every configuration, so
`AProgram.evalCC_compile` applies: the compiled trace and the emitted C
compute exactly `AProgram.denote`. -/
theorem wmProgram_wf (c : Cfg) : (wmProgram c).WF := by
  refine ⟨by simp [wmProgram, wmRegCount, rBad], ?_, ?_, ?_⟩
  · exact wmInit_wf c
  · exact wmBody_wf c
  · intro a ha
    exact absurd ha (by simp [wmProgram])

/-! ## Definedness

`ArrayMobiusDenotation` records definedness as the obligation that blocked
its transcription.  Here it costs three lines per partial instruction,
because `allDefined_lift_of_noDiv` retires every division-free stage at
once.  What is left is exactly the genuinely partial instructions: the
`urem`/`udiv` of the decode, the `urem` of the scan, the four divisions of
the ladder, and the single array read.
-/

/-- The division-free tail of the pre-load stage: everything after the trial
round. -/
def wmPreTail (c : Cfg) : List Instr :=
  selectBlock c ++ powerBlock ++ lambdaPre

theorem wmPre_eq (c : Cfg) :
    wmPre c = decodeBlock c ++ scanBlock ++ wmPreTail c := by
  simp [wmPre, wmPreTail, List.append_assoc]

/-- **The select/power/lambda stage is defined, unconditionally.**  One line,
because it contains no division and `allDefined_lift_of_noDiv` does the rest. -/
theorem wmPreTail_defined (c : Cfg) (len k : Nat) (s : AState) :
    AllDefined len k s (lift (wmPreTail c)) := by
  refine allDefined_lift_of_noDiv len k _ s ?_
  simp +decide [wmPreTail, selectBlock, powerBlock, powerRound, lambdaPre,
    List.all_append, List.all_flatMap, InstrBlock.NoDivI]

/-- **The post-load stage up to the ladder is defined, unconditionally.** -/
theorem lambdaPost_acc_cap_row_defined (c : Cfg) (len k : Nat) (s : AState) :
    AllDefined len k s
      (lift (lambdaPost ++ accBlock ++ capBlock c ++ rowBlock c)) := by
  refine allDefined_lift_of_noDiv len k _ s ?_
  simp +decide [lambdaPost, accBlock, capBlock, rowBlock, List.all_append,
    InstrBlock.NoDivI]

/-- **The reset stage is defined, unconditionally.** -/
theorem resetBlock_defined (len k : Nat) (s : AState) :
    AllDefined len k s (lift resetBlock) := by
  refine allDefined_lift_of_noDiv len k _ s ?_
  simp +decide [resetBlock, InstrBlock.NoDivI]

/-! ## The loop invariant

The single cross-iteration fact the body needs: between candidates the scan
accumulator is either cleared or holds a trial divisor `≤ B + 1`.  With
`wmOK`'s `B + 1 < tableLen` that is exactly what puts the seed-table read in
range, which is the one array access in the program.
-/

/-- What the body needs to know about the state it starts in. -/
structure Inv (c : Cfg) (s : AState) : Prop where
  /-- Every register holds a word. -/
  regsLt : ∀ j, s.regs j < M
  /-- The scan accumulator is cleared or holds a trial divisor. -/
  scan : s.regs rS = 0 ∨ (2 ≤ s.regs rS ∧ s.regs rS ≤ c.B + 1)

/-! ## What `wmOK` buys -/

theorem ok_n0 {c : Cfg} (h : wmOK c = true) : 2 ≤ c.n0 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1

theorem ok_B {c : Cfg} (h : wmOK c = true) : 1 ≤ c.B := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.2

theorem ok_tableLen {c : Cfg} (h : wmOK c = true) : c.B + 1 < c.tableLen := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem ok_range {c : Cfg} (h : wmOK c = true) : c.n0 + c.len ≤ 2 ^ 25 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.2

theorem ok_tableLen_le {c : Cfg} (h : wmOK c = true) : c.tableLen ≤ 2 ^ 20 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.2

theorem ok_capA {c : Cfg} (h : wmOK c = true) : 2500 * (c.capA + 2 ^ 35) < M := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

theorem ok_rowFit {c : Cfg} (h : wmOK c = true) :
    20016 * (c.n0 + c.len) ^ 2 < M := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

theorem ok_seedL {c : Cfg} (h : wmOK c = true) : c.seedL < 2 ^ 53 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem ok_acc0 {c : Cfg} (h : wmOK c = true) : c.acc0 ≤ c.capA := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem ok_seeds {c : Cfg} (h : wmOK c = true) :
    c.seeds.all (fun e => decide (e.1 < c.tableLen) && decide (e.2 < 2 ^ 53))
      = true := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- The row gate's literal is in range: the only configuration constant that
is not otherwise bounded, and the emitted `n >= lower` would compare against
`lower % 2⁶⁴` if it were not. -/
theorem ok_lower {c : Cfg} (h : wmOK c = true) : c.lower ≤ c.n0 + c.len := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem ok_B_lt {c : Cfg} (h : wmOK c = true) : c.B + 1 < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (ok_tableLen h) (ok_tableLen_le h)

theorem M_big : 2 ^ 25 < M := by decide

theorem ok_BM {c : Cfg} (h : wmOK c = true) : c.B < M := by
  have h1 := ok_B_lt h
  have : (2:Nat) ^ 20 < M := by decide
  omega

/-- The flat loop index is a word, and decodes without wrapping. -/
theorem ok_idx {c : Cfg} (h : wmOK c = true) {k : Nat} (hk : k < c.len * c.B) :
    k < M ∧ k / c.B < c.len ∧ k % c.B < c.B := by
  have hB : 0 < c.B := ok_B h
  have hlen : c.len ≤ 2 ^ 25 := by have := ok_range h; omega
  have hBlt : c.B ≤ 2 ^ 20 := by have := ok_B_lt h; omega
  have hprod : c.len * c.B ≤ 2 ^ 25 * 2 ^ 20 := Nat.mul_le_mul hlen hBlt
  have hfits : (2:Nat) ^ 25 * 2 ^ 20 < M := by decide
  refine ⟨by omega, ?_, Nat.mod_lt _ hB⟩
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)

/-! ## Definedness

Each of the three blocks containing a partial instruction, with the side
condition it needs named in its own statement.  Every other stage is
division-free and was retired wholesale by `allDefined_lift_of_noDiv` above.
-/

/-- The decode divisions are by the literal `B`. -/
theorem decodeBlock_defined (c : Cfg) (k : Nat) (s : AState) (hBM : c.B < M)
    (hB : 0 < c.B) : AllDefined c.tableLen k s (lift (decodeBlock c)) := by
  have hbne : ¬ (c.B % M = 0) := by rw [Nat.mod_eq_of_lt hBM]; omega
  rw [allDefined_lift]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
    simp [decodeBlock, InstrBlock.SDefined, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, hbne]

/-! ### The other two partial stages

The previous pass recorded two obstructions here, and both were the absence of
a generic primitive rather than anything about this program.

**The scan.**  Its `urem` divisor is `rD`, set by the *decode* four
instructions earlier, so the goal carried four nested `RegState.set`s.  That
is framing, and `Verified/RegFrame.lean` now does it: `srun_frame` erases a
block that does not write the register, on a `by decide` over register indices.

**The ladder.**  Unfolding `ladderBlock` inside `simp` tripped the kernel's
recursion guard outright — the ladder is the one block whose operands are
`fpD`-scale literals, and the `% M` around each `denoteOp` put a symbolic
register next to one of them.  Reordering the operands would fix it and would
also change the emitted C, invalidating the measured production run, so the
fix had to be proof-side: `Verified/BlockDefined.lean` advances the obligation
one stage at a time and turns *only* the divisions into values.  The ladder
proof below never unfolds the arithmetic of the twelve instructions that are
not divisions, so `fpD3` and `fpD` appear in no goal at all.

The sub-block names below are a `rfl`-provable regrouping of the very same
instruction lists — `decodeBlock`, `scanBlock` and `ladderBlock` are
unchanged, so the emitted C is unchanged.
-/

/-! #### The decode, read register by register -/

private def dR (c : Cfg) : Instr := .binop rR .urem .idx (.lit c.B)
private def dNq (c : Cfg) : Instr := .binop rN .udiv .idx (.lit c.B)
private def dNa (c : Cfg) : Instr := .binop rN .add (.reg rN) (.lit c.n0)
private def dD : Instr := .binop rD .add (.reg rR) (.lit 2)

private theorem decode_split_R (c : Cfg) :
    decodeBlock c = dR c :: [dNq c, dNa c, dD] := rfl

private theorem decode_split_N (c : Cfg) :
    decodeBlock c = [dR c, dNq c] ++ dNa c :: [dD] := rfl

private theorem decode_split_D (c : Cfg) :
    decodeBlock c = [dR c, dNq c, dNa c] ++ dD :: [] := rfl

/-- The round `r = k % B`. -/
theorem decode_rR (c : Cfg) (k : Nat) (s : RegState) (hk : k < M) (hB : 0 < c.B)
    (hBM : c.B < M) : srun k s (decodeBlock c) rR = k % c.B := by
  rw [decode_split_R, srun_read_head k rR (dR c) [dNq c, dNa c, dD] rfl rfl]
  simp only [dR]
  exact sval_binop_val (denoteOperand_idx_of_lt k s hk)
    (denoteOperand_lit_of_lt k s hBM) (denoteOp_urem_of_ne (by omega) hk)

private theorem decode_rR_pre (c : Cfg) (k : Nat) (s : RegState) (hk : k < M)
    (hB : 0 < c.B) (hBM : c.B < M) :
    srun k s [dR c, dNq c, dNa c] rR = k % c.B := by
  rw [show ([dR c, dNq c, dNa c] : List Instr) = dR c :: [dNq c, dNa c] from rfl,
    srun_read_head k rR (dR c) [dNq c, dNa c] rfl rfl]
  simp only [dR]
  exact sval_binop_val (denoteOperand_idx_of_lt k s hk)
    (denoteOperand_lit_of_lt k s hBM) (denoteOp_urem_of_ne (by omega) hk)

private theorem decode_rN_pre (c : Cfg) (k : Nat) (s : RegState) (hk : k < M)
    (hB : 0 < c.B) (hBM : c.B < M) :
    srun k s [dR c, dNq c] rN = k / c.B := by
  rw [show ([dR c, dNq c] : List Instr) = [dR c] ++ dNq c :: [] from rfl,
    srun_read_write k rN [dR c] (dNq c) [] rfl rfl]
  simp only [dNq]
  exact sval_binop_val (denoteOperand_idx_of_lt _ _ hk)
    (denoteOperand_lit_of_lt _ _ hBM) (denoteOp_udiv_of_ne (by omega) hk)

/-- The candidate `n = n0 + k / B`. -/
theorem decode_rN (c : Cfg) (k : Nat) (s : RegState) (hk : k < M) (hB : 0 < c.B)
    (hBM : c.B < M) (hsum : k / c.B + c.n0 < M) :
    srun k s (decodeBlock c) rN = k / c.B + c.n0 := by
  rw [decode_split_N, srun_read_write k rN [dR c, dNq c] (dNa c) [dD] rfl (by decide)]
  simp only [dNa]
  exact sval_binop_val (decode_rN_pre c k s hk hB hBM)
    (denoteOperand_lit_of_lt _ _
      (Nat.lt_of_le_of_lt (Nat.le_add_left c.n0 (k / c.B)) hsum))
    (denoteOp_add_of_lt hsum)

/-- The trial divisor `d = r + 2`. -/
theorem decode_rD (c : Cfg) (k : Nat) (s : RegState) (hk : k < M) (hB : 0 < c.B)
    (hBM : c.B < M) (hD : k % c.B + 2 < M) :
    srun k s (decodeBlock c) rD = k % c.B + 2 := by
  rw [decode_split_D, srun_read_write k rD [dR c, dNq c, dNa c] dD [] rfl rfl]
  simp only [dD]
  exact sval_binop_val (decode_rR_pre c k s hk hB hBM)
    (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_add_of_lt hD)

/-! #### The scan -/

private def sG0 : Instr := .binop rG .eq (.reg rS) (.lit 0)
private def sT1a : Instr := .binop rT1 .mul (.reg rD) (.reg rD)
private def sT1b : Instr := .binop rT1 .le (.reg rT1) (.reg rN)
private def sG1 : Instr := .binop rG .mul (.reg rG) (.reg rT1)
private def scanDiv : Instr := .binop rT2 .urem (.reg rN) (.reg rD)
private def sT2b : Instr := .binop rT2 .eq (.reg rT2) (.lit 0)
private def sG2 : Instr := .binop rG .mul (.reg rG) (.reg rT2)
private def sT1c : Instr := .binop rT1 .sub (.lit 1) (.reg rG)
private def sT1d : Instr := .binop rT1 .mul (.reg rT1) (.reg rS)
private def sT2c : Instr := .binop rT2 .mul (.reg rG) (.reg rD)
private def sS : Instr := .binop rS .add (.reg rT1) (.reg rT2)

private def scanPre : List Instr := [sG0, sT1a, sT1b, sG1]

private def scanPost : List Instr := [sT2b, sG2, sT1c, sT1d, sT2c, sS]

private theorem scanBlock_eq : scanBlock = scanPre ++ scanDiv :: scanPost := rfl

/-- **The trial round is defined as soon as its divisor is nonzero on entry.**

`rD` is written by the decode and read here, four instructions into a block
that never touches it, so the hypothesis is about the state the *decode*
leaves — which `decode_rD` computes. -/
theorem scanBlock_defined (k : Nat) (s : RegState) (hD : s rD ≠ 0) :
    SAllDefined k s scanBlock := by
  rw [scanBlock_eq]
  refine sAllDefined_stage (by decide) ?_ (sAllDefined_of_noDiv k _ _ (by decide))
  simp only [scanDiv]
  refine sDefined_urem ?_
  simp only [denoteOperand_reg]
  rw [srun_frame k rD scanPre (by decide)]
  exact hD

/-! #### What the scan leaves in `rS`

The one cross-iteration fact the body needs.  Its gate is a *flag*, and the
proof case-splits on that flag without evaluating any of the five instructions
that compute it — `BlockDefined.sval_mul_isBit` and `sval_eq_isBit` say a
product of comparisons is a bit, whatever the comparisons are about. -/

private def scanP3 : List Instr := [sG0, sT1a, sT1b]
private def scanQ : List Instr := scanPre ++ [scanDiv, sT2b]
private def scanR3 : List Instr := scanQ ++ [sG2]
private def scanR2 : List Instr := scanR3 ++ [sT1c]
private def scanR1 : List Instr := scanR2 ++ [sT1d]
private def scanR0 : List Instr := scanR1 ++ [sT2c]

private theorem scanBlock_eq_R0 : scanBlock = scanR0 ++ [sS] := rfl

/-- The scan's gate, at the point the tail consumes it. -/
private def gate (k : Nat) (s : RegState) : Nat := sval k (srun k s scanQ) sG2

private theorem gate_isBit (k : Nat) (s : RegState) : IsBit (gate k s) := by
  unfold gate
  refine sval_mul_isBit ?_ ?_
  · show IsBit (srun k s scanQ rG)
    unfold scanQ
    rw [srun_frame_append k rG scanPre [scanDiv, sT2b] rfl,
      show scanPre = scanP3 ++ [sG1] from rfl,
      srun_read_last k rG scanP3 sG1 rfl]
    refine sval_mul_isBit ?_ ?_
    · show IsBit (srun k s scanP3 rG)
      rw [show scanP3 = sG0 :: [sT1a, sT1b] from rfl,
        srun_read_head k rG sG0 [sT1a, sT1b] rfl rfl]
      exact sval_eq_isBit _ _ _ _ _
    · show IsBit (srun k s scanP3 rT1)
      rw [show scanP3 = [sG0, sT1a] ++ [sT1b] from rfl,
        srun_read_last k rT1 [sG0, sT1a] sT1b rfl]
      exact sval_le_isBit _ _ _ _ _
  · show IsBit (srun k s scanQ rT2)
    rw [show scanQ = (scanPre ++ [scanDiv]) ++ [sT2b] from rfl,
      srun_read_last k rT2 (scanPre ++ [scanDiv]) sT2b rfl]
    exact sval_eq_isBit _ _ _ _ _

/-- **A trial round either keeps the scan accumulator or replaces it by this
round's divisor.**  Together with `decode_rD` this is the entire cross-iteration
invariant `Inv.scan`: `rS` is `0` or a trial divisor `≤ B + 1`. -/
theorem scan_rS (k : Nat) (s : RegState) (hS : s rS < M) (hD : s rD < M) :
    srun k s scanBlock rS = s rS ∨ srun k s scanBlock rS = s rD := by
  have hM1 : (1 : Nat) < M := by decide
  have hgR3 : srun k s scanR3 rG = gate k s := by
    unfold gate scanR3
    exact srun_read_last k rG scanQ sG2 rfl s
  have hgR2 : srun k s scanR2 rG = gate k s := by
    unfold scanR2
    rw [srun_frame_append k rG scanR3 [sT1c] rfl]
    exact hgR3
  have hgR1 : srun k s scanR1 rG = gate k s := by
    unfold scanR1
    rw [srun_frame_append k rG scanR2 [sT1d] rfl]
    exact hgR2
  have hS2 : srun k s scanR2 rS = s rS := srun_frame k rS scanR2 rfl s
  have hD1 : srun k s scanR1 rD = s rD := srun_frame k rD scanR1 rfl s
  have hT1c : srun k s scanR2 rT1 = (denoteOp .sub 1 (gate k s)).getD 0 := by
    unfold scanR2
    rw [srun_read_last k rT1 scanR3 sT1c rfl]
    unfold sT1c
    rw [sval_binop, denoteOperand_lit_of_lt _ _ hM1, denoteOperand_reg, hgR3]
  have hT1R1 : srun k s scanR1 rT1 =
      (denoteOp .mul (srun k s scanR2 rT1) (s rS)).getD 0 := by
    unfold scanR1
    rw [srun_read_last k rT1 scanR2 sT1d rfl]
    unfold sT1d
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hS2]
  have hT1R0 : srun k s scanR0 rT1 = srun k s scanR1 rT1 := by
    unfold scanR0
    exact srun_frame_append k rT1 scanR1 [sT2c] rfl s
  have hT2R0 : srun k s scanR0 rT2 = (denoteOp .mul (gate k s) (s rD)).getD 0 := by
    unfold scanR0
    rw [srun_read_last k rT2 scanR1 sT2c rfl]
    unfold sT2c
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hgR1, hD1]
  have hfinal : srun k s scanBlock rS =
      (denoteOp .add (srun k s scanR0 rT1) (srun k s scanR0 rT2)).getD 0 := by
    rw [scanBlock_eq_R0, srun_read_last k rS scanR0 sS rfl]
    unfold sS
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg]
  rcases gate_isBit k s with hg | hg
  · left
    have h1 : (denoteOp .sub 1 (0 : Nat)).getD 0 = 1 := by
      rw [denoteOp_sub_of_le (Nat.zero_le 1) hM1]
      rfl
    have h2 : (denoteOp .mul 1 (s rS)).getD 0 = s rS := by
      rw [denoteOp_mul_of_lt (show 1 * s rS < M by omega)]
      exact Nat.one_mul _
    have h3 : (denoteOp .mul 0 (s rD)).getD 0 = 0 := by
      rw [denoteOp_mul_of_lt (show 0 * s rD < M by rw [Nat.zero_mul]; exact M_pos)]
      exact Nat.zero_mul _
    have h4 : (denoteOp .add (s rS) 0).getD 0 = s rS := by
      rw [denoteOp_add_of_lt (show s rS + 0 < M by omega)]
      exact Nat.add_zero _
    rw [hg, h1] at hT1c
    rw [hg, h3] at hT2R0
    rw [hfinal, hT1R0, hT1R1, hT1c, h2, hT2R0, h4]
  · right
    have h1 : (denoteOp .sub 1 (1 : Nat)).getD 0 = 0 := by
      rw [denoteOp_sub_of_le (Nat.le_refl 1) hM1]
      rfl
    have h2 : (denoteOp .mul 0 (s rS)).getD 0 = 0 := by
      rw [denoteOp_mul_of_lt (show 0 * s rS < M by rw [Nat.zero_mul]; exact M_pos)]
      exact Nat.zero_mul _
    have h3 : (denoteOp .mul 1 (s rD)).getD 0 = s rD := by
      rw [denoteOp_mul_of_lt (show 1 * s rD < M by omega)]
      exact Nat.one_mul _
    have h4 : (denoteOp .add 0 (s rD)).getD 0 = s rD := by
      rw [denoteOp_add_of_lt (show 0 + s rD < M by omega)]
      exact Nat.zero_add _
    rw [hg, h1] at hT1c
    rw [hg, h3] at hT2R0
    rw [hfinal, hT1R0, hT1R1, hT1c, h2, hT2R0, h4]

/-! #### The ladder -/

private def ladderA : List Instr :=
  [ .binop rT1 .mul (.reg rN) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit fpD3)
  , .binop rT2 .add (.reg rN) (.lit fpD3)
  , .binop rT2 .sub (.reg rT2) (.lit 1) ]

private def ladderDivA : Instr := .binop rT2 .udiv (.reg rT2) (.reg rN)

private def ladderB0 : List Instr := [ .binop rT1 .sub (.reg rT1) (.reg rT2) ]

private def ladderBset : Instr := .binop rT2 .mul (.reg rN) (.lit 2)

private def ladderDivB : Instr := .binop rT1 .udiv (.reg rT1) (.reg rT2)

private def ladderC0 : List Instr :=
  [ .binop rT2 .add (.reg rN) (.lit fpD)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT1 .sub (.reg rT2) (.reg rT1) ]

private def ladderCset : Instr := .binop rT2 .sub (.reg rN) (.lit 1)

private def ladderDivC : Instr := .binop rIU .udiv (.reg rT1) (.reg rT2)

private def ladderTail : List Instr :=
  [ .binop rT1 .mul (.reg rC) (.reg rIU)
  , .binop rL .add (.reg rL) (.reg rT1) ]

private def ladderC : List Instr :=
  (ladderC0 ++ [ladderCset]) ++ ladderDivC :: ladderTail

private def ladderBC : List Instr :=
  (ladderB0 ++ [ladderBset]) ++ ladderDivB :: ladderC

private theorem ladderBlock_eq :
    ladderBlock = ladderA ++ ladderDivA :: ladderBC := rfl

/-- The second ladder divisor, `2·n`, read off the one instruction that sets
it.  The three instructions of `ladderB0` are framed away, not evaluated. -/
private theorem ladder_setB (k : Nat) (u : RegState) (h : u rN * 2 < M) :
    srun k u (ladderB0 ++ [ladderBset]) rT2 = u rN * 2 := by
  rw [srun_read_last k rT2 ladderB0 ladderBset rfl]
  simp only [ladderBset]
  refine sval_binop_val ?_ (denoteOperand_lit_of_lt _ _ (by decide))
    (denoteOp_mul_of_lt h)
  simp only [denoteOperand_reg]
  exact srun_frame k rN ladderB0 (by decide) u

/-- The third ladder divisor, `n − 1`.  The machine computes it as
`n + (2⁶⁴ − 1)`; `denoteOp_sub_of_le` is what keeps that literal out of the
goal. -/
private theorem ladder_setC (k : Nat) (u : RegState) (h1 : 1 ≤ u rN)
    (h2 : u rN < M) :
    srun k u (ladderC0 ++ [ladderCset]) rT2 = u rN - 1 := by
  rw [srun_read_last k rT2 ladderC0 ladderCset rfl]
  simp only [ladderCset]
  refine sval_binop_val ?_ (denoteOperand_lit_of_lt _ _ (by decide))
    (denoteOp_sub_of_le h1 h2)
  simp only [denoteOperand_reg]
  exact srun_frame k rN ladderC0 (by decide) u

private theorem ladderC_defined (k : Nat) (v : RegState) (hN : 2 ≤ v rN)
    (hM : v rN < M) : SAllDefined k v ladderC := by
  refine sAllDefined_stage (by decide) ?_ (sAllDefined_of_noDiv k _ _ (by decide))
  simp only [ladderDivC]
  refine sDefined_udiv ?_
  simp only [denoteOperand_reg]
  rw [ladder_setC k v (by omega) hM]
  omega

private theorem ladderBC_defined (k : Nat) (u : RegState) (hN : 2 ≤ u rN)
    (hM : 2 * u rN < M) : SAllDefined k u ladderBC := by
  refine sAllDefined_stage (by decide) ?_ ?_
  · simp only [ladderDivB]
    refine sDefined_udiv ?_
    simp only [denoteOperand_reg]
    rw [ladder_setB k u (by omega)]
    omega
  · have e : srun k u ((ladderB0 ++ [ladderBset]) ++ [ladderDivB]) rN = u rN :=
      srun_frame k rN _ (by decide) u
    exact ladderC_defined k _ (by rw [e]; exact hN) (by rw [e]; omega)

/-- **The ladder is defined for every candidate `≥ 2` whose double is a word.**

Its three divisors are `n`, `2·n` and `n − 1`, and each is read with one
framing step.  What the proof does not do is the point: it never unfolds the
arithmetic of the twelve instructions that are not divisions, so the
`fpD`-scale literals they carry never enter a goal.  Doing that inside `simp`
is what reported `(kernel) deep recursion detected`. -/
theorem ladderBlock_defined (k : Nat) (s : RegState) (h2 : 2 ≤ s rN)
    (hM : 2 * s rN < M) : SAllDefined k s ladderBlock := by
  rw [ladderBlock_eq]
  refine sAllDefined_stage (by decide) ?_ ?_
  · simp only [ladderDivA]
    refine sDefined_udiv ?_
    simp only [denoteOperand_reg]
    rw [srun_frame k rN ladderA (by decide)]
    omega
  · have e : srun k s (ladderA ++ [ladderDivA]) rN = s rN :=
      srun_frame k rN _ (by decide) s
    exact ladderBC_defined k _ (by rw [e]; exact h2) (by rw [e]; exact hM)

/-! #### The seed-table index

The program's single array access.  Its index register is `(1 − isP)·p`:
zero when the candidate is prime, and otherwise the divisor the scan
committed, which `scan_rS` bounds by `B + 1 < tableLen`.  This is the last of
the named side conditions. -/

private def sel0 (c : Cfg) : Instr := .binop rC .eq (.reg rR) (.lit (c.B - 1))
private def sel1 : Instr := .binop rIsP .eq (.reg rS) (.lit 0)
private def sel2 : Instr := .binop rT1 .sub (.lit 1) (.reg rIsP)
private def sel3 : Instr := .binop rT2 .mul (.reg rT1) (.reg rS)
private def sel4 : Instr := .binop rT1 .mul (.reg rIsP) (.reg rN)
private def sel5 : Instr := .binop rP .add (.reg rT1) (.reg rT2)

private theorem selectBlock_eq (c : Cfg) :
    selectBlock c = [sel0 c, sel1, sel2, sel3, sel4, sel5] := rfl

private def lp0 : Instr := .binop rT1 .sub (.lit 1) (.reg rIsP)
private def lp1 : Instr := .binop rT2 .mul (.reg rT1) (.reg rP)

private theorem lambdaPre_eq : lambdaPre = [lp0] ++ [lp1] := rfl

/-- The primality flag, read off the one instruction that writes it. -/
private theorem sel_isP_val (k : Nat) (u : RegState) (c : Cfg) :
    sval k (srun k u [sel0 c]) sel1 = (if u rS = 0 then 1 else 0) := by
  unfold sel1
  rw [sval_binop, denoteOperand_reg, denoteOperand_lit_of_lt _ _ M_pos,
    srun_frame k rS [sel0 c] rfl, denoteOp_eq_val]
  rfl

private theorem select_rIsP (k : Nat) (u : RegState) (c : Cfg) :
    srun k u (selectBlock c) rIsP = (if u rS = 0 then 1 else 0) := by
  rw [selectBlock_eq,
    show ([sel0 c, sel1, sel2, sel3, sel4, sel5] : List Instr)
      = [sel0 c] ++ sel1 :: [sel2, sel3, sel4, sel5] from rfl,
    srun_read_write k rIsP [sel0 c] sel1 [sel2, sel3, sel4, sel5] rfl rfl]
  exact sel_isP_val k u c

/-- On a composite candidate the committed factor is the scan's divisor.  (The
prime case is not needed for definedness — the index is clamped to `0` there.) -/
private theorem select_rP_of_ne (k : Nat) (u : RegState) (c : Cfg)
    (hS : u rS < M) (h0 : u rS ≠ 0) :
    srun k u (selectBlock c) rP = u rS := by
  have hM1 : (1 : Nat) < M := by decide
  have hisp2 : srun k u [sel0 c, sel1] rIsP = 0 := by
    rw [show ([sel0 c, sel1] : List Instr) = [sel0 c] ++ sel1 :: [] from rfl,
      srun_read_write k rIsP [sel0 c] sel1 [] rfl rfl, sel_isP_val k u c,
      if_neg h0]
  have hisp4 : srun k u [sel0 c, sel1, sel2, sel3] rIsP = 0 := by
    rw [show ([sel0 c, sel1, sel2, sel3] : List Instr)
        = [sel0 c] ++ sel1 :: [sel2, sel3] from rfl,
      srun_read_write k rIsP [sel0 c] sel1 [sel2, sel3] rfl rfl, sel_isP_val k u c,
      if_neg h0]
  have hsub : (denoteOp .sub 1 (0 : Nat)).getD 0 = 1 := by
    rw [denoteOp_sub_of_le (Nat.zero_le 1) hM1]
    rfl
  have ht1_3 : srun k u [sel0 c, sel1, sel2] rT1 = 1 := by
    rw [show ([sel0 c, sel1, sel2] : List Instr) = [sel0 c, sel1] ++ [sel2] from rfl,
      srun_read_last k rT1 [sel0 c, sel1] sel2 rfl]
    unfold sel2
    rw [sval_binop, denoteOperand_lit_of_lt _ _ hM1, denoteOperand_reg, hisp2, hsub]
  have ht2_4 : srun k u [sel0 c, sel1, sel2, sel3] rT2 = u rS := by
    rw [show ([sel0 c, sel1, sel2, sel3] : List Instr)
        = [sel0 c, sel1, sel2] ++ [sel3] from rfl,
      srun_read_last k rT2 [sel0 c, sel1, sel2] sel3 rfl]
    unfold sel3
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, ht1_3,
      srun_frame k rS [sel0 c, sel1, sel2] rfl,
      denoteOp_mul_of_lt (show 1 * u rS < M by omega)]
    exact Nat.one_mul _
  have ht1_5 : srun k u [sel0 c, sel1, sel2, sel3, sel4] rT1 = 0 := by
    rw [show ([sel0 c, sel1, sel2, sel3, sel4] : List Instr)
        = [sel0 c, sel1, sel2, sel3] ++ [sel4] from rfl,
      srun_read_last k rT1 [sel0 c, sel1, sel2, sel3] sel4 rfl]
    unfold sel4
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hisp4,
      denoteOp_mul_of_lt (show 0 * srun k u [sel0 c, sel1, sel2, sel3] rN < M by
        rw [Nat.zero_mul]; exact M_pos)]
    exact Nat.zero_mul _
  have ht2_5 : srun k u [sel0 c, sel1, sel2, sel3, sel4] rT2 = u rS := by
    rw [show ([sel0 c, sel1, sel2, sel3, sel4] : List Instr)
        = [sel0 c, sel1, sel2, sel3] ++ [sel4] from rfl,
      srun_frame_append k rT2 [sel0 c, sel1, sel2, sel3] [sel4] rfl]
    exact ht2_4
  rw [selectBlock_eq,
    show ([sel0 c, sel1, sel2, sel3, sel4, sel5] : List Instr)
      = [sel0 c, sel1, sel2, sel3, sel4] ++ [sel5] from rfl,
    srun_read_last k rP [sel0 c, sel1, sel2, sel3, sel4] sel5 rfl]
  unfold sel5
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg, ht1_5, ht2_5,
    denoteOp_add_of_lt (show 0 + u rS < M by omega)]
  exact Nat.zero_add _

/-- **The seed-table index is in range**, so the one `load` is defined.

`lambdaPre` clamps the index to `0` on a prime candidate; otherwise it is the
scan's committed divisor, and `Inv.scan` bounds that by `B + 1`. -/
theorem load_index_lt (c : Cfg) (k : Nat) (u : RegState) (hS : u rS < M)
    (hinv : u rS = 0 ∨ u rS ≤ c.B + 1) (hlen : c.B + 1 < c.tableLen) :
    srun k u (selectBlock c ++ powerBlock ++ lambdaPre) rT2 < c.tableLen := by
  have hM1 : (1 : Nat) < M := by decide
  have hsub0 : (denoteOp .sub 1 (0 : Nat)).getD 0 = 1 := by
    rw [denoteOp_sub_of_le (Nat.zero_le 1) hM1]; rfl
  have hsub1 : (denoteOp .sub 1 (1 : Nat)).getD 0 = 0 := by
    rw [denoteOp_sub_of_le (Nat.le_refl 1) hM1]; rfl
  rw [srun_append]
  have hvIsP : srun k u (selectBlock c ++ powerBlock) rIsP
      = (if u rS = 0 then 1 else 0) := by
    rw [srun_frame_append k rIsP (selectBlock c) powerBlock rfl]
    exact select_rIsP k u c
  rw [lambdaPre_eq, srun_read_last k rT2 [lp0] lp1 rfl]
  unfold lp1
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg,
    srun_frame k rP [lp0] rfl,
    srun_read_head k rT1 lp0 [] rfl rfl]
  unfold lp0
  rw [sval_binop, denoteOperand_lit_of_lt _ _ hM1, denoteOperand_reg, hvIsP]
  by_cases h0 : u rS = 0
  · rw [if_pos h0, hsub1,
      denoteOp_mul_of_lt (show 0 * srun k u (selectBlock c ++ powerBlock) rP < M by
        rw [Nat.zero_mul]; exact M_pos)]
    show 0 * srun k u (selectBlock c ++ powerBlock) rP < c.tableLen
    rw [Nat.zero_mul]
    omega
  · have hvP : srun k u (selectBlock c ++ powerBlock) rP = u rS := by
      rw [srun_frame_append k rP (selectBlock c) powerBlock rfl]
      exact select_rP_of_ne k u c hS h0
    rw [if_neg h0, hsub0, hvP, denoteOp_mul_of_lt (show 1 * u rS < M by omega)]
    show 1 * u rS < c.tableLen
    rw [Nat.one_mul]
    omega

/-! ### Definedness of the whole body

The three side conditions above, composed.  `Inv` is the entry hypothesis,
`ok_idx` bounds the decode against the word size, the ladder's `2 ≤ n` comes
from `wmOK`'s `2 ≤ n0` and its `2·n < M` from `n0 + len ≤ 2²⁵`.
-/

/-- The decode's two divisions are by the literal `B`, so no state is read. -/
theorem decodeBlock_sdefined (c : Cfg) (k : Nat) (r : RegState) (hB : 0 < c.B)
    (hBM : c.B < M) : SAllDefined k r (decodeBlock c) := by
  rw [show decodeBlock c = ([] : List Instr) ++ dR c ::
      (([] : List Instr) ++ dNq c :: [dNa c, dD]) from rfl]
  refine sAllDefined_stage rfl ?_ ?_
  · simp only [dR]
    refine sDefined_urem ?_
    rw [denoteOperand_lit_of_lt _ _ hBM]
    omega
  · refine sAllDefined_stage rfl ?_ (sAllDefined_of_noDiv k _ _ rfl)
    simp only [dNq]
    refine sDefined_udiv ?_
    rw [denoteOperand_lit_of_lt _ _ hBM]
    omega

/-- Everything before the seed-table read. -/
theorem wmPre_sdefined (c : Cfg) (k : Nat) (r : RegState) (hB : 0 < c.B)
    (hBM : c.B < M) (hk : k < M) (hD : k % c.B + 2 < M) :
    SAllDefined k r (wmPre c) := by
  rw [wmPre_eq]
  refine sAllDefined_append (sAllDefined_append (decodeBlock_sdefined c k r hB hBM) ?_) ?_
  · refine scanBlock_defined k _ ?_
    rw [decode_rD c k r hk hB hBM hD]
    omega
  · refine sAllDefined_of_noDiv k _ _ ?_
    simp +decide [wmPreTail, selectBlock, powerBlock, powerRound, lambdaPre,
      List.all_append, List.all_flatMap, InstrBlock.NoDivI]

private def wmPostHead (c : Cfg) : List Instr :=
  lambdaPost ++ accBlock ++ capBlock c ++ rowBlock c

private theorem wmPost_eq (c : Cfg) :
    wmPost c = (wmPostHead c ++ ladderBlock) ++ resetBlock := rfl

/-- Everything after the seed-table read.  Only the ladder is partial, and its
hypothesis is about the candidate register `rN`, which nothing between the
decode and the ladder writes. -/
theorem wmPost_sdefined (c : Cfg) (k : Nat) (w : RegState) (h2 : 2 ≤ w rN)
    (hM : 2 * w rN < M) : SAllDefined k w (wmPost c) := by
  have hframe : srun k w (wmPostHead c) rN = w rN :=
    srun_frame k rN (wmPostHead c) rfl w
  rw [wmPost_eq]
  refine sAllDefined_append (sAllDefined_append ?_ ?_) ?_
  · refine sAllDefined_of_noDiv k _ _ ?_
    simp +decide [wmPostHead, lambdaPost, accBlock, capBlock, rowBlock,
      List.all_append, InstrBlock.NoDivI]
  · exact ladderBlock_defined k _ (by rw [hframe]; exact h2) (by rw [hframe]; exact hM)
  · exact sAllDefined_of_noDiv k _ _ (by decide)

/-- The post-load stage, stated for an *arbitrary* entry state.  Keeping the
state a variable is what stops any tactic from forcing `whnf` into the
137-instruction `srun` that the concrete state is: doing that detonates
(`maximum recursion depth`) even without a single `simp`, because the run
carries `fpD`-scale literals. -/
private theorem wmBody_post_defined (c : Cfg) (k : Nat) (t : AState)
    (ht : t.regs rN = k / c.B + c.n0) (h2 : 2 ≤ k / c.B + c.n0)
    (hM : 2 * (k / c.B + c.n0) < M) :
    AllDefined c.tableLen k (astep k t (.load rT3 rT2)) (lift (wmPost c)) := by
  refine (allDefined_lift c.tableLen k (wmPost c) _).mpr ?_
  have hrn : (astep k t (.load rT3 rT2)).regs rN = k / c.B + c.n0 := by
    show (t.writeReg rT3 (t.arr (t.regs rT2))).regs rN = _
    rw [AState.writeReg_regs_ne _ _ (show rN ≠ rT3 by decide)]
    exact ht
  exact wmPost_sdefined c k _ (by rw [hrn]; exact h2) (by rw [hrn]; exact hM)

/-- **The body is defined at every index the loop visits.**

Every partial instruction of the 137 is discharged: the decode's two divisions
by the literal `B`, the scan's `urem` by the decoded divisor, the seed-table
`load`, and the ladder's three divisions.  The only hypotheses are `wmOK`, the
loop bound, and the cross-iteration invariant `Inv`. -/
theorem wmBody_defined (c : Cfg) (hok : wmOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hs : Inv c s) :
    AllDefined c.tableLen k s (wmBody c) := by
  obtain ⟨hkM, hkdiv, hkmod⟩ := ok_idx hok hk
  have hB : 0 < c.B := ok_B hok
  have hBM : c.B < M := ok_BM hok
  have hBlt : c.B + 1 < 2 ^ 20 := ok_B_lt hok
  have hM20 : (2 : Nat) ^ 20 < M := by decide
  have hM26 : (2 : Nat) ^ 26 < M := by decide
  have hDlt : k % c.B + 2 < M := by omega
  have hlen : c.B + 1 < c.tableLen := ok_tableLen hok
  have hregs : ∀ j, s.regs j < M := hs.regsLt
  have hn0 : 2 ≤ c.n0 := ok_n0 hok
  have hrange : c.n0 + c.len ≤ 2 ^ 25 := ok_range hok
  -- The decoded candidate's two bounds, proved *before* `hNpre` enters the
  -- context: with that equation available `omega` substitutes `k / c.B` away
  -- and then no longer knows it is a `Nat`, so it cannot re-derive them.
  have h2N : 2 ≤ k / c.B + c.n0 := Nat.le_trans hn0 (Nat.le_add_left c.n0 (k / c.B))
  have hltN : k / c.B + c.n0 ≤ 2 ^ 25 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_of_lt hkdiv) c.n0) (by omega)
  have hMN : 2 * (k / c.B + c.n0) < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl 2) hltN) (by decide)
  have hNval : srun k s.regs (decodeBlock c) rN = k / c.B + c.n0 :=
    decode_rN c k s.regs hkM hB hBM (by omega)
  have hNpre : srun k s.regs (wmPre c) rN = k / c.B + c.n0 := by
    rw [wmPre_eq, srun_frame_append k rN (decodeBlock c ++ scanBlock) (wmPreTail c) rfl,
      srun_frame_append k rN (decodeBlock c) scanBlock rfl]
    exact hNval
  have hSpre : srun k s.regs (decodeBlock c ++ scanBlock) rS = s.regs rS ∨
      srun k s.regs (decodeBlock c ++ scanBlock) rS = k % c.B + 2 := by
    rw [srun_append]
    have h1 : srun k s.regs (decodeBlock c) rS = s.regs rS :=
      srun_frame k rS (decodeBlock c) rfl s.regs
    have h2 : srun k s.regs (decodeBlock c) rD = k % c.B + 2 :=
      decode_rD c k s.regs hkM hB hBM hDlt
    rcases scan_rS k (srun k s.regs (decodeBlock c)) (by rw [h1]; exact hregs rS)
      (by rw [h2]; omega) with h | h
    · exact Or.inl (by rw [h, h1])
    · exact Or.inr (by rw [h, h2])
  have hidx : srun k s.regs (wmPre c) rT2 < c.tableLen := by
    rw [wmPre_eq, srun_append]
    simp only [wmPreTail]
    refine load_index_lt c k _ (srun_regs_lt k _ s.regs hregs rS) ?_ hlen
    rcases hSpre with h | h
    · rw [h]
      rcases hs.scan with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.2
    · rw [h]
      exact Or.inr (by omega)
  have hregsEq : (arun k s (lift (wmPre c))).regs = srun k s.regs (wmPre c) :=
    arun_lift_regs k (wmPre c) s
  rw [show wmBody c = lift (wmPre c) ++ (.load rT3 rT2 :: lift (wmPost c)) from rfl,
    AllDefined_append]
  refine ⟨(allDefined_lift c.tableLen k (wmPre c) s).mpr
    (wmPre_sdefined c k s.regs hB hBM hkM hDlt), ?_, ?_⟩
  · show (arun k s (lift (wmPre c))).regs rT2 < c.tableLen
    rw [hregsEq]
    exact hidx
  · refine wmBody_post_defined c k _ ?_ h2N hMN
    rw [hregsEq]
    exact hNpre

/-! ## The candidate-level reference

An independently written mirror of what one candidate contributes, used by
the kernel smoke checks below and by the stated encoding obligation.  It
mirrors the machine's arithmetic — including the mod-`2⁶⁴` reductions on the
products that can wrap — at commit granularity.
-/

/-- The machine's trial scan, candidate-level. -/
def spfIn (B n : Nat) : Nat :=
  (List.range B).foldl
    (fun s r =>
      let d := r + 2
      if s = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else s) 0

/-- The machine's power chain, candidate-level (wraps mirrored). -/
def powChain (p n : Nat) : Bool :=
  ((List.range powerRounds).foldl
    (fun (st : Nat × Bool) _ =>
      let m := st.1 * p % M
      (m, st.2 || (m = n)))
    (p % M, p % M = n)).2

/-- Last-store-wins view of the seed table. -/
def seedAt (c : Cfg) (p : Nat) : Nat :=
  (((c.seeds.reverse.find? (fun e => e.1 = p)).map (fun e => e.2)).getD 0) % M

/-- What one candidate adds and checks.  State: `(bad, acc, L)`. -/
def wmStep (c : Cfg) (n : Nat) (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (bad, acc, L) := st
  let s := spfIn c.B n
  let isP := s = 0
  let p := if isP then n else s
  let pow := powChain p n
  let lam := if isP then L else if pow then seedAt c p else 0
  let addend := ((((lam >>> 20) + 1) * n % M) >>> 24) + 1
  let acc' := (acc + addend) % M
  let capBad := if c.capA < acc' then 1 else 0
  let rowBad :=
    if c.lower ≤ n ∧ ¬(acc' * 2500 % M < n * n % M * 20016 % M) then 1 else 0
  (bad + capBad + rowBad, acc', (L + incUWord n) % M)

/-- The whole sweep, candidate-level; the machine's output is its `bad`. -/
def wmRef (c : Cfg) : Nat :=
  ((List.range c.len).foldl (fun st q => wmStep c (c.n0 + q) st)
    (0, c.acc0 % M, c.seedL % M)).1

/-! ## The encoding obligation

Everything above is about the *program*.  The statement a certificate wants
is about the *reference*, whose identification with the goldbach tree's
`WM217Rows` is Mathlib-side work (`Nat.minFac`, `powerCheck`, the LeanCert
seed values).  `WMEncoding` is the obligation joining the two; it is proved at
the end of this file (`wmEncoding`).  An artifact run reads a number off a
**proved** denotation; it never establishes one
(`Verified/Algorithm/ArrayBridge.lean`).
-/

/-- **The encoding obligation** for a run of `wmProgram` to say anything at
all: the program denotes the candidate-level reference.  `wmOK c = true` is
part of the obligation (coverage, seed range, width budget). -/
def WMEncoding (c : Cfg) : Prop :=
  wmOK c = true → (wmProgram c).denote = some (wmRef c)

/-! ## Kernel smoke checks

A tiny configuration exercised in both verdicts.  These evaluate the full
135-instruction body against `wmRef` in the kernel — the two are written at
different granularity (flat rounds against candidates), so agreement is a
real cross-check of every gate and clamp above.
-/

/-- Ten candidates `10 … 19`, four rounds each; seeds for the bases `2, 3`.
`lower = 20`: no row is tested, so the verdict is `0` unless the cap trips. -/
def tinyCfg : Cfg :=
  { n0 := 10, len := 10, B := 4, lower := 20
  , seedL := 1000000, acc0 := 7, capA := 1000000000
  , tableLen := 8, seeds := [(2, 300000), (3, 500000)] }

theorem tiny_ok : wmOK tinyCfg = true := by decide

set_option maxRecDepth 400000 in
example : (wmProgram tinyCfg).denote = some (wmRef tinyCfg) := by decide

set_option maxRecDepth 400000 in
example : (wmProgram tinyCfg).denote = some 0 := by decide

/-- The same sweep with every row tested (`lower = 2`) and a starving cap:
both violation kinds fire, and the machine still matches the reference. -/
def tinyCfgBad : Cfg :=
  { tinyCfg with lower := 2, capA := 10 }

set_option maxRecDepth 400000 in
example : (wmProgram tinyCfgBad).denote = some (wmRef tinyCfgBad) := by decide

set_option maxRecDepth 400000 in
example : ∃ v, (wmProgram tinyCfgBad).denote = some v ∧ 0 < v := by
  refine ⟨(wmRef tinyCfgBad), by decide, by decide⟩


/-! ## The value of the body

Definedness says the 137 instructions *run*.  This section says what they
*compute*.  The discipline is the one `Verified/RegFrame.lean` prescribes: a
register read is always `srun_read_write` followed by one `denoteOp` value
lemma, on a state that stays a variable, so no instruction's arithmetic ever
enters a goal it does not belong to.
-/

section Values

/-! ### Flag algebra at instruction level

The four `denoteOp` facts a branchless block needs, stated on `if _ then 1
else 0` operands so that a gate is never a numeral in a goal.
-/

private theorem denoteOp_mul_bit (p q : Prop) [Decidable p] [Decidable q] :
    denoteOp .mul (if p then 1 else 0) (if q then 1 else 0)
      = some (if p ∧ q then 1 else 0) := by
  by_cases hp : p
  · by_cases hq : q
    · rw [if_pos hp, if_pos hq, if_pos (⟨hp, hq⟩ : p ∧ q)]; rfl
    · rw [if_pos hp, if_neg hq, if_neg (show ¬(p ∧ q) from fun h => hq h.2)]; rfl
  · rw [if_neg hp, if_neg (show ¬(p ∧ q) from fun h => hp h.1)]
    show some ((0 * _) % M) = _
    rw [Nat.zero_mul, Nat.zero_mod]

private theorem denoteOp_bor_bit (p q : Prop) [Decidable p] [Decidable q] :
    denoteOp .bor (if p then 1 else 0) (if q then 1 else 0)
      = some (if p ∨ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q
  · rw [if_pos hp, if_pos hq, if_pos (Or.inl hp)]; rfl
  · rw [if_pos hp, if_neg hq, if_pos (Or.inl hp)]; rfl
  · rw [if_neg hp, if_pos hq, if_pos (Or.inr hq)]; rfl
  · rw [if_neg hp, if_neg hq, if_neg (show ¬(p ∨ q) from fun h => h.elim hp hq)]; rfl

/-- Flag negation, as the machine writes it (`1 − g`). -/
private theorem denoteOp_sub_one_bit (p : Prop) [Decidable p] :
    denoteOp .sub 1 (if p then 1 else 0) = some (if p then 0 else 1) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp]
    exact denoteOp_sub_of_le (Nat.le_refl 1) (by decide)
  · rw [if_neg hp, if_neg hp]
    exact denoteOp_sub_of_le (Nat.zero_le 1) (by decide)

/-- Gating a word by a flag on the left. -/
private theorem denoteOp_gate_left (p : Prop) [Decidable p] {x : Nat} (hx : x < M) :
    denoteOp .mul (if p then 1 else 0) x = some (if p then x else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp, denoteOp_mul_of_lt (by rw [Nat.one_mul]; exact hx),
      Nat.one_mul]
  · rw [if_neg hp, if_neg hp]
    show some ((0 * x) % M) = _
    rw [Nat.zero_mul, Nat.zero_mod]

/-- Gating a word by a flag on the right. -/
private theorem denoteOp_gate_right (p : Prop) [Decidable p] {x : Nat} (hx : x < M) :
    denoteOp .mul x (if p then 1 else 0) = some (if p then x else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp, denoteOp_mul_of_lt (by rw [Nat.mul_one]; exact hx),
      Nat.mul_one]
  · rw [if_neg hp, if_neg hp]
    show some ((x * 0) % M) = _
    rw [Nat.mul_zero, Nat.zero_mod]

/-! ### The trial round, exactly

`scan_rS` above says the round keeps `rS` or replaces it by `rD`.  Here is
which, computed from the gate.
-/

private theorem scanP3_rG (k : Nat) (s : RegState) :
    srun k s scanP3 rG = (if s rS = 0 then 1 else 0) := by
  rw [show scanP3 = sG0 :: [sT1a, sT1b] from rfl,
    srun_read_head k rG sG0 [sT1a, sT1b] rfl rfl]
  unfold sG0
  exact sval_binop_val (denoteOperand_reg k s rS)
    (denoteOperand_lit_of_lt k s M_pos) (denoteOp_eq_val _ _)

private theorem scanP3_rT1 (k : Nat) (s : RegState) (hDD : s rD * s rD < M) :
    srun k s scanP3 rT1 = (if s rD * s rD ≤ s rN then 1 else 0) := by
  rw [show scanP3 = [sG0, sT1a] ++ [sT1b] from rfl,
    srun_read_last k rT1 [sG0, sT1a] sT1b rfl]
  unfold sT1b
  refine sval_binop_val ?_ ?_ (denoteOp_le_val _ _)
  · rw [denoteOperand_reg,
      show ([sG0, sT1a] : List Instr) = [sG0] ++ [sT1a] from rfl,
      srun_read_last k rT1 [sG0] sT1a rfl]
    unfold sT1a
    refine sval_binop_val ?_ ?_ (denoteOp_mul_of_lt hDD)
    · rw [denoteOperand_reg]; exact srun_frame k rD [sG0] rfl s
    · rw [denoteOperand_reg]; exact srun_frame k rD [sG0] rfl s
  · rw [denoteOperand_reg]; exact srun_frame k rN [sG0, sT1a] rfl s

private theorem scanPre_rG (k : Nat) (s : RegState) (hDD : s rD * s rD < M) :
    srun k s scanPre rG =
      (if s rS = 0 ∧ s rD * s rD ≤ s rN then 1 else 0) := by
  rw [show scanPre = scanP3 ++ [sG1] from rfl, srun_read_last k rG scanP3 sG1 rfl]
  unfold sG1
  refine sval_binop_val ?_ ?_ (denoteOp_mul_bit _ _)
  · rw [denoteOperand_reg]; exact scanP3_rG k s
  · rw [denoteOperand_reg]; exact scanP3_rT1 k s hDD

private theorem scanQ_rT2 (k : Nat) (s : RegState) (hD0 : s rD ≠ 0)
    (hN : s rN < M) :
    srun k s scanQ rT2 = (if s rN % s rD = 0 then 1 else 0) := by
  rw [show scanQ = (scanPre ++ [scanDiv]) ++ [sT2b] from rfl,
    srun_read_last k rT2 (scanPre ++ [scanDiv]) sT2b rfl]
  unfold sT2b
  refine sval_binop_val ?_ (denoteOperand_lit_of_lt _ _ M_pos) (denoteOp_eq_val _ _)
  rw [denoteOperand_reg, srun_read_last k rT2 scanPre scanDiv rfl]
  unfold scanDiv
  refine sval_binop_val ?_ ?_ (denoteOp_urem_of_ne hD0 hN)
  · rw [denoteOperand_reg]; exact srun_frame k rN scanPre rfl s
  · rw [denoteOperand_reg]; exact srun_frame k rD scanPre rfl s

private theorem gate_val (k : Nat) (s : RegState) (hDD : s rD * s rD < M)
    (hD0 : s rD ≠ 0) (hN : s rN < M) :
    gate k s =
      (if s rS = 0 ∧ s rD * s rD ≤ s rN ∧ s rN % s rD = 0 then 1 else 0) := by
  have h : gate k s =
      (if (s rS = 0 ∧ s rD * s rD ≤ s rN) ∧ s rN % s rD = 0 then 1 else 0) := by
    unfold gate sG2
    refine sval_binop_val ?_ ?_ (denoteOp_mul_bit _ _)
    · rw [denoteOperand_reg]
      unfold scanQ
      rw [srun_frame_append k rG scanPre [scanDiv, sT2b] rfl]
      exact scanPre_rG k s hDD
    · rw [denoteOperand_reg]; exact scanQ_rT2 k s hD0 hN
  rw [h]
  by_cases h1 : s rS = 0 <;> by_cases h2 : s rD * s rD ≤ s rN <;>
    by_cases h3 : s rN % s rD = 0 <;> simp [h1, h2, h3]

private theorem scan_rS_gate (k : Nat) (s : RegState) (hS : s rS < M)
    (hD : s rD < M) :
    srun k s scanBlock rS = if gate k s = 1 then s rD else s rS := by
  have hM1 : (1 : Nat) < M := by decide
  have hgR3 : srun k s scanR3 rG = gate k s := by
    unfold gate scanR3
    exact srun_read_last k rG scanQ sG2 rfl s
  have hgR2 : srun k s scanR2 rG = gate k s := by
    unfold scanR2
    rw [srun_frame_append k rG scanR3 [sT1c] rfl]
    exact hgR3
  have hgR1 : srun k s scanR1 rG = gate k s := by
    unfold scanR1
    rw [srun_frame_append k rG scanR2 [sT1d] rfl]
    exact hgR2
  have hS2 : srun k s scanR2 rS = s rS := srun_frame k rS scanR2 rfl s
  have hD1 : srun k s scanR1 rD = s rD := srun_frame k rD scanR1 rfl s
  have hT1c : srun k s scanR2 rT1 = (denoteOp .sub 1 (gate k s)).getD 0 := by
    unfold scanR2
    rw [srun_read_last k rT1 scanR3 sT1c rfl]
    unfold sT1c
    rw [sval_binop, denoteOperand_lit_of_lt _ _ hM1, denoteOperand_reg, hgR3]
  have hT1R1 : srun k s scanR1 rT1 =
      (denoteOp .mul (srun k s scanR2 rT1) (s rS)).getD 0 := by
    unfold scanR1
    rw [srun_read_last k rT1 scanR2 sT1d rfl]
    unfold sT1d
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hS2]
  have hT1R0 : srun k s scanR0 rT1 = srun k s scanR1 rT1 := by
    unfold scanR0
    exact srun_frame_append k rT1 scanR1 [sT2c] rfl s
  have hT2R0 : srun k s scanR0 rT2 =
      (denoteOp .mul (gate k s) (s rD)).getD 0 := by
    unfold scanR0
    rw [srun_read_last k rT2 scanR1 sT2c rfl]
    unfold sT2c
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hgR1, hD1]
  have hfinal : srun k s scanBlock rS =
      (denoteOp .add (srun k s scanR0 rT1) (srun k s scanR0 rT2)).getD 0 := by
    rw [scanBlock_eq_R0, srun_read_last k rS scanR0 sS rfl]
    unfold sS
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg]
  rcases gate_isBit k s with hg | hg
  · rw [if_neg (by rw [hg]; exact fun h => absurd h (by decide))]
    have h1 : (denoteOp .sub 1 (0 : Nat)).getD 0 = 1 := by
      rw [denoteOp_sub_of_le (Nat.zero_le 1) hM1]
      rfl
    have h2 : (denoteOp .mul 1 (s rS)).getD 0 = s rS := by
      rw [denoteOp_mul_of_lt (show 1 * s rS < M by omega)]
      exact Nat.one_mul _
    have h3 : (denoteOp .mul 0 (s rD)).getD 0 = 0 := by
      rw [denoteOp_mul_of_lt (show 0 * s rD < M by rw [Nat.zero_mul]; exact M_pos)]
      exact Nat.zero_mul _
    have h4 : (denoteOp .add (s rS) 0).getD 0 = s rS := by
      rw [denoteOp_add_of_lt (show s rS + 0 < M by omega)]
      exact Nat.add_zero _
    rw [hg, h1] at hT1c
    rw [hg, h3] at hT2R0
    rw [hfinal, hT1R0, hT1R1, hT1c, h2, hT2R0, h4]
  · rw [if_pos hg]
    have h1 : (denoteOp .sub 1 (1 : Nat)).getD 0 = 0 := by
      rw [denoteOp_sub_of_le (Nat.le_refl 1) hM1]
      rfl
    have h2 : (denoteOp .mul 0 (s rS)).getD 0 = 0 := by
      rw [denoteOp_mul_of_lt (show 0 * s rS < M by rw [Nat.zero_mul]; exact M_pos)]
      exact Nat.zero_mul _
    have h3 : (denoteOp .mul 1 (s rD)).getD 0 = s rD := by
      rw [denoteOp_mul_of_lt (show 1 * s rD < M by omega)]
      exact Nat.one_mul _
    have h4 : (denoteOp .add 0 (s rD)).getD 0 = s rD := by
      rw [denoteOp_add_of_lt (show 0 + s rD < M by omega)]
      exact Nat.zero_add _
    rw [hg, h1] at hT1c
    rw [hg, h3] at hT2R0
    rw [hfinal, hT1R0, hT1R1, hT1c, h2, hT2R0, h4]

/-- **The trial round, as a value.**  The one instruction of the eleven that
survives the round is `rS`, and this is what it holds. -/
theorem scanBlock_val (k : Nat) (s : RegState) (hS : s rS < M) (hD : s rD < M)
    (hDD : s rD * s rD < M) (hD0 : s rD ≠ 0) (hN : s rN < M) :
    srun k s scanBlock rS =
      (if s rS = 0 ∧ s rD * s rD ≤ s rN ∧ s rN % s rD = 0 then s rD else s rS) := by
  rw [scan_rS_gate k s hS hD, gate_val k s hDD hD0 hN]
  by_cases h : (s rS = 0 ∧ s rD * s rD ≤ s rN ∧ s rN % s rD = 0) <;> simp [h]

end Values

section Values2

/-! ### The commit gate and the factor select -/

/-- The commit gate `r = B − 1`. -/
theorem select_rC (k : Nat) (u : RegState) (c : Cfg) (hB : c.B - 1 < M) :
    srun k u (selectBlock c) rC = (if u rR = c.B - 1 then 1 else 0) := by
  rw [selectBlock_eq,
    show ([sel0 c, sel1, sel2, sel3, sel4, sel5] : List Instr)
      = sel0 c :: [sel1, sel2, sel3, sel4, sel5] from rfl,
    srun_read_head k rC (sel0 c) [sel1, sel2, sel3, sel4, sel5] rfl rfl]
  unfold sel0
  exact sval_binop_val (denoteOperand_reg _ _ _) (denoteOperand_lit_of_lt _ _ hB)
    (denoteOp_eq_val _ _)

/-- **The committed factor**, in both cases: the scan's divisor when the scan
found one, and the candidate itself when it did not. -/
theorem select_rP (k : Nat) (u : RegState) (c : Cfg) (hS : u rS < M)
    (hN : u rN < M) :
    srun k u (selectBlock c) rP = (if u rS = 0 then u rN else u rS) := by
  by_cases h0 : u rS = 0
  · rw [if_pos h0]
    have hM1 : (1 : Nat) < M := by decide
    have hisp2 : srun k u [sel0 c, sel1] rIsP = 1 := by
      rw [show ([sel0 c, sel1] : List Instr) = [sel0 c] ++ sel1 :: [] from rfl,
        srun_read_write k rIsP [sel0 c] sel1 [] rfl rfl, sel_isP_val k u c,
        if_pos h0]
    have hisp4 : srun k u [sel0 c, sel1, sel2, sel3] rIsP = 1 := by
      rw [show ([sel0 c, sel1, sel2, sel3] : List Instr)
          = [sel0 c] ++ sel1 :: [sel2, sel3] from rfl,
        srun_read_write k rIsP [sel0 c] sel1 [sel2, sel3] rfl rfl,
        sel_isP_val k u c, if_pos h0]
    have hsub : (denoteOp .sub 1 (1 : Nat)).getD 0 = 0 := by
      rw [denoteOp_sub_of_le (Nat.le_refl 1) hM1]; rfl
    have ht1_3 : srun k u [sel0 c, sel1, sel2] rT1 = 0 := by
      rw [show ([sel0 c, sel1, sel2] : List Instr) = [sel0 c, sel1] ++ [sel2] from rfl,
        srun_read_last k rT1 [sel0 c, sel1] sel2 rfl]
      unfold sel2
      rw [sval_binop, denoteOperand_lit_of_lt _ _ hM1, denoteOperand_reg, hisp2, hsub]
    have ht2_4 : srun k u [sel0 c, sel1, sel2, sel3] rT2 = 0 := by
      rw [show ([sel0 c, sel1, sel2, sel3] : List Instr)
          = [sel0 c, sel1, sel2] ++ [sel3] from rfl,
        srun_read_last k rT2 [sel0 c, sel1, sel2] sel3 rfl]
      unfold sel3
      rw [sval_binop, denoteOperand_reg, denoteOperand_reg, ht1_3,
        denoteOp_mul_of_lt (show 0 * srun k u [sel0 c, sel1, sel2] rS < M by
          rw [Nat.zero_mul]; exact M_pos)]
      exact Nat.zero_mul _
    have ht1_5 : srun k u [sel0 c, sel1, sel2, sel3, sel4] rT1 = u rN := by
      rw [show ([sel0 c, sel1, sel2, sel3, sel4] : List Instr)
          = [sel0 c, sel1, sel2, sel3] ++ [sel4] from rfl,
        srun_read_last k rT1 [sel0 c, sel1, sel2, sel3] sel4 rfl]
      unfold sel4
      rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hisp4,
        srun_frame k rN [sel0 c, sel1, sel2, sel3] rfl,
        denoteOp_mul_of_lt (show 1 * u rN < M by omega)]
      exact Nat.one_mul _
    have ht2_5 : srun k u [sel0 c, sel1, sel2, sel3, sel4] rT2 = 0 := by
      rw [show ([sel0 c, sel1, sel2, sel3, sel4] : List Instr)
          = [sel0 c, sel1, sel2, sel3] ++ [sel4] from rfl,
        srun_frame_append k rT2 [sel0 c, sel1, sel2, sel3] [sel4] rfl]
      exact ht2_4
    rw [selectBlock_eq,
      show ([sel0 c, sel1, sel2, sel3, sel4, sel5] : List Instr)
        = [sel0 c, sel1, sel2, sel3, sel4] ++ [sel5] from rfl,
      srun_read_last k rP [sel0 c, sel1, sel2, sel3, sel4] sel5 rfl]
    unfold sel5
    rw [sval_binop, denoteOperand_reg, denoteOperand_reg, ht1_5, ht2_5,
      denoteOp_add_of_lt (show u rN + 0 < M by omega)]
    exact Nat.add_zero _
  · rw [if_neg h0]
    exact select_rP_of_ne k u c hS h0

/-! ### The power chain

`powerBlock` seeds `rM := p`, `rPow := [p = n]`, and then runs 24 identical
rounds.  The rounds are folded, not unrolled: one induction on the round
count, with the two carried registers read through `RegFrame`.
-/

private def pr0 : Instr := .binop rM .mul (.reg rM) (.reg rP)
private def pr1 : Instr := .binop rT1 .eq (.reg rM) (.reg rN)
private def pr2 : Instr := .binop rPow .bor (.reg rPow) (.reg rT1)

private theorem powerRound_eq : powerRound = [pr0, pr1, pr2] := rfl

private def powList (m : Nat) : List Instr :=
  (List.range m).flatMap (fun _ => powerRound)

private theorem powList_succ (m : Nat) :
    powList (m + 1) = powList m ++ powerRound := by
  unfold powList
  rw [List.range_succ]
  simp

private theorem writes_powList {r : Nat} (h : writes r powerRound = false) :
    ∀ m, writes r (powList m) = false := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [powList_succ, writes_append, ih, h]; rfl

/-- The machine's power-chain transition, mirroring `powChain`'s step. -/
private def chainStep (p n : Nat) (st : Nat × Bool) : Nat × Bool :=
  let m := st.1 * p % M
  (m, st.2 || (m = n))

private def chainFold (p n m : Nat) (st : Nat × Bool) : Nat × Bool :=
  (List.range m).foldl (fun st _ => chainStep p n st) st

private theorem chainFold_succ (p n m : Nat) (st : Nat × Bool) :
    chainFold p n (m + 1) st = chainStep p n (chainFold p n m st) := by
  unfold chainFold
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem powChain_eq (p n : Nat) :
    powChain p n = (chainFold p n powerRounds (p % M, p % M = n)).2 := rfl

private theorem denoteOp_mul_mod (a b : Nat) :
    denoteOp .mul a b = some (a * b % M) := rfl

private theorem powList_val (k p n : Nat) :
    ∀ (m : Nat) (u : RegState), u rP = p → u rN = n →
      ∀ (a : Nat) (b : Bool), u rM = a → u rPow = (if b = true then 1 else 0) →
        srun k u (powList m) rM = (chainFold p n m (a, b)).1 ∧
        srun k u (powList m) rPow =
          (if (chainFold p n m (a, b)).2 = true then 1 else 0) := by
  intro m
  induction m with
  | zero => intro u _ _ a b hM hPow; exact ⟨hM, hPow⟩
  | succ m ih =>
      intro u hP hN a b hM0 hPow0
      obtain ⟨ihM, ihPow⟩ := ih u hP hN a b hM0 hPow0
      have hvP : srun k u (powList m) rP = p := by
        rw [srun_frame k rP (powList m) (writes_powList rfl m)]; exact hP
      have hvN : srun k u (powList m) rN = n := by
        rw [srun_frame k rN (powList m) (writes_powList rfl m)]; exact hN
      have hmval : srun k (srun k u (powList m)) [pr0] rM =
          (chainFold p n m (a, b)).1 * p % M := by
        rw [show ([pr0] : List Instr) = [] ++ pr0 :: [] from rfl,
          srun_read_write k rM [] pr0 [] rfl rfl]
        unfold pr0
        exact sval_binop_val (by rw [denoteOperand_reg]; exact ihM)
          (by rw [denoteOperand_reg]; exact hvP) (denoteOp_mul_mod _ _)
      have hT1 : srun k (srun k u (powList m)) [pr0, pr1] rT1 =
          (if (chainFold p n m (a, b)).1 * p % M = n then 1 else 0) := by
        rw [show ([pr0, pr1] : List Instr) = [pr0] ++ pr1 :: [] from rfl,
          srun_read_write k rT1 [pr0] pr1 [] rfl rfl]
        unfold pr1
        refine sval_binop_val ?_ ?_ (denoteOp_eq_val _ _)
        · rw [denoteOperand_reg]; exact hmval
        · rw [denoteOperand_reg,
            srun_frame k rN [pr0] rfl]
          exact hvN
      rw [powList_succ, chainFold_succ, srun_append, powerRound_eq]
      constructor
      · rw [show ([pr0, pr1, pr2] : List Instr) = [] ++ pr0 :: [pr1, pr2] from rfl,
          srun_read_write k rM [] pr0 [pr1, pr2] rfl rfl]
        unfold pr0
        exact sval_binop_val (by rw [denoteOperand_reg]; exact ihM)
          (by rw [denoteOperand_reg]; exact hvP) (denoteOp_mul_mod _ _)
      · rw [show ([pr0, pr1, pr2] : List Instr) = [pr0, pr1] ++ [pr2] from rfl,
          srun_read_last k rPow [pr0, pr1] pr2 rfl]
        unfold pr2
        refine Eq.trans (sval_binop_val ?_ ?_ (denoteOp_bor_bit
          ((chainFold p n m (a, b)).2 = true)
          ((chainFold p n m (a, b)).1 * p % M = n))) ?_
        · rw [denoteOperand_reg, srun_frame k rPow [pr0, pr1] rfl]; exact ihPow
        · rw [denoteOperand_reg]; exact hT1
        · unfold chainStep
          by_cases hb : (chainFold p n m (a, b)).2 = true <;>
            by_cases hq : (chainFold p n m (a, b)).1 * p % M = n <;>
            simp [hb, hq]

/-- **The prime-power flag.**  Over-acceptance through mod-`2⁶⁴` collisions is
mirrored exactly by `powChain`, so this is an equation and not an
inequality. -/
theorem powerBlock_rPow (k : Nat) (u : RegState) (hP : u rP < M) :
    srun k u powerBlock rPow =
      (if powChain (u rP) (u rN) = true then 1 else 0) := by
  have hsplit : powerBlock =
      [(.mov rM (.reg rP) : Instr), .binop rPow .eq (.reg rM) (.reg rN)] ++
        powList powerRounds := rfl
  have hseedM : srun k u [(.mov rM (.reg rP) : Instr),
      .binop rPow .eq (.reg rM) (.reg rN)] rM = u rP := by
    rw [show ([(.mov rM (.reg rP) : Instr),
        .binop rPow .eq (.reg rM) (.reg rN)] : List Instr)
        = [] ++ (.mov rM (.reg rP) : Instr) ::
            [(.binop rPow .eq (.reg rM) (.reg rN) : Instr)] from rfl,
      srun_read_write k rM [] (.mov rM (.reg rP)) [_] rfl rfl]
    exact sval_mov_val (denoteOperand_reg _ _ _)
  have hseedPow : srun k u [(.mov rM (.reg rP) : Instr),
      .binop rPow .eq (.reg rM) (.reg rN)] rPow =
      (if u rP = u rN then 1 else 0) := by
    rw [show ([(.mov rM (.reg rP) : Instr),
        .binop rPow .eq (.reg rM) (.reg rN)] : List Instr)
        = [(.mov rM (.reg rP) : Instr)] ++
            (.binop rPow .eq (.reg rM) (.reg rN) : Instr) :: [] from rfl,
      srun_read_write k rPow [_] (.binop rPow .eq (.reg rM) (.reg rN)) [] rfl rfl]
    refine sval_binop_val ?_ ?_ (denoteOp_eq_val _ _)
    · rw [denoteOperand_reg,
        show ([(.mov rM (.reg rP) : Instr)] : List Instr)
          = [] ++ (.mov rM (.reg rP) : Instr) :: [] from rfl,
        srun_read_write k rM [] (.mov rM (.reg rP)) [] rfl rfl]
      exact sval_mov_val (denoteOperand_reg _ _ _)
    · rw [denoteOperand_reg]
      exact srun_frame k rN [(.mov rM (.reg rP) : Instr)] rfl u
  have hseedP : srun k u [(.mov rM (.reg rP) : Instr),
      .binop rPow .eq (.reg rM) (.reg rN)] rP = u rP :=
    srun_frame k rP _ rfl u
  have hseedN : srun k u [(.mov rM (.reg rP) : Instr),
      .binop rPow .eq (.reg rM) (.reg rN)] rN = u rN :=
    srun_frame k rN _ rfl u
  rw [hsplit, srun_append]
  have h := (powList_val k (u rP) (u rN) powerRounds
    (srun k u [(.mov rM (.reg rP) : Instr),
      .binop rPow .eq (.reg rM) (.reg rN)]) hseedP hseedN
    (u rP) (decide (u rP = u rN)) hseedM (by rw [hseedPow]; simp)).2
  rw [h, powChain_eq, Nat.mod_eq_of_lt hP]

end Values2

section Values3

/-! ### The seed-table index, and the pre-load stage assembled -/

private theorem denoteOp_gate_left' (p : Prop) [Decidable p] {x : Nat} (hx : x < M) :
    denoteOp .mul (if p then 0 else 1) x = some (if p then 0 else x) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp]
    show some ((0 * x) % M) = _
    rw [Nat.zero_mul, Nat.zero_mod]
  · rw [if_neg hp, if_neg hp,
      denoteOp_mul_of_lt (by rw [Nat.one_mul]; exact hx), Nat.one_mul]

private theorem lambdaPre_rT1 (k : Nat) (u : RegState) (P : Prop) [Decidable P]
    (h : u rIsP = if P then 1 else 0) :
    srun k u lambdaPre rT1 = (if P then 0 else 1) := by
  rw [show lambdaPre = ([] : List Instr) ++ lp0 :: [lp1] from rfl,
    srun_read_write k rT1 [] lp0 [lp1] rfl rfl]
  unfold lp0
  exact sval_binop_val (denoteOperand_lit_of_lt _ _ (by decide))
    (by rw [denoteOperand_reg]; exact h) (denoteOp_sub_one_bit P)

private theorem lambdaPre_rT2 (k : Nat) (u : RegState) (P : Prop) [Decidable P]
    (h : u rIsP = if P then 1 else 0) (hP : u rP < M) :
    srun k u lambdaPre rT2 = (if P then 0 else u rP) := by
  rw [lambdaPre_eq, srun_read_last k rT2 [lp0] lp1 rfl]
  unfold lp1
  refine sval_binop_val ?_ ?_ (denoteOp_gate_left' P hP)
  · rw [denoteOperand_reg,
      show ([lp0] : List Instr) = ([] : List Instr) ++ lp0 :: [] from rfl,
      srun_read_write k rT1 [] lp0 [] rfl rfl]
    unfold lp0
    exact sval_binop_val (denoteOperand_lit_of_lt _ _ (by decide))
      (by rw [denoteOperand_reg]; exact h) (denoteOp_sub_one_bit P)
  · rw [denoteOperand_reg]; exact srun_frame k rP [lp0] rfl u

private def wmPreA (c : Cfg) : List Instr := decodeBlock c ++ scanBlock
private def wmPreB (c : Cfg) : List Instr := wmPreA c ++ selectBlock c
private def wmPreC (c : Cfg) : List Instr := wmPreB c ++ powerBlock

private theorem wmPre_split (c : Cfg) : wmPre c = wmPreC c ++ lambdaPre := rfl

/--
**Everything the pre-load stage computes.**

`r`, `n`, `S` and `p` are variables constrained by hypotheses, never terms, so
none of the program's constants ever appears inside a normal form.
-/
theorem wmPre_vals (c : Cfg) (k : Nat) (s : RegState) {r n S p : Nat}
    (hr : r = k % c.B) (hn : n = k / c.B + c.n0)
    (hSdef : S = (if s rS = 0 ∧ (r + 2) * (r + 2) ≤ n ∧ n % (r + 2) = 0
      then r + 2 else s rS))
    (hpdef : p = (if S = 0 then n else S))
    (hB : 0 < c.B) (hBM : c.B < M) (hkM : k < M) (hnM : n < M)
    (hddM : (r + 2) * (r + 2) < M) (hdM : r + 2 < M) (hSM : s rS < M)
    (hBm1 : c.B - 1 < M) (hpM : p < M) :
    srun k s (wmPre c) rN = n ∧
    srun k s (wmPre c) rS = S ∧
    srun k s (wmPre c) rC = (if r = c.B - 1 then 1 else 0) ∧
    srun k s (wmPre c) rIsP = (if S = 0 then 1 else 0) ∧
    srun k s (wmPre c) rP = p ∧
    srun k s (wmPre c) rPow = (if powChain p n = true then 1 else 0) ∧
    srun k s (wmPre c) rT1 = (if S = 0 then 0 else 1) ∧
    srun k s (wmPre c) rT2 = (if S = 0 then 0 else p) ∧
    srun k s (wmPre c) rL = s rL ∧
    srun k s (wmPre c) rAcc = s rAcc ∧
    srun k s (wmPre c) rBad = s rBad := by
  have hSM' : S < M := by rw [hSdef]; split <;> omega
  have hd0 : r + 2 ≠ 0 := by omega
  -- decode
  have hdec_rN : srun k s (decodeBlock c) rN = n := by
    rw [hn]; exact decode_rN c k s hkM hB hBM (by rw [← hn]; exact hnM)
  have hdec_rD : srun k s (decodeBlock c) rD = r + 2 := by
    rw [hr]; exact decode_rD c k s hkM hB hBM (by rw [← hr]; exact hdM)
  have hdec_rR : srun k s (decodeBlock c) rR = r := by
    rw [hr]; exact decode_rR c k s hkM hB hBM
  have hdec_rS : srun k s (decodeBlock c) rS = s rS :=
    srun_frame k rS (decodeBlock c) rfl s
  -- stage A: decode ++ scan
  have hA_rN : srun k s (wmPreA c) rN = n := by
    unfold wmPreA
    rw [srun_frame_append k rN (decodeBlock c) scanBlock rfl]; exact hdec_rN
  have hA_rR : srun k s (wmPreA c) rR = r := by
    unfold wmPreA
    rw [srun_frame_append k rR (decodeBlock c) scanBlock rfl]; exact hdec_rR
  have hA_rS : srun k s (wmPreA c) rS = S := by
    unfold wmPreA
    rw [srun_append,
      scanBlock_val k _ (by rw [hdec_rS]; exact hSM) (by rw [hdec_rD]; exact hdM)
        (by rw [hdec_rD]; exact hddM) (by rw [hdec_rD]; exact hd0)
        (by rw [hdec_rN]; exact hnM),
      hdec_rS, hdec_rD, hdec_rN, hSdef]
  have hA_rL : srun k s (wmPreA c) rL = s rL := srun_frame k rL (wmPreA c) rfl s
  have hA_rAcc : srun k s (wmPreA c) rAcc = s rAcc := srun_frame k rAcc (wmPreA c) rfl s
  have hA_rBad : srun k s (wmPreA c) rBad = s rBad := srun_frame k rBad (wmPreA c) rfl s
  -- stage B: ++ select
  have hB_rN : srun k s (wmPreB c) rN = n := by
    unfold wmPreB
    rw [srun_frame_append k rN (wmPreA c) (selectBlock c) rfl]; exact hA_rN
  have hB_rS : srun k s (wmPreB c) rS = S := by
    unfold wmPreB
    rw [srun_frame_append k rS (wmPreA c) (selectBlock c) rfl]; exact hA_rS
  have hB_rC : srun k s (wmPreB c) rC = (if r = c.B - 1 then 1 else 0) := by
    unfold wmPreB
    rw [srun_append, select_rC k _ c hBm1, hA_rR]
  have hB_rIsP : srun k s (wmPreB c) rIsP = (if S = 0 then 1 else 0) := by
    unfold wmPreB
    rw [srun_append, select_rIsP k _ c, hA_rS]
  have hB_rP : srun k s (wmPreB c) rP = p := by
    unfold wmPreB
    rw [srun_append, select_rP k _ c (by rw [hA_rS]; exact hSM')
      (by rw [hA_rN]; exact hnM), hA_rS, hA_rN, hpdef]
  have hB_rL : srun k s (wmPreB c) rL = s rL := by
    unfold wmPreB
    rw [srun_frame_append k rL (wmPreA c) (selectBlock c) rfl]; exact hA_rL
  have hB_rAcc : srun k s (wmPreB c) rAcc = s rAcc := by
    unfold wmPreB
    rw [srun_frame_append k rAcc (wmPreA c) (selectBlock c) rfl]; exact hA_rAcc
  have hB_rBad : srun k s (wmPreB c) rBad = s rBad := by
    unfold wmPreB
    rw [srun_frame_append k rBad (wmPreA c) (selectBlock c) rfl]; exact hA_rBad
  -- stage C: ++ power
  have hC_rPow : srun k s (wmPreC c) rPow = (if powChain p n = true then 1 else 0) := by
    unfold wmPreC
    rw [srun_append, powerBlock_rPow k _ (by rw [hB_rP]; exact hpM), hB_rP, hB_rN]
  have hC_rN : srun k s (wmPreC c) rN = n := by
    unfold wmPreC
    rw [srun_frame_append k rN (wmPreB c) powerBlock rfl]; exact hB_rN
  have hC_rS : srun k s (wmPreC c) rS = S := by
    unfold wmPreC
    rw [srun_frame_append k rS (wmPreB c) powerBlock rfl]; exact hB_rS
  have hC_rC : srun k s (wmPreC c) rC = (if r = c.B - 1 then 1 else 0) := by
    unfold wmPreC
    rw [srun_frame_append k rC (wmPreB c) powerBlock rfl]; exact hB_rC
  have hC_rIsP : srun k s (wmPreC c) rIsP = (if S = 0 then 1 else 0) := by
    unfold wmPreC
    rw [srun_frame_append k rIsP (wmPreB c) powerBlock rfl]; exact hB_rIsP
  have hC_rP : srun k s (wmPreC c) rP = p := by
    unfold wmPreC
    rw [srun_frame_append k rP (wmPreB c) powerBlock rfl]; exact hB_rP
  have hC_rL : srun k s (wmPreC c) rL = s rL := by
    unfold wmPreC
    rw [srun_frame_append k rL (wmPreB c) powerBlock rfl]; exact hB_rL
  have hC_rAcc : srun k s (wmPreC c) rAcc = s rAcc := by
    unfold wmPreC
    rw [srun_frame_append k rAcc (wmPreB c) powerBlock rfl]; exact hB_rAcc
  have hC_rBad : srun k s (wmPreC c) rBad = s rBad := by
    unfold wmPreC
    rw [srun_frame_append k rBad (wmPreB c) powerBlock rfl]; exact hB_rBad
  -- stage D: ++ lambdaPre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [wmPre_split]
  · rw [srun_frame_append k rN (wmPreC c) lambdaPre rfl]; exact hC_rN
  · rw [srun_frame_append k rS (wmPreC c) lambdaPre rfl]; exact hC_rS
  · rw [srun_frame_append k rC (wmPreC c) lambdaPre rfl]; exact hC_rC
  · rw [srun_frame_append k rIsP (wmPreC c) lambdaPre rfl]; exact hC_rIsP
  · rw [srun_frame_append k rP (wmPreC c) lambdaPre rfl]; exact hC_rP
  · rw [srun_frame_append k rPow (wmPreC c) lambdaPre rfl]; exact hC_rPow
  · rw [srun_append]; exact lambdaPre_rT1 k _ (S = 0) hC_rIsP
  · rw [srun_append,
      lambdaPre_rT2 k _ (S = 0) hC_rIsP (by rw [hC_rP]; exact hpM), hC_rP]
  · rw [srun_frame_append k rL (wmPreC c) lambdaPre rfl]; exact hC_rL
  · rw [srun_frame_append k rAcc (wmPreC c) lambdaPre rfl]; exact hC_rAcc
  · rw [srun_frame_append k rBad (wmPreC c) lambdaPre rfl]; exact hC_rBad

end Values3

section Values4

/-! ### The post-load stage: λ, the accumulator, the cap and the row -/

private theorem M_val : M = 18446744073709551616 := rfl

private theorem shiftRight_add_one_lt {a n : Nat} (ha : a < M) (hn : 1 ≤ n) :
    a >>> n + 1 < M := by
  rw [M_val] at ha ⊢
  rw [Nat.shiftRight_eq_div_pow]
  have h2 : (2:Nat) ≤ 2 ^ n := by
    calc (2:Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hq : a / 2 ^ n * 2 ^ n ≤ a := Nat.div_mul_le_self a (2 ^ n)
  have h3 : a / 2 ^ n * 2 ≤ a / 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ h2
  omega

private theorem denoteOp_mul_bit' (p q : Prop) [Decidable p] [Decidable q] :
    denoteOp .mul (if p then 0 else 1) (if q then 1 else 0)
      = some (if ¬ p ∧ q then 1 else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_neg (show ¬(¬ p ∧ q) from fun h => h.1 hp)]
    show some ((0 * _) % M) = _
    rw [Nat.zero_mul, Nat.zero_mod]
  · by_cases hq : q
    · rw [if_neg hp, if_pos hq, if_pos (⟨hp, hq⟩ : ¬ p ∧ q)]; rfl
    · rw [if_neg hp, if_neg hq, if_neg (show ¬(¬ p ∧ q) from fun h => hq h.2)]; rfl

/-! #### λ -/

private def lq0 : Instr := .binop rT1 .mul (.reg rT1) (.reg rPow)
private def lq1 : Instr := .binop rT3 .mul (.reg rT1) (.reg rT3)
private def lq2 : Instr := .binop rT2 .mul (.reg rIsP) (.reg rL)
private def lq3 : Instr := .binop rLam .add (.reg rT2) (.reg rT3)

private def lqA : List Instr := [lq0]
private def lqB : List Instr := lqA ++ [lq1]
private def lqC : List Instr := lqB ++ [lq2]

private theorem lambdaPost_eq : lambdaPost = lqC ++ [lq3] := rfl

/-- **The λ charged to this candidate.**  `isP` selects the running ladder;
otherwise the gate `pw` selects the seed cell the load produced. -/
theorem lambdaPost_rLam (k : Nat) (w : RegState) (isP pw : Prop)
    [Decidable isP] [Decidable pw]
    (h1 : w rT1 = if isP then 0 else 1) (h2 : w rPow = if pw then 1 else 0)
    (h3 : w rIsP = if isP then 1 else 0) (hL : w rL < M) (hT3 : w rT3 < M) :
    srun k w lambdaPost rLam =
      (if isP then w rL else (if pw then w rT3 else 0)) := by
  have hM0 : 0 < M := M_pos
  have hA_rT1 : srun k w lqA rT1 = (if ¬ isP ∧ pw then 1 else 0) := by
    unfold lqA
    rw [show ([lq0] : List Instr) = ([] : List Instr) ++ lq0 :: [] from rfl,
      srun_read_write k rT1 [] lq0 [] rfl rfl]
    unfold lq0
    exact sval_binop_val (a := if isP then 0 else 1) (b := if pw then 1 else 0)
      (by rw [denoteOperand_reg]; exact h1) (by rw [denoteOperand_reg]; exact h2)
      (denoteOp_mul_bit' isP pw)
  have hB_rT3 : srun k w lqB rT3 = (if ¬ isP ∧ pw then w rT3 else 0) := by
    unfold lqB
    rw [srun_read_last k rT3 lqA lq1 rfl]
    unfold lq1
    exact sval_binop_val (a := if ¬ isP ∧ pw then 1 else 0) (b := w rT3)
      (by rw [denoteOperand_reg]; exact hA_rT1)
      (by rw [denoteOperand_reg]; exact srun_frame k rT3 lqA rfl w)
      (denoteOp_gate_left (¬ isP ∧ pw) hT3)
  have hC_rT2 : srun k w lqC rT2 = (if isP then w rL else 0) := by
    unfold lqC
    rw [srun_read_last k rT2 lqB lq2 rfl]
    unfold lq2
    exact sval_binop_val (a := if isP then 1 else 0) (b := w rL)
      (by rw [denoteOperand_reg]; exact (srun_frame k rIsP lqB rfl w).trans h3)
      (by rw [denoteOperand_reg]; exact srun_frame k rL lqB rfl w)
      (denoteOp_gate_left isP hL)
  have hC_rT3 : srun k w lqC rT3 = (if ¬ isP ∧ pw then w rT3 else 0) := by
    unfold lqC
    rw [srun_frame_append k rT3 lqB [lq2] rfl]; exact hB_rT3
  have hsum : (if isP then w rL else 0) + (if ¬ isP ∧ pw then w rT3 else 0) < M := by
    by_cases hp : isP <;> by_cases hq : pw <;> simp [hp, hq] <;> omega
  have hval : sval k (srun k w lqC) lq3
      = (if isP then w rL else 0) + (if ¬ isP ∧ pw then w rT3 else 0) := by
    unfold lq3
    exact sval_binop_val (a := if isP then w rL else 0)
      (b := if ¬ isP ∧ pw then w rT3 else 0)
      (by rw [denoteOperand_reg]; exact hC_rT2)
      (by rw [denoteOperand_reg]; exact hC_rT3) (denoteOp_add_of_lt hsum)
  rw [lambdaPost_eq, srun_read_last k rLam lqC lq3 rfl, hval]
  by_cases hp : isP <;> by_cases hq : pw <;> simp [hp, hq]

/-! #### The accumulator -/

private def ac0 : Instr := .binop rT1 .lshr (.reg rLam) (.lit 20)
private def ac1 : Instr := .binop rT1 .add (.reg rT1) (.lit 1)
private def ac2 : Instr := .binop rT1 .mul (.reg rT1) (.reg rN)
private def ac3 : Instr := .binop rT1 .lshr (.reg rT1) (.lit 24)
private def ac4 : Instr := .binop rT1 .add (.reg rT1) (.lit 1)
private def ac5 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def ac6 : Instr := .binop rAcc .add (.reg rAcc) (.reg rT1)

private def acA : List Instr := [ac0]
private def acB : List Instr := acA ++ [ac1]
private def acC : List Instr := acB ++ [ac2]
private def acD : List Instr := acC ++ [ac3]
private def acE : List Instr := acD ++ [ac4]
private def acF : List Instr := acE ++ [ac5]

private theorem accBlock_eq : accBlock = acF ++ [ac6] := rfl

/-- **The dominating rescaled addend**, gated by the commit.  The `% M` in the
middle is the machine's, and `wmStep` carries the same one. -/
theorem accBlock_rAcc (k : Nat) (x : RegState) (commit : Prop) [Decidable commit]
    (hC : x rC = if commit then 1 else 0) (hlam : x rLam < M) :
    srun k x accBlock rAcc =
      (x rAcc +
        (if commit then ((((x rLam >>> 20) + 1) * x rN % M) >>> 24) + 1 else 0)) % M := by
  have hA : srun k x acA rT1 = x rLam >>> 20 := by
    unfold acA
    rw [show ([ac0] : List Instr) = ([] : List Instr) ++ ac0 :: [] from rfl,
      srun_read_write k rT1 [] ac0 [] rfl rfl]
    unfold ac0
    exact sval_binop_val (a := x rLam) (b := 20) (denoteOperand_reg _ _ _)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_lshr_of_lt hlam)
  have hB : srun k x acB rT1 = x rLam >>> 20 + 1 := by
    unfold acB
    rw [srun_read_last k rT1 acA ac1 rfl]
    unfold ac1
    exact sval_binop_val (a := x rLam >>> 20) (b := 1)
      (by rw [denoteOperand_reg]; exact hA)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_add_of_lt (shiftRight_add_one_lt hlam (by omega)))
  have hCC : srun k x acC rT1 = (x rLam >>> 20 + 1) * x rN % M := by
    unfold acC
    rw [srun_read_last k rT1 acB ac2 rfl]
    unfold ac2
    exact sval_binop_val (a := x rLam >>> 20 + 1) (b := x rN)
      (by rw [denoteOperand_reg]; exact hB)
      (by rw [denoteOperand_reg]; exact srun_frame k rN acB rfl x)
      (denoteOp_mul_mod _ _)
  have hD : srun k x acD rT1 = ((x rLam >>> 20 + 1) * x rN % M) >>> 24 := by
    unfold acD
    rw [srun_read_last k rT1 acC ac3 rfl]
    unfold ac3
    exact sval_binop_val (a := (x rLam >>> 20 + 1) * x rN % M) (b := 24)
      (by rw [denoteOperand_reg]; exact hCC)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_lshr_of_lt (Nat.mod_lt _ M_pos))
  have hE : srun k x acE rT1 = (((x rLam >>> 20 + 1) * x rN % M) >>> 24) + 1 := by
    unfold acE
    rw [srun_read_last k rT1 acD ac4 rfl]
    unfold ac4
    exact sval_binop_val (a := ((x rLam >>> 20 + 1) * x rN % M) >>> 24) (b := 1)
      (by rw [denoteOperand_reg]; exact hD)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_add_of_lt (shiftRight_add_one_lt (Nat.mod_lt _ M_pos) (by omega)))
  have hF : srun k x acF rT1 =
      (if commit then (((x rLam >>> 20 + 1) * x rN % M) >>> 24) + 1 else 0) := by
    unfold acF
    rw [srun_read_last k rT1 acE ac5 rfl]
    unfold ac5
    exact sval_binop_val (a := (((x rLam >>> 20 + 1) * x rN % M) >>> 24) + 1)
      (b := if commit then 1 else 0)
      (by rw [denoteOperand_reg]; exact hE)
      (by rw [denoteOperand_reg]; exact (srun_frame k rC acE rfl x).trans hC)
      (denoteOp_gate_right commit
        (shiftRight_add_one_lt (Nat.mod_lt _ M_pos) (by omega)))
  rw [accBlock_eq, srun_read_last k rAcc acF ac6 rfl]
  unfold ac6
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hF,
    srun_frame k rAcc acF rfl x]
  rfl

/-! #### The cap and the row -/

private def cp0 (c : Cfg) : Instr := .binop rT1 .gt (.reg rAcc) (.lit c.capA)
private def cp1 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def cp2 : Instr := .binop rBad .add (.reg rBad) (.reg rT1)

private theorem capBlock_eq (c : Cfg) : capBlock c = [cp0 c, cp1] ++ [cp2] := rfl

/-- **The cap violation**, gated by the commit. -/
theorem capBlock_rBad (k : Nat) (y : RegState) (c : Cfg) (commit : Prop)
    [Decidable commit] (hC : y rC = if commit then 1 else 0) (hcap : c.capA < M) :
    srun k y (capBlock c) rBad =
      (y rBad + (if commit ∧ c.capA < y rAcc then 1 else 0)) % M := by
  have h0 : srun k y [cp0 c] rT1 = (if c.capA < y rAcc then 1 else 0) := by
    rw [show ([cp0 c] : List Instr) = ([] : List Instr) ++ cp0 c :: [] from rfl,
      srun_read_write k rT1 [] (cp0 c) [] rfl rfl]
    unfold cp0
    exact sval_binop_val (a := y rAcc) (b := c.capA) (denoteOperand_reg _ _ _)
      (denoteOperand_lit_of_lt _ _ hcap) (denoteOp_gt_val _ _)
  have h1' : sval k (srun k y [cp0 c]) cp1
      = (if (c.capA < y rAcc) ∧ commit then 1 else 0) := by
    unfold cp1
    exact sval_binop_val (a := if c.capA < y rAcc then 1 else 0)
      (b := if commit then 1 else 0)
      (by rw [denoteOperand_reg]; exact h0)
      (by rw [denoteOperand_reg]; exact (srun_frame k rC [cp0 c] rfl y).trans hC)
      (denoteOp_mul_bit (c.capA < y rAcc) commit)
  have h1 : srun k y [cp0 c, cp1] rT1 =
      (if commit ∧ c.capA < y rAcc then 1 else 0) := by
    rw [show ([cp0 c, cp1] : List Instr) = [cp0 c] ++ [cp1] from rfl,
      srun_read_last k rT1 [cp0 c] cp1 rfl, h1']
    by_cases hx : commit <;> by_cases hy : c.capA < y rAcc <;> simp [hx, hy]
  rw [capBlock_eq, srun_read_last k rBad [cp0 c, cp1] cp2 rfl]
  unfold cp2
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg, h1,
    srun_frame k rBad [cp0 c, cp1] rfl y]
  rfl

private def rw0 : Instr := .binop rT1 .mul (.reg rN) (.reg rN)
private def rw1 : Instr := .binop rT1 .mul (.reg rT1) (.lit 20016)
private def rw2 : Instr := .binop rT2 .mul (.reg rAcc) (.lit 2500)
private def rw3 : Instr := .binop rT2 .ge (.reg rT2) (.reg rT1)
private def rw4 (c : Cfg) : Instr := .binop rLow .ge (.reg rN) (.lit c.lower)
private def rw5 : Instr := .binop rT2 .mul (.reg rT2) (.reg rLow)
private def rw6 : Instr := .binop rT2 .mul (.reg rT2) (.reg rC)
private def rw7 : Instr := .binop rBad .add (.reg rBad) (.reg rT2)

private def rwA : List Instr := [rw0]
private def rwB : List Instr := rwA ++ [rw1]
private def rwC : List Instr := rwB ++ [rw2]
private def rwD : List Instr := rwC ++ [rw3]
private def rwE (c : Cfg) : List Instr := rwD ++ [rw4 c]
private def rwF (c : Cfg) : List Instr := rwE c ++ [rw5]
private def rwG (c : Cfg) : List Instr := rwF c ++ [rw6]

private theorem rowBlock_eq (c : Cfg) : rowBlock c = rwG c ++ [rw7] := rfl

/-- **The row violation**, gated by the commit and by `n ≥ lower`.  The three
`% M`s are the machine's, and `wmStep` carries the same three. -/
theorem rowBlock_rBad (k : Nat) (z : RegState) (c : Cfg) (commit : Prop)
    [Decidable commit] (hC : z rC = if commit then 1 else 0) (hlow : c.lower < M) :
    srun k z (rowBlock c) rBad =
      (z rBad +
        (if commit ∧ c.lower ≤ z rN ∧
            ¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M)
          then 1 else 0)) % M := by
  have hA : srun k z rwA rT1 = z rN * z rN % M := by
    unfold rwA
    rw [show ([rw0] : List Instr) = ([] : List Instr) ++ rw0 :: [] from rfl,
      srun_read_write k rT1 [] rw0 [] rfl rfl]
    unfold rw0
    exact sval_binop_val (a := z rN) (b := z rN) (denoteOperand_reg _ _ _)
      (denoteOperand_reg _ _ _) (denoteOp_mul_mod _ _)
  have hB : srun k z rwB rT1 = z rN * z rN % M * 20016 % M := by
    unfold rwB
    rw [srun_read_last k rT1 rwA rw1 rfl]
    unfold rw1
    exact sval_binop_val (a := z rN * z rN % M) (b := 20016)
      (by rw [denoteOperand_reg]; exact hA)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_mul_mod _ _)
  have hCC : srun k z rwC rT2 = z rAcc * 2500 % M := by
    unfold rwC
    rw [srun_read_last k rT2 rwB rw2 rfl]
    unfold rw2
    exact sval_binop_val (a := z rAcc) (b := 2500)
      (by rw [denoteOperand_reg]; exact srun_frame k rAcc rwB rfl z)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_mul_mod _ _)
  have hDv : sval k (srun k z rwC) rw3 =
      (if z rAcc * 2500 % M ≥ z rN * z rN % M * 20016 % M then 1 else 0) := by
    unfold rw3
    exact sval_binop_val (a := z rAcc * 2500 % M)
      (b := z rN * z rN % M * 20016 % M)
      (by rw [denoteOperand_reg]; exact hCC)
      (by rw [denoteOperand_reg]
          exact (srun_frame_append k rT1 rwB [rw2] rfl z).trans hB)
      (denoteOp_ge_val _ _)
  have hD : srun k z rwD rT2 =
      (if ¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M) then 1 else 0) := by
    unfold rwD
    rw [srun_read_last k rT2 rwC rw3 rfl, hDv]
    by_cases hx : z rAcc * 2500 % M < z rN * z rN % M * 20016 % M <;>
      simp [hx] <;> omega
  have hE : srun k z (rwE c) rLow = (if c.lower ≤ z rN then 1 else 0) := by
    unfold rwE
    rw [srun_read_last k rLow rwD (rw4 c) rfl]
    unfold rw4
    exact sval_binop_val (a := z rN) (b := c.lower)
      (by rw [denoteOperand_reg]; exact srun_frame k rN rwD rfl z)
      (denoteOperand_lit_of_lt _ _ hlow) (denoteOp_ge_val _ _)
  have hE2 : srun k z (rwE c) rT2 =
      (if ¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M) then 1 else 0) := by
    unfold rwE
    rw [srun_frame_append k rT2 rwD [rw4 c] rfl]; exact hD
  have hF : srun k z (rwF c) rT2 =
      (if (¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M)) ∧ c.lower ≤ z rN
        then 1 else 0) := by
    unfold rwF
    rw [srun_read_last k rT2 (rwE c) rw5 rfl]
    unfold rw5
    exact sval_binop_val
      (a := if ¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M) then 1 else 0)
      (b := if c.lower ≤ z rN then 1 else 0)
      (by rw [denoteOperand_reg]; exact hE2)
      (by rw [denoteOperand_reg]; exact hE)
      (denoteOp_mul_bit (¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M))
        (c.lower ≤ z rN))
  have hGv : sval k (srun k z (rwF c)) rw6 =
      (if ((¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M)) ∧ c.lower ≤ z rN)
          ∧ commit then 1 else 0) := by
    unfold rw6
    exact sval_binop_val
      (a := if (¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M)) ∧
        c.lower ≤ z rN then 1 else 0)
      (b := if commit then 1 else 0)
      (by rw [denoteOperand_reg]; exact hF)
      (by rw [denoteOperand_reg]; exact (srun_frame k rC (rwF c) rfl z).trans hC)
      (denoteOp_mul_bit
        ((¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M)) ∧ c.lower ≤ z rN)
        commit)
  have hG : srun k z (rwG c) rT2 =
      (if commit ∧ c.lower ≤ z rN ∧
          ¬ (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M) then 1 else 0) := by
    unfold rwG
    rw [srun_read_last k rT2 (rwF c) rw6 rfl, hGv]
    by_cases h1 : commit <;>
      by_cases h2 : c.lower ≤ z rN <;>
      by_cases h3 : (z rAcc * 2500 % M < z rN * z rN % M * 20016 % M) <;>
      simp [h1, h2, h3]
  rw [rowBlock_eq, srun_read_last k rBad (rwG c) rw7 rfl]
  unfold rw7
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg, hG,
    srun_frame k rBad (rwG c) rfl z]
  rfl

end Values4

section Values5

/-! ### The ladder, and the scan reset -/

private theorem div_le_div_denom {a b c : Nat} (h : b ≤ c) (hb : 0 < b) :
    a / c ≤ a / b := by
  rw [Nat.le_div_iff_mul_le hb]
  exact Nat.le_trans (Nat.mul_le_mul_left _ h) (Nat.div_mul_le_self a c)

private theorem ladder_num_bounds {N : Nat} (hn : N ≤ 2 ^ 25) :
    N < M ∧ N * 2 + fpD3 < M ∧ N + fpD3 < M ∧ N + fpD < M := by
  refine ⟨Nat.lt_of_le_of_lt hn (by decide), ?_, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (Nat.mul_le_mul_right 2 hn) fpD3) (by decide)
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hn fpD3) (by decide)
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hn fpD) (by decide)

/-- The one genuinely arithmetic side condition of the ladder: the correction
term never exceeds the quantity it is subtracted from.  Everything is bounded
through `3·fpD/(2n) + 1 ≤ 3·fpD/4 + 1 ≤ fpD − 1`, so no numeral larger than
`fpD3` ever enters `omega`. -/
private theorem ladder_q_le (N : Nat) (h2 : 2 ≤ N) :
    ((N * 2 + fpD3) - (N + fpD3 - 1) / N) / (N * 2) ≤ N + fpD - 1 := by
  have hpos : 0 < N * 2 := by omega
  have s1 : ((N * 2 + fpD3) - (N + fpD3 - 1) / N) / (N * 2)
      ≤ (N * 2 + fpD3) / (N * 2) := Nat.div_le_div_right (Nat.sub_le _ _)
  have s2 : (N * 2 + fpD3) / (N * 2) = fpD3 / (N * 2) + 1 := by
    rw [Nat.add_div_left _ hpos]
  have s3 : fpD3 / (N * 2) ≤ fpD3 / 4 := div_le_div_denom (by omega) (by omega)
  have s4 : fpD3 / 4 + 1 ≤ fpD - 1 := by decide
  have s5 : 1 ≤ fpD := by decide
  omega

/-- The machine's ladder result is exactly `incUWord`: the same expression with
the operands in the order the emitted C uses. -/
private theorem ladder_iu_eq (N : Nat) :
    ((N + fpD - 1) - ((N * 2 + fpD3) - (N + fpD3 - 1) / N) / (N * 2)) / (N - 1)
      = incUWord N := by
  unfold incUWord
  rw [fpD3_eq, Nat.mul_comm N 2, Nat.add_comm (2 * N) (3 * fpD),
    Nat.add_comm N (3 * fpD), Nat.add_comm N fpD]

private def ld1 : Instr := .binop rT1 .mul (.reg rN) (.lit 2)
private def ld2 : Instr := .binop rT1 .add (.reg rT1) (.lit fpD3)
private def ld3 : Instr := .binop rT2 .add (.reg rN) (.lit fpD3)
private def ld4 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def ld5 : Instr := .binop rT2 .udiv (.reg rT2) (.reg rN)
private def ld6 : Instr := .binop rT1 .sub (.reg rT1) (.reg rT2)
private def ld7 : Instr := .binop rT2 .mul (.reg rN) (.lit 2)
private def ld8 : Instr := .binop rT1 .udiv (.reg rT1) (.reg rT2)
private def ld9 : Instr := .binop rT2 .add (.reg rN) (.lit fpD)
private def ld10 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def ld11 : Instr := .binop rT1 .sub (.reg rT2) (.reg rT1)
private def ld12 : Instr := .binop rT2 .sub (.reg rN) (.lit 1)
private def ld13 : Instr := .binop rIU .udiv (.reg rT1) (.reg rT2)
private def ld14 : Instr := .binop rT1 .mul (.reg rC) (.reg rIU)
private def ld15 : Instr := .binop rL .add (.reg rL) (.reg rT1)

private def lda1 : List Instr := [ld1]
private def lda2 : List Instr := lda1 ++ [ld2]
private def lda3 : List Instr := lda2 ++ [ld3]
private def lda4 : List Instr := lda3 ++ [ld4]
private def lda5 : List Instr := lda4 ++ [ld5]
private def lda6 : List Instr := lda5 ++ [ld6]
private def lda7 : List Instr := lda6 ++ [ld7]
private def lda8 : List Instr := lda7 ++ [ld8]
private def lda9 : List Instr := lda8 ++ [ld9]
private def lda10 : List Instr := lda9 ++ [ld10]
private def lda11 : List Instr := lda10 ++ [ld11]
private def lda12 : List Instr := lda11 ++ [ld12]
private def lda13 : List Instr := lda12 ++ [ld13]
private def lda14 : List Instr := lda13 ++ [ld14]

private theorem ladderBlock_eq' : ladderBlock = lda14 ++ [ld15] := rfl

/-- **The ladder advance.**  `rIU` is `incUWord n` exactly, and the gate makes
the advance happen once per candidate. -/
theorem ladderBlock_rL (k : Nat) (v : RegState) (commit : Prop) [Decidable commit]
    (hC : v rC = if commit then 1 else 0) (h2 : 2 ≤ v rN) (hn : v rN ≤ 2 ^ 25)
    (hLM : v rL < M) :
    srun k v ladderBlock rL =
      (v rL + (if commit then incUWord (v rN) else 0)) % M := by
  obtain ⟨hNM, hbA, hbB, hbC⟩ := ladder_num_bounds hn
  have hN0 : v rN ≠ 0 := by omega
  have hQ := ladder_q_le (v rN) h2
  have hfd : 1 ≤ fpD := by decide
  -- the divisor registers, one framing step each
  have e1 : srun k v lda1 rT1 = v rN * 2 := by
    unfold lda1
    rw [show ([ld1] : List Instr) = ([] : List Instr) ++ ld1 :: [] from rfl,
      srun_read_write k rT1 [] ld1 [] rfl rfl]
    unfold ld1
    exact sval_binop_val (a := v rN) (b := 2) (denoteOperand_reg _ _ _)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_mul_of_lt (by omega))
  have e2 : srun k v lda2 rT1 = v rN * 2 + fpD3 := by
    unfold lda2
    rw [srun_read_last k rT1 lda1 ld2 rfl]
    unfold ld2
    exact sval_binop_val (a := v rN * 2) (b := fpD3)
      (by rw [denoteOperand_reg]; exact e1)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_add_of_lt hbA)
  have e3 : srun k v lda3 rT2 = v rN + fpD3 := by
    unfold lda3
    rw [srun_read_last k rT2 lda2 ld3 rfl]
    unfold ld3
    exact sval_binop_val (a := v rN) (b := fpD3)
      (by rw [denoteOperand_reg]; exact srun_frame k rN lda2 rfl v)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_add_of_lt hbB)
  have e4 : srun k v lda4 rT2 = v rN + fpD3 - 1 := by
    unfold lda4
    rw [srun_read_last k rT2 lda3 ld4 rfl]
    unfold ld4
    exact sval_binop_val (a := v rN + fpD3) (b := 1)
      (by rw [denoteOperand_reg]; exact e3)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_sub_of_le (by have : 1 ≤ fpD3 := by decide
                              omega) hbB)
  have e5 : srun k v lda5 rT2 = (v rN + fpD3 - 1) / v rN := by
    unfold lda5
    rw [srun_read_last k rT2 lda4 ld5 rfl]
    unfold ld5
    exact sval_binop_val (a := v rN + fpD3 - 1) (b := v rN)
      (by rw [denoteOperand_reg]; exact e4)
      (by rw [denoteOperand_reg]; exact srun_frame k rN lda4 rfl v)
      (denoteOp_udiv_of_ne hN0 (by omega))
  have e6 : srun k v lda6 rT1 = (v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN := by
    unfold lda6
    rw [srun_read_last k rT1 lda5 ld6 rfl]
    unfold ld6
    refine sval_binop_val (a := v rN * 2 + fpD3) (b := (v rN + fpD3 - 1) / v rN)
      (by rw [denoteOperand_reg]
          exact (srun_frame_append k rT1 lda4 [ld5] rfl v).trans
            ((srun_frame_append k rT1 lda3 [ld4] rfl v).trans
              (srun_frame_append k rT1 lda2 [ld3] rfl v |>.trans e2)))
      (by rw [denoteOperand_reg]; exact e5) (denoteOp_sub_of_le ?_ hbA)
    have hdiv : (v rN + fpD3 - 1) / v rN ≤ v rN + fpD3 - 1 :=
      Nat.div_le_self _ _
    omega
  have e7 : srun k v lda7 rT2 = v rN * 2 := by
    unfold lda7
    rw [srun_read_last k rT2 lda6 ld7 rfl]
    unfold ld7
    exact sval_binop_val (a := v rN) (b := 2)
      (by rw [denoteOperand_reg]; exact srun_frame k rN lda6 rfl v)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_mul_of_lt (by omega))
  have e8 : srun k v lda8 rT1 =
      ((v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN) / (v rN * 2) := by
    unfold lda8
    rw [srun_read_last k rT1 lda7 ld8 rfl]
    unfold ld8
    exact sval_binop_val
      (a := (v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN) (b := v rN * 2)
      (by rw [denoteOperand_reg]
          exact (srun_frame_append k rT1 lda6 [ld7] rfl v).trans e6)
      (by rw [denoteOperand_reg]; exact e7)
      (denoteOp_udiv_of_ne (by omega) (by omega))
  have e9 : srun k v lda9 rT2 = v rN + fpD := by
    unfold lda9
    rw [srun_read_last k rT2 lda8 ld9 rfl]
    unfold ld9
    exact sval_binop_val (a := v rN) (b := fpD)
      (by rw [denoteOperand_reg]; exact srun_frame k rN lda8 rfl v)
      (denoteOperand_lit_of_lt _ _ (by decide)) (denoteOp_add_of_lt hbC)
  have e10 : srun k v lda10 rT2 = v rN + fpD - 1 := by
    unfold lda10
    rw [srun_read_last k rT2 lda9 ld10 rfl]
    unfold ld10
    exact sval_binop_val (a := v rN + fpD) (b := 1)
      (by rw [denoteOperand_reg]; exact e9)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_sub_of_le (by omega) hbC)
  have e11 : srun k v lda11 rT1 =
      (v rN + fpD - 1) -
        ((v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN) / (v rN * 2) := by
    unfold lda11
    rw [srun_read_last k rT1 lda10 ld11 rfl]
    unfold ld11
    exact sval_binop_val (a := v rN + fpD - 1)
      (b := ((v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN) / (v rN * 2))
      (by rw [denoteOperand_reg]; exact e10)
      (by rw [denoteOperand_reg]
          exact (srun_frame_append k rT1 lda9 [ld10] rfl v).trans
            ((srun_frame_append k rT1 lda8 [ld9] rfl v).trans e8))
      (denoteOp_sub_of_le hQ (by omega))
  have e12 : srun k v lda12 rT2 = v rN - 1 := by
    unfold lda12
    rw [srun_read_last k rT2 lda11 ld12 rfl]
    unfold ld12
    exact sval_binop_val (a := v rN) (b := 1)
      (by rw [denoteOperand_reg]; exact srun_frame k rN lda11 rfl v)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (denoteOp_sub_of_le (by omega) hNM)
  have e13 : srun k v lda13 rIU = incUWord (v rN) := by
    unfold lda13
    rw [srun_read_last k rIU lda12 ld13 rfl]
    unfold ld13
    refine Eq.trans (sval_binop_val (a := (v rN + fpD - 1) -
        ((v rN * 2 + fpD3) - (v rN + fpD3 - 1) / v rN) / (v rN * 2))
      (b := v rN - 1)
      (by rw [denoteOperand_reg]
          exact (srun_frame_append k rT1 lda11 [ld12] rfl v).trans e11)
      (by rw [denoteOperand_reg]; exact e12)
      (denoteOp_udiv_of_ne (by omega) (by omega))) ?_
    exact ladder_iu_eq (v rN)
  have hiuM : incUWord (v rN) < M := by
    rw [← ladder_iu_eq (v rN)]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have e14 : srun k v lda14 rT1 =
      (if commit then incUWord (v rN) else 0) := by
    unfold lda14
    rw [srun_read_last k rT1 lda13 ld14 rfl]
    unfold ld14
    exact sval_binop_val (a := if commit then 1 else 0) (b := incUWord (v rN))
      (by rw [denoteOperand_reg]; exact (srun_frame k rC lda13 rfl v).trans hC)
      (by rw [denoteOperand_reg]; exact e13)
      (denoteOp_gate_left commit hiuM)
  rw [ladderBlock_eq', srun_read_last k rL lda14 ld15 rfl]
  unfold ld15
  rw [sval_binop, denoteOperand_reg, denoteOperand_reg, e14,
    srun_frame k rL lda14 rfl v]
  rfl

/-! ### The scan reset -/

private def rs0 : Instr := .binop rT1 .sub (.lit 1) (.reg rC)
private def rs1 : Instr := .binop rS .mul (.reg rT1) (.reg rS)

private theorem resetBlock_eq : resetBlock = [rs0] ++ [rs1] := rfl

/-- **The scan accumulator is cleared exactly at the commit.** -/
theorem resetBlock_rS (k : Nat) (v : RegState) (commit : Prop) [Decidable commit]
    (hC : v rC = if commit then 1 else 0) (hSM : v rS < M) :
    srun k v resetBlock rS = (if commit then 0 else v rS) := by
  have h0 : srun k v [rs0] rT1 = (if commit then 0 else 1) := by
    rw [show ([rs0] : List Instr) = ([] : List Instr) ++ rs0 :: [] from rfl,
      srun_read_write k rT1 [] rs0 [] rfl rfl]
    unfold rs0
    exact sval_binop_val (a := 1) (b := if commit then 1 else 0)
      (denoteOperand_lit_of_lt _ _ (by decide))
      (by rw [denoteOperand_reg]; exact hC) (denoteOp_sub_one_bit commit)
  rw [resetBlock_eq, srun_read_last k rS [rs0] rs1 rfl]
  unfold rs1
  exact sval_binop_val (a := if commit then 0 else 1) (b := v rS)
    (by rw [denoteOperand_reg]; exact h0)
    (by rw [denoteOperand_reg]; exact srun_frame k rS [rs0] rfl v)
    (denoteOp_gate_left' commit hSM)

end Values5

section Values6

/-! ### The post-load stage, assembled -/

private def wpA : List Instr := lambdaPost ++ accBlock
private def wpB (c : Cfg) : List Instr := wpA ++ capBlock c
private def wpC (c : Cfg) : List Instr := wpB c ++ rowBlock c
private def wpD (c : Cfg) : List Instr := wpC c ++ ladderBlock

private theorem wmPost_split (c : Cfg) : wmPost c = wpD c ++ resetBlock := rfl

/-- **Everything the post-load stage computes.**  The four registers that
survive an iteration, as one step on `(bad, acc, L, S)`. -/
theorem wmPost_vals (c : Cfg) (k : Nat) (w : RegState)
    {n L acc bad S lam addend acc' : Nat} {isP pw commit : Prop}
    [Decidable isP] [Decidable pw] [Decidable commit]
    (hN : w rN = n) (hL : w rL = L) (hAcc : w rAcc = acc) (hBad : w rBad = bad)
    (hSr : w rS = S) (hCr : w rC = if commit then 1 else 0)
    (hT1 : w rT1 = if isP then 0 else 1) (hPow : w rPow = if pw then 1 else 0)
    (hIsP : w rIsP = if isP then 1 else 0)
    (hlam : lam = if isP then L else (if pw then w rT3 else 0))
    (haddend : addend = ((((lam >>> 20) + 1) * n % M) >>> 24) + 1)
    (hacc' : acc' = (acc + (if commit then addend else 0)) % M)
    (hLM : L < M) (hT3M : w rT3 < M) (hAccM : acc < M) (hSM : S < M)
    (h2 : 2 ≤ n) (hn25 : n ≤ 2 ^ 25) (hcapM : c.capA < M) (hlowM : c.lower < M) :
    srun k w (wmPost c) rAcc = acc' ∧
    srun k w (wmPost c) rBad =
      ((bad + (if commit ∧ c.capA < acc' then 1 else 0)) % M +
        (if commit ∧ c.lower ≤ n ∧
            ¬ (acc' * 2500 % M < n * n % M * 20016 % M) then 1 else 0)) % M ∧
    srun k w (wmPost c) rL = (L + (if commit then incUWord n else 0)) % M ∧
    srun k w (wmPost c) rS = (if commit then 0 else S) := by
  have hM0 : 0 < M := M_pos
  have hlamM : lam < M := by
    rw [hlam]; by_cases hp : isP <;> by_cases hq : pw <;> simp [hp, hq] <;> omega
  -- λ
  have hlp_rLam : srun k w lambdaPost rLam = lam := by
    rw [hlam, ← hL]
    exact lambdaPost_rLam k w isP pw hT1 hPow hIsP (by rw [hL]; exact hLM) hT3M
  have hlp_rC : srun k w lambdaPost rC = (if commit then 1 else 0) :=
    (srun_frame k rC lambdaPost rfl w).trans hCr
  have hlp_rN : srun k w lambdaPost rN = n :=
    (srun_frame k rN lambdaPost rfl w).trans hN
  have hlp_rAcc : srun k w lambdaPost rAcc = acc :=
    (srun_frame k rAcc lambdaPost rfl w).trans hAcc
  -- stage A: ++ accBlock
  have hA_rAcc : srun k w wpA rAcc = acc' := by
    unfold wpA
    rw [srun_append,
      accBlock_rAcc k _ commit hlp_rC (by rw [hlp_rLam]; exact hlamM),
      hlp_rLam, hlp_rN, hlp_rAcc, hacc', haddend]
  have hA_rBad : srun k w wpA rBad = bad := by
    unfold wpA
    rw [srun_frame_append k rBad lambdaPost accBlock rfl,
      srun_frame k rBad lambdaPost rfl w]
    exact hBad
  have hA_rC : srun k w wpA rC = (if commit then 1 else 0) := by
    unfold wpA
    rw [srun_frame_append k rC lambdaPost accBlock rfl]; exact hlp_rC
  have hA_rN : srun k w wpA rN = n := by
    unfold wpA
    rw [srun_frame_append k rN lambdaPost accBlock rfl]; exact hlp_rN
  have hA_rL : srun k w wpA rL = L := by
    unfold wpA
    rw [srun_frame_append k rL lambdaPost accBlock rfl,
      srun_frame k rL lambdaPost rfl w]
    exact hL
  have hA_rS : srun k w wpA rS = S := by
    unfold wpA
    rw [srun_frame_append k rS lambdaPost accBlock rfl,
      srun_frame k rS lambdaPost rfl w]
    exact hSr
  -- stage B: ++ capBlock
  have hB_rBad : srun k w (wpB c) rBad =
      (bad + (if commit ∧ c.capA < acc' then 1 else 0)) % M := by
    unfold wpB
    rw [srun_append, capBlock_rBad k _ c commit hA_rC hcapM, hA_rBad, hA_rAcc]
  have hB_rAcc : srun k w (wpB c) rAcc = acc' := by
    unfold wpB
    rw [srun_frame_append k rAcc wpA (capBlock c) rfl]; exact hA_rAcc
  have hB_rC : srun k w (wpB c) rC = (if commit then 1 else 0) := by
    unfold wpB
    rw [srun_frame_append k rC wpA (capBlock c) rfl]; exact hA_rC
  have hB_rN : srun k w (wpB c) rN = n := by
    unfold wpB
    rw [srun_frame_append k rN wpA (capBlock c) rfl]; exact hA_rN
  have hB_rL : srun k w (wpB c) rL = L := by
    unfold wpB
    rw [srun_frame_append k rL wpA (capBlock c) rfl]; exact hA_rL
  have hB_rS : srun k w (wpB c) rS = S := by
    unfold wpB
    rw [srun_frame_append k rS wpA (capBlock c) rfl]; exact hA_rS
  -- stage C: ++ rowBlock
  have hC_rBad : srun k w (wpC c) rBad =
      ((bad + (if commit ∧ c.capA < acc' then 1 else 0)) % M +
        (if commit ∧ c.lower ≤ n ∧
            ¬ (acc' * 2500 % M < n * n % M * 20016 % M) then 1 else 0)) % M := by
    unfold wpC
    rw [srun_append, rowBlock_rBad k _ c commit hB_rC hlowM, hB_rBad, hB_rAcc,
      hB_rN]
  have hC_rAcc : srun k w (wpC c) rAcc = acc' := by
    unfold wpC
    rw [srun_frame_append k rAcc (wpB c) (rowBlock c) rfl]; exact hB_rAcc
  have hC_rC : srun k w (wpC c) rC = (if commit then 1 else 0) := by
    unfold wpC
    rw [srun_frame_append k rC (wpB c) (rowBlock c) rfl]; exact hB_rC
  have hC_rN : srun k w (wpC c) rN = n := by
    unfold wpC
    rw [srun_frame_append k rN (wpB c) (rowBlock c) rfl]; exact hB_rN
  have hC_rL : srun k w (wpC c) rL = L := by
    unfold wpC
    rw [srun_frame_append k rL (wpB c) (rowBlock c) rfl]; exact hB_rL
  have hC_rS : srun k w (wpC c) rS = S := by
    unfold wpC
    rw [srun_frame_append k rS (wpB c) (rowBlock c) rfl]; exact hB_rS
  -- stage D: ++ ladderBlock
  have hD_rL : srun k w (wpD c) rL =
      (L + (if commit then incUWord n else 0)) % M := by
    unfold wpD
    rw [srun_append,
      ladderBlock_rL k _ commit hC_rC (by rw [hC_rN]; exact h2)
        (by rw [hC_rN]; exact hn25) (by rw [hC_rL]; exact hLM),
      hC_rL, hC_rN]
  have hD_rC : srun k w (wpD c) rC = (if commit then 1 else 0) := by
    unfold wpD
    rw [srun_frame_append k rC (wpC c) ladderBlock rfl]; exact hC_rC
  have hD_rS : srun k w (wpD c) rS = S := by
    unfold wpD
    rw [srun_frame_append k rS (wpC c) ladderBlock rfl]; exact hC_rS
  have hD_rAcc : srun k w (wpD c) rAcc = acc' := by
    unfold wpD
    rw [srun_frame_append k rAcc (wpC c) ladderBlock rfl]; exact hC_rAcc
  have hD_rBad : srun k w (wpD c) rBad =
      ((bad + (if commit ∧ c.capA < acc' then 1 else 0)) % M +
        (if commit ∧ c.lower ≤ n ∧
            ¬ (acc' * 2500 % M < n * n % M * 20016 % M) then 1 else 0)) % M := by
    unfold wpD
    rw [srun_frame_append k rBad (wpC c) ladderBlock rfl]; exact hC_rBad
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [wmPost_split]
  · rw [srun_frame_append k rAcc (wpD c) resetBlock rfl]; exact hD_rAcc
  · rw [srun_frame_append k rBad (wpD c) resetBlock rfl]; exact hD_rBad
  · rw [srun_frame_append k rL (wpD c) resetBlock rfl]; exact hD_rL
  · rw [srun_append,
      resetBlock_rS k _ commit hD_rC (by rw [hD_rS]; exact hSM), hD_rS]

end Values6

section Values7

/-! ### One flat round, in ordinary mathematics

`wmRound` is the step the machine takes on the four registers that survive an
iteration.  It is written at *round* granularity — the reference `wmStep` is
written at *candidate* granularity — and `BlockedFold` is what joins them.
-/

/-- The candidate this flat index decodes to. -/
def nOf (c : Cfg) (k : Nat) : Nat := k / c.B + c.n0

/-- This round's trial divisor. -/
def dOf (c : Cfg) (k : Nat) : Nat := k % c.B + 2

/-- The scan accumulator after this round. -/
def sOf (c : Cfg) (k S0 : Nat) : Nat :=
  if S0 = 0 ∧ dOf c k * dOf c k ≤ nOf c k ∧ nOf c k % dOf c k = 0
  then dOf c k else S0

/-- The factor this round commits (the candidate itself when the scan is
empty). -/
def pOf (c : Cfg) (k S0 : Nat) : Nat :=
  if sOf c k S0 = 0 then nOf c k else sOf c k S0

/-- The λ charged to this candidate. -/
def lamOf (c : Cfg) (k S0 L : Nat) : Nat :=
  if sOf c k S0 = 0 then L
  else if powChain (pOf c k S0) (nOf c k) then seedAt c (pOf c k S0) else 0

/-- The dominating rescaled addend, with the machine's truncation. -/
def addendOf (lam n : Nat) : Nat := ((((lam >>> 20) + 1) * n % M) >>> 24) + 1

/-- The accumulator after this round. -/
def wmAcc (c : Cfg) (k : Nat) (st : Nat × Nat × Nat × Nat) : Nat :=
  (st.2.1 + (if k % c.B = c.B - 1 then
    addendOf (lamOf c k st.2.2.2 st.2.2.1) (nOf c k) else 0)) % M

/-- **One flat round**, as a step on `(bad, acc, L, S)`. -/
def wmRound (c : Cfg) (k : Nat) (st : Nat × Nat × Nat × Nat) :
    Nat × Nat × Nat × Nat :=
  (((st.1 + (if k % c.B = c.B - 1 ∧ c.capA < wmAcc c k st then 1 else 0)) % M +
      (if k % c.B = c.B - 1 ∧ c.lower ≤ nOf c k ∧
          ¬ (wmAcc c k st * 2500 % M < nOf c k * nOf c k % M * 20016 % M)
        then 1 else 0)) % M,
   wmAcc c k st,
   (st.2.2.1 + (if k % c.B = c.B - 1 then incUWord (nOf c k) else 0)) % M,
   if k % c.B = c.B - 1 then 0 else sOf c k st.2.2.2)

/-! ### The body, as one step -/

private theorem wmBody_arun (c : Cfg) (k : Nat) (s : AState) :
    arun k s (wmBody c) =
      ⟨srun k (RegState.set (srun k s.regs (wmPre c)) rT3
        (s.arr (srun k s.regs (wmPre c) rT2))) (wmPost c), s.arr⟩ := by
  rw [show wmBody c = lift (wmPre c) ++ (.load rT3 rT2 :: lift (wmPost c)) from rfl,
    arun_append, arun_lift, arun_cons]
  show arun k ⟨RegState.set (srun k s.regs (wmPre c)) rT3
    (s.arr (srun k s.regs (wmPre c) rT2)), s.arr⟩ (lift (wmPost c)) = _
  rw [arun_lift]

private theorem set_ne {u : RegState} {v j : Nat} (h : j ≠ rT3) :
    RegState.set u rT3 v j = u j := by
  show (if j = rT3 then v else u j) = u j
  rw [if_neg h]

private theorem set_self {u : RegState} {v : Nat} :
    RegState.set u rT3 v rT3 = v := by
  show (if rT3 = rT3 then v else u rT3) = v
  rw [if_pos rfl]

/-- **The body computes `wmRound`.**  Every register of the 137 instructions is
accounted for: the four that survive an iteration by their values, the other
fifteen by being recomputed from the loop index. -/
theorem wmBody_obs (c : Cfg) (hok : wmOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ i, s.arr i = seedAt c i) :
    ((arun k s (wmBody c)).regs rBad, (arun k s (wmBody c)).regs rAcc,
      (arun k s (wmBody c)).regs rL, (arun k s (wmBody c)).regs rS) =
      wmRound c k (s.regs rBad, s.regs rAcc, s.regs rL, s.regs rS) := by
  obtain ⟨hkM, hkdiv, hkmod⟩ := ok_idx hok hk
  have hM0 : 0 < M := M_pos
  have hB : 0 < c.B := ok_B hok
  have hBM : c.B < M := ok_BM hok
  have hBlt : c.B + 1 < 2 ^ 20 := ok_B_lt hok
  have hn0 : 2 ≤ c.n0 := ok_n0 hok
  have hrange : c.n0 + c.len ≤ 2 ^ 25 := ok_range hok
  have h2n : 2 ≤ k / c.B + c.n0 :=
    Nat.le_trans hn0 (Nat.le_add_left c.n0 (k / c.B))
  have hn25 : k / c.B + c.n0 ≤ 2 ^ 25 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_of_lt hkdiv) c.n0) (by omega)
  have hnM : k / c.B + c.n0 < M := Nat.lt_of_le_of_lt hn25 (by decide)
  have hdM : k % c.B + 2 < M := by
    have : (2:Nat) ^ 20 < M := by decide
    omega
  have hddM : (k % c.B + 2) * (k % c.B + 2) < M := by
    have h1 : (k % c.B + 2) * (k % c.B + 2) ≤ 2 ^ 20 * 2 ^ 20 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
    omega
  have hBm1 : c.B - 1 < M := by omega
  have hSM : s.regs rS < M := hregs rS
  have hcapM : c.capA < M := by
    have h := ok_capA hok
    have h1 : c.capA ≤ 2500 * (c.capA + 2 ^ 35) :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hlowM : c.lower < M := by
    have h := ok_lower hok
    have : (2:Nat) ^ 25 < M := by decide
    omega
  -- the derived quantities
  have hSdef : sOf c k (s.regs rS) =
      (if s.regs rS = 0 ∧ (k % c.B + 2) * (k % c.B + 2) ≤ k / c.B + c.n0 ∧
        (k / c.B + c.n0) % (k % c.B + 2) = 0 then k % c.B + 2 else s.regs rS) := rfl
  have hpdef : pOf c k (s.regs rS) =
      (if sOf c k (s.regs rS) = 0 then k / c.B + c.n0 else sOf c k (s.regs rS)) := rfl
  have hSMM : sOf c k (s.regs rS) < M := by rw [hSdef]; split <;> omega
  have hpM : pOf c k (s.regs rS) < M := by rw [hpdef]; split <;> omega
  obtain ⟨hrN, hrS, hrC, hrIsP, hrP, hrPow, hrT1, hrT2, hrL, hrAcc, hrBad⟩ :=
    wmPre_vals c k s.regs (r := k % c.B) (n := k / c.B + c.n0)
      (S := sOf c k (s.regs rS)) (p := pOf c k (s.regs rS))
      rfl rfl hSdef hpdef hB hBM hkM hnM hddM hdM hSM hBm1 hpM
  -- the loaded cell
  have hT3 : s.arr (srun k s.regs (wmPre c) rT2) =
      seedAt c (if sOf c k (s.regs rS) = 0 then 0 else pOf c k (s.regs rS)) := by
    rw [hrT2, harr]
  have hT3M : seedAt c (if sOf c k (s.regs rS) = 0 then 0 else
      pOf c k (s.regs rS)) < M := by
    unfold seedAt
    exact Nat.mod_lt _ hM0
  have hlam : lamOf c k (s.regs rS) (s.regs rL) =
      (if sOf c k (s.regs rS) = 0 then s.regs rL
       else (if powChain (pOf c k (s.regs rS)) (k / c.B + c.n0) = true
             then seedAt c (if sOf c k (s.regs rS) = 0 then 0
                            else pOf c k (s.regs rS)) else 0)) := by
    unfold lamOf
    by_cases h : sOf c k (s.regs rS) = 0 <;> simp [h, nOf]
  rw [wmBody_arun]
  have hwN : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rN = k / c.B + c.n0 := by
    rw [set_ne (by decide)]; exact hrN
  have hwL : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rL = s.regs rL := by
    rw [set_ne (by decide)]; exact hrL
  have hwAcc : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rAcc = s.regs rAcc := by
    rw [set_ne (by decide)]; exact hrAcc
  have hwBad : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rBad = s.regs rBad := by
    rw [set_ne (by decide)]; exact hrBad
  have hwS : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rS = sOf c k (s.regs rS) := by
    rw [set_ne (by decide)]; exact hrS
  have hwC : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rC =
      (if k % c.B = c.B - 1 then 1 else 0) := by
    rw [set_ne (by decide)]; exact hrC
  have hwT1 : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rT1 =
      (if sOf c k (s.regs rS) = 0 then 0 else 1) := by
    rw [set_ne (by decide)]; exact hrT1
  have hwPow : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rPow =
      (if powChain (pOf c k (s.regs rS)) (k / c.B + c.n0) = true then 1 else 0) := by
    rw [set_ne (by decide)]; exact hrPow
  have hwIsP : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rIsP =
      (if sOf c k (s.regs rS) = 0 then 1 else 0) := by
    rw [set_ne (by decide)]; exact hrIsP
  have hwT3 : RegState.set (srun k s.regs (wmPre c)) rT3
      (s.arr (srun k s.regs (wmPre c) rT2)) rT3 =
      seedAt c (if sOf c k (s.regs rS) = 0 then 0 else pOf c k (s.regs rS)) := by
    rw [set_self]; exact hT3
  obtain ⟨hoAcc, hoBad, hoL, hoS⟩ :=
    wmPost_vals c k (RegState.set (srun k s.regs (wmPre c)) rT3
        (s.arr (srun k s.regs (wmPre c) rT2)))
      (n := k / c.B + c.n0) (L := s.regs rL) (acc := s.regs rAcc)
      (bad := s.regs rBad) (S := sOf c k (s.regs rS))
      (lam := lamOf c k (s.regs rS) (s.regs rL))
      (addend := addendOf (lamOf c k (s.regs rS) (s.regs rL)) (k / c.B + c.n0))
      (acc' := wmAcc c k (s.regs rBad, s.regs rAcc, s.regs rL, s.regs rS))
      (isP := sOf c k (s.regs rS) = 0)
      (pw := powChain (pOf c k (s.regs rS)) (k / c.B + c.n0) = true)
      (commit := k % c.B = c.B - 1)
      hwN hwL hwAcc hwBad hwS hwC hwT1 hwPow hwIsP
      (by rw [hlam, hwT3]) rfl rfl
      (hregs rL) (by rw [hwT3]; exact hT3M) (hregs rAcc) hSMM h2n hn25 hcapM hlowM
  unfold wmRound
  dsimp only [nOf]
  rw [hoAcc, hoBad, hoL, hoS]
  rfl

end Values7

section Blocking

open LeanCompCert.Ports.BlockedFold

/-! ### Re-blocking `len · B` flat rounds into `len` candidates

`Ports/BlockedFold.lean` supplies the re-association; what is proved here is
the statement about **one** block, whose size does not grow with `len`.
-/

/-- The scan accumulator after `m` trial rounds on candidate `n`. -/
def spfPart (n m : Nat) : Nat :=
  (List.range m).foldl
    (fun s r => let d := r + 2; if s = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else s) 0

theorem spfIn_eq_spfPart (B n : Nat) : spfIn B n = spfPart n B := rfl

theorem spfPart_succ (n m : Nat) :
    spfPart n (m + 1) =
      (if spfPart n m = 0 ∧ (m + 2) * (m + 2) ≤ n ∧ n % (m + 2) = 0
       then m + 2 else spfPart n m) := by
  unfold spfPart
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem ite_bit_le_one (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

private theorem idx_decode (B q r : Nat) (hB : 0 < B) (hr : r < B) :
    (q * B + r) % B = r ∧ (q * B + r) / B = q := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm q B, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · rw [Nat.mul_comm q B, Nat.add_comm (B * q) r, Nat.add_mul_div_left r q hB,
      Nat.div_eq_of_lt hr, Nat.zero_add]

/-- The rounds before the commit only advance the trial scan. -/
private theorem block_prefix (c : Cfg) (q bad acc L : Nat) (hB : 0 < c.B)
    (hbadM : bad < M) (haccM : acc < M) (hLM : L < M) :
    ∀ m, m ≤ c.B - 1 →
      (List.range m).foldl (fun x r => wmRound c (q * c.B + r) x)
          (bad, acc, L, 0)
        = (bad, acc, L, spfPart (q + c.n0) m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmB : m < c.B := by omega
      have hne : ¬ (m = c.B - 1) := by omega
      obtain ⟨hmod, hdiv⟩ := idx_decode c.B q m hB hmB
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      show wmRound c (q * c.B + m) (bad, acc, L, spfPart (q + c.n0) m) = _
      rw [spfPart_succ]
      unfold wmRound wmAcc sOf dOf nOf
      rw [hmod, hdiv]
      simp only [hne, false_and, if_false, Nat.add_zero,
        Nat.mod_eq_of_lt hbadM, Nat.mod_eq_of_lt haccM, Nat.mod_eq_of_lt hLM]

/-- **One block of `B` rounds is one candidate.**  The statement mentions no
problem size: it is about a single block. -/
theorem block_eq_wmStep (c : Cfg) (q bad acc L : Nat) (hB : 0 < c.B)
    (hbadM : bad + 2 < M) (haccM : acc < M) (hLM : L < M) :
    block c.B (fun x r => wmRound c r x) (bad, acc, L, 0) q
      = ((wmStep c (c.n0 + q) (bad, acc, L)).1,
         (wmStep c (c.n0 + q) (bad, acc, L)).2.1,
         (wmStep c (c.n0 + q) (bad, acc, L)).2.2, 0) := by
  have hlt : c.B - 1 < c.B := by omega
  obtain ⟨hmod, hdiv⟩ := idx_decode c.B q (c.B - 1) hB hlt
  have hrange : ∀ B', B' + 1 = c.B → List.range c.B = List.range B' ++ [B'] := by
    intro B' h; rw [← h]; exact List.range_succ
  have hspf0 : ∀ B', B' + 1 = c.B →
      spfIn c.B (c.n0 + q) =
        (if spfPart (c.n0 + q) B' = 0 ∧ (B' + 2) * (B' + 2) ≤ c.n0 + q ∧
          (c.n0 + q) % (B' + 2) = 0 then B' + 2 else spfPart (c.n0 + q) B') := by
    intro B' h
    rw [spfIn_eq_spfPart, ← h, spfPart_succ]
  have hnq : q + c.n0 = c.n0 + q := Nat.add_comm _ _
  rw [block_eq_shift, hrange (c.B - 1) (by omega), List.foldl_append,
    block_prefix c q bad acc L hB (by omega) haccM hLM (c.B - 1) (Nat.le_refl _)]
  show wmRound c (q * c.B + (c.B - 1))
    (bad, acc, L, spfPart (q + c.n0) (c.B - 1)) = _
  have hspf : (if spfPart (q + c.n0) (c.B - 1) = 0 ∧
        (c.B - 1 + 2) * (c.B - 1 + 2) ≤ q + c.n0 ∧
        (q + c.n0) % (c.B - 1 + 2) = 0
      then c.B - 1 + 2 else spfPart (q + c.n0) (c.B - 1))
      = spfIn c.B (c.n0 + q) := by
    rw [hspf0 (c.B - 1) (by omega), hnq]
  unfold wmRound wmAcc lamOf pOf sOf dOf nOf
  rw [hmod, hdiv, if_pos rfl, hspf, hnq]
  simp only [true_and, if_true]
  unfold wmStep addendOf
  simp only []
  have hb1 : ∀ (x y : Nat), x ≤ 1 → y ≤ 1 →
      ((bad + x) % M + y) % M = bad + x + y := by
    intro x y hx hy
    rw [Nat.mod_eq_of_lt (show bad + x < M by omega),
      Nat.mod_eq_of_lt (show bad + x + y < M by omega)]
  rw [hb1 _ _ (ite_bit_le_one _) (ite_bit_le_one _)]

end Blocking

section FoldValue

open LeanCompCert.Ports.BlockedFold

/-! ### The whole loop, folded -/

/-- `wmStep`'s committed factor, named. -/
private def pRef (c : Cfg) (n : Nat) : Nat :=
  if spfIn c.B n = 0 then n else spfIn c.B n

/-- `wmStep`'s λ, named. -/
private def lamRef (c : Cfg) (n L : Nat) : Nat :=
  if spfIn c.B n = 0 then L
  else if powChain (pRef c n) n then seedAt c (pRef c n) else 0

private theorem wmStep_apply (c : Cfg) (n b a l : Nat) :
    wmStep c n (b, a, l) =
      (b + (if c.capA < (a + addendOf (lamRef c n l) n) % M then 1 else 0)
         + (if c.lower ≤ n ∧
              ¬ ((a + addendOf (lamRef c n l) n) % M * 2500 % M
                 < n * n % M * 20016 % M) then 1 else 0),
       (a + addendOf (lamRef c n l) n) % M,
       (l + incUWord n) % M) := rfl

private theorem wmStep_bad_le (c : Cfg) (n b a l : Nat) :
    (wmStep c n (b, a, l)).1 ≤ b + 2 := by
  have h1 := ite_bit_le_one (c.capA < (a + addendOf (lamRef c n l) n) % M)
  have h2 := ite_bit_le_one (c.lower ≤ n ∧
    ¬ ((a + addendOf (lamRef c n l) n) % M * 2500 % M < n * n % M * 20016 % M))
  simp only [wmStep_apply]
  omega

private theorem wmStep_acc_lt (c : Cfg) (n b a l : Nat) :
    (wmStep c n (b, a, l)).2.1 < M := by
  rw [wmStep_apply]; exact Nat.mod_lt _ M_pos

private theorem wmStep_L_lt (c : Cfg) (n b a l : Nat) :
    (wmStep c n (b, a, l)).2.2 < M := by
  rw [wmStep_apply]; exact Nat.mod_lt _ M_pos

/-- The candidate-level fold, after `F` candidates. -/
private def wmStates (c : Cfg) (a l F : Nat) : Nat × Nat × Nat :=
  (List.range F).foldl (fun st q => wmStep c (c.n0 + q) st) (0, a, l)

/-- The round-level fold, re-blocked, after `F` candidates. -/
private def wmBlocks (c : Cfg) (a l F : Nat) : Nat × Nat × Nat × Nat :=
  (List.range F).foldl (block c.B (fun x r => wmRound c r x)) (0, a, l, 0)

private theorem wmStates_succ (c : Cfg) (a l F : Nat) :
    wmStates c a l (F + 1) = wmStep c (c.n0 + F) (wmStates c a l F) := by
  unfold wmStates
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem wmBlocks_succ (c : Cfg) (a l F : Nat) :
    wmBlocks c a l (F + 1) =
      block c.B (fun x r => wmRound c r x) (wmBlocks c a l F) F := by
  unfold wmBlocks
  rw [List.range_succ, List.foldl_append]
  rfl

/-- **The round-level fold is the candidate-level fold.**  Carried with the
three bounds that make the machine's truncations invisible. -/
private theorem wmBlocks_eq (c : Cfg) (hB : 0 < c.B) (a l : Nat)
    (haM : a < M) (hlM : l < M) (hlen : 2 * c.len + 2 < M) :
    ∀ F, F ≤ c.len →
      wmBlocks c a l F = ((wmStates c a l F).1, (wmStates c a l F).2.1,
          (wmStates c a l F).2.2, 0)
        ∧ (wmStates c a l F).1 ≤ 2 * F
        ∧ (wmStates c a l F).2.1 < M ∧ (wmStates c a l F).2.2 < M := by
  intro F
  induction F with
  | zero => intro _; exact ⟨rfl, Nat.zero_le _, haM, hlM⟩
  | succ F ih =>
      intro hF
      obtain ⟨ihEq, ihBad, ihAcc, ihL⟩ := ih (by omega)
      have hbadM : (wmStates c a l F).1 + 2 < M := by omega
      have hstep : wmStates c a l (F + 1) =
          wmStep c (c.n0 + F)
            ((wmStates c a l F).1, (wmStates c a l F).2.1,
             (wmStates c a l F).2.2) := wmStates_succ c a l F
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [wmBlocks_succ, ihEq,
          block_eq_wmStep c F _ _ _ hB hbadM ihAcc ihL, hstep]
      · rw [hstep]
        exact Nat.le_trans (wmStep_bad_le c _ _ _ _) (by omega)
      · rw [hstep]; exact wmStep_acc_lt c _ _ _ _
      · rw [hstep]; exact wmStep_L_lt c _ _ _ _

/-- **The flat round fold equals the reference.**  `BlockedFold.foldl_range_mul`
re-associates the `len · B` applications into `len` blocks; `block_eq_wmStep`
identifies one block. -/
theorem foldl_wmRound_eq_wmRef (c : Cfg) (hok : wmOK c = true) :
    ((List.range (c.len * c.B)).foldl (fun x r => wmRound c r x)
      (0, c.acc0 % M, c.seedL % M, 0)).1 = wmRef c := by
  have hB : 0 < c.B := ok_B hok
  have hrange : c.n0 + c.len ≤ 2 ^ 25 := ok_range hok
  have hlen : 2 * c.len + 2 < M := by
    have h1 : c.len ≤ 2 ^ 25 := by omega
    have h2 : 2 * (2:Nat) ^ 25 + 2 < M := by decide
    omega
  have hacc : c.acc0 % M < M := Nat.mod_lt _ M_pos
  have hseed : c.seedL % M < M := Nat.mod_lt _ M_pos
  rw [foldl_range_mul c.len c.B (fun x r => wmRound c r x)]
  exact congrArg Prod.fst
    (wmBlocks_eq c hB _ _ hacc hseed hlen c.len (Nat.le_refl _)).1

end FoldValue

section Init

/-! ### The initialization block

Two register writes and one `store` per seed row.  Everything here is proved
by induction over the seed list, so its cost is independent of the `595` rows
the production configuration carries.
-/

private def storeTriple (e : Nat × Nat) : List AInstr :=
  [ .scalar (.mov rT1 (.lit e.1)), .scalar (.mov rT2 (.lit e.2)), .store rT1 rT2 ]

private def initMovs (c : Cfg) : List Instr :=
  [ .mov rAcc (.lit c.acc0), .mov rL (.lit c.seedL) ]

private theorem wmInit_eq (c : Cfg) :
    wmInit c = lift (initMovs c) ++ c.seeds.flatMap storeTriple := rfl

private theorem storeTriple_regs (k : Nat) (e : Nat × Nat) (s : AState) (j : Nat) :
    (arun k s (storeTriple e)).regs j =
      (if j = rT2 then e.2 % M else if j = rT1 then e.1 % M else s.regs j) := rfl

private theorem storeTriple_arr (k : Nat) (e : Nat × Nat) (s : AState) (i : Nat) :
    (arun k s (storeTriple e)).arr i =
      (if i = e.1 % M then e.2 % M else s.arr i) := rfl

private theorem find?_snoc_none {α : Type _} {p : α → Bool} {a : α} :
    ∀ {l : List α}, l.find? p = none →
      (l ++ [a]).find? p = (if p a then some a else none) := by
  intro l
  induction l with
  | nil =>
      intro _
      show ([a] : List α).find? p = _
      by_cases ha : p a
      · rw [List.find?_cons_of_pos ha, if_pos ha]
      · rw [List.find?_cons_of_neg ha, if_neg ha]; rfl
  | cons b l ih =>
      intro h
      by_cases hb : p b
      · rw [List.find?_cons_of_pos hb] at h; exact absurd h (by simp)
      · rw [List.cons_append, List.find?_cons_of_neg hb,
          ih (by rw [List.find?_cons_of_neg hb] at h; exact h)]

private theorem find?_snoc_some {α : Type _} {p : α → Bool} {a x : α} :
    ∀ {l : List α}, l.find? p = some x → (l ++ [a]).find? p = some x := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b l ih =>
      intro h
      by_cases hb : p b
      · rw [List.find?_cons_of_pos hb] at h
        rw [List.cons_append, List.find?_cons_of_pos hb]; exact h
      · rw [List.find?_cons_of_neg hb] at h
        rw [List.cons_append, List.find?_cons_of_neg hb]; exact ih h

/-- The seed table, cell by cell: the **last** store to a cell wins, which is
exactly what `seedAt`'s `reverse.find?` reads. -/
private theorem stores_arr (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState) (i : Nat), (∀ e ∈ l, e.1 < M) →
      (arun k s (l.flatMap storeTriple)).arr i =
        ((l.reverse.find? (fun e => decide (e.1 = i))).map (fun e => e.2 % M)).getD
          (s.arr i) := by
  intro l
  induction l with
  | nil => intro s i _; rfl
  | cons e l ih =>
      intro s i hall
      have hmem : ∀ f ∈ l, f.1 < M := fun f hf => hall f (List.mem_cons_of_mem e hf)
      have he : e.1 < M := hall e (List.mem_cons_self ..)
      show (arun k (arun k s (storeTriple e)) (l.flatMap storeTriple)).arr i = _
      rw [ih _ i hmem, storeTriple_arr, Nat.mod_eq_of_lt he,
        show (e :: l).reverse = l.reverse ++ [e] from by simp]
      cases hfind : l.reverse.find? (fun f => decide (f.1 = i)) with
      | some x => rw [find?_snoc_some hfind]; simp
      | none =>
          rw [find?_snoc_none hfind]
          by_cases hi : e.1 = i
          · subst hi; simp
          · rw [if_neg (fun h : i = e.1 => hi h.symm)]
            simp [hi]

private theorem stores_regs (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState) (j : Nat), j ≠ rT1 → j ≠ rT2 →
      (arun k s (l.flatMap storeTriple)).regs j = s.regs j := by
  intro l
  induction l with
  | nil => intro s j _ _; rfl
  | cons e l ih =>
      intro s j h1 h2
      show (arun k (arun k s (storeTriple e)) (l.flatMap storeTriple)).regs j = _
      rw [ih _ j h1 h2, storeTriple_regs, if_neg h2, if_neg h1]

private theorem stores_regs_lt (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState), (∀ j, s.regs j < M) →
      ∀ j, (arun k s (l.flatMap storeTriple)).regs j < M := by
  intro l
  induction l with
  | nil => intro s h j; exact h j
  | cons e l ih =>
      intro s h j
      show (arun k (arun k s (storeTriple e)) (l.flatMap storeTriple)).regs j < M
      refine ih _ ?_ j
      intro j'
      rw [storeTriple_regs]
      split
      · exact Nat.mod_lt _ M_pos
      · split
        · exact Nat.mod_lt _ M_pos
        · exact h j'

private theorem stores_defined (c : Cfg) (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState), (∀ e ∈ l, e.1 < c.tableLen) →
      c.tableLen ≤ 2 ^ 20 →
      AllDefined c.tableLen k s (l.flatMap storeTriple) := by
  intro l
  induction l with
  | nil => intro s _ _; trivial
  | cons e l ih =>
      intro s hall hlen
      have he : e.1 < c.tableLen := hall e (List.mem_cons_self ..)
      have heM : e.1 < M := by
        have : (2:Nat) ^ 20 < M := by decide
        omega
      show AllDefined c.tableLen k s (storeTriple e ++ l.flatMap storeTriple)
      rw [AllDefined_append]
      refine ⟨⟨trivial, trivial, ?_, trivial⟩, ?_⟩
      · show (astep k (astep k s (.scalar (.mov rT1 (.lit e.1))))
          (.scalar (.mov rT2 (.lit e.2)))).regs rT1 < c.tableLen
        show (if rT1 = rT2 then e.2 % M else
          (if rT1 = rT1 then e.1 % M else s.regs rT1)) < c.tableLen
        rw [if_neg (by decide), if_pos rfl, Nat.mod_eq_of_lt heM]
        exact he
      · exact ih _ (fun f hf => hall f (List.mem_cons_of_mem e hf)) hlen

private theorem initMovs_rAcc (c : Cfg) :
    srun 0 initialState (initMovs c) rAcc = c.acc0 % M := by
  rw [show initMovs c = (.mov rAcc (.lit c.acc0) : Instr) ::
      [(.mov rL (.lit c.seedL) : Instr)] from rfl,
    srun_read_head 0 rAcc (.mov rAcc (.lit c.acc0)) [_] rfl rfl]
  rfl

private theorem initMovs_rL (c : Cfg) :
    srun 0 initialState (initMovs c) rL = c.seedL % M := by
  rw [show initMovs c = [(.mov rAcc (.lit c.acc0) : Instr)] ++
      [(.mov rL (.lit c.seedL) : Instr)] from rfl,
    srun_read_last 0 rL [_] (.mov rL (.lit c.seedL)) rfl]
  rfl

/-- The state the initialization block reaches. -/
def wmEntry (c : Cfg) : AState := arun 0 initialAState (wmInit c)

theorem wmEntry_rBad (c : Cfg) : (wmEntry c).regs rBad = 0 := by
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift,
    stores_regs 0 c.seeds _ rBad (by decide) (by decide)]
  show srun 0 initialState (initMovs c) rBad = 0
  rw [srun_frame 0 rBad (initMovs c) rfl]
  rfl

theorem wmEntry_rS (c : Cfg) : (wmEntry c).regs rS = 0 := by
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift,
    stores_regs 0 c.seeds _ rS (by decide) (by decide)]
  show srun 0 initialState (initMovs c) rS = 0
  rw [srun_frame 0 rS (initMovs c) rfl]
  rfl

theorem wmEntry_rAcc (c : Cfg) : (wmEntry c).regs rAcc = c.acc0 % M := by
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift,
    stores_regs 0 c.seeds _ rAcc (by decide) (by decide)]
  exact initMovs_rAcc c

theorem wmEntry_rL (c : Cfg) : (wmEntry c).regs rL = c.seedL % M := by
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift,
    stores_regs 0 c.seeds _ rL (by decide) (by decide)]
  exact initMovs_rL c

theorem wmEntry_regs_lt (c : Cfg) (j : Nat) : (wmEntry c).regs j < M := by
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift]
  refine stores_regs_lt 0 c.seeds _ ?_ j
  intro j'
  exact srun_regs_lt 0 (initMovs c) initialState (fun _ => M_pos) j'

/-- **The seed table is in the array.**  Cell `i` holds `seedAt c i`, the value
`wmRef` reads. -/
theorem wmEntry_arr (c : Cfg) (hok : wmOK c = true) (i : Nat) :
    (wmEntry c).arr i = seedAt c i := by
  have hlenM : c.tableLen ≤ 2 ^ 20 := ok_tableLen_le hok
  have hM20 : (2:Nat) ^ 20 < M := by decide
  have hseeds := ok_seeds hok
  rw [List.all_eq_true] at hseeds
  have hall : ∀ e ∈ c.seeds, e.1 < M := by
    intro e he
    have := hseeds e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  unfold wmEntry
  rw [wmInit_eq, arun_append, arun_lift, stores_arr 0 c.seeds _ i hall]
  show _ = seedAt c i
  unfold seedAt
  cases hfind : c.seeds.reverse.find? (fun e => decide (e.1 = i)) with
  | some x => rfl
  | none => rfl

theorem wmInit_defined (c : Cfg) (hok : wmOK c = true) :
    AllDefined c.tableLen 0 initialAState (wmInit c) := by
  have hlenM : c.tableLen ≤ 2 ^ 20 := ok_tableLen_le hok
  have hseeds := ok_seeds hok
  rw [List.all_eq_true] at hseeds
  rw [wmInit_eq, AllDefined_append]
  refine ⟨allDefined_lift_of_noDiv _ _ _ _ rfl, ?_⟩
  refine stores_defined c 0 c.seeds _ ?_ hlenM
  intro e he
  have := hseeds e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem wmInit_reaches (c : Cfg) (hok : wmOK c = true) :
    denoteAInstrs c.tableLen 0 initialAState (wmInit c) = some (wmEntry c) :=
  denoteAInstrs_eq_arun c.tableLen 0 (wmInit c) initialAState (wmInit_defined c hok)

end Init

section Denotation

/-! ### The encoding obligation, discharged -/

/-- The artifact's loop invariant: registers are words, the scan accumulator
is cleared or holds a trial divisor, and the array still holds the seed
table. -/
def WMInv (c : Cfg) (s : AState) : Prop :=
  (∀ j, s.regs j < M) ∧
  (s.regs rS = 0 ∨ (2 ≤ s.regs rS ∧ s.regs rS ≤ c.B + 1)) ∧
  (∀ i, s.arr i = seedAt c i)

theorem seedAt_lt (c : Cfg) (i : Nat) : seedAt c i < M := by
  unfold seedAt
  exact Nat.mod_lt _ M_pos

private theorem wmBody_arr (c : Cfg) (k : Nat) (s : AState) :
    (arun k s (wmBody c)).arr = s.arr := by
  rw [wmBody_arun]

private theorem wmBody_regs_lt (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ i, s.arr i < M) (j : Nat) :
    (arun k s (wmBody c)).regs j < M := by
  rw [wmBody_arun]
  show srun k (RegState.set (srun k s.regs (wmPre c)) rT3
    (s.arr (srun k s.regs (wmPre c) rT2))) (wmPost c) j < M
  refine srun_regs_lt k (wmPost c) _ ?_ j
  intro j'
  show (if j' = rT3 then s.arr (srun k s.regs (wmPre c) rT2)
        else srun k s.regs (wmPre c) j') < M
  split
  · exact harr _
  · exact srun_regs_lt k (wmPre c) s.regs hregs j'

private theorem wmBody_rS (c : Cfg) (hok : wmOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ i, s.arr i = seedAt c i) :
    (arun k s (wmBody c)).regs rS =
      (if k % c.B = c.B - 1 then 0 else sOf c k (s.regs rS)) :=
  congrArg (fun t : Nat × Nat × Nat × Nat => t.2.2.2)
    (wmBody_obs c hok k hk s hregs harr)

/-- **The program denotes the candidate-level reference.**

Definedness (`wmBody_defined`), the value of every register (`wmBody_obs`) and
the re-blocking of the flat `len · B` loop (`foldl_wmRound_eq_wmRef`),
assembled through `ArrayFoldBridge.AProgram.denote_eq_obs_foldl_mem`.  No fold
is evaluated anywhere. -/
theorem wmProgram_denote (c : Cfg) (hok : wmOK c = true) :
    (wmProgram c).denote = some (wmRef c) := by
  have hB : 0 < c.B := ok_B hok
  have hstep : ∀ (index : Nat) (s : AState), index < c.len * c.B → WMInv c s →
      denoteAInstrs c.tableLen index s (wmBody c) =
        some (arun index s (wmBody c)) := by
    intro index s hidx hinv
    exact denoteAInstrs_eq_arun c.tableLen index (wmBody c) s
      (wmBody_defined c hok index hidx s ⟨hinv.1, hinv.2.1⟩)
  have hclosed : ∀ (index : Nat) (s : AState), index < c.len * c.B → WMInv c s →
      WMInv c (arun index s (wmBody c)) := by
    intro index s hidx hinv
    obtain ⟨hregs, hscan, harr⟩ := hinv
    have harrM : ∀ i, s.arr i < M := fun i => by rw [harr i]; exact seedAt_lt c i
    refine ⟨fun j => wmBody_regs_lt c index s hregs harrM j, ?_, ?_⟩
    · rw [wmBody_rS c hok index hidx s hregs harr]
      split
      · exact Or.inl rfl
      · unfold sOf dOf
        split
        · have hmod : index % c.B < c.B := Nat.mod_lt _ hB
          exact Or.inr ⟨by omega, by omega⟩
        · exact hscan
    · intro i
      rw [wmBody_arr c index s]
      exact harr i
  have hobs : ∀ (index : Nat) (s : AState), index < c.len * c.B → WMInv c s →
      ((arun index s (wmBody c)).regs rBad, (arun index s (wmBody c)).regs rAcc,
        (arun index s (wmBody c)).regs rL, (arun index s (wmBody c)).regs rS) =
        wmRound c index (s.regs rBad, s.regs rAcc, s.regs rL, s.regs rS) := by
    intro index s hidx hinv
    exact wmBody_obs c hok index hidx s hinv.1 hinv.2.2
  have hentry : WMInv c (wmEntry c) :=
    ⟨wmEntry_regs_lt c, Or.inl (wmEntry_rS c), wmEntry_arr c hok⟩
  have hres := AProgram.denote_eq_obs_foldl_mem (wmProgram c) (WMInv c)
    (fun index s => arun index s (wmBody c))
    (fun s => (s.regs rBad, s.regs rAcc, s.regs rL, s.regs rS))
    (fun index a => wmRound c index a) (fun a => a.1) (wmEntry c)
    (wmInit_reaches c hok) hentry hstep hclosed hobs (fun _ _ => rfl)
  have hlc : (wmProgram c).loopCount = c.len * c.B := rfl
  rw [hres, hlc,
    show ((wmEntry c).regs rBad, (wmEntry c).regs rAcc, (wmEntry c).regs rL,
        (wmEntry c).regs rS) = (0, c.acc0 % M, c.seedL % M, 0) from by
      rw [wmEntry_rBad, wmEntry_rAcc, wmEntry_rL, wmEntry_rS],
    foldl_wmRound_eq_wmRef c hok]

/-- **`WMEncoding`, proved.**  The obligation the previous pass could only
state. -/
theorem wmEncoding (c : Cfg) : WMEncoding c := fun hok => wmProgram_denote c hok

end Denotation

end LeanCompCert.Ports.RamareWM217
