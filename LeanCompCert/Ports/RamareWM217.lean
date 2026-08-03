import LeanCompCert.Ports.RS62Increments
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

**Not proved here**: `wmProgram_denote` — that `denote = some (wmRef c)` for
every admissible `c`.  That is the encoding obligation; it is *stated* below
as `WMEncoding`, shaped for `ArrayFoldBridge` (the body is one flat loop, the
array is written only in `init`), and it is what turns a run of this artifact
into `WM217Rows` through the goldbach tree's
`checkWeightedMomentTable_eq_true_iff`.  Definedness (above) is one of its two
halves; the other two are the *value* of the body — every register, not just
the divisors — and the re-blocking of the flat `len·B` loop into candidates.
Until they are proved, a campaign entry for this artifact must carry
`evaluates_atom_predicate: false`.
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
  c.seeds.all (fun e => decide (e.1 < c.tableLen) && decide (e.2 < 2 ^ 53))

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
  exact h.1.1.1.1.1.1.1.1.1.1

theorem ok_B {c : Cfg} (h : wmOK c = true) : 1 ≤ c.B := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem ok_tableLen {c : Cfg} (h : wmOK c = true) : c.B + 1 < c.tableLen := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.2

theorem ok_range {c : Cfg} (h : wmOK c = true) : c.n0 + c.len ≤ 2 ^ 25 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.2

theorem ok_tableLen_le {c : Cfg} (h : wmOK c = true) : c.tableLen ≤ 2 ^ 20 := by
  simp only [wmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

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

/-! ## The encoding obligation, stated

Everything above is about the *program*.  The statement a certificate wants
is about the *reference*, whose identification with the goldbach tree's
`WM217Rows` is Mathlib-side work (`Nat.minFac`, `powerCheck`, the LeanCert
seed values).  This is the gap, written down rather than assumed away: an
artifact run reads a number off a **proved** denotation; it never establishes
one (`Verified/Algorithm/ArrayBridge.lean`).
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

end LeanCompCert.Ports.RamareWM217
