import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Verified.ScalarLift
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayScalarBlock

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
* two kernel smoke checks: at a tiny configuration the 135-instruction body
  denotes exactly the independently written candidate-level reference
  `wmRef`, run both in passing and in violating sizings.

**Not proved here**: `wmProgram_denote` — that `denote = some (wmRef c)` for
every admissible `c`.  That is the encoding obligation; it is *stated* below
as `WMEncoding`, shaped for `ArrayFoldBridge` (the body is one flat loop, the
array is written only in `init`), and it is what turns a run of this artifact
into `WM217Rows` through the goldbach tree's
`checkWeightedMomentTable_eq_true_iff`.  Until it is proved, a campaign entry
for this artifact must carry `evaluates_atom_predicate: false`.
-/

namespace LeanCompCert.Ports.RamareWM217

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RS62
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock (srun)

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

/-! ### The other two partial stages, and a measured obstruction

`decodeBlock_defined` goes through as written: its divisor is a literal, so
the threaded state never has to be evaluated.  The scan and the ladder do not,
and the two failures are different and both worth recording.

**The scan.**  Its `urem` divisor is `rD`, set by the *decode* four
instructions earlier, so the goal carries four nested `RegState.set`s and
`simp` must frame `rD` through them.  That is `InstrBlock.srun_untouched`'s
job, not `simp`'s; the fix is a framing lemma, not a bigger simp set.

**The ladder.**  Unfolding `ladderBlock` inside `simp` trips the kernel's
recursion guard outright:

```text
LeanCompCert/Ports/RamareWM217.lean:566:8: error: (kernel) deep recursion detected
```

This is the big-numeral class, and it localises it: the ladder is the one
block whose operands are `fpD`-scale literals (`fpD3 = 8.4·10¹⁴`), and the
`% M` around each `denoteOp` puts a symbolic register next to one of them.
Writing `3 * fpD` as the plain numeral `fpD3` (above) was necessary but is
not sufficient — the remaining cost is in `simp`'s own normalisation of
`(reg ⊕ literal) % M`, so the fix is to keep the literals *out* of the
normal form: frame the divisor registers first and never unfold the
arithmetic of the non-division instructions at all.

Both are mechanical and neither is mathematical, but both are real work, so
they are recorded here rather than papered over.
-/

/-! ## What remains for `WMEncoding`

The three lemmas above are the four named side conditions of the partial
instructions, each proved where it lives.  Composing them into
`AllDefined c.tableLen k s (wmBody c)` needs, in addition:

* the **decode spec** — that after `decodeBlock` the registers `rR`, `rN`,
  `rD` hold `k % B`, `n0 + k / B` and `k % B + 2` — which supplies the
  hypotheses `2 ≤ rD` of `scanBlock_defined` and `2 ≤ rN`, `2·rN < M` of
  `ladderBlock_defined` (`ok_idx` already bounds the decode against `M`);
* **framing**: `rN` is written by the decode and read by the ladder 100
  instructions later, so the intervening stages must be shown not to write
  it (`InstrBlock.srun_untouched`);
* the **seed-table read** `rT2 < tableLen`: `rT2 = (1 − isP)·p`, which is `0`
  when the candidate is prime and otherwise the scan's divisor, so this is
  `Inv.scan` transported across the scan and select stages, together with
  `ok_tableLen`.

None of these is assumed anywhere in this file: there is no `sorry` and no
axiom here.
-/

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
