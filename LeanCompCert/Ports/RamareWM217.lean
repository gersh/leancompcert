import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Verified.ScalarLift
import LeanCompCert.Verified.ArrayBridge

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

/-! ## The body, in blocks -/

/-- Decode: `r = i % B`, `n = n0 + i / B`, `d = r + 2`. -/
def decodeBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop rR .urem .idx (.lit c.B))
  , .scalar (.binop rN .udiv .idx (.lit c.B))
  , .scalar (.binop rN .add (.reg rN) (.lit c.n0))
  , .scalar (.binop rD .add (.reg rR) (.lit 2)) ]

/-- One trial round:
`s := if s = 0 ∧ d·d ≤ n ∧ n % d = 0 then d else s`. -/
def scanBlock : List AInstr :=
  [ .scalar (.binop rG .eq (.reg rS) (.lit 0))
  , .scalar (.binop rT1 .mul (.reg rD) (.reg rD))
  , .scalar (.binop rT1 .le (.reg rT1) (.reg rN))
  , .scalar (.binop rG .mul (.reg rG) (.reg rT1))
  , .scalar (.binop rT2 .urem (.reg rN) (.reg rD))
  , .scalar (.binop rT2 .eq (.reg rT2) (.lit 0))
  , .scalar (.binop rG .mul (.reg rG) (.reg rT2))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg rG))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rS))
  , .scalar (.binop rT2 .mul (.reg rG) (.reg rD))
  , .scalar (.binop rS .add (.reg rT1) (.reg rT2)) ]

/-- Commit gate and factor select: `isP = (s = 0)`, `p = isP ? n : s`. -/
def selectBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop rC .eq (.reg rR) (.lit (c.B - 1)))
  , .scalar (.binop rIsP .eq (.reg rS) (.lit 0))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg rIsP))
  , .scalar (.binop rT2 .mul (.reg rT1) (.reg rS))
  , .scalar (.binop rT1 .mul (.reg rIsP) (.reg rN))
  , .scalar (.binop rP .add (.reg rT1) (.reg rT2)) ]

/-- One power-chain round: `m := m·p`, `pow := pow ∨ (m = n)`. -/
def powerRound : List AInstr :=
  [ .scalar (.binop rM .mul (.reg rM) (.reg rP))
  , .scalar (.binop rT1 .eq (.reg rM) (.reg rN))
  , .scalar (.binop rPow .bor (.reg rPow) (.reg rT1)) ]

/-- `pow = (∃ k ≤ powerRounds + 1, p^k = n)`, by a multiplication chain.
Over-acceptance through mod-`2⁶⁴` collisions is sound: it only inflates. -/
def powerBlock : List AInstr :=
  [ .scalar (.mov rM (.reg rP))
  , .scalar (.binop rPow .eq (.reg rM) (.reg rN)) ] ++
  (List.range powerRounds).flatMap (fun _ => powerRound)

/-- The ladder value charged to the candidate:
`lam = isP ? L : (pow ? seeds[p] : 0)`.  The table index is clamped to `0`
in the prime case, so the read stays in range. -/
def lambdaBlock : List AInstr :=
  [ .scalar (.binop rT1 .sub (.lit 1) (.reg rIsP))
  , .scalar (.binop rT2 .mul (.reg rT1) (.reg rP))
  , .load rT3 rT2
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rPow))
  , .scalar (.binop rT3 .mul (.reg rT1) (.reg rT3))
  , .scalar (.binop rT2 .mul (.reg rIsP) (.reg rL))
  , .scalar (.binop rLam .add (.reg rT2) (.reg rT3)) ]

/-- The dominating rescaled addend, gated by the commit:
`acc += C · ((n·(⌊lam/2²⁰⌋ + 1)) >>> 24 + 1)`. -/
def accBlock : List AInstr :=
  [ .scalar (.binop rT1 .lshr (.reg rLam) (.lit 20))
  , .scalar (.binop rT1 .add (.reg rT1) (.lit 1))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rN))
  , .scalar (.binop rT1 .lshr (.reg rT1) (.lit 24))
  , .scalar (.binop rT1 .add (.reg rT1) (.lit 1))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rC))
  , .scalar (.binop rAcc .add (.reg rAcc) (.reg rT1)) ]

/-- The cap test: a committed accumulator beyond `capA` is a violation, so a
`0` verdict certifies the width budget as well as the rows. -/
def capBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop rT1 .gt (.reg rAcc) (.lit c.capA))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rC))
  , .scalar (.binop rBad .add (.reg rBad) (.reg rT1)) ]

/-- The row test, at commits with `n ≥ lower`:
violation unless `2500·acc < 20016·n²`. -/
def rowBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop rT1 .mul (.reg rN) (.reg rN))
  , .scalar (.binop rT1 .mul (.reg rT1) (.lit 20016))
  , .scalar (.binop rT2 .mul (.reg rAcc) (.lit 2500))
  , .scalar (.binop rT2 .ge (.reg rT2) (.reg rT1))
  , .scalar (.binop rLow .ge (.reg rN) (.lit c.lower))
  , .scalar (.binop rT2 .mul (.reg rT2) (.reg rLow))
  , .scalar (.binop rT2 .mul (.reg rT2) (.reg rC))
  , .scalar (.binop rBad .add (.reg rBad) (.reg rT2)) ]

/-- `incUWord n`, instruction for instruction
(`Ports/RS62Increments.lean`), then the gated ladder advance. -/
def ladderBlock : List AInstr :=
  [ .scalar (.binop rT1 .mul (.reg rN) (.lit 2))
  , .scalar (.binop rT1 .add (.reg rT1) (.lit (3 * fpD)))
  , .scalar (.binop rT2 .add (.reg rN) (.lit (3 * fpD)))
  , .scalar (.binop rT2 .sub (.reg rT2) (.lit 1))
  , .scalar (.binop rT2 .udiv (.reg rT2) (.reg rN))
  , .scalar (.binop rT1 .sub (.reg rT1) (.reg rT2))
  , .scalar (.binop rT2 .mul (.reg rN) (.lit 2))
  , .scalar (.binop rT1 .udiv (.reg rT1) (.reg rT2))
  , .scalar (.binop rT2 .add (.reg rN) (.lit fpD))
  , .scalar (.binop rT2 .sub (.reg rT2) (.lit 1))
  , .scalar (.binop rT1 .sub (.reg rT2) (.reg rT1))
  , .scalar (.binop rT2 .sub (.reg rN) (.lit 1))
  , .scalar (.binop rIU .udiv (.reg rT1) (.reg rT2))
  , .scalar (.binop rT1 .mul (.reg rC) (.reg rIU))
  , .scalar (.binop rL .add (.reg rL) (.reg rT1)) ]

/-- Clear the scan accumulator at the last round of each candidate. -/
def resetBlock : List AInstr :=
  [ .scalar (.binop rT1 .sub (.lit 1) (.reg rC))
  , .scalar (.binop rS .mul (.reg rT1) (.reg rS)) ]

/-- The loop body: 137 instructions, every one executed every iteration. -/
def wmBody (c : Cfg) : List AInstr :=
  decodeBlock c ++ scanBlock ++ selectBlock c ++ powerBlock ++
    lambdaBlock ++ accBlock ++ capBlock c ++ rowBlock c ++ ladderBlock ++
    resetBlock

/-- Initialization: the two carried registers, then the seed table. -/
def wmInit (c : Cfg) : List AInstr :=
  [ .scalar (.mov rAcc (.lit c.acc0))
  , .scalar (.mov rL (.lit c.seedL)) ] ++
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

private theorem decodeBlock_wf (c : Cfg) :
    ∀ a ∈ decodeBlock c, a.WF wmRegCount := by
  intro a ha
  simp only [decodeBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem scanBlock_wf : ∀ a ∈ scanBlock, a.WF wmRegCount := by
  intro a ha
  simp only [scanBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem selectBlock_wf (c : Cfg) :
    ∀ a ∈ selectBlock c, a.WF wmRegCount := by
  intro a ha
  simp only [selectBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem powerRound_wf : ∀ a ∈ powerRound, a.WF wmRegCount := by
  intro a ha
  simp only [powerRound, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem powerBlock_wf : ∀ a ∈ powerBlock, a.WF wmRegCount := by
  intro a ha
  simp only [powerBlock, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at ha
  rcases ha with (h|h) | ⟨_, _, h⟩
  · subst h; simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]
  · subst h; simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]
  · exact powerRound_wf a h

private theorem lambdaBlock_wf : ∀ a ∈ lambdaBlock, a.WF wmRegCount := by
  intro a ha
  simp only [lambdaBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem accBlock_wf : ∀ a ∈ accBlock, a.WF wmRegCount := by
  intro a ha
  simp only [accBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem capBlock_wf (c : Cfg) : ∀ a ∈ capBlock c, a.WF wmRegCount := by
  intro a ha
  simp only [capBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem rowBlock_wf (c : Cfg) : ∀ a ∈ rowBlock c, a.WF wmRegCount := by
  intro a ha
  simp only [rowBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem ladderBlock_wf : ∀ a ∈ ladderBlock, a.WF wmRegCount := by
  intro a ha
  simp only [ladderBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

private theorem resetBlock_wf : ∀ a ∈ resetBlock, a.WF wmRegCount := by
  intro a ha
  simp only [resetBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

theorem wmBody_wf (c : Cfg) : ∀ a ∈ wmBody c, a.WF wmRegCount := by
  intro a ha
  rw [wmBody] at ha
  rcases List.mem_append.mp ha with h | h
  rotate_left
  · exact resetBlock_wf a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact ladderBlock_wf a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact rowBlock_wf c a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact capBlock_wf c a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact accBlock_wf a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact lambdaBlock_wf a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact powerBlock_wf a h
  rcases List.mem_append.mp h with h | h
  rotate_left
  · exact selectBlock_wf c a h
  rcases List.mem_append.mp h with h | h
  · exact decodeBlock_wf c a h
  · exact scanBlock_wf a h

theorem wmInit_wf (c : Cfg) : ∀ a ∈ wmInit c, a.WF wmRegCount := by
  intro a ha
  simp only [wmInit, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at ha
  rcases ha with (h | h) | ⟨e, _, he⟩
  · subst h; simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]
  · subst h; simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]
  · rcases he with h|h|h <;> subst h <;>
      simp +decide [AInstr.WF, Instr.WF, Operand.WF, wmRegCount]

/-- **The program is well formed** at every configuration, so
`AProgram.evalCC_compile` applies: the compiled trace and the emitted C
compute exactly `AProgram.denote`. -/
theorem wmProgram_wf (c : Cfg) : (wmProgram c).WF := by
  refine ⟨by simp [wmProgram, wmRegCount, rBad], ?_, ?_, ?_⟩
  · exact wmInit_wf c
  · exact wmBody_wf c
  · intro a ha
    exact absurd ha (by simp [wmProgram])

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
