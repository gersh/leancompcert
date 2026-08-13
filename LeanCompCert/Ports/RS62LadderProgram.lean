import LeanCompCert.Ports.RS62LoopE
import LeanCompCert.Verified.ScalarLift
import LeanCompCert.Verified.Sieve

/-!
# The RS62 anchor ladder as a register program

`Ports/RS62LoopE.lean` puts `MathExtras.RS62Ladder.loopE` into fold form and
proves the three levers a migration needs — `loopE_eq_foldl`,
`loopE_of_chain`, `loopE_eq_word`.  `Ports/RS62Increments.lean` proves that the
per-step increments, whose source form needs a 106-bit numerator, are equal to
expressions in which every intermediate is below `2⁵¹`.

This file is the next step: an actual `AProgram` that walks a window of the
ladder.  It is the shape the artifact pipeline consumes —
`AProgram.evalCC_compile` compiles it, `emitRolled` emits it, and
`Trusted.evidenced_decide` can admit a run of it.

## The shape: a fixed-shape scan, flattened

There is no control flow, so the primality guard cannot be a loop that stops
when it finds a factor.  `Verified/Sieve.lean` already supplies the
data-independent form: `spfScan bound n` folds `spfStep n` over exactly `bound`
rounds, and `spfFixed_eq_leastFactor` proves that with `n < (bound + 2)²` the
scan computes the smallest factor.

The program flattens candidate × round into one loop of `f · B` iterations.
At index `i`:

* `r = i % B` is the round and `d = r + 2` the trial divisor;
* `q = i / B` is the candidate offset and `n = n₀ + q` the candidate — derived
  from the index rather than carried, so the loop invariant needs no bound on
  how many iterations have run;
* one `spfStep` round updates the scan accumulator;
* on the last round of a candidate (`r = B − 1`) the accumulator is consulted,
  the increments are added if it is still zero, and the accumulator is reset.

The increments are computed with `incLWord` / `incUWord` **every** iteration,
because there is no branch to skip them; they are gated to zero by
multiplication.  That is what makes the per-iteration cost six divisions rather
than one, and it is the price of the fragment's data independence.

## What this file proves and what it does not

Proved here: the program is well formed (`ladderProgram_wf`), so
`AProgram.evalCC_compile` applies and the emitted C computes exactly
`AProgram.denote`.

This low-level module states the denotation obligation as `LadderEncoding`.
The downstream `Ports/RS62LadderEncoding.lean` module now proves it for the
fixed-shape `scanPrime` predicate under explicit coverage and word-room
premises.  The reusable ingredients exposed here are:

* `FoldBridge.Program.denote_eq_foldl` turns the program into a `List.foldl`
  over `List.range (f · B)` — size-independent, proved once;
* `RS62.loopE_eq_foldl` turns the ladder into a `List.foldl` over
  `List.range' n₀ f`;
* `Sieve.spfFixed_eq_leastFactor` identifies the flattened scan's verdict with
  the smallest factor.

The downstream proof supplies the re-blocking between the two index spaces
and all word-modulus side conditions without evaluating either fold.

## Scale

`B` must cover `√n`, so a window ending at `N` costs `Σ √n ≈ ⅔ N^{3/2}`
rounds: at `N = 3.24 × 10⁸`, the anchor ladder's endpoint, that is
`1.2 × 10¹³` iterations — out of reach.  The fixed-shape scan is the right
shape for a window of a few million and the wrong shape for the whole run;
the alternatives are a variable-budget micro-step machine (`≈ 1.5 × 10¹¹`
rounds) or an array sieve (`≈ 10⁹`), and the latter is the one whose
denotation is not characterised anywhere in this package.
-/

namespace LeanCompCert.Ports.RS62Ladder

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RS62

/-! ## Register conventions -/

/-- Lower fixed-point accumulator. -/
def rSL : Nat := 0
/-- Upper fixed-point accumulator. -/
def rSU : Nat := 1
/-- The candidate `n`, recomputed from the loop index each iteration. -/
def rN : Nat := 2
/-- The smallest-factor scan accumulator for the current candidate. -/
def rAcc : Nat := 3
/-- The round `i % B`. -/
def rR : Nat := 4
/-- The trial divisor `r + 2`. -/
def rD : Nat := 5
/-- The `spfStep` gate. -/
def rG : Nat := 6
/-- Scratch. -/
def rT1 : Nat := 7
/-- Scratch. -/
def rT2 : Nat := 8
/-- `m = n − 1`, the increment argument. -/
def rM : Nat := 9
/-- `incLWord m`. -/
def rIL : Nat := 10
/-- `incUWord m`. -/
def rIU : Nat := 11
/-- The commit gate `r = B − 1`. -/
def rC : Nat := 12
/-- The prime gate: committing and the scan found nothing. -/
def rPr : Nat := 13

/-- Registers used. -/
def ladderRegCount : Nat := 14

/-! ## The body

Forty-seven instructions, in four groups: decode the index, one `spfStep`
round, the two increments, and the gated commit.  Every one of them executes
on every iteration.
-/

/-- Decode: `r = i % B`, `n = n₀ + i / B`, `d = r + 2`. -/
def decodeBlock (n0 B : Nat) : List Instr :=
  [ .binop rR .urem .idx (.lit B)
  , .binop rN .udiv .idx (.lit B)
  , .binop rN .add (.reg rN) (.lit n0)
  , .binop rD .add (.reg rR) (.lit 2) ]

/-- One `spfStep` round: `acc := if acc = 0 ∧ d·d ≤ n ∧ n % d = 0 then d else acc`.

The blend reads `acc` **before** it is written — the ordering the mux pattern
warns about, and the reason `rT1` holds `(1 − g)·acc` before `rAcc` is
touched. -/
def scanBlock : List Instr :=
  [ .binop rG .eq (.reg rAcc) (.lit 0)
  , .binop rT1 .mul (.reg rD) (.reg rD)
  , .binop rT1 .le (.reg rT1) (.reg rN)
  , .binop rG .mul (.reg rG) (.reg rT1)
  , .binop rT2 .urem (.reg rN) (.reg rD)
  , .binop rT2 .eq (.reg rT2) (.lit 0)
  , .binop rG .mul (.reg rG) (.reg rT2)
  , .binop rT1 .sub (.lit 1) (.reg rG)
  , .binop rT1 .mul (.reg rT1) (.reg rAcc)
  , .binop rT2 .mul (.reg rG) (.reg rD)
  , .binop rAcc .add (.reg rT1) (.reg rT2) ]

/-- `incLWord m = (fpD − ((3·fpD + 2m) + (fpD−1)/m) / (2m)) / (m−1)`,
instruction for instruction. -/
def incLBlock : List Instr :=
  [ .binop rT1 .mul (.reg rM) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit (3 * fpD))
  , .binop rT2 .udiv (.lit (fpD - 1)) (.reg rM)
  , .binop rT1 .add (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.reg rM) (.lit 2)
  , .binop rT1 .udiv (.reg rT1) (.reg rT2)
  , .binop rT1 .sub (.lit fpD) (.reg rT1)
  , .binop rT2 .sub (.reg rM) (.lit 1)
  , .binop rIL .udiv (.reg rT1) (.reg rT2) ]

/-- `incUWord m = ((fpD + m − 1) − ((3·fpD + 2m) − (3·fpD + m − 1)/m) / (2m)) / (m−1)`,
instruction for instruction. -/
def incUBlock : List Instr :=
  [ .binop rT1 .mul (.reg rM) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit (3 * fpD))
  , .binop rT2 .add (.reg rM) (.lit (3 * fpD))
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT2 .udiv (.reg rT2) (.reg rM)
  , .binop rT1 .sub (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.reg rM) (.lit 2)
  , .binop rT1 .udiv (.reg rT1) (.reg rT2)
  , .binop rT2 .add (.reg rM) (.lit fpD)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT1 .sub (.reg rT2) (.reg rT1)
  , .binop rT2 .sub (.reg rM) (.lit 1)
  , .binop rIU .udiv (.reg rT1) (.reg rT2) ]

/-- The gated commit: on the last round of a candidate, add the increments if
the scan found no factor, then clear the accumulator. -/
def commitBlock (B : Nat) : List Instr :=
  [ .binop rC .eq (.reg rR) (.lit (B - 1))
  , .binop rT1 .eq (.reg rAcc) (.lit 0)
  , .binop rPr .mul (.reg rC) (.reg rT1)
  , .binop rM .sub (.reg rN) (.lit 1) ] ++
  incLBlock ++ incUBlock ++
  [ .binop rT1 .mul (.reg rPr) (.reg rIL)
  , .binop rSL .add (.reg rSL) (.reg rT1)
  , .binop rT2 .mul (.reg rPr) (.reg rIU)
  , .binop rSU .add (.reg rSU) (.reg rT2)
  , .binop rT1 .sub (.lit 1) (.reg rC)
  , .binop rAcc .mul (.reg rT1) (.reg rAcc) ]

/-- The loop body. -/
def ladderBody (n0 B : Nat) : List Instr :=
  decodeBlock n0 B ++ scanBlock ++ commitBlock B

/-! ## The program -/

/--
The ladder over the window `[n₀, n₀ + f)`, scanned with `B` trial-division
rounds per candidate, starting from the fixed-point state `(SL₀, SU₀)`.

`out` selects which accumulator the artifact reports: `rSL` or `rSU`.  One
`AProgram` denotes one number, so a two-sided ladder claim is two programs and
two runs.
-/
def ladderScalarProgram (n0 f B SL0 SU0 out : Nat) : Program :=
  { regCount := ladderRegCount
  , loopCount := f * B
  , init := [ .mov rSL (.lit SL0), .mov rSU (.lit SU0) ]
  , body := ladderBody n0 B
  , epilogue := []
  , output := out }

/-- The same program on the array machine, which is what the artifact pipeline
and `evidenced_decide` speak.  The array is empty. -/
def ladderProgram (n0 f B SL0 SU0 out : Nat) : AProgram :=
  AProgram.ofProgram (ladderScalarProgram n0 f B SL0 SU0 out)

/-- Well-formedness of the scalar program: every register index is below
`ladderRegCount`, at every configuration. -/
theorem ladderScalarProgram_wf (n0 f B SL0 SU0 out : Nat)
    (hOut : out < ladderRegCount) :
    (ladderScalarProgram n0 f B SL0 SU0 out).WF := by
  refine ⟨hOut, ?_, ?_, ?_⟩ <;>
    simp [ladderScalarProgram, ladderBody, decodeBlock, scanBlock, commitBlock,
      incLBlock, incUBlock, Instr.WF, Operand.WF, ladderRegCount, rSL, rSU, rN,
      rAcc, rR, rD, rG, rT1, rT2, rM, rIL, rIU, rC, rPr]

/-- **The program is well formed**, so `AProgram.evalCC_compile` applies: the
compiled CCIR trace, and therefore the emitted C, computes exactly
`AProgram.denote`. -/
theorem ladderProgram_wf (n0 f B SL0 SU0 out : Nat)
    (hOut : out < ladderRegCount) :
    (ladderProgram n0 f B SL0 SU0 out).WF :=
  AProgram.ofProgram_WF (ladderScalarProgram_wf n0 f B SL0 SU0 out hOut)

/-- The denotation is the scalar machine's, unchanged. -/
theorem ladderProgram_denote (n0 f B SL0 SU0 out : Nat) :
    (ladderProgram n0 f B SL0 SU0 out).denote =
      (ladderScalarProgram n0 f B SL0 SU0 out).denote :=
  AProgram.ofProgram_denote _

/-! ## The encoding obligation

Everything above is about the *program*.  The statement a certificate wants is
about the *ladder*.  It is defined here to avoid a dependency cycle and proved
for `scanPrime` in `Ports/RS62LadderEncoding.lean`.
-/

/--
**The encoding obligation.**  What has to be true for a run of
`ladderProgram` to say anything about `RS62.loopE`.

`p` is the ladder's primality guard.  `B` must cover the window's square root
(`n₀ + f ≤ (B + 2)²`) for `Sieve.spfFixed_eq_leastFactor` to identify the
flattened scan with the true smallest factor; that hypothesis is part of the
obligation, not an aside.
-/
def LadderEncoding (p : Nat → Bool) (n0 f B SL0 SU0 : Nat) : Prop :=
  (ladderProgram n0 f B SL0 SU0 rSL).denote =
      some (loopE p f n0 SL0 SU0).1 ∧
  (ladderProgram n0 f B SL0 SU0 rSU).denote =
      some (loopE p f n0 SL0 SU0).2

/--
Given the encoding, a pair of artifact values *is* a ladder segment — and
`RS62.loopE_of_chain` then composes segments into the whole run without
re-evaluating any of them.
-/
theorem loopE_of_encoding {p : Nat → Bool} {n0 f B SL0 SU0 vL vU : Nat}
    (henc : LadderEncoding p n0 f B SL0 SU0)
    (hL : (ladderProgram n0 f B SL0 SU0 rSL).denote = some vL)
    (hU : (ladderProgram n0 f B SL0 SU0 rSU).denote = some vU) :
    loopE p f n0 SL0 SU0 = (vL, vU) := by
  obtain ⟨hencL, hencU⟩ := henc
  have eL : (loopE p f n0 SL0 SU0).1 = vL := by
    have := hencL.symm.trans hL
    exact Option.some.inj this
  have eU : (loopE p f n0 SL0 SU0).2 = vU := by
    have := hencU.symm.trans hU
    exact Option.some.inj this
  calc loopE p f n0 SL0 SU0
      = ((loopE p f n0 SL0 SU0).1, (loopE p f n0 SL0 SU0).2) := rfl
    _ = (vL, vU) := by rw [eL, eU]

end LeanCompCert.Ports.RS62Ladder
