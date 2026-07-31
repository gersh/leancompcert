import LeanCompCert.Ports.RS62LadderProgram

/-!
# One segment of the RS62 anchor ladder, as an artifact

The ternary-goldbach development's `MathExtras.RS62Ladder.loopE` walks the
primes from `101` and accumulates a two-sided fixed-point enclosure of
`log ∏_{p ≤ y} p/(p−1)` at scale `D = 2⁴⁸`.  The production claim is

```
loopE 99999900 101 0 0 = (386481147529431, 386487029388140)      -- y = 10⁸
```

together with 120 further checkpoints of the same run out to `y = 3.24 × 10⁸`.
Those are prefixes of a single run, so `Ports.RS62.loopE_of_chain` composes
segments of it without re-evaluating any of them.

**This certificate is one such segment**: the first `65 536` candidates,
`n ∈ [101, 65 637)`, containing `6 531` primes.  The trial-division scan is
given `B = 256` rounds per candidate, which covers the window's square root
(`65 636 < 258² = 66 564`), so `Verified.Sieve.spfFixed_eq_leastFactor` applies
across it.  The loop is `65 536 × 256 = 16 777 216` iterations.

Two programs, because one `AProgram` denotes one number: the artifact reports
the lower accumulator or the upper one, and a two-sided claim needs both.

## What the numbers below are

`expectedSL` and `expectedSU` are the values an independent exact-integer
computation produces for this window; the emitted `main` compares the
program's output against them and exits `0` only on agreement.  They are
**corroborated, not proved** — the step from `denote = some n` to a statement
about `loopE` is `Ports.RS62Ladder.LadderEncoding`, which is not discharged.
-/

namespace LeanCompCert.Testing.RS62LadderCertificate

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RS62Ladder

/-- Window start: the ladder's head value is certified separately, so the fold
begins at `101`. -/
def n0 : Nat := 101

/-- Candidates in this segment. -/
def f : Nat := 65536

/-- Trial-division rounds per candidate; `n0 + f - 1 < (B + 2)²`. -/
def B : Nat := 256

/-- `D · (log ∏_{p < 65637} p/(p−1) − log ∏_{p < 101} p/(p−1))`, rounded down
at every prime. -/
def expectedSL : Nat := 243790673307260

/-- The same, rounded up at every prime. -/
def expectedSU : Nat := 243796549405313

def programSL : AProgram := ladderProgram n0 f B 0 0 rSL
def programSU : AProgram := ladderProgram n0 f B 0 0 rSU

theorem programSL_wf : programSL.WF :=
  ladderProgram_wf n0 f B 0 0 rSL (by decide)

theorem programSU_wf : programSU.WF :=
  ladderProgram_wf n0 f B 0 0 rSU (by decide)

def symbolNameSL : String := "RS62.ladderSL65k"
def symbolNameSU : String := "RS62.ladderSU65k"

private def mainC (symbol : String) (expected : Nat) : String :=
  "\nstatic uint64_t cells[1];\n" ++
  "int main(void)\n{\n" ++
  "    return " ++ symbol ++ "((uint64_t)(uintptr_t)cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emittedCSL : Except (Array String) String := do
  let source ← programSL.emitRolled symbolNameSL
  pure (source ++ mainC "l_RS62_ladderSL65k" expectedSL)

def emittedCSU : Except (Array String) String := do
  let source ← programSU.emitRolled symbolNameSU
  pure (source ++ mainC "l_RS62_ladderSU65k" expectedSU)

end LeanCompCert.Testing.RS62LadderCertificate
