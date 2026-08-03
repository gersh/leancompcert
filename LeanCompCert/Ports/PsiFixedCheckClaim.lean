import LeanCompCert.Ports.PsiFixedCheckRound
import LeanCompCert.Verified.Package
import LeanCompCert.Verified.Rolled

/-!
# The ψ fixed-point check, packaged

`psProgram_denote` (in `Ports/PsiFixedCheckRound.lean`) proves that the
register program's denotation is `pass · ok` of the `psRound` fold.  This file
packages the program as a `Computation` — the object a run-admission fact is
stated about — and pins the emitted function's name.

The identification of the fold with the consumer's own per-candidate
mathematics (`Nat.minFac`, `IsPrimePow`, the rational `logUB` majorant)
requires Mathlib and lives on the consumer side; it is imported there, not
assumed here.

Nothing here is a certificate, nothing here asserts that any execution
happened, and nothing here adds an axiom.
-/

namespace LeanCompCert.Ports.PsiFixedCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

/-- The emitted C function's name, matching `bench/PsiFixedEmit.lean`. -/
def psName (P : Params) : String :=
  "PsiFixedCheck" ++ toString P.start ++ "x" ++ toString P.fuel ++ "x" ++
    toString P.td ++ "x" ++ toString P.K ++ "x" ++ toString P.lo

/-- The packaged computation whose acceptance a run of the CompCert-compiled
artifact is evidence for. -/
def psComputation (P : Params) : Verified.Computation :=
  (psProgram P).toComputation (psName P) (psProgram_wf P)

/-- Acceptance of the packaged computation is exactly the program's
denotation. -/
theorem psComputation_returns (P : Params) (n : Nat) :
    (psComputation P).Returns ((n : Nat) : Int) ↔
      (psProgram P).denote = some n :=
  Reflect.toComputation_returns (psProgram P) (psName P) (psProgram_wf P) n

/-- A run returning `1` forces `pass = ok = 1` on the `psRound` fold. -/
theorem psFinal_of_denote (P : Params) (hP : P.Sane)
    (h : (psProgram P).denote = some 1) :
    (psFinalVals P).pass = 1 ∧ (psFinalVals P).ok = 1 := by
  rw [psProgram_denote P hP] at h
  have h1 : (psFinalVals P).pass * (psFinalVals P).ok = 1 :=
    Option.some.inj h
  constructor
  · exact Nat.eq_one_of_mul_eq_one_right h1
  · exact Nat.eq_one_of_mul_eq_one_left h1

/-! ## Kernel checks

Tiny configurations, evaluated in the kernel: the machine fold matches the
intended semantics on both an accepting and a rejecting sizing.

* `K = 2²⁹` dominates every possible per-candidate average, so the scan
  accepts;
* `K = 0` rejects at the first candidate with a positive Λ̂ (`n = 2`), and
  the masked window `lo = 3` delays that rejection past `n = 2` only if the
  test is genuinely masked below `lo` — `n = 3` is again a prime, so it still
  rejects.
-/

namespace Check

set_option maxRecDepth 20000000

example :
    (psProgram ⟨1, 3, 3, 2 ^ 29, 1⟩).denote = some 1 := by decide +kernel

example :
    (psProgram ⟨1, 3, 3, 0, 1⟩).denote = some 0 := by decide +kernel

example :
    (psProgram ⟨1, 2, 3, 0, 3⟩).denote = some 1 := by decide +kernel

end Check

end LeanCompCert.Ports.PsiFixedCheck
