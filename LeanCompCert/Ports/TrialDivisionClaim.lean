import LeanCompCert.Ports.TrialDivisionBlockSpec
import LeanCompCert.Verified.Algorithm.Spec

/-!
# The trial-division fold as a `ProgramClaim`

`Ports/TrialDivisionFold.lean` proves what the register program denotes;
`Ports/TrialDivisionBlockSpec.lean` proves that one block of `D` rounds is one
candidate.  This module composes them into the single implication a consumer
needs, and packages it as a `ProgramClaim`.

The proposition is deliberately stated in plain `Nat`:

```
(List.range fuel).foldl (fun a q => a + progTerm div (start + q)) 0 ≤ bound
```

No `Program`, no register, no `% M`, and no Mathlib.  The number-theoretic
identification of `progTerm` with a certificate's own per-element term — that
`progTerm D n` is `⌈2⁴⁹·2^{ω(n)} / (n·φ(n))⌉` for squarefree `n` in range —
belongs to the consumer, which has Mathlib; it is imported there, not assumed
here.

## What this does and does not establish

`ProgramClaim.prove` takes a `Computation.Returns` hypothesis.  This module
neither creates nor admits one.  Everything below is an ordinary Lean theorem
about `Program.denote`; nothing here asserts that any physical execution
happened, and nothing here adds an axiom.
-/

namespace LeanCompCert.Ports.TrialDivisionClaim

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Algorithm
open LeanCompCert.Ports.TrialDivisionFold
open LeanCompCert.Ports.TrialDivisionBlockSpec

/-- The per-candidate sum the compiled program accumulates. -/
def progSum (P : Params) : Nat :=
  (List.range P.fuel).foldl (fun a q => a + progTerm P.div (P.start + q)) 0

/--
**The consumer's entry point.**

If the compiled program returns the accepting value `1`, then the plain `Nat`
sum of the per-candidate terms is within the certified bound.

Both halves are one-way, as they should be: the program returning `1` says
that no accumulator step wrapped *and* the total was within `bound`, and only
the second is carried forward.  A program that returned `0` would say nothing,
which is exactly what a certificate is entitled to.
-/
theorem progSum_le_of_denote (P : Params) (hP : P.Sane) (hD : 2 ≤ P.div)
    (hb : P.bound < M) (hrun : (tdProgram P).denote = some 1) :
    progSum P ≤ P.bound := by
  rw [tdProgram_denote P hP hb] at hrun
  have hcond :
      ((List.range (P.fuel * P.div)).foldl
          (fun v k => tdRound P k v) initVals).ok = 1 ∧
        ((List.range (P.fuel * P.div)).foldl
          (fun v k => tdRound P k v) initVals).acc ≤ P.bound := by
    split at hrun
    · assumption
    · exact Nat.noConfusion (Option.some.inj hrun)
  obtain ⟨hok, hle⟩ := hcond
  have hacc0 : initVals.acc = 0 := rfl
  have hMpos : (0 : Nat) < M := M_pos
  have hexact :
      ((List.range (P.fuel * P.div)).foldl
        (fun v k => tdRound P k v) initVals).acc =
      initVals.acc + progSum P :=
    flat_acc_of_ok P hD initVals (by rw [hacc0]; exact hMpos) hok
  rw [hexact, hacc0, Nat.zero_add] at hle
  exact hle

/--
The claim, ready for any independent provider of a `Computation.Returns`
fact — the kernel for a small instance, a local runner, or an attested
remote run.  This library depends on none of them.
-/
def tdClaim (P : Params) (hP : P.Sane) (hD : 2 ≤ P.div) (hb : P.bound < M) :
    ProgramClaim (progSum P ≤ P.bound) := {
  program := tdProgram P
  wellFormed := tdProgram_wf P
  acceptingValue := 1
  sound := progSum_le_of_denote P hP hD hb
}

@[simp] theorem tdClaim_program (P : Params) (hP : P.Sane) (hD : 2 ≤ P.div)
    (hb : P.bound < M) : (tdClaim P hP hD hb).program = tdProgram P := rfl

@[simp] theorem tdClaim_acceptingValue (P : Params) (hP : P.Sane)
    (hD : 2 ≤ P.div) (hb : P.bound < M) :
    (tdClaim P hP hD hb).acceptingValue = 1 := rfl

end LeanCompCert.Ports.TrialDivisionClaim
