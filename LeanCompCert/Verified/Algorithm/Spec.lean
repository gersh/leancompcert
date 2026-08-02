import LeanCompCert.Verified.Package

/-!
# Certified algorithms

This module separates the three proofs that are easy to conflate in a large
finite certificate:

1. a reference algorithm succeeds only when the mathematical proposition is
   true (`Algorithm.Ensures`);
2. a `Reflect.Program` refines that algorithm (`ProgramRefinement`);
3. a successful compiled computation therefore proves the proposition
   (`ProgramClaim`).

No execution or attestation premise appears here.  `ProgramClaim.prove` takes
an ordinary `Computation.Returns` hypothesis.  A local runner, an attestation
package, or `gpu_prover` may supply that hypothesis without this axiom-free
library depending on any of them.
-/

namespace LeanCompCert.Verified.Algorithm

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

/-- An executable reference algorithm.  `none` means that the certificate did
not succeed; `some output` is a successful certificate result. -/
structure Algorithm (Input : Type u) (Output : Type v) where
  run : Input → Option Output

namespace Algorithm

/-- Every successful return of `algorithm` establishes `proposition input`.

This is the algorithm-to-mathematics obligation.  It is deliberately
independent of registers, CCIR, C emission, and execution evidence. -/
def Ensures (algorithm : Algorithm Input Output)
    (proposition : Input → Prop) : Prop :=
  ∀ input output, algorithm.run input = some output → proposition input

/-- A total reference computation viewed as an always-successful algorithm. -/
def ofPure (run : Input → Output) : Algorithm Input Output :=
  ⟨fun input => some (run input)⟩

/-- A Boolean checker viewed as a certificate algorithm.  It returns the
unit witness exactly when the checker accepts. -/
def ofChecker (check : Input → Bool) : Algorithm Input Unit :=
  ⟨fun input => if check input then some () else none⟩

@[simp] theorem ofPure_run (run : Input → Output) (input : Input) :
    (ofPure run).run input = some (run input) := rfl

@[simp] theorem ofChecker_run (check : Input → Bool) (input : Input) :
    (ofChecker check).run input = if check input then some () else none := rfl

/-- Prove a checker sound by proving the mathematical meaning of `true`. -/
theorem ofChecker_ensures {check : Input → Bool} {proposition : Input → Prop}
    (sound : ∀ input, check input = true → proposition input) :
    (ofChecker check).Ensures proposition := by
  intro input output hrun
  simp only [ofChecker_run] at hrun
  split at hrun
  · next h => exact sound input h
  · contradiction

/-- Strengthen or change the mathematical postcondition of an algorithm. -/
theorem Ensures.mono {algorithm : Algorithm Input Output}
    {P Q : Input → Prop} (hP : algorithm.Ensures P)
    (hPQ : ∀ input, P input → Q input) : algorithm.Ensures Q := by
  intro input output hrun
  exact hPQ input (hP input output hrun)

end Algorithm

/-- A proved one-way refinement from a register program to a reference
algorithm.

`decode` states which machine results are successful source-level outputs.
The refinement theorem is intentionally conditional on successful decoding:
a checker may return machine value `0` for rejection while `decode 0 = none`.
Only accepted results need to refine a successful algorithm run. -/
structure ProgramRefinement (algorithm : Algorithm Input Output) where
  program : Input → Program
  wellFormed : ∀ input, (program input).WF
  decode : Input → Nat → Option Output
  refines : ∀ input value output,
    (program input).denote = some value →
    decode input value = some output →
    algorithm.run input = some output

namespace ProgramRefinement

/-- A decoded successful program result is a successful reference result. -/
theorem source_succeeds (algorithm : Algorithm Input Output)
    (refinement : ProgramRefinement algorithm)
    {input : Input} {value : Nat} {output : Output}
    (returned : (refinement.program input).denote = some value)
    (decoded : refinement.decode input value = some output) :
    algorithm.run input = some output :=
  refinement.refines input value output returned decoded

end ProgramRefinement

/-- A reference algorithm, its mathematical soundness proof, and its verified
compilation/refinement packaged as one reusable object. -/
structure CertifiedAlgorithm (Input : Type u) (Output : Type v)
    (proposition : Input → Prop) where
  algorithm : Algorithm Input Output
  sound : algorithm.Ensures proposition
  compilation : ProgramRefinement algorithm

/-- A closed compiled claim: if the program returns `acceptingValue`, the
proposition follows.

Unlike `Decision`, this requires only the forward implication needed by
certificate algorithms.  `toDecision` is available when completeness is also
known. -/
structure ProgramClaim (proposition : Prop) where
  program : Program
  wellFormed : program.WF
  acceptingValue : Nat
  sound : program.denote = some acceptingValue → proposition

namespace ProgramClaim

/-- Package the claim's program into the existing proved CCIR/C computation. -/
def computation (claim : ProgramClaim proposition) (name : String) :
    Computation :=
  claim.program.toComputation name claim.wellFormed

/-- The structural bridge from computation acceptance back to the program
denotation used in `ProgramClaim.sound`. -/
theorem returns_iff (claim : ProgramClaim proposition) (name : String) :
    (claim.computation name).Returns ((claim.acceptingValue : Nat) : Int) ↔
      claim.program.denote = some claim.acceptingValue :=
  Reflect.toComputation_returns claim.program name claim.wellFormed
    claim.acceptingValue

/-- A successful run of the packaged computation proves the proposition. -/
theorem prove (claim : ProgramClaim proposition) (name : String)
    (accepted :
      (claim.computation name).Returns ((claim.acceptingValue : Nat) : Int)) :
    proposition :=
  claim.sound ((claim.returns_iff name).mp accepted)

/-- The same forward theorem starting from the proved generated-C model. -/
theorem prove_target (claim : ProgramClaim proposition) (name : String)
    (accepted :
      (claim.computation name).targetResult =
        some ((claim.acceptingValue : Nat) : Int)) : proposition :=
  claim.prove name
    ((claim.computation name).targetReturns_iff
      ((claim.acceptingValue : Nat) : Int) |>.mp accepted)

/-- Recover the older equivalence-oriented `Decision` API when the algorithm
is also complete for the claimed proposition. -/
def toDecision (claim : ProgramClaim proposition) (name : String)
    (complete : proposition →
      claim.program.denote = some claim.acceptingValue) :
    Decision proposition := {
  computation := claim.computation name
  acceptingValue := ((claim.acceptingValue : Nat) : Int)
  specification := (claim.returns_iff name).trans ⟨claim.sound, complete⟩
}

end ProgramClaim

namespace CertifiedAlgorithm

/-- Specialize a certified algorithm to one closed input and one decoded
accepting result.  The result is ready for compilation and for any independent
provider of a `Computation.Returns` fact. -/
def claim (certified : CertifiedAlgorithm Input Output proposition)
    (input : Input) (acceptingValue : Nat) (output : Output)
    (decoded :
      certified.compilation.decode input acceptingValue = some output) :
    ProgramClaim (proposition input) := {
  program := certified.compilation.program input
  wellFormed := certified.compilation.wellFormed input
  acceptingValue
  sound := by
    intro returned
    exact certified.sound input output
      (certified.compilation.refines input acceptingValue output returned decoded)
}

end CertifiedAlgorithm

end LeanCompCert.Verified.Algorithm
