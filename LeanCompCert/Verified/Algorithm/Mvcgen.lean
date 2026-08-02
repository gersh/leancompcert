import LeanCompCert.Verified.Algorithm.Spec
import Std.Tactic.Do

/-!
# `mvcgen` support for reference algorithms

Importing this module makes Lean's `Std.Do` Hoare logic and `mvcgen` tactic
available alongside `Verified.Algorithm`.  The intended workflow is:

1. write the reference computation in ordinary monadic `do` notation;
2. prove its result/postcondition theorem with `mvcgen` and loop invariants;
3. use that theorem to discharge `Algorithm.Ensures`;
4. prove `ProgramRefinement` once for the chosen compiler/combinator.

The wrappers below normalize the two most useful kinds of reference program
to `Algorithm`.  They contain no proof automation and add no axioms; keeping
the wrappers small prevents the public API from depending on tactic internals.
-/

namespace LeanCompCert.Verified.Algorithm

/-- An `Id`-based do-program returning `Option` is already a reference
certificate algorithm. -/
def Algorithm.ofId (body : Input → Id (Option Output)) :
    Algorithm Input Output :=
  ⟨fun input => body input⟩

/-- Run a stateful reference program from its mathematical initial state and
retain only its optional certificate result. -/
def Algorithm.ofStateM (initial : Input → State)
    (body : Input → StateM State (Option Output)) : Algorithm Input Output :=
  ⟨fun input => (body input (initial input)).1⟩

@[simp] theorem Algorithm.ofId_run
    (body : Input → Id (Option Output)) (input : Input) :
    (Algorithm.ofId body).run input = body input := rfl

@[simp] theorem Algorithm.ofStateM_run
    (initial : Input → State) (body : Input → StateM State (Option Output))
    (input : Input) :
    (Algorithm.ofStateM initial body).run input =
      (body input (initial input)).1 := rfl

end LeanCompCert.Verified.Algorithm
