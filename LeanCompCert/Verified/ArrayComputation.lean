import LeanCompCert.Verified.Algorithm.ArrayBridge

/-!
# A closed, compiled *array* computation

`Verified/Decide.lean` packages a scalar `Reflect.Program` as a `Computation`
with `Computation.Returns`, and `Verified/Package.lean`'s
`Reflect.toComputation_returns` makes acceptance **equivalent** to the
program's denotation.  That equivalence is what lets a scalar artifact's
run admission be written as one line, `(…).Returns 0`.

The array machine has no such packaging, and it cannot have the same one.
`Verified/ArrayBridge.lean` records why: `AProgram.evalCC_compile` is proved
in the **defined-denotation direction only**,

```text
  p.denote = some n  →  (compiled trace).output = some (n : Int)
```

because that is the compiler-correctness direction consumed by certificates.
The typed indexed lowering no longer has the former integerized-pointer
aliasing issue, but this module does not add or assume a converse theorem.

This module supplies the array analogue of `Computation` **with that
asymmetry preserved**:

* `AComputation` bundles a well-formed `AProgram` with an admissible array
  base, and `AComputation.sourceResult` runs the compiled CCIR-with-memory
  trace and reads the output local — exactly the quantity
  `Algorithm.trace_value_unique` takes as its `hRun` hypothesis;
* `AComputation.Returns` is the one-line predicate an artifact's run
  admission asserts;
* `AComputation.value_of_returns` is the **honest run rule**: a *proved*
  denotation plus an observed run value forces the two to agree.  There is
  deliberately no `iff`.  A run of an array program **reads a proved
  denotation off; it never establishes one.**

The consequence for a certificate is a discipline, not a weakening: the
denotation must be a theorem before the run means anything at all.  Compare
`Ports/RamareWM217.lean`, whose `wmProgram_denote` is exactly that theorem.

## What the run admission trusts

`sourceResult` is the CCIR-with-memory model, not the physical machine.
`AComputation.targetResult_eq` below is `AProgram.evalC_compile` specialised
to this packaging: for any lowering of the compiled trace and any related
generated-C state, the emitted C leaves the same value in the output local.
So the *compiler* is not additionally trusted by a run admission; the C
runtime and the physical run are.

## Why the base may be fixed

`BaseOk` is the only constraint on the array's base address, and
`AProgram.evalCC_compile` holds at **every** admissible base — the denotation
does not mention the base at all.  A run admission may therefore be stated at
any convenient admissible base (`0` is one); it is not a claim about the
address the physical run happened to receive.
-/

namespace LeanCompCert.Verified.ArrayComputation

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment

/--
A closed, compiled array computation: a well-formed `AProgram` together with
an admissible base address for its single array.
-/
structure AComputation where
  /-- The program. -/
  program : AProgram
  /-- Well-formedness, so `AProgram.evalCC_compile` applies. -/
  wellFormed : program.WF
  /-- The array's base address in the model. -/
  base : Int
  /-- The array fits the `u64` address space without wrapping. -/
  baseOk : BaseOk program.arrayLen base
  /-- The name the emitter gives the compiled function. -/
  name : String

namespace AComputation

/-- Run the compiled CCIR-with-memory trace and read the output local. -/
def sourceResult (a : AComputation) : Option Int :=
  Option.bind (evalMCCSequence (a.program.initialMCC a.base) a.program.compile)
    (fun m : MCCState => m.env ⟨a.program.output + 1⟩)

/-- The one-line predicate an artifact's run admission asserts. -/
def Returns (a : AComputation) (value : Int) : Prop :=
  a.sourceResult = some value

/--
**The honest run rule.**

A *proved* denotation and an observed run value agree.  Note the direction:
`hDenote` is a hypothesis, not a conclusion — the run reads the number off a
denotation that must already be a theorem.
-/
theorem value_of_returns (a : AComputation) {n v : Nat}
    (hDenote : a.program.denote = some n)
    (hRun : a.Returns ((v : Nat) : Int)) : v = n :=
  Algorithm.trace_value_unique a.program a.wellFormed a.base a.baseOk n v
    hDenote hRun

/--
**The generated-C leg.**  `AProgram.evalC_compile` for this packaging: any
lowering of the compiled trace, run from any related C state, leaves the
denotation in the output local.  So a run admission does not additionally
trust the compiler.
-/
theorem targetResult_eq (a : AComputation) (fn : CCIR.Function)
    (statements : List C.CStmt)
    (hFrag : ∀ mi ∈ a.program.compile, mi.WellFormed fn)
    (hLower : lowerMSequence fn a.program.compile = .ok statements)
    (t : MCState) (hMRel : MRel (a.program.initialMCC a.base) t)
    (n : Nat) (hDenote : a.program.denote = some n) :
    Option.bind (evalMCSequence t statements)
        (fun t => t.env (ABI.localName (a.program.output + 1)))
      = some ((n : Nat) : Int) :=
  AProgram.evalC_compile a.program a.wellFormed a.base a.baseOk fn statements
    hFrag hLower t hMRel n hDenote

end AComputation

end LeanCompCert.Verified.ArrayComputation
