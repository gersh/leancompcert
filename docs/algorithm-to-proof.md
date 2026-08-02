# From an algorithm to a mathematical proof

`LeanCompCert.Verified.Algorithm` packages the reusable proof architecture for
certificate algorithms.  Use it when the proposition is not conveniently
proved by directly evaluating `Program.denote`, but you can prove that a
normal reference algorithm is sound and that the fixed-shape register program
refines it.

The boundary is:

```text
reference algorithm succeeds
  -> mathematical proposition                 Algorithm.Ensures

compiled Program returns a decodable result
  -> reference algorithm succeeds             ProgramRefinement

compiled Computation returns the accepted value
  -> mathematical proposition                 ProgramClaim.prove
```

All three arrows are Lean theorems.  None asserts that a physical execution
happened.

## 1. Write a reference certificate algorithm

An `Algorithm Input Output` returns `Option Output`.  `none` is rejection or
failure; `some output` is successful certification.  Its mathematical
obligation is:

```lean
algorithm.Ensures proposition
-- forall input output,
--   algorithm.run input = some output -> proposition input
```

For a Boolean checker, `Algorithm.ofChecker` makes `true` return the unit
witness and `false` return `none`.  `Algorithm.ofChecker_ensures` reduces
soundness to the familiar theorem

```lean
forall input, check input = true -> proposition input
```

This implication, rather than an equivalence, is intentional.  A certificate
only needs to show that acceptance cannot lie.  If completeness is available,
`ProgramClaim.toDecision` recovers the older equivalence-oriented `Decision`
API.

## 2. Use `mvcgen` for the algorithm proof

Import:

```lean
import LeanCompCert.Verified.Algorithm.Mvcgen
```

This imports Lean Std's `Std.Do` Hoare logic and `mvcgen`; it does not add a
Mathlib dependency.  Write the reference algorithm in ordinary monadic `do`
notation, then supply loop invariants to `mvcgen`.  A typical invariant relates
the mutable accumulator to the mathematical fold over the consumed prefix:

```lean
open Std.Do

theorem run_eq_fold (input : Input) : run input = referenceFold input := by
  generalize h : run input = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨cursor, acc⟩ =>
      ⌜acc = cursor.prefix.foldl mathematicalStep initial⌝
  all_goals simp_all [List.foldl_append]
```

`mvcgen` helps with the source-level loop and state invariants.  It does not
prove that a `Reflect.Program` implements the algorithm.  That is the next,
separate proof.

## 3. Prove the compiled refinement

`ProgramRefinement algorithm` contains:

- an input-indexed, closed `Reflect.Program`;
- its structural `Program.WF` proof;
- a decoder from machine result words to source-level outputs;
- a theorem saying any successfully decoded result is a successful result of
  the reference algorithm.

Use the existing compiler-correctness combinators to prove that theorem:

- `FoldBridge` for counted folds and observations of register state;
- `EarlyExit` for poison-flag implementations of early return;
- `Straight` and `Frontend` for expression and straight-line blocks;
- `Segment` and `ListFold` for shards, guards, and tables;
- `Verified/Algorithm/ArrayBridge.lean` for array programs.

Array programs are a different machine (`AProgram`, over `AState`) with their
own refinement structure, `AProgramRefinement`, and their own claim,
`AProgramClaim`.  Three modules carry an array port:

- `Verified/ArrayState.lean` and `Verified/ArrayBridge.lean` — the array
  machine and its compiler bridge into CCIR and generated C;
- `Verified/ArrayFoldBridge.lean` — the reasoning bridge, the array analogue
  of `FoldBridge`, turning `AProgram.denote` into a `List.foldl`.  Its
  body-simulation hypothesis is restricted to `index < loopCount`, which is
  load-bearing: a body that decodes a divisor from the loop index is
  genuinely undefined at an adversarial index;
- `Verified/Algorithm/ArrayBridge.lean` — the refinement bridge.  `ArrayLoop`
  bundles the simulation obligations; `AProgramRefinement.ofArrayLoopOn` and
  `ofDenotationOn` produce the refinement.

One asymmetry is deliberate and is not hidden.  The array compiler bridge is
one-way — `p.denote = some n → (trace).output = some n`, not the converse,
because `u64` address arithmetic is not injective over the whole register
range.  So `AProgramClaim` carries **no** `Computation.Returns` iff.  A run of
an array artifact reads a *proved* denotation off (`trace_value_unique`); it
never establishes one.

`AProgramRefinement.ofDenotationOn` takes the arithmetic side conditions of
the denotation as an explicit `Admissible` predicate and requires the decoder
to reject inadmissible inputs, so audit item 2 below covers them too.

`CertifiedAlgorithm` packages the reference soundness and compiled refinement.
Specializing it to an input, accepted machine value, and decoded output with
`certified.claim` produces a `ProgramClaim`.

The complete executable example is
[`LeanCompCert/Testing/AlgorithmProof.lean`](../LeanCompCert/Testing/AlgorithmProof.lean).
It contains a mutable modular-sum loop proved by `mvcgen`, a fixed-shape
register program proved with `FoldBridge`, and the final compiled claim.

## 4. Keep execution evidence outside this library

`ProgramClaim.prove` accepts a `Computation.Returns` hypothesis.  It neither
creates nor admits one.  This makes the execution provider replaceable:

- the kernel may establish the result for a small computation;
- a local workflow may opt into its own named admission;
- `gpu_prover` may verify remote/GPU evidence and expose its own explicitly
  named run-admission axiom.

For an attested run, `gpu_prover` should discharge the existing abstract
`RunAdmission` boundary.  LeanCompCert's axiom-free `returns_of_receipt`
theorem then produces `Computation.Returns`; pass that result to
`ProgramClaim.prove`.  The algorithm library therefore has no dependency on
receipt formats, cryptography, networks, TEEs, or GPUs.

## Audit checklist

For each new algorithm, check:

1. `Algorithm.Ensures` states the intended mathematical proposition.
2. `ProgramRefinement.decode` rejects every non-accepting machine result.
3. The refinement proof is structural, not a large `decide` evaluation.
4. `Program.WF` is proved for every input in the family.
5. `#print axioms` on the final theorem contains no native-evaluation axiom.
6. Any physical-run admission comes from the intended external provider and
   is visible by name in `#print axioms`.
