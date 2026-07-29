# Tutorial 4 — The trust chain: what is proved, where, and by whom

This package's value is a precisely-drawn trust story. This tutorial
walks the whole chain and shows how to audit it yourself.

## The theorem side (Lean's kernel, axiom-free of native trust)

A certificate theorem like `referenceSum = expectedValue` rests on:

1. **Your `decide +kernel`** — Lean's kernel evaluates `Program.denote`
   (a plain fold) and your reference fold. Nothing else is evaluated.
2. **The reflection bridge** (`Program.evalCC_compile`,
   `toComputation_returns`) — structural theorems that the compiled CCIR
   trace computes exactly the denotation.
3. **The preservation proof** (`Proof.lowerSequence_correct` and the
   per-instruction lemmas) — the production lowering from CCIR to the
   restricted-C model preserves semantics, for every instruction shape
   in the fragment (arithmetic, comparisons, casts; memory `load`/`store`
   via `Verified.MemFragment`).
4. **Scale-free packaging** (`Program.toComputation`) — lowering success
   and fragment membership are structural facts, so no obligation grows
   with trace size.

Audit it: `#print axioms yourTheorem`. The acceptance suite's gate
(`scripts/AxiomAudit.lean`) fails CI if any certificate acquires
`ofReduceBool`, `ofReduceNat`, or `Lean.trustCompiler`. Expected sets
are `[propext]` up to `[propext, Classical.choice, Quot.sound]`.

## The artifact side (CompCert + three validation layers + Coq semantics)

The emitted C is compiled by CompCert, whose machine-checked theorem
covers C-to-assembly. Around it, the acceptance suite runs four gates:

1. **Translation validation** — `clightgen -normalize` must accept every
   certificate unit: the emitted subset is formal Clight.
2. **Structural correspondence (Python)** —
   `scripts/clight-correspond.py` requires the C and Clight sides to
   have identical ordered operator/dataflow event streams;
   mutation-tested (a single flipped operator fails).
3. **Structural correspondence (Coq kernel)** —
   `scripts/clight-correspond-coq.py` re-does the comparison *inside
   Coq*: the event extraction is a Coq `Fixpoint` over CompCert's actual
   AST, and equality is discharged by `vm` conversion at `Qed`.
4. **Direct emission + semantics** (`Verified.ClightEmit`,
   `scripts/coq/ClightFragmentSem.v`, `scripts/clight-direct-verify.py`)
   — the Clight AST is generated *directly* from the proven statement
   lists (no C printer, no clightgen parser in this path), and Coq's
   kernel proves, via a fragment evaluator shown sound against
   `ClightBigstep.exec_stmt`, that **CompCert's own bigstep semantics
   computes the certified value** — for every global environment and
   every memory (`eval_funcall function_entry2 ge m (Internal f) nil E0
   m (Vlong value)`).

## What remains trusted, stated plainly

- Lean's kernel and Coq's kernel (the two proof checkers).
- CompCert's stated assumptions: assembler, linker, hardware.
- On the classic C path: the C pretty-printer (mitigated by gates 2–3);
  on the direct path this drops out, but the direct path currently
  covers the straight-line temp-only fragment (E0 traces, unchanged
  memory) — exactly what the shipped certificates are; rolled/looped
  artifacts keep gates 1–3.
- The tie between the Lean-side and Coq-side results is the shared
  certified constant, not a single cross-prover proof.
- The native binary's exit status is **never** a theorem. That is a
  permanent design commitment: admitting it would reintroduce exactly
  the trust `native_decide` carries.

## Running the whole audit

```console
./scripts/test-compcert.sh
```

builds everything, runs the Lean test suite, compiles and executes every
certificate under CompCert, runs all four artifact gates, checks the
axiom audit, and finishes with the Python compatibility suite. Each gate
prints a one-line verdict; the suite fails on any regression.
