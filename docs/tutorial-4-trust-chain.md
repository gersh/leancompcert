# Tutorial 4 — The trust chain: what is proved, where, and by whom

> **Vocabulary.** *Denotation* means what a program computes as ordinary
> Lean arithmetic, defined mathematically rather than by running anything;
> *reflection* means proving something by computing a `Bool` and appealing
> to a theorem that says the `Bool` being `true` implies the statement.
> [What is proved](what-is-proved.md) defines these, says what a *program*
> is and everything you can write in one, and separates what is proved from
> what is merely observed.

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
4. **Proved scalar compilation + exact semantics**
   (`Verified.ProgramClightEmit`, `scripts/coq/ClightDSLCompiler.v`,
   `scripts/coq/ClightFragmentSem.v`, `scripts/coq/ClightMemorySem.v`,
   `scripts/clight-direct-verify.py`)
   — Lean's proof-gated emitter serializes `Reflect.Program`, and the exact
   Clight AST is defined by Coq's proved `compile_program` (no C printer or
   clightgen parser in this path). `compile_program_correct` proves generically
   that the DSL denotation is preserved.  An independent fragment evaluator,
   proved sound against `ClightBigstep.exec_stmt`, checks again that
   **CompCert's own bigstep semantics computes the certified value** — for
   every global environment and
   every memory (`eval_funcall function_entry2 ge m (Internal f) nil E0
   m (Vlong value)`).  The once-and-for-all Coq endpoint also has proved
   fuelled-loop and CompCert-memory variants: a successful check of a rolled
   body, or of a pointer-parameter body with full-width dereference loads and
   stores, implies `exec_stmt` and `eval_funcall` for that same Clight AST.
   The regressions instantiate both variants with concrete Clight functions.
   Neither the scalar compiler theorem nor the fixed-point instance uses
   Lean's `native_decide`; its safety and denotation premises are kernel proved.

## What remains trusted, stated plainly

- Lean's kernel and Coq's kernel (the two proof checkers).
- CompCert's stated assumptions: assembler, linker, hardware.
- On the classic C path: the C pretty-printer (mitigated by gates 2–3);
  on the direct path this drops out.  The production direct emitter and
  per-certificate check currently cover the straight-line temp-only fragment
  (E0 traces, unchanged memory). The generic Coq theorem also covers rolled
  control flow and CompCert memory loads/stores. For production arrays,
  `Verified.ArrayRolled` proves the counter-driven trace equal to the literal
  trace used by the denotation proof; the Coq development proves the flat-array/
  CompCert-block load/store invariant, simulates every supported flat execution
  into real CompCert memory, and derives the zero-array relation from the actual
  `Init_space` global; and `scripts/clight-array-verify.py` binds the complete
  production `clightgen` AST to the generic theorem.  For the production Möbius
  array function the chain is closed: `scripts/coq/ArrayMobiusStaged.v` refines
  the fast specialized step to the exact Clight loop body, stage by stage, and
  ends in `production_end_to_end_99952` — an unconditional
  `ClightBigstep.eval_funcall` theorem for that exact AST, from
  `Genv.init_mem`, `Qed`-checked as the last step of the array gate.  Two
  things remain true on that path: the AST Coq reasons about is `clightgen`'s
  parse of the printed C, so gates 1–3 carry the printer there rather than
  removing it; and on the Lean side the value `99952` at `L = 100000` is
  corroborated by the artifact, not kernel-proved — the kernel checks the
  denotation against the trial-division reference at `L = 8, 16, 24`
  (`Testing/ArrayMobiusCertificate.lean`).
- Lean and Coq still cannot share a proof term.  On the proved scalar path,
  however, the boundary is now the serialized first-order `Reflect.Program`,
  not merely a shared result constant: Lean requires kernel-checkable
  `CompCertWF` and denotation proofs, Coq independently computes that serialized
  program, and `compile_program_correct` proves the exact generated Clight AST.
  The classic pretty-printed-C and production-array paths retain their
  separately documented parser/correspondence boundaries.
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
