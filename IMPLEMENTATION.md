# Implementation status

This repository implements the specification's initial engineering objective
with two deliberately separate pipelines.

## Executable hybrid pipeline

`lean-compcert build` asks the pinned Lean frontend to emit application C,
applies only the recorded mechanical normalizations, compiles every generated
application translation unit with CompCert, links the conventional atomics
adapter and prebuilt Lean runtime, and differentially runs the result against a
conventional Lean build.

Implemented:

- `build`, `emit-c`, `compile-ir`, `check-runtime`, and `doctor`;
- CompCert preprocessing, compilation, linking, execution, and differential
  stdout/stderr/exit-status checks;
- exact command and compiler-version provenance;
- standalone runtime ABI and build manifests;
- runtime ABI drift rejection;
- machine-readable runtime classification;
- deterministic flexible-array normalization for Lean static constructors and
  strings;
- the Version 0.1 list/closure/IO acceptance program;
- an allocation/reference-count stress workload.

Only CompCert's accepted C-to-assembly portion receives CompCert's semantic
preservation guarantee. The Lean frontend and C emitter, normalization,
runtime, adapter, assembler, linker, external libraries, operating system, and
hardware remain in the trusted boundary.

## Direct LCNF pipeline

`lean-compcert compile-ir` installs the Lean 4.32 impure-LCNF pass, converts
compiler data through the stable `LeanCompCert.LCNF` view, validates it, lowers
supported declarations to typed CCIR, validates the restricted typed C AST,
emits CompCert-compatible C, and compiles every successfully lowered
declaration to an object with `ccomp`.

Implemented directly from LCNF:

- fixed-width scalar types and literals;
- first-order functions and direct calls;
- modular arithmetic, comparisons, and shifts;
- explicit control flow and constructor cases;
- object constructors, object-field stores/projections, retain, and release;
- precise per-declaration rejection artifacts.

Currently rejected by the direct path:

- boxed `Nat`/`Int` and erased/tagged wrapper operations;
- closure allocation, partial application, and indirect calls;
- scalar constructor-field layouts and destructive reset/reuse;
- join points requiring block-parameter/phi lowering;
- full IO and module initialization.

The hybrid pipeline is therefore the usable Version 0.1 executable path. The
direct LCNF path is the architecture for replacing ordinary Lean C emission as
the supported subset expands.

## Machine-checked proof

`LeanCompCert/Proof/PureSemantics.lean` now proves semantic preservation for
arbitrary-length straight-line traces containing scalar assignments and ten
unsigned fixed-width binary operations. The proof uses an executable
computation model for the restricted C AST, relates source locals to their
actual emitted C names, and connects each target statement to the production
`Lower.lowerInstruction` function. It contains no proof placeholders.

This is a deliberately bounded theorem, not an end-to-end result. It does not
yet cover LCNF-to-CCIR lowering, branches/loops, function calls, heap/runtime
operations, or a correspondence with CompCert's Coq Clight semantics. See
[PROOF.md](PROOF.md) for the theorem chain and exact boundary.

## Deferred research milestones

The specification explicitly makes end-to-end verification, a complete
CompCert-built runtime, strict standalone builds, and direct Clight emission
later milestones. None is claimed here. In particular, the new scalar theorem
does not constitute a machine-checked semantic-preservation proof from LCNF or
full CCIR to Clight.

Run all implemented acceptance checks with:

```console
./scripts/test-compcert.sh
```
