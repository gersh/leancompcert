# lean-compcert

`lean-compcert` is an experimental backend project for compiling Lean-generated
application code with CompCert. It includes a working Version 0.1 hybrid driver,
a compatibility reconnaissance tool, and an initial direct LCNF-to-restricted-C
path for pure fixed-width declarations.

See [IMPLEMENTATION.md](IMPLEMENTATION.md) for the implemented/deferred feature
boundary and [PROOF.md](PROOF.md) for the machine-checked scalar preservation
theorem. [VERIFIED_DECIDE.md](VERIFIED_DECIDE.md) describes the axiom-free
`verified_decide` proof-by-reflection interface built on that theorem.
Its current prominent-project substitution results are recorded in
[compatibility/native-decide-2026-07-28.md](compatibility/native-decide-2026-07-28.md).

It does **not** claim end-to-end verified compilation from Lean. When generated
C is accepted by CompCert, only the C-to-assembly portion receives CompCert's
semantic-preservation guarantee, subject to CompCert's assumptions and external
functions.

## Quick start

Requirements:

- Lean 4.30 or newer (the repository pins Lean 4.32.1);
- Python 3.11 or newer;
- CompCert's `ccomp` on `PATH`, or an explicit `--ccomp` path.

Build and differentially test a Lean executable directly from a checkout:

```console
./bin/lean-compcert build Main.lean
```

Or install the command in an isolated environment:

```console
python3 -m venv .venv
.venv/bin/pip install -e .
lean-compcert build Main.lean
```

The default output is `.lake/build/lean-compcert/<module>/`, containing:

- Lean's generated C and a mechanically normalized copy when required;
- a CompCert object and linked executable;
- a conventional reference executable used for differential testing;
- `build-manifest.json`, including exact commands and the trust boundary;
- `report.json`, a machine-readable build/provenance report;
- `report.md`, a minimized human-readable compatibility report;
- CompCert preprocessing and intermediate outputs.

The other driver commands are:

```console
./bin/lean-compcert emit-c Main.lean
./bin/lean-compcert compile-ir Main.lean
./bin/lean-compcert check-runtime
./bin/lean-compcert doctor
```

`build` compares stdout, stderr, and exit status with Lean's standard C backend
by default. Use `--no-differential-check` only when a reference run is not
wanted. Common controls include `--ccomp`, `--target`, `--profile`,
`--runtime`, `--opt-level`, `--debug-symbols`, `--reject-unsafe`, and
`--report`. Each build also writes `abi-manifest.json`; pass its
`runtimeAbiHash` back through `--expected-runtime-abi-hash` to make a later
build fail if Lean's ABI headers or the runtime shim changed.

## Compatibility probe

For low-level reconnaissance without the build-manifest wrapper:

```console
./bin/lean-compcert-probe Main.lean
```

Its default output is `.lake/build/lean-compcert-probe/<module>/`.

Useful options:

```console
lean-compcert-probe Main.lean \
  --ccomp /opt/CompCert/ccomp \
  --target x86_64-linux \
  --attempt-rewrites \
  --differential-check
```

Mechanical rewrites are made only in a separate `*.rewritten.c` copy. To compare
automatically built executables with arguments, repeat `--run-arg`. To compare
two already linked executables instead:

```console
lean-compcert-probe Main.lean \
  --reference-command "./build/Main-standard arg" \
  --candidate-command "./build/Main-compcert arg"
```

Both command options are required together. Standard output, standard error,
and exit status must all match.

The normalizer handles Lean's static flexible-array initializers for strings,
constructors, closures, object arrays, and scalar arrays. These rewrites use
fixed-size anonymous structures (or omit a zero-length tail member) while
preserving the documented Lean field order.

The driver and probe default to the hybrid runtime boundary. Their CompCert
include path
shadows `<stdatomic.h>` with a narrow ABI-preserving declaration and links
`runtime/adapters/atomics.c`, compiled by Lean's host compiler. Reports identify
this adapter, the prebuilt Lean runtime, assembler, linker, and system libraries
as outside the CompCert-compiled application boundary.

## Development

```console
lake build
python3 -m unittest discover -s tests
```

The focused semantic-preservation proof can be checked with:

```console
lake build LeanCompCert.Proof.PureSemantics
```

The verified-decision example uses:

```lean
example : computation.Returns 42 := by
  verified_decide using
    LeanCompCert.Verified.Decision.forResult computation 42
```

The probe automatically uses `lake env lean` when the input belongs to a Lake
package, allowing package imports to resolve normally.

## Backend core and current boundary

The Lean library now includes a typed CCIR, validator, interpreter, restricted
C AST, Profile 1 validator/emitter, ABI model, and pure first-order lowering.
The `lean-compcert` executable exposes a runnable integration program:

```console
lake build
.lake/build/bin/lean-compcert demo
.lake/build/bin/lean-compcert emit-demo-c .lake/build/integration/pure.c
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o .lake/build/integration/pure .lake/build/integration/pure.c
.lake/build/integration/pure
```

For compiler-API reconnaissance, importing
`LeanCompCert.CompilerAdapter.Pass` installs a Lean 4.32 impure-LCNF capture
pass. Set `LEAN_COMPCERT_LCNF_DIR` while compiling to write deterministic
per-declaration stable-view artifacts. Direct Lean compiler API usage is
isolated in `LCNF/AdapterV4_32.lean`. `lean-compcert compile-ir` automates this
capture and directly emits restricted C for the supported pure, unboxed,
fixed-width subset, then verifies every emitted translation unit by compiling
it to an object with CompCert. Boxed wrappers and closures are currently
rejected with per-declaration diagnostics.

The general `build` command currently uses Lean's ordinary C emitter followed
by narrowly defined normalization. This lets the Version 0.1 list-and-closure
acceptance program run today while keeping the manifest honest: the
LCNF-to-C normalization, Lean runtime, atomics adapter, assembler, linker, and
system libraries are outside CompCert's C-to-assembly theorem.

Run the complete local acceptance path—including real Lean LCNF capture,
stable-view lowering, CompCert compilation, native execution, the ordinary-C
probe, and both test suites—with:

```console
./scripts/test-compcert.sh
```

Compatibility results for pinned upstream Lake, Batteries, Aesop, mathlib4,
and doc-gen4 revisions are recorded in
[compatibility/prominent-projects-2026-07-28.md](compatibility/prominent-projects-2026-07-28.md).
