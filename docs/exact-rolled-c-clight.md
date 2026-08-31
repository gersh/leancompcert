# Exact rolled C to CompCert Clight

This route checks a separately emitted rolled C function without running its
long loop in either proof kernel. It covers both scalar
`Verified.Reflect.Program` and mutable-array `Verified.ArrayState.AProgram`.
Lean emits two artifacts from the same program:

- restricted C produced by `Verified.Reflect.emitRolled` or
  `Verified.ArrayState.AProgram.emitRolled`;
- a compact Coq contract produced by
  `Verified.ProgramClightEmit.emitRolledProgramContract` or
  `Verified.ArrayProgramClightEmit.emitRolledAProgramContract`.

For scalar programs, the contract contains the semantic `dsl_program` and a
count-free `emitter_source`. For array programs, those are `adsl_program` and
`array_emitter_source`, with a literal array length. Both contracts contain
structural well-formedness proofs and the relation between the binary-Z loop
limit and the semantic loop count. Their final theorems keep the denotation as
a premise. Even a trillion-iteration count is therefore represented
symbolically rather than unfolded or evaluated.

## Run the checked example

Emit both artifacts. The focused runner works even when unrelated aggregate
library targets are being developed:

```console
lake env lean --run bench/RolledFixedPointExactEmit.lean \
  /tmp/rolled-10m.c /tmp/rolled-10m-source.v
```

Then point the exact checker at the CompCert 3.17 source/build tree whose Coq
libraries and `clightgen` were built together:

```console
scripts/clight-exact-rolled.py \
  --compcert /path/to/CompCert-3.17 \
  /tmp/rolled-10m.c \
  /tmp/rolled-10m-source.v \
  /tmp/rolled-10m-check
```

`COMPCERT_DIR` may be set instead of passing `--compcert`. The checker selects
`clightgen` from that tree, probes for a compatible `coqc`, and applies a
120-second and 4-GiB address-space limit to each subprocess by default. Use
`--timeout` and `--memory-limit-gib` to change those fail-closed limits.

A successful default run kernel-checks two statements:

1. the complete function AST imported from `clightgen -normalize` is equal to
   `compile_emitted_rolled_program` applied to the Lean-emitted count-free
   source; and
2. that exact imported function preserves `dsl_denote` in CompCert's
   `ClightBigstep.eval_funcall` semantics.

The equality includes the function signature, parameters, locals and temps,
their types and order, casts, loop shape, expressions, return, and statement
sequencing. It is stronger than the older event-stream correspondence tools.
Run the built-in positive and single-operator-mutation controls with:

```console
scripts/clight-exact-rolled.py \
  --compcert /path/to/CompCert-3.17 \
  --self-test /tmp/rolled-exact-self-test
```

Use `--syntax-only` only when the exact AST equality is wanted without the
generic semantic corollary. If a contract contains more than one definition,
the selector flags shown by `--help` make every source, lemma, and C-function
choice explicit.

## Mutable AProgram route

The array route proves the same exact whole-function equality, including the
single `uint64_t *` parameter, pointer addition generated for subscripting,
`Ederef` loads, `Sassign` stores, temporary declarations, loop, and return.
It then applies `compile_array_emitted_rolled_program_correct`, which threads
real CompCert memory through each statement and returns a final memory. The
premise `flat_block_rel ... m b (8 * array_len)` says that the supplied block
is a valid zero-filled array of the required byte length; the proof also uses
the explicit no-pointer-wrap and bounds conditions in `adsl_wf`.

Run the checked load/store example with:

```console
lake env lean --run bench/ArrayExactEmit.lean \
  /tmp/array.c /tmp/array-source.v

scripts/clight-exact-array.py \
  --compcert /path/to/CompCert-3.17 \
  --proof-cache /tmp/array-generic-proof-cache \
  /tmp/array.c /tmp/array-source.v /tmp/array-check
```

For a sharded campaign, pass the same `--proof-cache` directory to every
invocation. The cache key includes the generic proof sources, Coq version,
CompCert tree, and check mode; a file lock makes parallel population safe.
Thus the relatively memory-intensive flat-memory library is checked once,
while each shard only checks its compact source contract, clightgen AST, and
exact equality theorem. The array checker defaults to a 2-GiB per-process cap;
after the cache is populated, the trillion-iteration regression passes under
a 1-GiB cap (about 572 MiB measured resident memory).

For another `p : Verified.ArrayState.AProgram`, prove the structural `p.WF`,
`p.loopCount < Verified.Reflect.M`, and `8 * p.arrayLen ≤
Verified.Reflect.M`. Emit C with `p.emitRolled` and emit the compact contract
with `Verified.ArrayProgramClightEmit.emitRolledAProgramContract`. These are
structural obligations; the contract generator never traverses the loop or
evaluates `p.denote`. Runtime division and array-index definedness are carried
by the theorem's explicit `adsl_denote source = Some w` premise.

## Use it for another program

For a `p : Verified.Reflect.Program`, prove `p.CompCertWF` and
`p.loopCount < Verified.Reflect.M`, then define both artifacts without
evaluating `p.denote` (a small `main` can write them as in
`bench/RolledFixedPointExactEmit.lean`):

```lean
open LeanCompCert

def emittedC : Except (Array String) String :=
  Verified.Reflect.emitRolled p "Project.entry"

def emittedContract : String :=
  Verified.ProgramClightEmit.emitRolledProgramContract
    "Project_entry" p hCompCertWF hCount
```

The checkers reject syntax outside their respective rolled-emitter layouts.
The array checker is the exact-C endpoint of the `AProgram`/Clight-memory
pipeline, rather than a lossy event-stream comparison.

## Trust boundary and non-claims

The Coq proof is about the exact `clightgen`-imported **function**, not an
entire executable or a record that the function was run. The remaining
boundaries are:

- Lean and Coq do not share proof terms. The first-order source serialization
  is checked as Coq data, but identifying it as the intended Lean program is a
  cross-kernel artifact-generation boundary.
- The scalar theorem assumes `dsl_denote source = Some w`; the array theorem
  assumes `adsl_denote source = Some w`. A long native or Phala run must
  supply the result/evidence separately.
- CompCert backend correctness, the chosen `main`/invocation, assembler,
  linker, platform, and hardware must be composed separately to make a claim
  about an executable run.
- A Phala receipt must bind the exact artifact digest, parameters, shard,
  nonce, output, toolchain, and attestation key before an opt-in Lean
  attestation axiom can admit that run.
- This is not a theorem about the general partial `CCIR.evalPure`; it is a
  compiler and semantic theorem for the restricted first-order instruction
  fragment serialized by `Reflect.Program`.
