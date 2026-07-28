# `verified_decide`

`LeanCompCert.Verified.Decide` provides two axiom-free proof modes.

For a closed, total, kernel-reducible proposition, use the drop-in form:

```lean
example : (List.range 1000).length = 1000 := by
  verified_decide
```

This expands to `decide +kernel` with a larger local recursion allowance. It
does not invoke native code.

For a computation packaged in the proved compiler fragment, use:

```lean
import LeanCompCert.Verified.Decide

example : computation.Returns 42 := by
  verified_decide using
    LeanCompCert.Verified.Decision.forResult computation 42
```

A complete runnable example is in
`LeanCompCert/Testing/VerifiedDecide.lean`.

## What a computation contains

`Verified.Computation` packages:

- a CCIR function and straight-line instruction trace;
- the corresponding restricted-C statements;
- a well-formedness proof;
- a proof that the statements were returned by the production lowering
  function;
- the local containing the result.

`Computation.result_preserved` proves that evaluating the generated-C model
returns exactly the result of evaluating the CCIR model.
`Computation.producedByLowerInstruction` additionally connects every statement
to the real `Lower.lowerInstruction` invocation at its source index.

`Verified.Decision p` adds an accepting result and a once-per-algorithm
specification:

```lean
computation.Returns acceptingValue ↔ p
```

After that specification is proved, each closed instance can use
`verified_decide using decision`.

## Why this does not use `native_decide`

`native_decide` obtains speed by trusting a native evaluator through a special
axiom. `verified_decide` intentionally uses Lean's kernel-checkable `decide`
on the closed CCIR result equality. The native CompCert executable may be run
as a fast independent check, but its exit status is not admitted as a theorem.

The no-argument form is a sound substitute when kernel reduction can expose
the computation. The `using` form additionally connects a supported CCIR
computation to the restricted generated-C model. Neither form can prove facts
about opaque or `partial` definitions unless those definitions provide logical
specifications.

## Run the example through CompCert

```console
lake build
.lake/build/bin/lean-compcert emit-verified-decide-c /tmp/verified-decide.c
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o /tmp/verified-decide /tmp/verified-decide.c
/tmp/verified-decide
```

The executable returns zero when the compiled computation returns 42. The full
acceptance suite performs this check automatically:

```console
./scripts/test-compcert.sh
```

## Current fragment

The computation proof currently supports straight-line scalar assignment and
unsigned fixed-width add, subtract, multiply, divide, remainder, bitwise
and/or/xor, left shift, and logical-right shift.

Branches, recursive algorithms, comparisons, arrays, heap operations, and the
formal Clight bridge remain future extensions. Until those are proved,
`verified_decide` is a foundation for verified decision procedures rather than
a drop-in replacement for every use of `native_decide`.

Real-world substitution results for Lean/Lake, mathlib, Batteries, Aesop, and
doc-gen4 are recorded in
[compatibility/native-decide-2026-07-28.md](compatibility/native-decide-2026-07-28.md).
Run their pinned compatibility matrix with:

```console
./scripts/test-native-decide-compat.sh
```
