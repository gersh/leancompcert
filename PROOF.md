# Semantic-preservation proof

`LeanCompCert/Proof/PureSemantics.lean` contains a machine-checked Lean proof
for the current scalar, straight-line core. It proves a theorem about the
production lowering functions; it is not a claim of whole-Lean verified
compilation.

## Models

The source state maps `CCIR.LocalId` values to mathematical integers. The target
state maps emitted C identifiers to integers. `EnvRel` says that
`ABI.localName id.value` contains the value of source local `id`.

The CCIR and C models define their type widths, normalization, and binary
operators separately; `bitWidth_lowerType`, `normalize_lowerType`, and
`evalBinary_lowerType` prove that the corresponding scalar computations agree.
Division and remainder by zero evaluate to `none`. Unsupported pointer, memory,
call, floating-point, and runtime operations are outside this model.

The proved instruction fragment contains:

- scalar assignment;
- unsigned add, subtract, multiply, divide, and remainder;
- unsigned bitwise and, or, and xor;
- unsigned left and logical-right shifts.

## Theorems

The proof is layered:

1. `lowerOperand_correct` proves operand lowering.
2. `lowerBinary_unsigned_correct` proves expression lowering for every
   supported unsigned binary operation.
3. `lowerAssignment_correct` and `lowerBinary_assignment_correct` prove that
   source and target assignment steps preserve `EnvRel`.
4. `lowerStraight_is_lowerInstruction` proves that a successfully produced
   statement is exactly the statement returned by the production
   `Lower.lowerInstruction`, not a duplicate test compiler.
5. `lowerSequence_is_lowerInstructions` lifts that syntactic connection to
   arbitrary-length traces.
6. `lowerSequence_correct` proves semantic preservation for every successfully
   lowered, well-formed trace by induction over its length.

There are no proof placeholders or axioms in this proof module. `lake build`
kernel-checks all the theorems.

## Exact boundary

This closes a useful first proof obligation:

```text
straight-line scalar CCIR
        ≈
restricted generated-C computation model
```

It does not yet close these boundaries:

```text
Lean / LCNF semantics
        → full CCIR control flow, calls, and memory
        → CompCert Clight semantics
        → CompCert assembly semantics
```

In particular, the repository's C AST currently has its own restricted
executable semantics. A checked bridge to CompCert's Coq `Clight` semantics
still requires the CompCert Coq development or `clightgen` output, neither of
which is supplied by a compiler-only `ccomp` installation. Shifts also need
the usual C/Clight definedness hypotheses before this scalar model can be
identified with Clight execution.

The hybrid path that recompiles Lean's ordinary emitted C is not covered by
this proof.

`LeanCompCert.Verified.Decide` builds an axiom-free proof-by-reflection API on
top of this result. See [VERIFIED_DECIDE.md](VERIFIED_DECIDE.md).

## Check it

```console
lake build LeanCompCert.Proof.PureSemantics
```

The complete acceptance suite also builds the proof because
`LeanCompCert.lean` imports the proof module:

```console
./scripts/test-compcert.sh
```
