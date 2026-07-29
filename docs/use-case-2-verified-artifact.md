# Use case 2 — A compiled artifact you can trust

**You are here because:** you want an actual native binary — to ship, to
schedule, to run at full machine speed — and you want a machine-checked
account of what it computes, not "the compiler seemed to work".

This guide is the end-to-end recipe. The deep dives it links to:
[Tutorial 4](tutorial-4-trust-chain.md) (the full trust chain and how to
audit it), [Tutorial 5](tutorial-5-loops-and-scale.md) (rolled loops,
arrays, large artifacts).

## What is proved, exactly

Three machine-checked layers meet at the artifact:

1. **In Lean's kernel:** your certificate theorem
   (`referenceSum = expectedValue`, standard axioms only — see use case
   1), plus the structural chain `Program.evalCC_compile` →
   `toComputation_returns` → `lowerSequence_correct` carrying that value
   through the compiled CCIR trace to the restricted-C model:
   `computation.targetResult = some expectedValue`. That last theorem is
   about the *C statements the emitter will print* — their formal
   semantics computes your value.
2. **In Coq's kernel:** for the direct-emission path, CompCert's own
   bigstep semantics computes the certified value —
   `eval_funcall ge m (Internal f) nil E0 m (Vlong value)` for **every**
   global environment and **every** memory (proved via a fragment
   evaluator shown sound against `ClightBigstep.exec_stmt`; see
   `scripts/coq/ClightFragmentSem.v`).
3. **CompCert's theorem** (machine-checked in Coq, independent of this
   package): the assembly it generates preserves the semantics of the
   Clight program. Composed with layer 2: the machine code computes your
   certified value, up to CompCert's stated assumptions.

**The honest boundary.** On the classic path (pretty-printed C fed to
`ccomp`), the C printer sits between layers 1 and 3. It is *validated*,
not proved: `clightgen -normalize` must accept every unit (the emitted
subset is formal Clight), a structural correspondence checker requires
identical ordered operator/dataflow event streams between the C and its
Clight translation (mutation-tested — one flipped operator fails), and
the same comparison is re-done inside Coq with the equality discharged
at `Qed`. On the direct path the printer drops out entirely — the Clight
AST is generated straight from the proven statement lists — currently
for the straight-line fragment. This package never claims verified
compilation of general Lean code; the claim is scoped to certificates
authored in the fragment, and that scope is exactly what the gates
check.

## Step by step

**1. Author and certify** the computation as in use case 1 (steps 1–2):
a `Program`, `Program.toComputation`, a kernel-checked certificate.

**2. Emit the C translation unit.** The stable entry point:

```lean
def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[computation.fn] }
  pure (source ++ mainC)   -- mainC: your `int main` wrapper
```

Write it to a file from your `Main` (see `examples/consumer/Main.lean`),
or model it on the CLI's `emit-*-c` commands.

**3. Compile with CompCert:**

```console
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o artifact artifact.c
```

**4. For big loops, emit rolled.** A 10⁷-iteration fold would unroll to
gigabytes of C; `emitRolled` compiles the body once into a single
`while` loop — a 2 KB artifact — and `rolledTrace_eq_augmented` proves
the rolled form's semantics equals the standard unrolled semantics, so
every theorem from step 1 still applies (Tutorial 5).

**5. Run the verification gates** over your artifact the way the
acceptance suite does — `clightgen` acceptance, then the two
correspondence checkers:

```console
clightgen -normalize artifact.c && test -s artifact.v
python3 scripts/clight-correspond.py artifact.c artifact.v
python3 scripts/clight-correspond-coq.py artifact.c artifact.v workdir/
```

For straight-line certificates, the direct path additionally proves the
CompCert-semantics theorem itself
(`scripts/clight-direct-verify.py`, driven by a Clight AST emitted from
the proven statements — see the `emit-clight-fixedpoint-v` command for
the working model).

## Why you should trust this method

- Each layer is checked by a proof **kernel** (Lean's or Coq's), not by
  a test suite: what the C model computes (Lean), what CompCert's
  semantics assigns to the artifact (Coq), and what the generated
  assembly does (CompCert's own theorem, in Coq).
- The one unproved step — the C printer, on the classic path — is
  fenced by three independent validators, one of which re-checks the
  correspondence inside Coq's kernel, and is eliminated outright on the
  direct path.
- The claims are *scoped and enforced*: the axiom audit fails CI on any
  native-evaluation axiom, and the acceptance suite
  (`./scripts/test-compcert.sh`) runs every gate on every certificate,
  so the trust story you read here is re-established mechanically on
  each run.

What you are still trusting: the two proof kernels, and CompCert's
stated assumptions (assembler, linker, hardware) — the same residual
base as any CompCert-compiled, Coq-verified development.
