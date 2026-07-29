# Use case 1 — A verified `native_decide`

**You are here because:** you have a finite computation standing in for a
proof obligation, `native_decide` is not trusted enough for your setting,
and plain `decide` is too slow at your problem size.

This guide is the end-to-end recipe. The deep dives it links to:
[Tutorial 1](tutorial-1-first-certificate.md) (a complete worked
certificate), [Tutorial 3](tutorial-3-replacing-native-decide.md)
(migrating real recursive code, kernel-scale discipline).

## What is proved, exactly

At the end of this recipe you hold a Lean theorem of the form

```lean
theorem certificate : referenceSum = expectedValue
```

where `referenceSum` is *your* Lean function (a fold, a recursion — your
statement, unchanged) and the proof is checked by **Lean's kernel and
nothing else**. Audit it yourself:

```lean
#print axioms certificate
-- [propext, Classical.choice, Quot.sound]  — the standard axioms only
```

Compare `native_decide`: its proofs carry `Lean.ofReduceBool`, an axiom
saying "whatever the compiled native evaluator printed is true" — which
silently extends your trusted base to Lean's compiler, a C compiler, the
Lean runtime, and every `@[implemented_by]` in scope. The certificate
above carries none of that: if Lean's kernel is sound, the theorem is
true. That is the entire trust story on the theorem side, and it is why
this method is trustworthy — the fast native machinery below is
*never* part of the proof. The acceptance suite even enforces this
mechanically (`scripts/AxiomAudit.lean` fails CI if any certificate
acquires a native-evaluation axiom).

## How the speed problem is solved

The kernel cannot brute-force a 10⁸-step computation the way native code
can, so the package splits `native_decide`'s two jobs:

1. **The proof** runs in the kernel, made feasible by structure: the
   computation is authored as a bounded register `Program`, the kernel
   evaluates only its `denote` fold (plus your reference function), big
   folds are **chunked** into kernel-sized segments combined by proved
   lemmas, and data-dependent recursion enters through once-per-algorithm
   equivalence lemmas (see Tutorial 3). This is a one-time cost per
   certificate, and Lake caches it: the proof is re-checked only when
   the certificate file actually changes.
2. **The native runs** — for finding the constant while you develop, and
   for cross-checking continuously — use CompCert-compiled binaries via
   `check-native`, cached so that nothing re-runs unless the code
   actually changed (next section).

## Step by step

**1. Author the computation as a `Program`** (`Verified.Reflect`): an
`init` block, a `body` run once per loop index, an `epilogue`, `u64`
registers. The `expr!` macro (`Verified.Frontend`) compiles arithmetic
expressions to instruction sequences with a proved correctness theorem.
Tutorial 1 walks a complete example in ~40 lines.

**2. State and prove the certificate.** `Program.toComputation` packages
the program with structural well-formedness and lowering evidence — no
proof obligation grows with problem size. The certificate is discharged
by `decide +kernel` on the denotation (via the `verified_decide` tactic
or `Decision.prove`). At production scale, follow the chunking
discipline (Tutorial 3): a monolithic 150,000-element fold was measured
to crash the kernel; a few thousand elements per chunk is comfortable.

**3. Get fast native runs that don't repeat themselves.** Register your
certificates and expose the cached runner — five lines in your own
project's `Main`:

```lean
import LeanCompCert.NativeCheck
open LeanCompCert

def nativeCerts : List NativeCheck.Cert := [⟨"demo", MyProject.emittedC⟩]

def main (args : List String) : IO UInt32 :=
  NativeCheck.run nativeCerts args
```

Then:

```console
$ lake exe myproject check-native
[run] demo: compiled with CompCert, native check passed
$ lake exe myproject check-native      # recompile, edit other files, rerun…
[cached] demo: C unchanged since last passing run
```

Each certificate's generated C has a self-checking `main` (exit 0 exactly
when the computed value equals the certified constant). The runner
compiles it with `ccomp`, runs it, and stamps the result keyed by the
**content hash of the generated C** plus the ccomp version. Rebuilding
your project, editing unrelated files, or re-running the command does
not re-execute anything; only a certificate whose generated C actually
changed is recompiled and re-run. Stamps are written only on passing
runs, so failures always retry. (`--force` re-runs everything; `--dir`
relocates the cache; `--include` adds C include paths.)

The working external-project version of all of this is
[examples/consumer/](../examples/consumer/) — an ordinary Lake project
whose `consumer check-native` does exactly the above.

## Why you should trust this method

- **The theorem's trusted base is Lean's kernel, full stop.** Every
  helper along the way — the reflection bridge (`Program.evalCC_compile`),
  the packaging (`toComputation_returns`), the equivalence library — is
  itself a kernel-checked theorem, not a tool you have to believe. Put
  bluntly: **you do not have to trust this package's authors at all.** A
  bug in our lemmas or tactics cannot produce a false theorem — it can
  only fail to typecheck. The worst this package can do is not compile.
- **Nothing fast is trusted.** The CompCert binary's exit status is
  never admitted as a theorem — a permanent design commitment, enforced
  by the axiom-audit CI gate. If the native cross-check and the kernel
  ever disagreed, the kernel wins and the discrepancy is a bug report,
  not a soundness incident.
- **The cross-check is itself high-assurance.** The binary is compiled
  by CompCert, whose C-to-assembly correctness theorem is machine-checked
  in Coq — so a disagreement genuinely means something is wrong, rather
  than "gcc did something".
- **You can audit everything locally**: `#print axioms` on your
  certificate, and `./scripts/test-compcert.sh` for the package's own
  gates.

What you are still trusting: Lean's kernel (as with *any* Lean proof),
and — for the cross-check binary only, never the theorem — CompCert's
stated assumptions (assembler, linker, hardware).
