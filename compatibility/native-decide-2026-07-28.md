# `native_decide` compatibility — 2026-07-28

## Outcome

`verified_decide` now has two sound modes:

```lean
by verified_decide
by verified_decide using decision
```

The first uses `decide +kernel` with `maxRecDepth := 100000`. The second checks
a packaged computation in LeanCompCert's proved CCIR-to-restricted-C fragment
and applies its specification. Neither mode invokes native evaluation or adds a
native-decision axiom.

All pinned projects build, and the complete executable compatibility script
passes:

```console
./scripts/test-native-decide-compat.sh
```

This upgrade removes the need for all four Lean/Lake `native_decide` examples.
It also handles mathlib's closed arithmetic proposition. It deliberately does
not claim an axiom-free proof for mathlib's 17 pretty-printer snapshots:
Lean's current logical definition of the renderer is opaque.

## Pinned revisions and builds

| Project | Revision | Actual tactic sites | Build |
|---|---|---:|---:|
| Lean/Lake 4.32.1 | `f054605aea4b840552cca2e725580bffd1e1b704` | 4 | compatibility sources pass |
| mathlib4 4.32.1 | `520045ab14e26149ee970e2e617ca04b09bde5d6` | 18 | 8,654 jobs pass |
| Batteries 4.32.0 | `023ce7d62a0531e22a5331e20b587817a80d49ff` | 0 | 217 jobs pass |
| Aesop 4.32.0 | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` | 0 | 173 jobs pass |
| doc-gen4 4.32.1 | `4df39adbbe5f699a7653f526e0e6faa2d34d404e` | 0 | 194 jobs pass |

Comments, documentation, tactic declarations, and text-linter patterns are
excluded from the site count.

## Lean and Lake: 4 of 4

| Site | Replacement | Result |
|---|---|---|
| `Init.Tactics`: `(List.range 1000).length = 1000` | kernel `verified_decide` | passes, no axioms |
| `Lake.Build.Trace`: three `Hash.ofHex` cases | kernel `verified_decide` in a legacy test | passes; only `propext`, `Quot.sound` |
| `Lean.Data.Lsp.LanguageFeatures`: token types | `cases v <;> rfl` | passes |
| `Lean.Data.Lsp.LanguageFeatures`: token modifiers | `cases v <;> rfl` | passes |

The two LSP propositions call JSON stringification on each side, but after
constructor case splitting the calls are definitionally identical. Evaluating
the opaque formatter was unnecessary.

Lake's source uses Lean's new `module` system. Definitions from the module being
compiled are opaque to kernel evaluation at that point. Its check is a
non-exported sanity example, so
`compatibility/native-decide/lean-4.32.1-no-native-decide.patch` moves the
unchanged proposition to a legacy test after importing the compiled module.
There it is kernel-reducible. The patch also contains the list and LSP
replacements and passes `patch --dry-run` against the installed 4.32.1 source.

Reproducers:

- `compatibility/native-decide/LeanLakeInterop.lean`
- `compatibility/native-decide/LeanLspInterop.lean`
- `compatibility/native-decide/lean-4.32.1-no-native-decide.patch`

## mathlib: package support, one logical blocker

`compatibility/native-decide/MathlibInterop.lean` proves both:

- the closed arithmetic goal with no-argument `verified_decide`; and
- a packaged scalar CCIR computation with `verified_decide using decision`.

The occurrence in `MathlibTest/Linter/DeprecatedSyntax.lean` is intentionally
not replaced in the pinned source. That fixture exists specifically to verify
that mathlib warns about the literal `native_decide` syntax; replacing it would
delete the behavior under test. Its proposition, `1 + 1 = 2`, is supported.

The other 17 occurrences are exact `reprStr`/`Format.pretty` String snapshots
in `MathlibTest/Algebra/Polynomial.lean`. Kernel evaluation reaches:

```text
Std.Format.pretty
  → Std.Format.prettyM
  → @_private.Init.Data.Format.Basic.0.Std.Format.be
```

`be` is a private `partial def`. Its compiled implementation can run, but the
logical environment contains neither a reducible body nor an equation/specification
theorem for its result. Consequently:

- `native_decide` succeeds by trusting compiler execution;
- `decide`, `decide +kernel`, and no-argument `verified_decide` cannot reduce
  the proposition;
- no tactic-only change can construct an axiom-free proof of the exact String
  equation.

`compatibility/native-decide/MathlibOpaque.expected-failure.lean` locks in this
safety property: the matrix requires the kernel-only tactic to reject the
opaque computation and checks that the failure stops in `Std.Format`.

Resolving these 17 exact propositions requires changing the definitions, not
the tactic: refactor the pretty-printer into a total logical function and prove
it equivalent to the runtime implementation, or provide and prove a logical
specification for the partial renderer. Introducing an axiom or silently using
`native_decide` would defeat the requested assurance.

## Axiom audit

`compatibility/native-decide/TacticSyntax.lean` checks the public examples.
Observed dependencies:

| Theorem | Axioms |
|---|---|
| kernel arithmetic | none |
| `List.range 1000` | none |
| packaged CCIR source result | `propext` |
| generated-C model result | `propext`, `Classical.choice`, `Quot.sound` |
| Lake hash cases | `propext`, `Quot.sound` |

There is no native evaluation axiom in these proofs.

## Meaning of “verified”

The no-argument mode is verified by Lean's kernel but has no C connection. The
`using` mode additionally consumes the machine-checked semantic-preservation
theorem for LeanCompCert's supported CCIR fragment. It does not yet translate
an arbitrary Lean proposition, polynomial pretty-printer, String algorithm, or
recursive program into CCIR.

Thus every pinned package is build-tested and every reducible Lean/Lake site
has an axiom-free replacement. The 17 mathlib renderer propositions are
reported as unsupported rather than unsoundly “proved.”
