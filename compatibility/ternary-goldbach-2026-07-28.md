# Ternary-Goldbach compilation run — 2026-07-28

- Date: 2026-07-28
- Host: AArch64 Linux
- CompCert: 3.17
- Project: <https://github.com/gersh/ternary-goldbach-lean>
- Revision: `700178d068c3763e8f161c9116fda41fccc074cb` (2026-07-26)
- Toolchain: Lean 4.32.0

## Outcome

Every generated C translation unit of the ternary-goldbach `Math` package —
including all 340 `Math/Problems/TernaryGoldbach` modules and every
`native_decide` certificate module — is compiled to an AArch64 object by
CompCert, with zero rejections:

| Tree | Units | Compiled unchanged | After mechanical rewrite | Rejected |
|---|---:|---:|---:|---:|
| `Math/Problems/TernaryGoldbach` | 340 | 318 | 22 | 0 |
| entire `Math` package | 2273 | 2142 | 131 | 0 |

Total CompCert compile time for the full package was about 300 CPU-seconds.

Every rewrite applied was one of the four named ABI-preserving flexible-array
materializations already established by the prominent-projects run (static
strings, constructors, closures, and object arrays); no previously unseen
construct appeared anywhere in the package:

| Rewrite (full-package counts) | Units |
|---|---:|
| materialize static constructor flexible array | 76 |
| materialize static string flexible array | 73 |
| materialize static closure flexible array | 63 |
| materialize static object-array flexible array | 2 |

The rewritten certificate-tree units include the quarantined `native_decide`
certificate modules themselves (`Certs/Ge3SquarefreeDeficitHeadPoly.c`, the
ordinary-contract certificate leaves, and the `Compact*NativeInputs` tables
that feed the large-odd certificate provider).

## Reproduction

```console
python3 scripts/compile-ir-tree.py <ternary-goldbach>/.lake/build/ir \
  --include runtime/include \
  --include "$(lean --print-prefix)/include" \
  --jobs 18 \
  --output /tmp/tg-compcert
```

The script compiles each unit directly, retries once with
`lean_compcert_probe.rewrite.mechanical_rewrite` when the unchanged source is
rejected, and writes `report.json` with per-unit status, applied rewrites,
and diagnostics.

## Boundary

These results show that the complete Lean-generated application code of the
ternary-goldbach development is within CompCert's accepted language after the
recorded mechanical normalizations. They do not by themselves constitute a
CompCert-compiled `native_decide` replay:

- the dependency closure (mathlib and the other packages) was materialized
  from build caches without generated C, so those objects remain
  conventionally compiled; regenerating their IR and mapping every module
  object into the link graph is the remaining step for a fully
  CompCert-compiled evaluator executable (the doc-gen4 mixed-link check in
  the prominent-projects run demonstrates the linking technique);
- compiling the certificate evaluators with a verified compiler shrinks the
  compiler part of `native_decide`'s trust surface but still trusts Lean's C
  emitter, the runtime, and the executable-replay step. The axiom-free
  alternative demonstrated in `LeanCompCert/Testing/` — packaging the
  certificate computation in the proved CCIR fragment and discharging it
  with `verified_decide` — removes the native trust entirely for the
  supported fragment.
