# Changelog

## Unreleased

- **Documentation restructured around the two use cases** — a verified
  `native_decide` (`docs/use-case-1-verified-native-decide.md`) and a
  trusted compiled artifact (`docs/use-case-2-verified-artifact.md`) —
  each stating exactly what is proved and why the method is
  trustworthy; README leads with them, tutorials remain as deep dives.
- **Consumer `check-native`**: `NativeCheck` is exported from the root
  `LeanCompCert` module, gained a repeatable `--include DIR` flag, and
  the `examples/consumer` project wires the cached native cross-check in
  five lines (`consumer check-native`).
- **`check-native`** (`lean-compcert check-native`): cached native
  cross-check pipeline. Emits every registered certificate's generated
  C, compiles it with CompCert, runs the self-checking binary, and
  caches by content hash of the generated C plus ccomp version — only
  certificates whose C actually changed are recompiled and re-run
  (`--force`, `--dir DIR`). The acceptance suite runs it twice and fails
  if the second run is not fully cached. The run remains a cross-check:
  its exit status is never admitted as a theorem.
- **Startup fix**: rolled emission (`Verified/Rolled.lean`) lowered
  against the fully unrolled `toFn` context — at 10⁷ iterations this
  materialized ~10⁸ instructions during module initialization, costing
  ~235 s on *every* CLI invocation. Lowering now uses a `loopCount := 1`
  typing context (`loweringContext`), which declares the identical
  locals; emitted C is byte-identical and startup drops to ~0.4 s.
- `lakefile.toml` version corrected to 0.2.0.
- **Stamp hardening**: `check-native` cache keys now cover the include
  configuration and the *contents* of non-toolchain header directories
  (e.g. the CompCert runtime shim), so editing a shim header or bumping
  the Lean toolchain re-runs affected certificates. Verified: failed
  compiles/runs write no stamps and exit 1.
- README consistency: the proof-boundary section now reflects the
  implemented M6 Clight bridge instead of describing it as future work;
  the versioning section says 0.2.x; use-case 1 states explicitly that a
  bug in this package cannot produce a false theorem — it can only fail
  to typecheck.

## 0.2.0 — 2026-07-28

*(2026-07-29: documentation refresh — five tutorials in `docs/`, README
restructured around the completed roadmap, all tutorial code samples
verified against the build.)*

The verified-computation package release (roadmap M1–M4 milestones and
partial M2/M3/M5/M6/M7; see ROADMAP.md for per-milestone status):

- **Scale-free packaging** (`Verified/Package.lean`): `Program.toComputation`
  with fully structural `wellFormed`/`lowered` evidence.
- **Reflection bridge** (`Verified/Reflect.lean`): register DSL with the
  structural denotation theorem `Program.evalCC_compile`.
- **Rolled loops** (`Verified/Rolled.lean`): rolled emission with the
  complete correspondence `rolledTrace_eq_augmented`.
- **Wide arithmetic** (`Verified/Limb.lean`, `Verified/SignedLimb.lean`,
  `Verified/Log2Fixed.lean`): proved add/sub/compare/multiply/divide,
  sign-magnitude integers, bounded log2.
- **Equivalence library** (`Verified/EarlyExit.lean`,
  `Verified/GcdEquiv.lean`, `Verified/SqrtEquiv.lean`,
  `Verified/Sieve.lean`): early-exit ≡ predicated folds, fixed-shape
  gcd/sqrt equal to `Nat.gcd`/`Nat.sqrt`, fixed-shape smallest-factor
  scan equal to the reference recursion.
- **Certificates** (`Testing/*Certificate.lean`): goldbach-shaped folds
  (§14.1 squarefree Mertens, 128-bit accumulation, fixed-point products),
  axiom-free, CompCert-compiled and executed.
- **CI gates**: axiom audit (no native-evaluation axioms) and clightgen
  translation validation of every certificate unit.
- **Tooling**: batch IR compilation (`scripts/compile-ir-tree.py`) —
  the whole ternary-goldbach `Math` package compiles under CompCert with
  zero rejections.

## 0.1.0 — initial public release
