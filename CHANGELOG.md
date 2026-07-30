# Changelog

## Unreleased

- **The reduced cite families, computed** — the one-shot `[0, L)` Möbius
  sieve of `Ports/ArrayMobius.lean` needs the whole range resident, so `10¹²`
  would be 24 TB.  `Ports/ArraySegSieve.lean` is its offset, multi-window
  successor: cell `i` stands for `lo + s·L + i`, one `AProgram` walks
  `segCount` windows, and memory stays `3L` cells however long the walk.  The
  first multiple of `p` inside a window is one `urem` when the prime cursor
  advances; the accumulation phase zeroes the two cells it has just read, so
  no clear pass is needed and the bridge's zero-filled initial memory is
  exactly the state every window wants.  Measured at `lo = 10¹⁰`: `16.6 MB`
  resident against `1.56 GB` for the one-shot form, at a 4% cost.
  - Two residue blocks ride on the sieve.  `mertensResidue` carries
    `M(n) = Σ μ(m)`, `Q(n) = Σ |μ(m)|` and the CDEM fixed-point discrepancy
    `G(n) = Q(n)·2³⁶ − ⌊(6/π²)·2³⁶⌋·n` with their running extrema — the
    residues of `mertensM_hurst_sqrt` and of the CDEM reproducible squarefree
    head, on **one** pass.  `mobiusOverNResidue` carries
    `T(n) = Σ μ(m)·round(2⁶²/m)` — the residue of Platt's (2.11) and of
    Platt's stronger rigorously-computed range.
  - Every real-valued majorant is compared once per artifact, in the
    epilogue, against an exact integer threshold computed in Lean: `Nat.sqrt`
    of a rational cross-multiplication, and a Machin computation of `π` in
    integer arithmetic for `⌊(6/π²)·2³⁶⌋ = 41 776 432 333`.  No `√` and no
    `π` appears in the artifact; the loop body only adds and compares machine
    words.
  - `segProgram_wf` proves well-formedness at every `(lo, L, segCount)` and
    either residue — by a `Bool` mirror that reduces definitionally, so the
    proof is `rfl` and does not grow with the 146-instruction body.
    `mertensProgram_compiled` / `mobiusProgram_compiled` instantiate
    `AProgram.evalCC_compile`.  Base trio.
  - Corroboration: kernel evaluation against trial division at `[1, 24]`;
    slot-for-slot agreement with `bench/ref_seg.c` at `10⁸`, where
    `M(10⁸) = 1928` and `Q(10⁸) = 60 792 694`, and at `lo = 10¹⁰`;
    `bench/seg_chain.sh` walking a geometric window schedule with zero
    violations for all four families over the initial stretch.  Registered as
    the `mobius-seg` native certificate.
  - Cost, and what is still out of reach, in
    `bench/results/array_seg_folds.md`: `68 ns` per integer under CompCert,
    so `7.7·10⁹` is 8.6 minutes, `10¹²` is 19.7 hours and `10¹⁶` is 25
    core-years (embarrassingly parallel, with no serial carry dependency).
    Two of the six reduced families — `ch25_lemma_9_2_psi` and
    `ramare_zuniga_lemma_6_2` — are **not** integer folds: their summands are
    logarithms of primes, and they are not implemented.  Emission, not
    execution, is what currently caps `hi` at about `10¹⁰`.

- **Verified multi-precision modular arithmetic** — the binding
  obstruction across the ternary-Goldbach corpus is gone.  The fragment's
  only division is `udiv`/`urem` at 64 ÷ 64 → 64, so `x·y mod N` for a
  ~90-bit `N` (a 128 ÷ 64 division) was inexpressible.  Montgomery
  reduction needs **no division at all**:
  - `Verified/Montgomery.lean` — the algebra over `Nat`: exactness of the
    Montgomery shift (`redcStep_mul`, the reduction-side analogue of
    `MulWide.hl_spec`), `montMul_spec`, cancellation of `Bˢ` modulo an odd
    modulus, square-and-multiply in the Montgomery domain, and the
    end-to-end `montExp_spec : montExp … = a ^ e % N`.
  - `Verified/Mont2.lean` — its two-limb realization in the fragment's own
    instruction set (`montMul2_val`), plus division-free entry into the
    domain by doubling (`dblIter_val`).  Every machine form is `+`, `-`,
    `*`, `&`, `<<`, `>>` and the proved `<`; the emitted C contains zero
    divisions.
  - `Verified/InstrBlock.lean`, `Verified/Straight.lean` — total
    straight-line block layers, so a 30 000-instruction body is reasoned
    about by composition, never by unfolding.
  - `Ports/TGProth.lean`, `Testing/ProthCertificate.lean` — stage (b) of
    the Helfgott–Platt Goldbach ladder, previously recorded as **not
    expressible** and 75.1 % of the reference producer's cost.  The
    emitted artifact is 33 KB of C, 3 744 bytes linked, branchless, and
    costs **2.25× GMP's `mpz_powm`** (1.57× with gcc) on the same 91-bit
    modulus.  `prothProgram_denote` proves the artifact's denotation is `0`
    exactly when `a^((N−1)/2) mod N = N − 1`.  Registered as the `proth`
    native certificate.  See `bench/results/tg_proth.md`.
- **Freestanding artifact emission**: emitted artifacts no longer link
  glibc.  A CompCert object for an emitted artifact has zero undefined
  symbols; the dependency was entirely gcc's startup glue.  `ccomp -c` +
  a checked-in `_start` (`runtime/start/`) + `ld` gives a static binary
  with zero undefined dynamic symbols, 70 504 → 1 472 bytes for
  `rolled-10m`.  `check-native` links this way by default (`--hosted`
  restores the old path), and its exit-code classification now
  distinguishes a value disagreement (exit 1, the only such status) from
  abnormal termination (128 + signal), which is never reported as a
  disagreement.  The spurious `#include <lean/lean.h>` is gone.

- **Verification-gate hardening** (audit follow-up):
  - `check-runtime` now fails with status `runtime-missing` when no
    runtime C sources are found, instead of reporting `compatible`
    having checked nothing; `runtime_hash` raises when the project's
    runtime ABI inputs are absent instead of hashing `<missing>`
    placeholders (both were reachable from a non-editable pip install,
    which does not ship `runtime/`).
  - `lean-compcert-probe` exits 3 (not 0) on `probe-incomplete`, so a
    missing `ccomp` can no longer look like success to a caller gating
    on the exit code.
  - The acceptance suite's axiom gate is now an allowlist: any axiom
    outside `propext`/`Classical.choice`/`Quot.sound` — including
    `sorryAx` and bespoke axioms, not just the native-evaluation axioms
    — fails the build. `Computation.result_preserved` joined the audit
    list.
- **Correspondence checkers compare calls in full**: both
  `clight-correspond.py` and the Coq-kernel checker
  (`clight-correspond-coq.py`, `ECall` now carries the destination and
  argument descriptors) compare a call's result destination and every
  argument, not just the callee name; the Coq self-test's mini
  certificate exercises a call, and its negative control must fail at
  the lemma stage (an infrastructure failure no longer counts as a
  rejected mutant). Leading-underscore identifier conflation
  (`lstrip` → `removeprefix`) fixed; function-pointer callees are
  parse errors.
- **`clight-direct-verify.py`** caches `.vo` files keyed on content plus
  the exact `coqc` and CompCert flags (switching toolchains no longer
  reuses a stale cache), and honors `COMPCERT_DIR`/`COQC`; the
  acceptance suite's Coq gates honor `COMPCERT_DIR` instead of a
  hardcoded path.
- **Normalizer**: removing an empty flexible-array member that is not
  the last initializer field no longer leaves a stray comma.
- **Python packaging**: version aligned to 0.2.0 (build manifests
  previously recorded a stale 0.1.0 `backendVersion`).
- Minor robustness: `_CoqProject` token-scan off-by-one, empty
  `-version` output guards, `run_command` no longer treats an explicit
  empty environment as "inherit"; ROADMAP's stale "Sequencing and
  effort" section rewritten to match the implemented milestones.

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
