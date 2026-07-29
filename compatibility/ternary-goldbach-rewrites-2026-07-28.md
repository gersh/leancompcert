# Verification-friendly rewrites of the goldbach checker algorithms — 2026-07-28

Question: can the data-dependent algorithms behind the ternary-goldbach
`native_decide` certificates be rewritten in forms the proved fragment can
express (fixed-shape control flow) without losing significant performance?

Answer: **yes for every family, and in the two hottest cases the
verification-friendly form is faster than the original.** The exceptions
are precisely characterized below.

## Benchmarks

CompCert 3.17 (`ccomp -O2`), AArch64 Linux. Every pair validates by
computing identical results.

| Kernel | Data-dependent form | Fixed-shape rewrite | Ratio |
|---|---:|---:|---|
| `minFac` sweep to 10⁷ | 1.791 s (early-exit trial division) | **0.058 s (SPF sieve)** | **31× faster** |
| `minFac` per-element to 10⁶ | 0.065 s | 0.628 s (predicated trial division) | 9.7× slower, grows ~√N |
| integer sqrt, 5·10⁶ calls | 0.310 s (Newton to convergence) | **0.093 s (fixed 6 Newton steps)** | **3.3× faster** |
| gcd, 2·10⁶ pairs | 0.138 s (early-exit Euclid) | 1.044 s (192 fixed binary-gcd rounds) | 7.6× slower |
| guarded fold, 5·10⁷ steps | 0.026 s (early exit) | 0.038 s (poison flag) | 1.5× slower |

Benchmark source: `tests/benchmarks/rewrite-bench.c`;
reproducible with `ccomp -O2` alone.

## Per-family rewrites

**Factorization sweeps** (RS62 ladders, CDEM Möbius, §14.1 Mertens,
deficit products — the bulk of the integer families). Per-element
`minFac`/`Squarefree` trial division predicates badly (√N per element).
But all of these are *range sweeps*, and the smallest-prime-factor sieve
computes every `minFac`/`μ`/`φ`/`Squarefree` value in the range with a
**data-independent iteration space** (`Σ_{p ≤ √N} N/p` — every loop bound
is a function of static indices, never of computed values) — and it is
31× faster than the early-exit code it replaces. The production
`MStar140M`, `factorTable`, and `totientSieve` engines already work this
way. Cost: array state, which is the real verification requirement (see
below).

**Integer square roots** (`loop410`, `Sqrt218`, nested roots). Newton
with a fixed iteration count (6 rounds for 64-bit from a bit-length
initial guess, plus a bounded final clamp) beats the convergence loop by
3.3×. The production `Sqrt218Engine` already uses the even better
incremental form (`nextFloorSqrt`: maintain `⌊√n⌋` across the sweep at
O(1) per step, one predicated increment) — fixed-shape as-is.

**Early-exit folds** (`bandRun`, `loop410`'s `Option` aborts, ladder
guard failures). A poison/ok flag carried through a full-length fold is
semantically identical and costs 1.5× — and since the abort path only
fires when a certificate is false, the success path (the only path a
shipped certificate takes) does the same arithmetic either way.

**gcd.** Fixed-round binary gcd costs ~7.6×. But gcd only enters the
certificates through ℚ normalization, and the correct rewrite is to
**avoid gcd entirely**: the dyadic `roundOut`-at-`2^48` discipline (which
the newer CorC13/Appendix-A kernels already use) keeps all interval
arithmetic at fixed width with no normalization, turning the ℚ kernels
into machine-word/multi-word integer computations. The older
`BandIntervalExpr` path that lets ℚ denominators grow multiplicatively is
the thing to migrate, and it gains performance by doing so — unbounded
gcd on growing bignums is the single most expensive operation in the
current checkers. The few genuine gcd uses (`Nat.Coprime` in `gvSourceQ`,
66² small pairs) tolerate 7.6× trivially.

**Adaptive bisection** (`adaptiveUpper`, fuel 10–16 — the one truly
value-dependent recursion tree). Rewrite as a **witness transform**: run
the adaptive search natively and untrusted, record the resulting
partition as a literal cell list, and let the certificate check the fixed
list — per-cell kernel evaluation plus an adjacency/coverage chain, both
fixed-shape. The verified work equals the adaptive run's successful leaf
checks, so there is no slowdown; the certificate grows by the partition
literal. The repository already uses exactly this pattern
(`corC13Cells`, the FKS2 `cells_NN` tables, `chainOK`), so this is a
migration of the remaining `adaptiveUpper` call sites to an existing
in-house idiom, not a new technique.

## Monadic recursion as the verification interface

The right way to package these rewrites is **monadic combinators with
recursion, proved by induction on the recursion structure** — the
question "can we use monads and recursion and do induction on that" is
exactly the architecture:

- The reflection bridge already does this in miniature:
  `Program.denote` is a computation in the `Option` monad, its loop is
  `List.foldlM`, and the bridge theorem is an induction over the fold —
  a monadic-recursion proof.
- Each rewrite above becomes a combinator whose **denotation** is the
  natural recursive monadic function and whose **compilation** is the
  fixed-shape form, with a once-per-combinator equivalence lemma proved
  by induction on fuel (structural recursion) or on the measure
  (well-founded recursion):
  - `iterN k f` — fixed-iteration recursion (Newton, gcd rounds):
    already expressible; its denotation/compilation lemma is induction
    on `k`;
  - `foldRangeE` — early-exit fold in `Except`/`Option`: denotes the
    early-exit recursion, compiles to the poison-flag predicated fold.
    **This lemma is now proved**, generically over the state type and
    step function: `LeanCompCert/Verified/EarlyExit.lean` establishes
    soundness (`foldE_of_foldP`), completeness (`foldP_of_foldE`), and
    the acceptance characterization (`foldP_accepts_iff`, axioms:
    `propext` only) by exactly the frozen-state induction described
    here;
  - `sieve`-shaped combinators — nested folds with statically-computed
    inner bounds: the control flow is a fixed shape (compilable through
    `foldTrace` composition); the state is an array, which is the one
    genuinely new proof obligation.
- Data-dependent *recursion depth* (raw `minFac`, `muFast`) is the only
  shape where induction on the recursion does not align with a static
  compilation — and the sweep/sieve rewrite removes every production
  occurrence of it.

## Consequences for the verification roadmap

1. **General CFG simulation is not on the critical path.** With these
   rewrites, no production certificate family needs data-dependent
   branches or back-edges: fixed-trip loops (which reduce to the proved
   `foldTrace` at packaging time, and need only a simple counted-loop
   construct for rolled emission at scale) plus predication cover
   everything except adaptive bisection, which the witness transform
   removes.
2. **Arrays with static iteration spaces become the top-priority
   extension** — they unlock the sieve engines (31× over the current
   early-exit code) and the big Ramaré/CDEM tables. The required memory
   model is benign: disjoint arrays, in-bounds writes at
   statically-ranged indices, no aliasing.
3. **Dyadic fixed-point migration** of the remaining gcd-normalized ℚ
   kernels is both the verification enabler and a performance win for
   the 940 ℚ atoms.
