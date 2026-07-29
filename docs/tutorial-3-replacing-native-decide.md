# Tutorial 3 — Replacing `native_decide`: the equivalence architecture

`native_decide` proves finite facts by trusting Lean's compiler, a C
compiler, and the runtime. This package replaces that trust with kernel
checking — but naive `decide` fails at production scale. The working
architecture has three layers, and understanding it is the key to
migrating real certificate suites (the ternary-goldbach development's
1,371 atoms are the reference workload; see `compatibility/`).

## The three layers

```text
reference function          -- your natural recursion (early exits,
   ↕  equivalence lemma     --  gcd, sqrt, minFac … all fine here)
fixed-shape function        -- predicated / fuel-guarded / sieve form
   ↕  Program.denote (defeq by construction)
Program                     -- compiled, packaged, CompCert-checked
```

Data-dependent recursion is only a problem for *compilation*. On the
pure Lean side, ordinary induction proves the reference recursion equal
to a fixed-shape form — once per algorithm — and the kernel then
evaluates whichever side is cheaper. Nothing about your original
statements changes.

## The proved equivalence library

| Shape | Module | Main theorem |
|---|---|---|
| Early-exit fold ≡ poison-flag fold | `Verified.EarlyExit` | `foldP_accepts_iff` |
| Euclid gcd ≡ fixed-round guarded gcd | `Verified.GcdEquiv` | `gcdFuel_eq` (+ `gcdFuel_u64`) |
| `Nat.sqrt` ≡ fixed Newton + clamp | `Verified.SqrtEquiv` | `isqrt_eq` |
| Least factor ≡ fixed-shape scan | `Verified.Sieve` | `spfFixed_eq_leastFactor` |
| Per-cell sieve sweep (array form) | `Verified.ArrayState` | `sieveSweep_cell` |

Use them as templates: each is an induction on the recursion structure
(fuel, measure, or range) with a frozen-state or least-hit invariant.
For the early-exit case the direction you usually need is one-sided —
certificates are implications, so soundness of the fixed form suffices.

## Worked pattern: an early-exit ladder

The goldbach `bandRun`-style loops abort when an accumulator leaves its
band. Migration recipe:

1. State the reference as `foldE step init indices` (`Verified.EarlyExit`).
2. The fixed form is `foldP step (init, true) indices` — the flag
   freezes the state after a failure. `foldP_accepts_iff` says the
   predicated run accepts iff the early-exit run succeeds.
3. Realize `foldP` in a `Program` body: the flag is a register; each
   guarded update is a comparison mask (`ok := ok &&& stillInBand`).
   On a *successful* run the masks never fire, so the native check does
   the same arithmetic either way (~1.5× overhead measured).
4. Certify as in Tutorial 1; the `Decision.specification` chains
   `toComputation_returns` with your equivalence lemma.

## Kernel-scale discipline (important)

Monolithic full-height folds can exhaust the kernel outright — a
150,000-element production Mertens pipeline was measured to crash
`decide +kernel` (stack overflow at 25 GB). The cure is **chunking**:
state the certificate as partial sums over segments small enough for the
kernel (a few thousand elements each), certify each chunk, and combine
with a proved (evaluation-free) addition lemma. This mirrors the
sharding the goldbach development already uses. Also set
`set_option maxRecDepth 800000` in certificate files.

## What the benchmarks say about fixed-shape costs

Measured with CompCert-compiled binaries
(`compatibility/ternary-goldbach-rewrites-2026-07-28.md`,
`tests/benchmarks/rewrite-bench.c`): smallest-prime-factor **sieves beat
early-exit trial division 31×** (prefer the array form over per-element
predication, which loses ~√N); fixed-iteration Newton sqrt is 3.3×
*faster* than the convergence loop; poison-flag folds cost 1.5×; avoid
gcd entirely by working in dyadic fixed-point (`Verified.Dyadic`) rather
than normalized rationals.

## Where Mathlib-dependent equivalences live

This package is Mathlib-free by design. Lemmas relating *Mathlib*
functions (`Nat.minFac`, `Nat.totient`, `Squarefree`) to the package's
reference functions belong in the consumer project, in the goldbach
development's "proven in the consumer" style — the package exposes the
denotations they target (e.g. `Sieve.leastFactor`).
