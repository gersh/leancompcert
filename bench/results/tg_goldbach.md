# The Helfgott–Platt Goldbach prime ladder in the proved fragment

Target: `tg_goldbach_ladder_native.cpp` (532 lines, arXiv:1305.3062v2
§§2–4), the native producer of the ternary-Goldbach prime ladder.  It
sieves the progression `k · 2⁵² + 1` by every prime below `16000`, applies
the paper's ordered small-witness Proth test with GMP, and writes a
delta-encoded rung stream.

Everything below is measured on this box (aarch64, 20 cores, shared).
**CPU (user) time throughout** — wall time on this machine is inflated by a
load average near 50.

## Verdict by stage

| stage | expressible in the proved `u64` fragment | share of reference cost |
|---|---|---|
| (a) progression sieve | **yes, as a different algorithm** — same predicate, trial division instead of block sieving | 22.6 % |
| (b) Proth test | ~~**no**~~ → **yes** — the obstruction below was removed; see `tg_proth.md` | 75.1 % |
| (c) ladder assembly | **yes, exactly** — and the whole gap condition turns out to be a `u64` bound on the delta stream already on the wire | 2.4 % |

The stage that does not port is the one that costs three quarters of the
run.  Ported stages (a) and (c) together account for 25 % of the reference.

## The reference, recalibrated

`bench/results/tg_reference.csv`, from an instrumented private copy of the
producer (timers around `makeBlock` and `ProthTester::test`; the reference
tree itself is untouched).

| range | user s | records | candidates sieved | Proth tests | sieve s | Proth s |
|---|---|---|---|---|---|---|
| 4·10²² | 0.07 | 10 276 | 16 777 216 | 30 768 | 0.038 | 0.037 |
| 4·10²³ | 0.56 | 102 866 | 100 663 296 | 318 674 | 0.183 | 0.393 |
| 4·10²⁴ | 5.72 | 1 030 123 | 889 192 448 | 3 332 528 | 1.342 | 4.284 |
| 4·10²⁵ | 62.51 | 10 314 483 | 8 891 924 480 | 34 717 454 | 14.099 | 46.933 |

Unit costs: **1.59 ns per sieved candidate**, **1.35 µs per Proth test**.

Marginal rate over 4·10²⁴ → 4·10²⁵: **6.34·10²³ range-units/s**,
**163 485 records/s**.  Fitted law over the measured decades
4·10²² … 4·10²⁵: `t ≈ (R / 6.34·10²³) s`, with a residual +9 % per decade
of superlinearity (the Proth exponent grows with the ladder height, so the
square-and-multiply gains a few steps per decade).

Extrapolating the *fitted law* one and a half decades past its range:

* full 10²⁷ ladder, linear model: **1 580 s ≈ 0.44 core-hours**;
* with the observed per-decade drift: **≈ 1 720 s ≈ 0.48 core-hours**;
* record count at 10²⁷: ≈ 2.5·10⁸ rungs.

The calibration this work was asked to check (4.42·10²³ range-units/s,
114 338 records/s, 2 261 s = 0.63 core-hours) is **confirmed as a safe
upper bound** — it is 1.4× conservative relative to CPU time here, which is
exactly what measuring wall clock on a loaded box produces.  The prior cost
model of ~119 days / \$2 650 is wrong by about four orders of magnitude.

## Stage (a) — the sieve: ported, and slower

`LeanCompCert/Ports/TGSieve.lean`.  What is proved:

* `dvd_proth_iff` — for an **odd** modulus `p` and the residue `r` with
  `p ∣ r·2ⁿ+1`, `p ∣ k·2ⁿ+1 ↔ k ≡ r (mod p)`.  Primality is never used, as
  in the reference.  This is why a 64-bit machine can sieve a 90-bit
  progression at all.
* `sieveTable_valid` — all 1861 shipped rows `(p, r)` satisfy the defining
  property; decided in the kernel, no evaluation axiom.
* `hitCount_eq_zero_iff` — the specification: a candidate survives iff it
  is nonzero and no tabulated modulus divides its Proth number.  This is
  `ProgressionSieve::makeBlock`'s postcondition.
* `sieveProgram_denote` — the bridge: the `Reflect.Program`'s denotation is
  exactly the reference's survivor count of the window.  Proved by
  simulation through `FoldBridge.Program.denote_eq_scalar_foldl`; every
  hypothesis is `∀`-quantified over states and indices, so it holds at a
  window of ten and at the reference's block of `2²⁴` at the same cost.
* `sieveProgram_wf` — well-formedness, program-sized, not window-sized.

**Why the port changes the algorithm.**  The reference's speed comes from a
mutable survivor array: a block costs `O(1)` amortized writes per
candidate.  The proved emission fragment (`Reflect` → `Rolled` → C) has
registers and no memory.  `Verified/ArrayState.lean` models memory and
`Verified/MemFragment.lean` proves the CCIR load/store lowering, but no
`AProgram.compile`/`toFn` joins them to the emitter, so there is no proved
array→C path.  The expressible form is therefore memoryless: test every
candidate against all 1861 moduli, three instructions each.

Measured (`bench/results/tg_sieve.csv`), window `[10¹², 10¹² + n)`:

| n | C bytes | emit s | ccomp s | ccomp run ms | gcc -O2 run ms |
|---|---|---|---|---|---|
| 20 000 | 255 726 | 0.87 | 1.65 | 121.8 | 26.5 |
| 100 000 | 255 731 | 0.87 | 1.65 | 553.7 | 123.7 |
| 500 000 | 255 731 | 0.86 | 1.65 | 2712.7 | 627.5 |

Rolled emission works as designed: C size and CompCert compile time are
**constant** in the window (255 KB, 1.65 s), run time is exactly linear.
All three binaries exit 0, i.e. the CompCert-compiled artifact reproduces
the survivor count of an independent Python replay (`bench/tg_replay.py`).

| | per candidate | vs reference sieve |
|---|---|---|
| reference block sieve | 1.59 ns | 1× |
| this port, gcc -O2 | 1.26 µs | **792×** |
| this port, `ccomp` | 5.43 µs | **3 422×** |

The decomposition is clean: **792×** is the price of losing the mutable
array (trial division instead of block sieving), and a further **4.3×** is
CompCert's code quality — gcc turns `k % p` for a literal `p` into a
multiply-and-shift, CompCert emits a real 64-bit `udiv` 1861 times per
candidate.

A fairer framing: the reference sieves 32× more candidates than it examines
(889 M sieved for 27.6 M examined at 4·10²⁴), because a block serves many
ladder steps.  Sieving only the candidates the reference actually examines
would cost this port 1 560 s against the reference's 62.5 s at 4·10²⁵ —
**25×**, not 3 400×.

Identified but not built: a bit-parallel form testing 64 candidates per
`u64` word, with one register per modulus holding the running offset,
costs ≈ 175 register operations per 64 candidates and would close most of
the 792×.  It needs ~1900 live locals in one loop body; whether CompCert's
register allocator survives that is unmeasured.

## Stage (b) — the Proth test: not expressible

`ProthTester::test` computes, for `N = k·2⁵²+1` (up to 2⁹⁰ at 10²⁷), the
first witness `a ∈ {2,3,5,…,29}` with `jacobi(a, N) = −1`, then
`a^((N−1)/2) mod N` and compares with `N − 1`.

The binding obstruction is **width, specifically the division**:

* `mpz_powm` needs `x·y mod N` with `N` about 90 bits.  The fragment's only
  division is `udiv`/`urem` at 64 ÷ 64 → 64.  Reducing a 128-bit product
  modulo a 90-bit modulus is a 128 ÷ 64 division, which the fragment cannot
  express.  `Verified/MulWide.lean` proves the 128-bit *product* circuit
  (`hl_spec`), but there is no counterpart for the reduction; a Montgomery
  or Barrett route would need a proved two-limb reduction the package does
  not have.

Three further obstructions, each individually survivable, are listed so the
verdict is not overstated:

* `mpz_jacobi` is a Euclid-like loop with a data-dependent trip count and
  branches on parity and on residues mod 8.  A fixed-fuel branchless binary
  Jacobi (2·90 iterations) *is* expressible in principle.
* The 90-step square-and-multiply and the Jacobi loop are inner loops
  inside the candidate scan; `Program`/`LProgram` have exactly one loop
  with a straight-line body.  Unrolling the inner loops into the body is
  what rolled emission already does elsewhere, so this alone is not fatal.
* `findLargestProth` returns at the first accepted candidate and `test`
  returns at the first quadratic non-residue.  The fragment has no branch;
  `Verified/EarlyExit.lean` models early exit at fold level but has no
  compile-to-C bridge.  Branchless re-encoding is possible at the cost of
  always paying the worst case.

Verdict: **not expressible today.**  The single thing that would change the
answer is a proved 128 ÷ 64 division (or a proved two-limb Montgomery
reduction) in the fragment.

> **Superseded.**  The proved two-limb Montgomery reduction now exists
> (`Verified/Montgomery.lean`, `Verified/Mont2.lean`), so stage (b) *is*
> expressible, and at 2.25× GMP with CompCert.  See
> `bench/results/tg_proth.md`.  The three secondary obstructions above
> also dissolve, because they belong to the *producer's* witness search,
> not to the verifier: the checker is handed the witness and only has to
> check one modular exponentiation.  The Jacobi loop, the early exits and
> the nested inner loops are all producer-side.

## Stage (c) — ladder assembly: ported exactly

`LeanCompCert/Ports/TGLadder.lean`.  The result worth having is the
word-safe reduction:

* `gap_le_iff` — rungs are Proth numbers `k·2ⁿ+1`, so two rungs differ by
  `(k′−k)·2ⁿ` and the 90-bit inequality `N′ ≤ N + step` **is** the
  machine-word inequality `k′ − k ≤ step / 2ⁿ`.  At the reference's
  `step = 4·10¹⁸ − 2` and `n = 52` that bound is **888**, and the deltas it
  bounds are exactly the varints the producer already writes.  No 128-bit
  arithmetic is needed anywhere in the check.  Measured on real streams:
  `max_delta = 888` is attained, so the bound is tight.
* `covers` — the coverage theorem: rungs climbing from the anchor in steps
  of at most `step`, ending within `step` of the target, leave no point of
  `(anchor, target]` uncovered.  Induction on the chain; cost independent
  of the number of rungs.
* `gapChain_of_deltas`, `covers_of_deltas`, `covers_of_accepts` — a delta
  stream bounded by `step / 2ⁿ` builds such a chain, so acceptance by the
  `u64` checker implies coverage.
* `ladderProgram_denote` — the bridge, fail-closed: the `LProgram`'s output
  is `0` **iff** every delta lies in `[1, bound]` and the deltas total the
  declared value.

Measured on the producer's own stream for range 4·10²³
(`bench/results/tg_ladder.csv`):

| records | C bytes | emit s | ccomp s | run ms | exit |
|---|---|---|---|---|---|
| 1 000 | 222 576 | 0.78 | 0.26 | 1.355 | 0 |
| 5 000 | 1 110 577 | 10.49 | 2.16 | 1.395 | 0 |
| 10 275 | 2 281 631 | 40.31 | 7.62 | 1.551 | 0 |

Exit 0 on real data: a CompCert-compiled, Lean-proved checker accepts the
reference producer's actual ladder segment.  Fail-closed behaviour is
demonstrated too — pushing one delta to 889 (one past the proved bound), or
declaring a total off by one, both make the artifact exit nonzero.

The index list is data, so emission is unrolled and C size grows with the
record count; Lean-side emission is quadratic in the block
(≈ 1.0 ms/record at 1 000-record blocks, 4.7 ms/record at 10 275).  Small
blocks are therefore strongly preferred, and
`Verified/Segment.foldl_range'_of_chain` is the recombination lemma that
makes them sound.  At 1 000-record blocks the full 2.5·10⁸-rung ladder
would cost ≈ 2.6·10⁵ s ≈ **72 core-hours** to check — about 150× the cost
of *producing* it, but embarrassingly parallel and proof-carrying.

## Reproducing

```
bench/tg_goldbach.sh path/to/tg_goldbach_ladder_native.cpp
```

Rebuilds the reference (it requires its own source digest and GMP),
recalibrates it, emits and compiles both artifacts, cross-checks them
against `bench/tg_replay.py`, and exercises the two fail-closed rejections.

## Trust

`scripts/AxiomAudit.lean` covers all nineteen new theorems.  Every one
depends on at most `propext`, `Classical.choice`, `Quot.sound`; the sieve
module's results use only `propext` and `Quot.sound`.  No `sorry`, no
`native_decide`.  `lake build`, `lake exe lean-compcert check-native` and
`lean-compcert-tests` all pass.

Not trusted, and not claimed to be: the emitted C artifacts.  `emitRolled`
and `emitUnrolled` are emission choices, exactly as elsewhere in this
package; the artifacts are independent cross-checks whose exit status is
not a theorem.  The theorems are about `Program.denote` / `LProgram.denote`
and the reference-level predicates.
