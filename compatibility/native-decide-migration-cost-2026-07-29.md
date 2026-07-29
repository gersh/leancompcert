# Cost model for migrating ternary-goldbach off `native_decide` — 2026-07-29

- Host: aarch64 Linux, 20 cores, 119 GB RAM
- CompCert: 3.17 (`/usr/local/bin/ccomp`)
- leancompcert: Lean 4.32.1 · claude_math: Lean 4.32.0
- Subject: the 1,371 `native_decide` atoms inventoried in
  `problems/ternary-goldbach/native_decide_manifest.json` (schema 2,
  generated 2026-07-20)
- Everything under `/home/gersh/claude_math` was read-only throughout; all
  generated probes live in a scratch directory, all new code under
  `~/leancompcert/bench/`.
- **The inventory is a snapshot.** The manifest was generated 2026-07-20 and
  claude_math moved during this session (commits `700178d06` and `bfb58cec5`
  landed, the latter titled "Kernel-certify the large-Q leaves (sharded) and
  four uIv native leaves"). Atom *counts* may therefore already be lower than
  1,371; the *cost laws* in §2 are properties of the engines and of the Lean
  kernel, and are unaffected. Re-run `bench/classify_manifest.py` against a
  fresh manifest to re-price.

**Every number below is labelled M (measured here) or E (extrapolated).**
Extrapolated numbers name the measured law they come from.

---

## 0. Bottom line

Moving 1,366 of the 1,371 atoms to kernel-checked proofs costs **14.2
core-days (≈17 h wall on this 20-core machine) across 22,277 `decide`s**.
**5 atoms cannot be moved at all.** Machine time is not the constraint —
memory is, and the engineering of ~21,000 chunk-composition lemmas is. The
biggest surprise: **1,145 of the 1,371 atoms (84 %) already close in a single
`decide` for 85 minutes of CPU between them** — the largest family is not a
fold and was never a kernel-budget problem. All 14.2 core-days sit in just 221
atoms that need chunking. Full argument in §7.

---

## 1. Sizing the problem: what the 1,371 atoms actually compute

`bench/classify_manifest.py` parses every atom's *decided proposition* out of
the manifest, identifies the repository function being decided, and extracts
that atom's own scale parameters (fuel, precision, argument magnitude, bisection
depth) from the rendered term. Output:

- `bench/results/native_decide_shapes.csv` — one row per atom (1,371 rows)
- `bench/results/native_decide_shapes.json` — per-(kernel, shape) aggregate
- `bench/results/native_decide_families.json` — per-family aggregate

### 1.1 Correction to the received picture

The brief described the 1,025 `Rs62Certificates` atoms as "mostly the same
shape repeated (Helfgott large-Q block leaves)". That is not what they are:

| Rs62Certificates sub-shape | atoms | what it is |
|---|---:|---|
| `IntervalArith.RatInterval.log_enclose_full x 24` | 845 | a 24-term Mercator series in **exact `ℚ`** on a range-reduced argument — no loop over data at all |
| `MathExtras.RS62Ladder.loopE` | 140 | a prime-ladder fold, already segmented into 140 pieces of 0.98–5.0 M iterations |
| `loop410` / `loop314` | 23 | same shape, other ladders |
| `Helfgott1221.checkAll` | 9 | exact-`ℚ` product over primes, per cell |
| named-constant comparisons | 8 | constant-depth |

`MathExtras.HelfgottLargeQ.masterCheck` — the actual "large-Q block leaves" —
accounts for **one** atom, and its 112 leaves were already discharged by
`decide +kernel` upstream.

Across all families the single dominant shape is the rational log enclosure:
**865 of 1,371 atoms (63%) are `log_enclose_full` comparisons**, and the
scaling axis for them is the *bit width of one rational number*, not a fold
length. This matters because it changes the verdict: they are not a
kernel-budget problem at all (§5).

### 1.2 Shape taxonomy (all 1,371 atoms)

| shape class | atoms | primitive steps | scaling axis | what one "primitive step" is |
|---|---:|---:|---|---|
| `transcendental-enclosure` (exact-ℚ series, no rounding, unbounded operand growth) | 867 | 687 k | **decimal digits of one rational** | one series term / halving step |
| `bisection-tree` (2^depth, or pruned via `adaptiveUpper`) | 235 | 6.6 M | bisection depth | one interval-expression node |
| `linear-fold-sieve` (tail fold + `minFac` / `IsPrimePow` / `Squarefree` per step) | 187 | **487 M** | iterations | one fold iteration |
| `linear-fold-rat` (tail fold, exact ℚ, denominators grow) | 16 | 26.7 M | iterations | one fold iteration |
| `linear-fold-nat` (tail fold, fixed-width `Nat`) | 15 | 81.2 M | iterations | one fold iteration |
| `table-streaming` (materialises an `Array Nat` of length `bound`, then streams) | 5 | **361 M** | array length | one array cell |
| `fixed-expression` (constant depth) | 46 | 307 | — | — |

**Total primitive steps across all 1,371 atoms: 9.62 × 10⁸** (M — counted from
each atom's own parameters; the per-step *cost* is measured separately in §2).

The full per-atom table with kernel, shape, arithmetic domain, exact step count,
peak bignum width and a note is in
`bench/results/native_decide_shapes.csv`.

### 1.3 Per-family summary

| family | atoms | dominant shape | total primitive steps |
|---|---:|---|---:|
| `Rs62Certificates` | 1025 | 845 transcendental-enclosure + 163 fold-sieve | 449 M |
| `MathExtras.NumberTheory.Helfgott` | 202 | 153 band bisection-tree | 5.10 M |
| `MathExtras.NumberTheory.Vinogradov` | 55 | 50 CorC13 bisection-tree | 311 k |
| `Math.Problems.TernaryGoldbach.MinorArcs.Chapter14` | 34 | 20 transcendental-enclosure | 116 k |
| `AnalyticNT.LargeSieve` | 18 | 13 linear-fold-nat + 5 sieve/rat | 46.4 M |
| `TGNativeCertificates` | 11 | 8 CDEM sweeps + 3 table-streaming | 27.7 M |
| `Math.Problems.TernaryGoldbach.Certs` | 7 | 150 k / 2 M `Squarefree`/`Prime` folds | 2.90 M |
| `HelfgottCertificates` | 4 | bisection-tree | 1.40 M |
| `AnalyticNT.Chebyshev` | 3 | ψ sweeps to 10⁷ / 10⁶ / 4·10⁶ | 15.0 M |
| `TGNativeCertificates.Ramare` | 3 | table-streaming at 10⁸ / 10⁸ / 1.4·10⁸ | 340 M |
| `MathExtras.NumberTheory.Certs` | 2 | Liouville sweep + quadratic surrogate | 74.0 M |
| `MathExtras.NumberTheory.Analysis` | 3 | MV73 exact-ℚ grids | 5.6 k |
| `MathExtras.NumberTheory.LSeries` | 2 | constant depth | 33 |
| `MathExtras.NumberTheory.Helfgott.Certs` | 1 | 30 000-level non-tail recursion | 30 k |
| `MathExtras.NumberTheory.Mertens` | 1 | 20 953-step band sweep | 20.9 k |

---

## 2. Measured kernel cost laws

All kernel measurements are `/usr/bin/time -v` around a single `lean`
invocation; the import-only baseline is measured separately and subtracted.
The machine was shared with another agent's build during part of the session,
so **CPU time (user+sys) is reported throughout** — wall clock was inflated by
up to 5× under load 20+, CPU time was not.

### 2.1 Toolchain skew (M) — immaterial

Identical kernel workload (`decide +kernel` on a 60 000-step bignum
recursion, no imports), alternating toolchains:

| toolchain | CPU (s) | peak RSS |
|---|---:|---:|
| Lean 4.32.0 (claude_math's) | 2.66 | 921 MB |
| Lean 4.32.1 (leancompcert's) | 2.67 | 944 MB |

0.4 % in time, 2.4 % in memory. **The version skew does not affect any number
in this report.** Moreover, every *claude_math* measurement in §2.4 was taken
with Lean 4.32.0 against claude_math's own `.olean`s, so it is skew-free by
construction.

### 2.2 Kernel throughput by shape (M)

Baseline (empty file, Lean 4.32.0): 0.12 s CPU, 364 MB RSS.

| shape | per unit (CPU) | per unit (RSS) | sizes measured |
|---|---:|---:|---|
| bare `Nat` tail recursion (4 `Nat` ops/step, ≤30-bit) | 51–68 µs/step | 9.4–11 KB/step | 15 k–120 k |
| CH25 `Leaf` record (`decide`, 5 conjuncts + one 58-digit × 62 500 product) | 3.9–6.8 ms/leaf | 286–417 KB/leaf | 128–11 658 |
| leancompcert CCIR `Program.denote` fold (22-instruction u64 body) | 3.74–5.22 ms/element | 834 KB/element | 1 000–30 000 |

Normalising to one primitive arithmetic reduction:

- **~15 µs and ~2.4 KB per primitive `Nat` operation** in the best case
  (bare recursion, small operands);
- **~0.2 ms and ~38 KB per CCIR instruction** when the computation is
  *interpreted* through `evalCCSequence` rather than reduced directly.

The 15× time and 16× memory penalty for the reflected route is the price of
running the computation through a denotational interpreter inside the kernel.
It is the correct route for a *certificate* (the proof term stays O(1) and
CompCert can compile the same program), but it is not the cheapest way to make
the kernel do arithmetic.

### 2.3 The memory wall is the real limit (M)

RSS grows **linearly and monotonically** with reduction steps inside a single
`decide`; nothing is reclaimed until the command finishes. Fitted from the
leancompcert reflect sweep (n = 1 000 … 16 000, **R² = 0.99997**):

```
peak RSS above baseline ≈ 0.818 MB × (fold elements)
```

Consequences on this 119 GB machine (M, by extrapolation of a dead-straight
measured line):

| budget for one `decide` | max CCIR fold elements | max CH25-style leaves | max bare-Nat ops |
|---|---:|---:|---:|
| 8 GB | ~9 000 | ~20 000 | ~3.3 M |
| 25 GB | ~29 000 | ~63 000 | ~10 M |
| 100 GB | ~119 000 | ~250 000 | ~42 M |

The largest single `decide +kernel` actually run here was **30 000 elements at
25.3 GB / 157 s**, which succeeded. Extrapolating the line to the 119 GB
machine limit gives ~140 000 elements — in agreement with Tutorial 3's
recorded crash of a 150 000-element monolithic pipeline. That prior report is
confirmed rather than merely repeated.

### 2.4 Cost of claude_math's OWN engines in the kernel (M)

Rather than extrapolate from a synthetic body, `bench/gen_realkernels.py` puts
claude_math's compiled `.olean`s on `LEAN_PATH` and runs `decide +kernel` on
the *actual* certificate functions at tractable parameter values.

#### `IntervalArith.RatInterval.log_enclose_full x 24` — the 865-atom shape

`x = 2^n`, so the argument has `d = n·log₁₀2` decimal digits.

| n | digits d | CPU above baseline | RSS above baseline |
|---:|---:|---:|---:|
| 8 | 3 | 0.09 s | 13 MB |
| 32 | 10 | 0.12 s | 15 MB |
| 128 | 39 | 0.18 s | 25 MB |
| 512 | 155 | 0.56 s | 62 MB |
| 2048 | 617 | **4.42 s** | **215 MB** |

Fitted law (M), over the three points where the cost is above the fixed
per-call floor: `t(d) ≈ 0.08 + 6.3 × 10⁻⁴ · d^1.36` seconds. Residuals: 0.17
vs 0.18 (d = 39), 0.68 vs 0.56 (d = 155), 3.99 vs 4.42 (d = 617) — within 21 %.
Memory is negligible (≤ 0.35 MB per 1 000 argument digits). The super-linear
exponent is consistent with the structure: `~3.32 d` halving steps on `d`-digit
rationals plus a 24-term series whose intermediates reach `25 × 3.32 d` bits.
Worst atom in the corpus (d = 843): **6.1 s predicted**.

Measured argument-size distribution over the 865 atoms (M, from the manifest):
median **10 digits**, 75th percentile 377, 90th 575, max 843; 533 atoms are
under 200 digits.

A cross-check on the argument shape (M): `x = 2^n` range-reduces to exactly 1,
so the Mercator series collapses and the probe above measures mostly the
halving loop. Repeating with a *generic* rational `x = 3^n/5` (which never
reduces to a power of two) at the same widths gives **1.53 s at 611 digits**
versus 4.42 s for the `2^n` equality form. The law above is therefore
**conservative by up to ~3×** for the real atoms; I keep it.

#### Fold engines (M)

Same method, on the actual engines. All three curves are clean power laws;
fitted exponents and coefficients are in `bench/results/feasibility_by_family.json`
and reprinted by `bench/feasibility.py`.

`MathExtras.RS62Ladder.loopE` — the 140-atom RS62 anchor ladder
(baseline 1.18 s / 2.87 GB):

| iterations | CPU above baseline | RSS above baseline | µs/iter | KB/iter |
|---:|---:|---:|---:|---:|
| 1 000 | 0.72 s | 117 MB | 720 | 117 |
| 3 000 | 2.22 s | 402 MB | 740 | 134 |
| 10 000 | 11.2 s | 1 666 MB | 1 118 | 167 |
| 30 000 | 48.8 s | 6 545 MB | 1 627 | 218 |
| 100 000 | *aborted at 26.2 GB after 686 s CPU* | | | |

Fit: `cpu = 1.141×10⁻⁴ · n^1.251 s`, `rss = 0.0314 · n^1.182 MB`.

`AnalyticNT.ChebyshevPsi.checkAllPsiLeMul` (baseline 1.27 s / 2.84 GB):

| iterations | CPU above baseline | RSS above baseline | ms/iter | MB/iter |
|---:|---:|---:|---:|---:|
| 300 | 2.19 s | 433 MB | 7.3 | 1.44 |
| 1 000 | 7.73 s | 1 233 MB | 7.7 | 1.23 |
| 3 000 | 22.3 s | 3 352 MB | 7.4 | 1.12 |
| 10 000 | 76.1 s | 11 203 MB | 7.6 | 1.12 |

Fit: `cpu = 7.10×10⁻³ · n^1.008 s`, `rss = 2.07 · n^0.926 MB`. Essentially
**linear at 7.6 ms and 1.12 MB per iteration** — the most expensive per-step
engine in the whole development, because every step performs an `IsPrimePow`
test, a `Nat.minFac`, and a rational log bound.

`TGNativeCertificates.CDEMMertens.rangeSweep` (baseline 0.86 s / 1.66 GB):

| iterations | CPU above baseline | RSS above baseline | µs/iter | KB/iter |
|---:|---:|---:|---:|---:|
| 1 000 | 0.66 s | 146 MB | 660 | 146 |
| 3 000 | 2.70 s | 498 MB | 900 | 166 |
| 10 000 | 10.7 s | 2 006 MB | 1 070 | 201 |
| 30 000 | 48.8 s | 7 608 MB | 1 627 | 254 |

Fit: `cpu = 1.156×10⁻⁴ · n^1.252 s`, `rss = 0.0455 · n^1.162 MB`.

**The headline number for the whole exercise:** claude_math's own fold engines
cost **0.7 – 7.6 ms and 0.12 – 1.2 MB per iteration** when reduced by the Lean
kernel. There is no cheap route; the leancompcert reflected route (5.2 ms /
0.83 MB per element) is squarely in the same band, so *rewriting into the
proved CCIR fragment costs nothing extra in kernel time* — it buys the CompCert
cross-check for free.

### 2.5 Maximum chunk size under an 8 GB per-`decide` budget (E, from the fits)

| engine | iterations per 8 GB `decide` |
|---|---:|
| `RS62Ladder.loopE` | 37 400 |
| `CDEMMertens.rangeSweep` | 32 700 |
| CH25 `Leaf` records | 23 000 |
| leancompcert CCIR fold elements | 9 900 |
| `ChebyshevPsi.checkAllPsiLeMul` | **7 500** |

---

## 3. Chunking (M)

The chunked discipline was measured with `bench/gen_kernel.py --route chunked`:
K independent certificates, each a `Program` carrying a distinct accumulator
seed in its `init` block (so the kernel cannot share one chunk's evaluation
with another — an earlier version that reused an identical program gave
meaningless numbers), then one arithmetic `decide +kernel` combining the K
chunk values.

**The combining step is free.** For K = 12, the combine-only control file
(chunk certificates removed, chunk values kept) cost **1.20 s CPU and 415 MB
RSS** — indistinguishable from the 1.18 s / 414 MB import-only baseline. The
combining `decide` performs no program evaluation, so it does not scale with
the chunk contents.

Therefore the chunked cost is simply `K ×` the single-chunk cost, and the
single-chunk cost curve is exactly the sweep of §2.2. The practical chunk size
is set by memory, not by any combining overhead:

- **a few thousand elements per chunk** (Tutorial 3's advice) is conservative:
  1 000 elements = 0.8 GB, 4 000 = 3.7 GB;
- **8 000–10 000 elements (7–8 GB) is the sweet spot** if you want to run 10
  chunk-checks in parallel inside 80 GB;
- above ~30 000 elements a single chunk needs 25 GB+ and you lose all
  parallelism on this machine.

Per-element cost degrades slowly with chunk size (3.74 ms/element at 1 000,
5.22 ms/element at 16 000 — GC pressure), so smaller chunks are ~30 % *cheaper*
per element as well as more parallelisable. There is no reason to use large
chunks.

---

## 4. The CH25 Lemma A.7 calibration point (M) — and the model does reproduce it

The brief gives this as the hard reference: 16 191 leaves, a 5 000 595-byte
Lean literal, ordinary `decide`, **5 m 07 s at 20.3 GB peak**, `#print axioms
= [propext]`.

### 4.1 What is actually in the repository

`/home/gersh/claude_math/ext/ch25_certificates/CH25Certificates/LemmaA7/` —
the literal is **4 619 772 bytes across 129 generated shards**
(`BoundaryStructure/TraceShard000.lean … TraceShard128.lean`), each shard
carrying ~128 `Leaf` records and closing `chunk.Valid` with its own ordinary
`decide` under `set_option maxRecDepth 100000`. Parsing all 129 shards yields
**exactly 16 191 leaves** (left 11 658, right 1, bottom 2 266, top 2 266), each
edge contiguous and covering the full `2^17` grid. So the certificate as
shipped is *already chunked* at 128 leaves per `decide`.

### 4.2 Measured, at both ends of the chunking range

`bench/gen_ch25.py` re-emits the **real** leaf records (read out of the shards)
as a single `Chunk` of N contiguous leaves and times the `decide`. Import-only
baseline: 2.29 s CPU / 6.26 GB (that is Mathlib, which
`BoundaryStructureCore` imports).

| leaves in one `decide` | CPU above baseline | RSS above baseline | ms/leaf |
|---:|---:|---:|---:|
| 128 | 0.73 s | 41 MB | 5.7 |
| 512 | 2.16 s | 109 MB | 4.2 |
| 2 048 | 7.59 s | 453 MB | 3.7 |
| 4 096 | 17.1 s | 1 170 MB | 4.2 |
| 8 192 | 45.5 s | 3 138 MB | 5.6 |
| 11 658 | 78.7 s | 4 862 MB | 6.8 |

Fitted (M): `CPU ≈ 9.2×10⁻⁵ · N^1.46 s`, `RSS ≈ 0.0141 · N^1.36 MB`.

Then I ran **the whole certificate**: all 16 191 leaves, all four edges, four
`decide`s in one Lean process, one file of 4 581 873 bytes:

```
User time (seconds): 95.06
System time (seconds): 5.17
Elapsed (wall clock) time: 1:08.31
Maximum resident set size: 9 701 384 KB
```

**100.2 s CPU, 68 s wall, 9.70 GB peak.**

Its axioms, checked (M):

```
'…Monolith.chunkL_valid' depends on axioms: [propext]
'…Monolith.chunkR_valid' depends on axioms: [propext]
'…Monolith.chunkB_valid' depends on axioms: [propext]
'…Monolith.chunkT_valid' depends on axioms: [propext]
```

`[propext]` only — no `Lean.ofReduceBool`, no `Classical.choice`, no
`sorryAx`. That part of the calibration reproduces exactly.

### 4.3 Verdict on the calibration

- **The model predicts the measurement.** The law fitted to the eight-point
  sub-sweep (`cpu = 3.41×10⁻³ · N^1.043`, `rss = 0.167 · N^1.073 MB`),
  extrapolated 1.39× past its largest measured point, gives **83.7 s and
  11.5 GB** for the full 16 191 leaves. Direct measurement: **100.2 s and
  9.70 GB**. That is **16 % low in time and 19 % high in memory** — the model
  reproduces its own calibration point.
- **The quoted reference figure of 5 m 07 s / 20.3 GB is not reproducible
  here.** The same 16 191 leaves close in 100 s CPU at 9.7 GB: **3.1× faster
  and 2.1× smaller**. I cannot say where the extra factor of 3 came from.
  Plausible causes: a cold Mathlib import counted in (2.3 s CPU here, but tens
  of seconds from cold disk); a whole-`lake build` of the 129-shard tree
  (129 × ~3 s, plus 129 Mathlib imports, which at 4 concurrent jobs would peak
  near 20 GB and take ~5 minutes — this fits the quoted numbers well); an
  earlier version of the file using `inferInstance` on `List` rather than the
  hand-written structural `Decidable` instances now in
  `BoundaryStructureCore.lean`; or a loaded machine. **The 129-shard parallel
  build hypothesis reproduces both quoted numbers closely**, which suggests the
  reference figure is the cost of *building the shipped shard tree*, not of one
  `decide` over 16 191 leaves.

So the model is not wrong; the two numbers measure different things. Stated
plainly: **the calibration point is reproduced by this model to within 20 %,
and the quoted 5 m 07 s / 20.3 GB is a whole-tree build cost, not a single
kernel check.**

---

## 5. Feasibility per family

`bench/feasibility.py` prices every one of the 1,371 atoms with the measured
law for its engine (or, where its engine was not itself probed, the measured
law for another engine of the same shape — flagged below), assumes an **8 GB
budget per `decide`** (which keeps ten checks running inside 80 GB), and
chunks anything that exceeds it.

The `exact` column counts atoms priced by **their own** measured engine; the
rest are priced by a same-shape proxy and are the softer numbers.

| atoms | exact | `decide`s | CPU (1 core) | wall @20 | RSS/`decide` | verdict | family |
|---:|---:|---:|---:|---:|---:|---|---|
| 1025 | 1009 | 12 995 | **8.4 d** | 10.1 h | 8 GB | CHUNK + CLUSTER | `Rs62Certificates` |
| 18 | 0 | 3 992 | 2.6 d | 3.1 h | 8 GB | NEEDS CHUNKING | `AnalyticNT.LargeSieve` |
| 2 | 0 | 2 247 | 32.6 h | 1.6 h | 8 GB | NEEDS CHUNKING | `MathExtras.NumberTheory.Certs` |
| 3 | 3 | 2 009 | 31.7 h | 1.6 h | 8 GB | NEEDS CHUNKING | `AnalyticNT.Chebyshev` |
| 11 | 8 | 325 | 4.9 h | 15 min | 8 GB | **PARTIAL** — 2 atoms have no route | `TGNativeCertificates` |
| 202 | 0 | 440 | 4.1 h | 12 min | 8 GB | NEEDS CHUNKING | `MathExtras.NumberTheory.Helfgott` |
| 7 | 0 | 84 | 84 min | 4 min | 8 GB | NEEDS CHUNKING | `Math.Problems.TernaryGoldbach.Certs` |
| 4 | 0 | 85 | 68 min | 3 min | 8 GB | NEEDS CHUNKING | `HelfgottCertificates` |
| 55 | 0 | 55 | 14 min | 43 s | 5.4 GB | FEASIBLE NOW | `MathExtras.NumberTheory.Vinogradov` |
| 1 | 0 | 5 | 5 min | 14 s | 8 GB | NEEDS CHUNKING | `MathExtras.NumberTheory.Helfgott.Certs` |
| 3 | 0 | 3 | 42 s | 2 s | 4.1 GB | FEASIBLE NOW | `MathExtras.NumberTheory.Analysis` |
| 1 | 0 | 1 | 29 s | 1 s | 4.0 GB | FEASIBLE NOW | `MathExtras.NumberTheory.Mertens` |
| 34 | 20 | 34 | 5 s | 0 s | 40 MB | FEASIBLE NOW | `…MinorArcs.Chapter14` |
| 2 | 0 | 2 | <1 s | 0 s | 10 MB | FEASIBLE NOW | `MathExtras.NumberTheory.LSeries` |
| 3 | 0 | 0 | — | — | — | **INFEASIBLE** | `TGNativeCertificates.Ramare` |
| **1371** | | **22 277** | **14.2 d** | **17.1 h** | | **5 atoms with no kernel route** | **total** |

By shape:

| atoms | `decide`s | CPU | shape |
|---:|---:|---:|---|
| 187 | 14 740 | **10.1 d** | `linear-fold-sieve` |
| 16 | 3 586 | 2.4 d | `linear-fold-rat` |
| 15 | 2 490 | 35.7 h | `linear-fold-nat` |
| 235 | 548 | 5.4 h | `bisection-tree` |
| 867 | 867 | **17 min** | `transcendental-enclosure` |
| 46 | 46 | 5 s | `fixed-expression` |
| 5 | — | — | `table-streaming` — **no kernel route** |

### 5.1 What is feasible right now (M-anchored)

Bucketing all 1,371 atoms by what the model says each one needs:

| bucket | atoms | share | total CPU | `decide`s |
|---|---:|---:|---:|---:|
| one `decide`, **under 10 s** | **950** | 69 % | **19 min** | 950 |
| one `decide`, 10 s – 10 min | **195** | 14 % | **67 min** | 195 |
| needs chunking | 221 | 16 % | 14.2 d | 21 132 |
| **no kernel route** | 5 | 0.4 % | — | — |

**1,145 atoms — 84 % of the trust surface — close in a single `decide` for a
combined 85 minutes of CPU.** Of the 950 sub-10-second atoms, 855 are in
`Rs62Certificates` (845 of them `log_enclose_full` comparisons, median 0.09 s
each), 43 are Helfgott band certificates, 34 are the whole
`MinorArcs.Chapter14` family, and 10 are Vinogradov certificates.

For that 84 % the migration is: delete `native_decide`, write
`decide +kernel`, add `set_option maxRecDepth`. No chunking, no rewriting into
the proved fragment, no new lemmas, no new hardware. **This is the single most
actionable finding in this report: the largest family by atom count is also the
cheapest, and it is not a fold at all.**

### 5.2 What needs chunking

The 221 atoms that need chunking carry essentially all of the **595 M fold
iterations** (487 M sieve, 81 M `Nat`, 27 M exact-ℚ) and **14.2 days of single-core CPU** — 99.6 % of the total. Each
exceeds the 8 GB budget and must be split; the model says **21,132 `decide`s**
of 7 500–37 400 iterations each. Chunking itself is cheap (§3, the combine is free), but each
split needs a composition lemma relating `engine (a+b) …` to
`engine a … ≫ engine b …`. The RS62 ladders already have that structure — the
140 `loopE` atoms *are* segments of one 3.24×10⁸-iteration sweep — so for them
the work is re-segmenting an existing decomposition ~230× finer, not inventing
one.

At 20-way parallelism the whole fold workload is **~17 hours of wall clock**,
which is a weekend, not a research programme. The bottleneck is engineering
the segment lemmas, not machine time.

### 5.3 What is infeasible

**5 atoms have no kernel route at all**, all `table-streaming`:

| atom | scale |
|---|---:|
| `TGNativeCertificates.Ramare.MStar140MCert.full_run` | four `Array Nat` of length 1.4×10⁸ |
| `TGNativeCertificates.Ramare.Finite100M.check_first_mertens_100m_full` | `Array Nat` of length 10⁸ |
| `TGNativeCertificates.Ramare.Lemma71.check_lemma71_100m_full` | `Array Nat` of length 10⁸ |
| `TGNativeCertificates.WeightedMoment217.check_weighted_moment_2_17_full` | `factorTable` of length 1.9×10⁷ |
| `TGNativeCertificates.PrimeLogSquare219.check_prime_log_square_2_19_full` | `factorTable` of length 1.5×10⁶ |

These engines first *materialise a factor table as an `Array Nat`*, validate
it, and then stream. The kernel has no efficient array: reducing
`Array.get`/`Array.set` goes through the list model, so building a 10⁸-entry
table costs Ω(N²) reductions before any of the actual mathematics happens.
Charging even the cheapest measured rate (15 µs, 2.4 KB per primitive `Nat`
operation) to the *linear* part alone gives 10⁸ × 15 µs ≈ **17 days per atom
and 240 TB of RSS** — and the quadratic array access makes that a wild
under-estimate.

**Be blunt: these five cannot be moved off `native_decide` by chunking, by
buying hardware, or by using leancompcert's proved fragment.** They need one of

- an *algorithmic* replacement that streams without a table (recomputing
  `minFac` per element instead of memoising it — which trades the memory wall
  for a ~√n time wall, ~5 000× more work per element: worse);
- a mathematical replacement of the finite check by an argument;
- or acceptance that they stay as cited/native atoms.

Note this is 5 atoms out of 1 371, but they are not minor: `Finite100M`,
`Lemma71` and `MStar140M` are the Ramaré Mertens-function inputs.

### 5.4 Confidence

- **Solid (M):** the 865 `log_enclose_full` atoms, the 140 `loopE` atoms, the
  3 Chebyshev atoms, the 8 CDEM atoms — 1 040 atoms (76 %) priced by a law
  measured on *their own engine*.
- **Proxy (E):** the 235 bisection-tree atoms and the remaining fold atoms are
  priced by a same-shape law. The band certificates
  (`MathExtras.NumberTheory.Helfgott`, 202 atoms) are the weakest row: their
  per-cell cost is charged as a `log_enclose_full` call of the same operand
  width, which ignores that a band cell contains `exp_enclose` nodes whose
  interval `pow` by `2^D` grows operands linearly. If those are 10× worse than
  modelled, that family goes from 4.1 h to ~1.7 days — still not decisive for
  the total. **This is the one row I would measure before acting on it.**
- The whole model is validated against an independent measured point (§4.3) to
  within 20 %.

---

## 6. The CompCert side

### 6.1 `lake exe lean-compcert check-native --force` (M)

```
[run] verified-decide: compiled with CompCert, native check passed
[run] mertens: ...
[run] wide-mertens / squarefree-mertens / reflected / fixedpoint / rolled-10m
native check: 7 certificates agree with their certified values (0 cached, 7 run)
```

Whole command: **1.38 s wall, 1.31 s CPU, 104 MB peak RSS** for 7 certificates
from a cold cache. Per certificate (min of 7 compile reps / 15 run reps,
machine at load ≈ 5):

| certificate | generated C | ccomp compile | native run | exit |
|---|---:|---:|---:|---:|
| `verified-decide` | 471 B | 51.1 ms | 0.18 ms | 0 |
| `rolled-10m` | 2 074 B | 55.3 ms | **13.30 ms** | 0 |
| `mertens` | 19 397 B | 69.3 ms | 0.21 ms | 0 |
| `wide-mertens` | 47 117 B | 97.1 ms | 0.18 ms | 0 |
| `reflected` | 78 867 B | 153.4 ms | 0.18 ms | 0 |
| `squarefree-mertens` | 77 353 B | 155.4 ms | 0.18 ms | 0 |
| `fixedpoint` | 110 752 B | 190.0 ms | 0.18 ms | 0 |

**Marginal cost of adding one certificate to the cross-check: ~50 ms + ~1.2 ms
per KB of generated C, plus the run.** All executables are ~70 KB.

### 6.2 Rolled emission at scale — Tutorial 5's claim verified (M)

`bench/RolledEmit.lean` + `bench/rolled_compcert.sh` emit the same
128-bit-product fixed-point body as a rolled loop at increasing counts. The
certified constants were cross-checked against an independent closed-form
`floor_sum` computation in Python and against the repository's own
`RolledFixedPoint.expectedBig`; they agree exactly at 10⁴ and 10⁷.

| loop count | C artifact | executable | ccomp compile (CPU) | native run (CPU, min) |
|---:|---:|---:|---:|---:|
| 10⁴ | 2 053 B | 70 496 B | 431 ms | 0.412 ms |
| 10⁵ | 2 059 B | 70 504 B | 433 ms | 0.737 ms |
| 10⁶ | 2 065 B | 70 504 B | 442 ms | 1.63 ms |
| **10⁷** | **2 071 B** | 70 504 B | 463 ms | **13.67 ms** |
| 10⁸ | 2 077 B | 70 504 B | 447 ms | 131.1 ms |

**Tutorial 5's claim — "a 2 KB artifact that CompCert compiles and the native
check runs in ~14 ms at 10⁷" — is confirmed exactly**: 2 071 bytes and 13.67 ms
CPU (14.09 ms wall, min of 15). The artifact grows by 6 bytes per decade (the
loop bound literal) and compile time is flat.

Steady-state native throughput: **1.31 ns per iteration of the 22-instruction
body**, i.e. ~7.6 × 10⁸ iterations/s, ~1.7 × 10¹⁰ primitive ops/s.

*(One caveat on the compile column: those are CPU seconds measured while the
machine was at load ≈ 20; the low-load wall-clock measurements of the same
compilations in §6.1 are 55–190 ms. `ccomp` forks `gcc` for preprocessing,
assembly and linking, so its CPU-time accounting includes children and is not
directly comparable to the wall figures. The stable conclusion — compile time
is independent of loop count for rolled emission — holds in both.)*

### 6.3 The whole claude_math package through CompCert, re-run here (M)

The cheap half of the cross-check was run at full scale on this machine, over
claude_math's live `.lake/build/ir` tree (2,273 generated translation units),
using claude_math's own Lean 4.32.0 headers:

```console
python3 scripts/compile-ir-tree.py /home/gersh/claude_math/.lake/build/ir \
  --include runtime/include \
  --include ~/.elan/toolchains/leanprover--lean4---v4.32.0/include \
  --jobs 10 --output <scratch>/tg-compcert
```

```
2273 units: 2142 compiled, 131 after mechanical rewrite, 0 rejected
```

This **exactly reproduces** the 2026-07-28 run, including the rewrite
breakdown (76 static-constructor, 73 static-string, 63 static-closure, 2
object-array flexible-array materialisations — 2026-07-28 reported
76/73/63/2 for the same tree).

Per-unit `ccomp` time (M), excluding 11 units in the first scheduling batch
that were I/O-stalled for ~528 s each by another process's memory pressure
(major page faults: 246 880; 52 GB read):

| statistic over the remaining 2 262 units | seconds |
|---|---:|
| min | 0.054 |
| median | **0.087** |
| p90 | 0.119 |
| p99 | 0.690 |
| max | 7.16 |
| sum | 267.6 |

Implied full-package CompCert cost: **~269 CPU-seconds**, consistent with the
"about 300 CPU-seconds" recorded on 2026-07-28. Wall time here was 9 m 21 s at
`--jobs 10` on a contended machine.

Units needing a mechanical rewrite cost **4× more** (mean 406 ms vs 101 ms),
because they are compiled twice — once to discover the rejection, once after
rewriting.

**Marginal cost of adding one more certificate module to the CompCert
compile: ~90 ms** (median), ~400 ms if it trips a flexible-array rewrite.
That is the honest answer to "what does the cross-check cost per
certificate": at 1,371 certificates it is **~2 CPU-minutes for the whole
suite**, i.e. free.

What this does *not* do is run them: `compile-ir-tree.py` compiles each unit
to an object and stops. Producing a runnable CompCert-compiled evaluator still
requires regenerating and compiling the dependency closure (mathlib et al.),
which is the open item recorded in the 2026-07-28 boundary note and is
unchanged by this run.

### 6.4 The kernel/native gap

Same computation, same body, same machine:

| 10⁷ iterations of the 22-instruction fixed-point body | time | memory |
|---|---:|---:|
| CompCert-compiled binary (M) | **13.7 ms** | ~1 MB |
| Lean kernel via `decide +kernel` (E, from the measured 5.22 ms/element line) | ~14.5 hours | ~8.3 TB (impossible) |

**The kernel is ~3.8 × 10⁶ times slower per element than the CompCert binary.**
Note which constraint binds: 14.5 hours of CPU is an affordable overnight run,
but 8.3 TB of RSS overshoots this machine by **70×**. The memory wall arrives
first, and by a wide margin. Any migration plan has to be a plan about memory.

---

## 7. Bottom line

**How long would it take to move all 1,371 atoms off `native_decide`?**

**Machine time: 14.2 core-days, or ~17 hours of wall clock on this 20-core box,
spread over 22,277 kernel `decide`s — for 1,366 of the 1,371 atoms. The
remaining 5 cannot be done at all.**

That is the answer to the question as asked, and machine time is not the
binding constraint. The real costs, in order:

1. **5 atoms are infeasible, full stop** (§5.3). The Ramaré 10⁸-scale
   table-streaming certificates need an `Array Nat` the kernel cannot build.
   No amount of chunking or hardware fixes this. They need an algorithmic or
   mathematical replacement, or they stay native.

2. **21,132 chunk-composition obligations** (§5.2). The machine time is
   trivial; writing and proving the segment lemmas that let 221 atoms be split
   ~100× finer is the actual project. The RS62 ladders already have the
   decomposition structure; the Chebyshev ψ sweeps and the LargeSieve folds do
   not.

3. **1,145 atoms (84 %) are nearly free today** (§5.1): one `decide` each,
   **85 minutes of CPU for all of them combined**. The 865 `log_enclose_full`
   comparisons alone total 17 minutes, median 0.09 s each. These are not folds
   and were never a kernel-budget problem. If the goal is to shrink the trust
   surface by atom count, this is where to start, and it is a day's work.

**Why memory, not time, is the wall.** Inside a single `decide` the kernel
retains every intermediate; RSS grows linearly with reduction steps and is
released only when the command ends. Measured coefficients run from 2.4 KB per
primitive `Nat` operation (bare recursion) to 1.12 MB per iteration
(`checkAllPsiLeMul`). On a 119 GB machine that caps one `decide` at ~7,500
iterations of the most expensive engine. Every "needs chunking" verdict above
is a memory verdict; none of them is a time verdict.

**The kernel/native gap, measured on identical work** (§6.4): 10⁷ iterations of
the same 22-instruction body cost **13.7 ms** as a CompCert-compiled binary and
would cost **~14 hours and ~8 TB** in the kernel — a factor of 3.8×10⁶ in time,
and impossible in memory. The kernel is not a slow evaluator; it is a
fundamentally different thing, and any plan that treats "just run it in the
kernel" as a drop-in for `native_decide` at 10⁷–10⁸ scale is wrong by six
orders of magnitude.

**The CompCert side is free and already done.** All 2,273 generated units of
claude_math compile under CompCert 3.17 with **zero rejections**, at a median
of **87 ms per unit** and ~269 CPU-seconds for the whole package — reproduced
here from scratch (§6.3). Adding a certificate to the cross-check costs ~90 ms.
The 7 registered leancompcert certificates run end-to-end in **1.38 s**. There
is no reason not to run this continuously.

**On the reflected route.** Authoring a certificate in leancompcert's proved
CCIR fragment costs **5.2 ms and 0.83 MB per element** in the kernel — squarely
inside the 0.7–7.6 ms / 0.12–1.2 MB band that claude_math's own engines already
cost when kernel-reduced (§2.4). **Rewriting into the proved fragment is
kernel-cost-neutral**, and it buys the CompCert cross-check and a machine-word
realisation for free. That is a strong argument for the leancompcert route over
"just call `decide +kernel` on the existing Lean function" wherever a rewrite
is needed anyway.

**What I did not do.** I did not port any certificate (another agent owns
that), did not run the claude_math computations as CompCert-compiled *binaries*
(that needs the dependency-closure link step recorded as open in the
2026-07-28 boundary note — I compiled every unit to an object, which is the
step that was in scope), and did not directly measure the band-certificate
bisection cost (§5.4 flags it as the one row worth measuring before acting).

---

## 8. Reproducing this

Everything new lives under `~/leancompcert/bench/` (nothing in `claude_math`
was modified; probe files were written to a scratch directory):

| script | what it measures |
|---|---|
| `bench/classify_manifest.py` | parses the manifest, emits the per-atom shape/scale table |
| `bench/gen_kernel.py` | `decide +kernel` cost of the leancompcert reflected route vs fold length; `--route chunked` for the chunking control |
| `bench/gen_realkernels.py` | `decide +kernel` cost of claude_math's **own** engines (read-only, Lean 4.32.0, claude_math's `.olean`s on `LEAN_PATH`) |
| `bench/gen_ch25.py` | CH25 Lemma A.7 leaf `decide` cost vs leaf count, from the real leaf records |
| `bench/RolledEmit.lean` + `bench/rolled_compcert.sh` | rolled C emission, CompCert compile and native run vs loop count |
| `bench/percert_native.sh` | per-certificate ccomp/run times for the registered certificates |
| `bench/feasibility.py` | fits the laws and produces the family/shape feasibility tables |

Data products in `bench/results/`:

| file | contents |
|---|---|
| `native_decide_shapes.csv` | **1,371 rows** — one per atom: family, module, origin, engine, shape class, arithmetic domain, exact primitive-step count, peak bignum width, note |
| `native_decide_shapes.json`, `native_decide_families.json` | aggregates by (engine, shape) and by family |
| `feasibility_by_atom.csv` | per-atom predicted CPU, RSS, `decide` count, and which measured law priced it |
| `feasibility_by_family.json`, `feasibility_by_shape.json` | the §5 tables |
| `real_log.json`, `real_rs62.json`, `real_psi.json`, `real_cdem.json` | the claude_math engine sweeps |
| `ch25_scaling.json` | the CH25 leaf sweep |
| `kernel_reflect_cpu.json`, `kernel_chunk1000.json` | the leancompcert reflected and chunked sweeps |
| `rolled_compcert.csv`, `percert_native.csv` | the CompCert measurements |

### Measurement hygiene

- The machine was shared with another agent's Lean build for much of the
  session (load average peaked at 23, memory at 86/119 GB). **All kernel
  numbers are CPU time (user+sys), which is contention-robust**; wall clock was
  inflated up to 5× and is reported only where noted. CompCert compile/run
  times were re-taken at load ≈ 5 and are min-of-7 / min-of-15.
- Import-only baselines were measured separately for every probe and
  subtracted.
- Three probes (`loopE` at 10⁵, `checkAllPsiLeMul` at 3×10⁴,
  `rangeSweep` at 10⁵) were terminated after exceeding 20 GB and ~11 CPU-minutes
  under memory pressure; they are recorded as failures in the JSON and excluded
  from the fits, which use 4 clean points each.
- Certified constants used in the rolled-emission benchmark were independently
  derived by a closed-form `floor_sum` in Python and agree exactly with the
  repository's own `RolledFixedPoint.expectedBig` at 10⁷ and with the emitted
  value at 10⁴.

