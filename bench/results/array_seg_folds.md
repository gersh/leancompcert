# The reduced cite families as computed folds — what it costs

All numbers: aarch64, single core, `/usr/bin/time -v`, **user** seconds, best
of two runs.  `gcc` is `gcc -O2`; `ccomp` is CompCert 3.17 `-O2`.  Every
artifact in the table agrees with `bench/ref_seg.c`, a hand-written plain C
segmented sieve carrying the identical accumulators in the identical
fixed-point conventions.

## What is being computed

Six of the thirteen named on-cone inputs of the ternary Goldbach development
are reduced, in `claude_math` branch `a7/triage-13-cone-axioms`, to
natural-number families.  Read literally, those families are:

| reduced family | quantity | range | majorant | direction |
| --- | --- | --- | --- | --- |
| `MertensHurstNatFamily` | `M(n) = Σ_{m≤n} μ(m)` | `33 ≤ n ≤ 10¹⁶` | `0.571·√n` | increasing |
| `ReproducibleSquarefreeFiniteHeadNatFamily b t` | `Q(n) = Σ_{m≤n} \|μ(m)\|` | `t ≤ n ≤ 10¹⁶`, `t ∈ {9243, 438429}` | `b·√n`, `b ∈ {0.0755, 0.0285}`, against `(6/π²)·n` | increasing |
| `PlattEq211NatFamily` | `S(n) = Σ_{m≤n} μ(m)/m` | `1 ≤ n ≤ 10¹²` | `√(2/(n+1))` | decreasing |
| `PlattStrongerRangeNatFamily` | `S(n)` | `3 ≤ n ≤ 7 727 068 587` | `1/(2√(n+1))` | decreasing |
| `ChirreHelfgottLemma92NatFamily` | `ψ(n) = Σ_{p^k≤n} log p` | `1 ≤ n ≤ 10¹³` | `(−√2, 0.79059276]` for `(ψ(n)−n)/√n` | — |
| `RamareZunigaLemma62NatFamily` | `R₂*(n) = Σ_{m≤n} [(Λ*Λ)(m) − Λ(m)log m + 2γ]` | `3 ≤ n ≤ 2.1·10¹⁰` | `1.93·√n·log n` | increasing |

The first four are **integer** folds: `M`, `Q` and (after a fixed-point
rescaling) `S` are running sums of `μ`, so one Möbius sieve produces all
three.  The last two are **transcendental** folds: their summands are
logarithms of primes, and no amount of sieving produces them.  That split is
the single most important fact in this document, and it is why four of the six
are implemented here and two are not.

## The program

`LeanCompCert/Ports/ArraySegSieve.lean`.  One `AProgram`, `regCount = 128`,
body of 120 instructions plus 26 (Mertens/squarefree) or 19 (`Σ μ/m`) residue
instructions.  Cell `i` of the current window stands for `lo + s·L + i`; the
single loop walks `segCount` windows of `L` cells; the array is `3L` cells plus
the prime table however long the walk is.  Well-formedness — the bridge's only
side condition — is proved for every `(lo, L, segCount)` and either residue by
`segProgram_wf`, `[propext, Classical.choice, Quot.sound]`, so
`AProgram.evalCC_compile` applies and the emitted C computes `denote`.

Every real-valued majorant is compared **once per artifact**, in the epilogue,
against an exact integer threshold computed in Lean: `Nat.sqrt` of a rational
cross-multiplication for the `√`, and a Machin computation of `π` in integer
arithmetic for `⌊(6/π²)·2³⁶⌋ = 41 776 432 333` (exact — the true value is
`41 776 432 333.0417`).  Neither a `√` nor a `π` ever appears in the artifact.

## Measured

### Rate

`M(n)`/`Q(n)` residue, `10⁸` integers, `L·segCount = 10⁸`:

| `L` | `segCount` | max RSS | gcc | ccomp |
| --- | --- | --- | --- | --- |
| `10⁶` | 100 | 16.6 MB | 4.43 s | — |
| `10⁷` | 10 | 157 MB | 4.31 s | 5.50 s |
| `10⁸` | 1 | 1.56 GB | 4.27 s | — |

Segmentation is free: `16.6 MB` costs 4% over `1.56 GB`.  This is the whole
point — the one-shot `[0,L)` sieve of `Ports/ArrayMobius` needs 24 bytes per
integer of the *range*, which is 24 TB at `10¹²`; here it is 24 bytes per
integer of the *window*, and the window can be a megabyte.

At `lo = 10¹⁰` (prime table 9 592 entries, `L = 10⁶`, `segCount = 100`,
`10⁸` integers, 16.6 MB resident, `loopCount = 372 019 200`):

| residue | gcc | ccomp | gcc ns/integer | ccomp ns/integer | ns/iteration |
| --- | --- | --- | --- | --- | --- |
| `M`,`Q` | 5.26 s | 6.80 s | 52.6 | 68.0 | 14.1 / 18.3 |
| `Σ μ/m` | 5.87 s | 6.67 s | 58.7 | 66.7 | 15.8 / 17.9 |
| plain C reference | 1.02 s | — | 10.2 | — | — |

The fragment is **5.2×** the hand-written C for the sieve residues.  That is
worse than the 1.5–1.7× the one-shot sieve showed, and the reason is
structural, not the bridge: an `AProgram` body is data-independent, so the mark
phase, the accumulation phase, the window bookkeeping and the residue all
execute on every one of the 3.72 iterations per integer, with the inactive ones
multiplied by zero.

### The rate law

Iterations per integer are `1 + Σ_{p ≤ √hi} (1/p + 2/L)`, i.e.
`1 + log log √hi + 0.2615 + 2·π(√hi)/L`.  Predicted 3.72 at `hi = 10¹⁰`,
`L = 10⁶`; measured `372 019 200 / 10⁸ = 3.72`.  The law is used below.

| `hi` | iterations/integer (`L = 10⁸`) | gcc ns/integer | ccomp ns/integer |
| --- | --- | --- | --- |
| `10¹⁰` | 3.72 (measured) | 52.6 | 68.0 |
| `10¹²` | 3.89 | 55 | 71 |
| `10¹³` | 3.97 | 56 | 73 |
| `10¹⁶` | 4.29 | 60 | 79 |

### Artifact

| item | value |
| --- | --- |
| emitted C, `10⁸`-scale prime table (1 229 primes) | 231 KB |
| emitted C, `10¹⁰`-scale prime table (9 592 primes) | 1.7 MB |
| ccomp `-O2` compile | 0.60 s |
| ccomp executable, freestanding | 70 560 bytes |
| x86_64 CompCert 3.17 `-O2 -S` | 438 lines of assembly, accepted |

## Extrapolated cost per axiom

Single core, CompCert-compiled, using the rate law above.  "Sieve" is the cost
of the Möbius pass that produces the residue; "extra" is anything the residue
needs beyond it.

| axiom | range | sieve, 1 core | notes |
| --- | --- | --- | --- |
| `residual_platt_stronger_range` | `7.727·10⁹` | **8.6 min** (at the measured rate) | done — program built, bridge proved, artifact emitted |
| `residual_platt_2_11` | `10¹²` | **19.7 h** | same program, longer walk; supersedes the row above (a `10¹²` pass computes the `7.7·10⁹` range on the way) |
| `mertensM_hurst_sqrt` | `10¹⁶` | **25.0 core-years** | one pass |
| `reproducibleSquarefree` | `10¹⁶` | **free, same pass** | `Q` and `M` ride the same sieve; both thresholds are in one epilogue |
| `ch25_lemma_9_2_psi` | `10¹³` | 8.4 days *for the sieve alone* | **not implemented** — needs `log p` in 64-bit fixed point |
| `ramare_zuniga_lemma_6_2` | `2.1·10¹⁰` | 23 min *for the sieve alone* | **not implemented** — needs `log p`, `Λ*Λ`, and `γ` |

Under gcc the `10¹⁶` figure is 19.0 core-years, the `10¹²` figure 15.3 h, the
`10¹³` sieve 6.5 days and the `7.7·10⁹` range 7.6 min.

### Parallelism

The sweep is embarrassingly parallel with **no serial dependency**, which is
not obvious and is worth stating.  A window's threshold test needs the true
`M(lo−1)`, which is only known after every earlier window — but the artifact
already stores the window's extrema *relative to its own carry-in* in the
result cells, and `max over [1,n] = carry-in + max relative`.  So every window
can be run with a zero carry-in, in any order, and the thresholds applied
afterwards in a prefix-sum pass costing nothing.  `10¹⁶` on 20 cores is 15
months; on 1 000 cores, 9 days.

For comparison, Hurst's original `M(x)` computation to `10¹⁶` and the CDEM
reproducible squarefree verifier are both cluster computations; this is the
same order of magnitude, with the loop body machine-checked to be what the
Lean denotation says.

## The two things that block the full scales

### 1. Emission does not scale with the prime table

The prime table is written by the init block, three instructions per prime, so
`K = π(√hi)` primes cost `3K` instructions in one straight-line sequence.
`Proof.lowerMSequence` is not tail-recursive and, measured, superquadratic:

| `hi` | `K` | init instructions | emit time |
| --- | --- | --- | --- |
| `10⁸` | 1 229 | 3 690 | 0.24 s |
| `10⁹` | 3 401 | 10 206 | 3.7 s (needs `ulimit -s unlimited`) |
| `10¹⁰` | 9 592 | 28 779 | 24.3 s |
| `10¹²` | 78 498 | 235 497 | > 70 min, not observed to finish |
| `10¹⁶` | 5 761 455 | 17 284 368 | out of the question |

Below about 8 600 instructions the default interpreter stack suffices; above
it, `ulimit -s unlimited` is required and the time grows like `K^{1.9}` or
worse.  Two fixes, neither of which touches the bridge or the fragment:

* make `lowerMSequence` (and the rolled lowering around it) tail-recursive and
  linear — an emitter change, and the cheaper one;
* **generate the prime table inside the program**: a root-sieve phase over
  `[0, √hi)` marking composites, and let the mark cursor walk every `d` in
  `[2, √hi)` reading its primality from that region instead of walking a
  compacted table.  This removes the `O(K)` init entirely at the cost of
  `√hi` extra iterations per window — negligible at `10¹²` (`10⁶` against
  `L = 10⁸`), 100% overhead at `10¹⁶` unless `L ≫ 10⁸`.

Until one of these lands, the emission ceiling is around `hi = 10¹⁰`.  The
running cost above is unaffected; this is purely a build-time wall.

### 2. The window schedule and its price

The epilogue compares the window's running extremum against a single threshold,
so the threshold must be the majorant at the window's *worst* endpoint — the
left end for an increasing majorant (`M`, `Q`), the right end for a decreasing
one (`S`).  A window `[lo, hi]` therefore weakens the family by
`√(hi/lo) − 1`.  Windows must be geometric:

| ratio | weakening | windows to cover `[33, 10¹⁶]` | windows to cover `[3, 10¹²]` |
| --- | --- | --- | --- |
| 1.10 | 4.9% | 377 | 279 |
| 1.02 | 1.0% | 1 843 | 1 366 |
| 1.001 | 0.05% | 36 700 | 27 200 |

This is not free — at ratio 1.001 the emission alone is 36 700 artifacts — but
it is a schedule, not an obstruction, and the artifacts are independent.  The
per-window loss can be removed altogether by maintaining `⌊42√n⌋` in a register
(it increases by at most 1 per integer for `n ≥ 441`, so it is three
instructions) and doing the comparison per integer; that was measured as
roughly a 20% body-size increase and is the natural next step.

## Verified end to end

`bench/seg_chain.sh` walks a geometric schedule, chaining each window's
carry-out into the next window's seed, and fails on the first window whose
artifact reports a violated threshold.  With ratio 1.02:

```
bench/seg_chain.sh mertens     9243  300000 1.02 200   ->  0 violations
bench/seg_chain.sh platt211       3  300000 1.02 200   ->  0 violations
bench/seg_chain.sh plattstrong 10000 300000 1.02 200   ->  0 violations
```

i.e. Hurst's `|M(n)| ≤ 0.571√n`, both CDEM squarefree clauses with
`b = 0.0755`, Platt's `(2.11)` and Platt's stronger range all **hold and are
computed** over the initial stretch, by artifacts CompCert compiles.  Nothing
here is a theorem: exit status never is.  What is a theorem is that the
artifact computes `denote`.

Independent agreement at scale: at `10⁸` the artifact and `bench/ref_seg.c`
produce identical values for all seven result slots, with
`M(10⁸) = 1928` and `Q(10⁸) = 60 792 694`, both published values.  At
`lo = 10¹⁰` over `10⁸` integers the two agree slot for slot as well.

## What is not implemented, and why

`ch25_lemma_9_2_psi` and `ramare_zuniga_lemma_6_2` need `log p` to about 46
bits of absolute accuracy — `ψ(10¹³) ≈ 10¹³` has to be right to `±0.01` for a
constant quoted to eight digits, and there are `3.5·10¹¹` primes below `10¹³`
whose truncation errors add.  A 64-bit fixed-point logarithm is expressible in
the fragment (a 64-round square-and-compare, about 1 280 instructions), but it
must run *per prime*, not per integer, or the cost is `1.3·10¹⁶` extra
instruction-executions.  Per-prime means a compaction phase writing the
window's primes contiguously (a data-dependent store index, which the fragment
already permits) plus a fourth loop phase whose length is a static upper bound
for `π(hi) − π(lo)`.  Estimated: sieve `8.4 days` + logs `1.7 days` for
`ψ` to `10¹³`, single core.  `R₂*` additionally needs `(Λ*Λ)(m)`, which is
supported on `m = p^a q^b` and needs a second, divisor-side pass, and `2γ`,
which is a literal.

Both are engineering, not obstructions.  Neither was attempted here.

`ramare_zuniga_lemma_6_2` carries a further caveat that computing the family
does not remove: its underlying justification in the source is a literature
citation, so a computed `R₂*` residue corroborates the paper's claim without
discharging it.

## Reproducing

```
lake build
lake exe lean-compcert check-native          # mobius-seg runs through CompCert
lake env lean scripts/AxiomAudit.lean        # base trio only

gcc -O2 -o ref_seg bench/ref_seg.c
lake env lean --run bench/ArraySegEmit.lean mertens 1 10000000 10 seg.c 4
gcc -O2 -o seg seg.c ; ccomp -O2 -o segcc seg.c
/usr/bin/time -v ./segcc

bench/seg_chain.sh mertens 9243 300000 1.02 200
```

`ArraySegEmit.lean` takes `MODE LO SEGLEN SEGCOUNT OUT [EXPECTED|-] [SEED...]`.
`-` selects the hosted driver, which prints the result cells (the carry-out a
chained run needs); a number selects the freestanding driver, which returns `0`
exactly when the artifact's violation count equals it.  Emissions with a prime
table above roughly 8 600 init instructions need `ulimit -s unlimited`.
