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

`LeanCompCert/Ports/ArraySegSieve.lean`.  One `AProgram`, `regCount = 192`,
core body of 111 instructions plus 27 (Mertens/squarefree), 31 (the same with
per-integer thresholds) or 19 (`Σ μ/m`) residue instructions — 138, 142 and
130 in total, constant at every scale.  Cell `i` of the current window stands
for `lo + s·L + i`; the single loop walks `rootCount + segCount` windows of
`L` cells; the array is `3L` cells plus the prime table.  Well-formedness —
the bridge's only side condition — is proved for every `(lo, L, segCount)` and
every residue by `segProgram_wf`, `[propext, Classical.choice, Quot.sound]`,
so `AProgram.evalCC_compile` applies and the emitted C computes `denote`.

**The prime table is computed by the program, not carried by it.**  The first
`rootCount = ⌈√hi / L⌉` windows sweep `[1, rootCount·L]` with the same
instructions; two selectors make the mark cursor stop at `π(⌊√(rootCount·L)⌋)`
rather than `π(⌊√hi⌋)`, and make the accumulation pass append `n` to the table
instead of feeding the residue, exactly when `n`'s cell was never marked and
`2 ≤ n ≤ ⌊√hi⌋` — which at that size says precisely that `n` is a prime above
every bootstrap prime.  What the init block still spells out is `π(⌊√L⌋)`
primes, a function of the window size and not of the range.

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

At `lo = 10¹⁰` (prime table 9 632 entries, `L = 10⁶`, `segCount = 100`,
`10⁸` integers, 24 MB resident, `loopCount = 375 739 392` — one root window
and a hundred main ones):

| residue | gcc | ccomp | gcc ns/integer | ccomp ns/integer | ns/iteration |
| --- | --- | --- | --- | --- | --- |
| `M`,`Q` | 5.36 s | 6.65 s | 53.6 | 66.5 | 14.3 / 17.7 |
| `M`,`Q`, per-integer thresholds | 5.40 s | 6.81 s | 54.0 | 68.1 | 14.4 / 18.1 |
| plain C reference | 1.02 s | — | 10.2 | — | — |

Mean of three, with one core otherwise busy.  Against the same measurement of
the previous artifact — the one that carried its prime table in the init block
and could not be built past `10¹⁰` — 5.08 s / 6.56 s, the whole of the root
sieve plus per-integer thresholds costs **6% under gcc and 4% under ccomp**:

| variant | body | `loopCount` | gcc | ccomp |
| --- | --- | --- | --- | --- |
| init-block table, one threshold per artifact | 120 | 372 019 200 | 5.08 s | 6.56 s |
| root sieve, one threshold per artifact | 138 | 375 739 392 | 5.36 s | 6.65 s |
| root sieve, threshold at every integer | 142 | 375 739 392 | 5.40 s | 6.81 s |

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

The emitted C no longer grows with `hi`.  It grows — very slowly — with the
*window* size `L`, because the bootstrap table the init block spells out is
the primes below `√L`; `L` is a memory choice, not a range choice.

| `hi` | `L` | init instructions | emit | emitted C | `ccomp -O2` | ccomp peak RSS |
| --- | --- | --- | --- | --- | --- | --- |
| `10¹⁰` | `10⁶` | 512 | 0.29 s | 45 463 B | 0.08 s | 23.8 MB |
| `10¹²` | `10⁶` | 512 | 0.82 s | 45 474 B | 0.06 s | 24.0 MB |
| `10¹⁶` | `10⁸` | 3 695 | 61.6 s | 234 746 B | 0.53 s | 129 MB |

`10¹²` and `10¹⁰` differ by eleven bytes of C — the loop bound and the
literals.  The `10¹⁶` emit time is the emit-time `π(10⁸)` count, a segmented
sieve in Lean; the artifact itself is 235 KB because `L = 10⁸` needs the
1 229 primes below `10⁴` as bootstrap.

For comparison, the same three configurations on the previous artifact: 1.7 MB
in 24.3 s, **13.9 MB in 1 972 s which `ccomp` would not compile**, and
17 284 368 init instructions which was never attempted.

| item | value |
| --- | --- |
| emitted C, `10⁸` scale (`L = 10⁷`) | 94 855 bytes |
| ccomp executable, hosted link | 70 568 bytes |
| ccomp object, freestanding (`mobius-seg` certificate) | 3 216 bytes |
| ccomp executable, freestanding (`as` + `ld`, no libc) | 3 288 bytes |
| x86_64 CompCert 3.17 `-O2 -S` | accepted |

## Extrapolated cost per axiom

Single core, CompCert-compiled, using the rate law above.  "Sieve" is the cost
of the Möbius pass that produces the residue; "extra" is anything the residue
needs beyond it.

Rates re-measured on the current program: `17.70` ns/iteration for the
Mertens/squarefree residue under `ccomp` (`14.27` under gcc), `18.90` for
`Σ μ/m` (`16.05`), `18.12` for the per-integer Mertens variant (`14.37`).

| axiom | range | sieve, 1 core | notes |
| --- | --- | --- | --- |
| `residual_platt_stronger_range` | `7.727·10⁹` | **9.0 min** | **done — the chain runs to completion, 663 windows, 0 violations, 2 h 23 min wall at `SEGLEN = 200`** |
| `residual_platt_2_11` | `10¹²` | **20.4 h** | same program, longer walk; supersedes the row above (a `10¹²` pass computes the `7.7·10⁹` range on the way).  Emits in 0.8 s, `ccomp` takes it in 0.06 s |
| `mertensM_hurst_sqrt` | `10¹⁶` | **24.1 core-years** | one pass; 24.6 with per-integer thresholds.  Emits in 62 s, `ccomp` in 0.53 s |
| `reproducibleSquarefree` | `10¹⁶` | **free, same pass** | `Q` and `M` ride the same sieve; both thresholds are in the same residue |
| `ch25_lemma_9_2_psi` | `10¹³` | 8.7 days *for the sieve alone* | **not implemented** — needs `log p` in 64-bit fixed point |
| `ramare_zuniga_lemma_6_2` | `2.1·10¹⁰` | 24 min *for the sieve alone* | **not implemented** — needs `log p`, `Λ*Λ`, and `γ` |

Under gcc the `10¹⁶` figure is 19.4 core-years, the `10¹²` figure 17.3 h and
the `7.7·10⁹` range 7.6 min.

The two rows that were "blocked at build time" in the previous revision of
this document are the first three: all of them now emit in under a minute and
compile under CompCert in under a second.

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

## The two build-time walls, and how they were removed

Both are gone.  Recorded here because the diagnosis of the first one was
wrong in a way worth remembering.

### 1. The interpreter's recursion guard, at `hi ≈ 2·10⁸`

`MemFragment.lowerMSequence` and `Proof.lowerSequence` built their result on
the way *out* of the recursion (`pure (stmt :: statements)` after the
recursive call), so one interpreter frame stayed alive per instruction.
Emission runs in the Lean interpreter, whose recursion guard fires at roughly
ten thousand frames.  A `plattstrong` chain died at

```
deep recursion was detected at 'interpreter'
#10107 LeanCompCert.Verified.MemFragment.lowerMSequence
```

with `hi = 1.95·10⁸` — the prime table there is 1 650 entries, six `MInstr`
each, 10 040 frames.  That is **forty times below** the `7.7·10⁹` target and
four orders of magnitude below where `ccomp` chokes, so it, and not the size
of the translation unit, was the binding constraint.

Both are now accumulator-passing and tail-recursive, with the two equations of
the naive definition recovered as `lowerMSequence_nil` / `lowerMSequence_cons`
(and the `lowerSequence` pair), so `lowerMSequence_correct` and every proof
around it is unchanged apart from `simp only [...]` becoming `rw`.  Measured
on `plattstrong` at `SEGLEN = 200`:

| `lo` | before | after |
| --- | --- | --- |
| `1.91·10⁸` | 18 s | — |
| `2.0·10⁸` | deep recursion | 1.15 s, 302 KB of C |
| `1.0·10⁹` | deep recursion | 3.58 s, 603 KB |
| `7.0·10⁹` | deep recursion | 17.7 s, 1.43 MB |

### 2. The init-block prime table, at `hi ≈ 10¹⁰`

Three instructions per prime, `K = π(√hi)` primes: 28 779 statements at
`10¹⁰`, 235 497 at `10¹²`, 17 284 368 at `10¹⁶`.  The `10¹²` artifact did
emit — 13.9 MB of C in 1 972 s — but `ccomp -O2 -c` segfaulted on it in 3.9 s
at the default 8 MB stack, and with `ulimit -s unlimited` was still running
after 282 s having reached **30.5 GB** resident, at which point it was killed.
`gcc -O2` was never reached.

The root-sieve phase described above deletes the table.  What the init block
spells out is now the primes below `√L`, a function of the window size:
`10¹²` and `10¹⁰` emit *the same 45 KB of C*, and `ccomp -O2` takes it in
0.06 s at 24 MB resident.  The full table is in the table above.

The costs are `rootCount·L ≈ √hi` extra integers swept and 18 extra body
instructions, together 5.5% (gcc) / 1.4% (ccomp) — measured, not estimated.

### 3. The window schedule, which was a price rather than a wall

The epilogue compares one running extremum against one threshold, so the
threshold must be the majorant at the window's *worst* endpoint — the left end
for an increasing majorant (`M`, `Q`), the right end for a decreasing one
(`S`).  A window `[lo, hi]` therefore tests the family `√(hi/lo) − 1` more
strictly than it is stated.  Windows must be geometric:

| ratio | weakening | windows to cover `[33, 10¹⁶]` | windows to cover `[3, 10¹²]` |
| --- | --- | --- | --- |
| 1.10 | 4.9% | 350 | 278 |
| 1.02 | 1.0% | 1 684 | 1 340 |
| 1.001 | 0.05% | 33 362 | 26 546 |

For the two Mertens/squarefree families this is now removable, and the
`mertenslive` modes remove it.  `⌊√n⌋` rises by at most one per integer, so it
is a register and three instructions; every majorant here is `α√n`, so
`⌊α·⌊√n⌋⌋` — sound, since `⌊√n⌋ ≤ √n` and every `α` is rounded down to a
dyadic — is a multiply and a shift.  Testing all four clauses at every integer
then makes the four running extrema unnecessary, so the residue is 31
instructions against 27: **1% of the body, and the schedule loss is zero.**

Demonstrated on one artifact covering `[9243, 100 009 242]`, a range ratio of
10 817 that the windowed mode would need 470 windows for:

```
mertenslive  [9243, 100009242]  -> violations 0
mertens      [9243, 100009242]  -> violations 4   (all four clauses)
```

and its three carry-outs agree exactly with `bench/ref_seg.c`, with the
maintained `⌊√n⌋` coming out at `10 000 = ⌊√10⁸⌋`.

The clauses themselves have their own oracle, `bench/ref_live.py`, which
sieves `μ` directly and applies the four tests in the residue's arithmetic.
It agrees with the artifact on the violation count and all four result slots
for both CDEM constants:

```
b = 0.0755, [1, 100000]  ->  920 violations, M = −48, Q = 60 794, ⌊√n⌋ = 316
b = 0.0285, [1,  60000]  ->  17 255 violations, M = −83, Q = 36 473, ⌊√n⌋ = 244
```

(the violations are all below `n = 33` and `n = 438 429` respectively, which
is where the two families begin; the `10⁸` run reports the same 920).

The extremum residue is kept, because it buys something the live one cannot:
its artifacts can be run with a **zero carry-in in any order** and reconciled
by a prefix pass afterwards, since `max over [1,n] = carry-in + max relative`.
Per-integer testing needs the true `M(lo−1)` inside the artifact, so a chain
of live artifacts is serial.  One core wants `mertenslive`; a thousand cores
want `mertens` and a schedule.

For the two `Σ μ(m)/m` families the majorant is `C/√n`, so the per-integer
threshold is a division rather than a multiply, and it was not done.

## Verified end to end

`bench/seg_chain.sh` walks a geometric schedule, chaining each window's
carry-out into the next window's seed, and fails on the first window whose
artifact reports a violated threshold.

### Platt's stronger range, whole

```
bench/seg_chain.sh plattstrong 10000 7727000000 1.02 200 ccomp
  -> 663 windows, chain complete over [10001, 7 727 000 000], 0 violations
     2 h 23 min wall, single core, every artifact compiled by CompCert 3.17

bench/seg_chain.sh plattstrong     4      10001 1.02   1 ccomp
  -> chain complete over [4, 10001], 0 violations
```

Together these cover `[3, 7.727·10⁹]` — the second chain's first artifact
carries `S(3)` in as its seed, and the seed is inside the extremum the
epilogue tests, so `n = 3` is checked.  `PlattStrongerRangeNatFamily` is
stated on `3 ≤ n ≤ 7 727 068 587`, so the last 68 587 integers are not in
this run; the schedule reaches them by raising `HI`.

Before the emitter was made tail-recursive this chain died at `1.95·10⁸`
with a `deep recursion` in the Lean interpreter.

### The other three families over the initial stretch

```
bench/seg_chain.sh mertens     9243  300000 1.02 200   ->  0 violations
bench/seg_chain.sh mertens2  438429 3000000 1.02 5000  ->  0 violations
bench/seg_chain.sh platt211       3  300000 1.02 200   ->  0 violations
bench/seg_chain.sh plattstrong 10000 300000 1.02 200   ->  0 violations
```

i.e. Hurst's `|M(n)| ≤ 0.571√n`, both CDEM squarefree clauses at both
constants, Platt's `(2.11)` and Platt's stronger range all **hold and are
computed**, by artifacts CompCert compiles.  Nothing here is a theorem: exit
status never is.  What is a theorem is that the artifact computes `denote`.

One thing the extremum residue does that is worth knowing: it seeds the
running extrema with the carry-in, so an artifact over `[lo, hi]` really tests
`[lo−1, hi]`.  A chain must therefore start at a `lo` where the family already
holds at `lo−1`; `plattstrong` from `lo = 3` fails on `|S(2)| = 0.5`, which is
true and is not a statement about the range `n ≥ 3`.

Independent agreement at scale: at `10⁸` the artifact and `bench/ref_seg.c`
produce identical values for all seven result slots, with
`M(10⁸) = 1928` and `Q(10⁸) = 60 792 694`, both published values.  At
`lo = 10¹⁰` over `10⁸` integers the two agree slot for slot as well.  Both
residues, and the per-integer variant, were re-checked against the oracle
after the root-sieve phase landed.

`bench/seg_sweep.sh` does the same comparison over a grid — `segLen` from 1 to
10 000, `hi` from 3 to `10¹⁰ + 10⁶`, both residues, 98 configurations, all
agreeing.  The grid exists because of one corner that did not: at
`segLen ≤ 3` **and** `hi ≤ 15` the root sweep is at most three integers, so
`⌊√rootLen⌋ ≤ 1` and the bootstrap prime list came out empty — while the
window-start reset installs the literal `2` and *its* first multiple, and the
mark step that follows uses them before the cursor-exhausted test can
intervene.  The root phase then marked a cell with a prime it had not
tabulated, failed to collect `2`, and left a `0` in the table for the main
phase to take a `urem` by.  `denote` is `none` there, so no theorem was
affected, but the artifact computed a wrong number quietly and
`seg_chain.sh plattstrong 4 10001 1.02 1` reported a violation at `n = 13`
that does not exist.  `Cfg.ofRange` now takes `max (⌊√rootLen⌋) 2`, which is
sound because a longer bootstrap list only marks more.

The invocation of `seg_chain.sh` has two constraints, both of which produce a
**spurious** violation — one that looks like a counterexample and is not — when
broken; they are spelled out in the script's header.  Briefly:
`ceil((LO−1)/SEGLEN)·SEGLEN ≤ LO`, or the threshold-ignored priming windows
overshoot `LO`; and `SEGLEN ≤ (RATIO−1)·LO`, or the *effective* window ratio
exceeds `RATIO` and the single epilogue threshold is taken far too far from
the window.  At `LO = 10000, RATIO = 1.02` the second means `SEGLEN ≤ 200`:
`SEGLEN = 10000` makes the first window `[10001, 20000]`, an effective ratio
of 2, and `plattstrong` fails it.  Neither constraint applies to the
`mertenslive` modes, which have no window-ratio loss at all.

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

# the artifact against the oracle, slot for slot
lake env lean --run bench/ArraySegEmit.lean mertens 1 10000000 10 h.c -
gcc -O2 -o h h.c && ./h && ./ref_seg 1 10000000 10

# the wall that used to be here: a 1e12-scale artifact, emitted and compiled
lake env lean --run bench/ArraySegEmit.lean mertens 1 1000000 1000000 e12.c 4
/usr/bin/time -v ccomp -O2 -o e12 e12.c

# per-integer thresholds: one artifact over a range ratio of 10 817
lake env lean --run bench/ArraySegEmit.lean mertenslive 9243 1000000 100 l.c - \
    1099511627774 5626 4611686536415883054

bench/seg_chain.sh mertens 9243 300000 1.02 200
```

`ArraySegEmit.lean` takes `MODE LO SEGLEN SEGCOUNT OUT [EXPECTED|-] [SEED...]`.
`-` selects the hosted driver, which prints the result cells (the carry-out a
chained run needs); a number selects the freestanding driver, which returns `0`
exactly when the artifact's violation count equals it.  `MODE` is `mertens`,
`mertens2`, `mertenslive`, `mertenslive2`, `platt211` or `plattstrong`.
`ulimit -s unlimited` is no longer needed at any scale reached here.
