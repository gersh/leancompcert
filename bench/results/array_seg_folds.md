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
| `PlattStrongerRangeNatFamily` | `S(n)` | `3 ≤ n ≤ 7 727 068 586`, **plus a separate clause at `n = 7 727 068 587`** | `1/(2√(n+1))`; the extra clause `1/(2√n)` | decreasing |
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

| `L` | `segCount` | max RSS | gcc |
| --- | --- | --- | --- |
| `10⁶` | 100 | 16.9 MB | 4.54 s |
| `10⁷` | 10 | 158 MB | 4.81 s |
| `10⁸` | 1 | 1.56 GB | 8.49 s |

Segmentation is free, and now slightly better than free: `16.9 MB` beats
`1.56 GB`.  The last row is the root phase showing through — `rootCount` is at
least one window, so at `segCount = 1` the root sweep *doubles* the work.  It
is a fixed `⌈√hi / L⌉` windows against `segCount`, so it disappears as soon as
the walk is long, which is the case every real run is in.  This is the whole
point — the one-shot `[0,L)` sieve of `Ports/ArrayMobius` needs 24 bytes per
integer of the *range*, which is 24 TB at `10¹²`; here it is 24 bytes per
integer of the *window*, and the window can be a megabyte.

At `lo = 10¹⁰` (prime table 9 632 entries, `L = 10⁶`, `segCount = 100`,
`10⁸` integers, a 24 MB array and 16.9 MB resident,
`loopCount = 375 739 392` — one root window and a hundred main ones):

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

The fragment is **5.3×** the hand-written C for the sieve residues.  That is
worse than the 1.5–1.7× the one-shot sieve showed, and the reason is
structural, not the bridge: an `AProgram` body is data-independent, so the mark
phase, the accumulation phase, the window bookkeeping, the root machinery and
the residue all execute on every one of the 3.76 iterations per integer, with
the inactive ones multiplied by zero.

### The rate law

Iterations per integer are
`(1 + rootCount/segCount) · (1 + Σ_{p ≤ √hi} (1/p + 2/L))`, i.e.
`1 + log log √hi + 0.2615 + 2·π(√hi)/L` with the root windows on top.  The
root term is `rootCount/segCount ≈ √hi/(L·segCount) = √hi/(hi−lo)`, so it is
one part in `√hi` for a full-range pass and vanishes from the table; at
`L = 10⁶`, `segCount = 100` it is the 1% by which `375 739 392` exceeds
`372 019 200`.

| `hi` | iterations/integer (`L = 10⁸`) | gcc ns/integer | ccomp ns/integer |
| --- | --- | --- | --- |
| `10¹⁰` | 3.76 (measured) | 53.6 | 66.5 |
| `10¹²` | 3.89 | 56 | 69 |
| `10¹³` | 3.97 | 57 | 70 |
| `10¹⁶` | 4.29 | 61 | 76 |

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
| `residual_platt_stronger_range` | `7.727·10⁹` | **9.0 min** windowed, **10.2 min** per-integer | **done — but the range is `n ≤ 7 727 068 586`, not `7 727 068 587`: the family is false at the stated endpoint (see "The last 3 204 integers" below).**  Windowed: 663 windows, 0 violations, 2 h 23 min wall at `SEGLEN = 200`; per-integer with the two-limb accumulator: one artifact, no window loss, no boundary |
| `residual_platt_2_11` | `10¹²` | **20.4 h** projected, **31.3 h measured** | **done — `[1, 10¹²]`, 1092 windows, two phases, zero violations; see "The `10¹²` run" below.**  Supersedes the row above (a `10¹²` pass computes the `7.7·10⁹` range on the way) |
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
0.06 s at 24 MB resident.  The numbers are in the artifact table above.

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
epilogue tests, so `n = 3` is checked.

Before the emitter was made tail-recursive this chain died at `1.95·10⁸`
with a `deep recursion` in the Lean interpreter.

### The last 3 204 integers, and what is actually at the top

`PlattStrongerRangeNatFamily` is, literally, a **conjunction of two clauses**:

```
(∀ n : ℕ, 3 ≤ n → n + 1 ≤ 7727068587 →
     |Σ_{m≤n} μ(m)/m| ≤ 1/(2√(n+1)))            -- clause 1, i.e. n ≤ 7 727 068 586
∧    |Σ_{m≤7727068587} μ(m)/m| ≤ 1/(2√7727068587)   -- clause 2, the endpoint
```

The windowed chain above legitimately certifies clause 1 only to
**7 727 065 383** — a window boundary — so 3 204 integers were outstanding.
Three separate things were in the way, and they have three different answers.

**(1) Window granularity — 3 178 integers, no new mathematics.**  One
comparison per artifact means one threshold per artifact, taken at the
window's worst point; for the antitone majorant `1/(2√(n+1))` that is the
window's right end, so the chain has to stop at a boundary the whole window
survives.  `mobiusLiveResidue` removes it as `mertensLiveResidue` does for the
increasing majorants — except that the trick is not the same one.  `⌊√n⌋` is a
register, but `2⁶¹/√(n+1)` is a *reciprocal* square root and is not; so the
residue keeps `c = ⌈√(n+1)⌉` (it rises exactly when `n ≥ c²`, and then `c²`
rises by `2c − 1`) and **divides**: the in-loop test is

```
|V| + budget + 1  ≤  ⌊2⁶¹/c⌋          one udiv, nothing above 2⁶³
```

and `⌊2⁶¹/c⌋ ≤ 2⁶¹/c ≤ 2⁶¹/√(n+1)` makes it a sound test of `1/(2√(n+1))`.
With it the sweep runs to **7 727 068 561** — the first genuinely uncertifiable
integer at accumulator scale `2⁶²` is `7 727 068 562`, twenty-five short of the
endpoint.

The register-level refinement for this 50-instruction block is now proved as
`MobiusResidueRealisation.mobiusLiveResidue_denote`.  A source build of that
proof, serialized under a 5 GiB soft / 6 GiB hard cgroup limit with swap
disabled, took **0.83 s wall / 3.27 s user** and peaked at **628,680 KiB RSS**.
This closes the block-to-`resStep` arrow; the whole-program sieve-to-Möbius
signal refinement remains separate.

The next model-composition layer is also proved: `accStep_mu` combines the
weight and two-limb sections, `ResInv.step` derives machine range safety and
advances one exact Möbius signal, and `resRun_inv` plus
`resFold_range_eq_resRun` chain the transparent invariant across a window.  A
fresh source compile of the extended `MobiusResidueWindow.lean`, under the same
5/6 GiB no-swap cap, took **0.73 s wall / 2.25 s user** and peaked at
**643,600 KiB RSS**.  `resStep_viol_eq` and `resRun_zero_all_pass` prove that
zero final violations imply every transparent comparison passed;
`stepAbs_exact_bound`, `StepPass.sound`, and `resRun_zero_sound` now turn all
of those passes into the exact cross-multiplied source family.  Only the
whole-program segmented-sieve-to-Möbius signal refinement remains open on
this arithmetic route.

**(2) The rounding budget — 25 more integers, by widening the accumulator.**
`round(2⁶²/m)` costs half an ulp per term, so the test subtracts `⌈n/2⌉`,
which at `n = 7.7·10⁹` is `1.47·10⁻⁴` of the threshold — six steps of
`μ(n)/n`, and the family is tighter than that at the top.  Carrying the
accumulator at scale `2⁷⁸` in **two limbs** (the shape `Verified/AddWide.lean`
proves) and shifting back to scale `2⁶²` for the comparison replaces the
budget by `⌈n/2¹⁷⌉ + 1`, i.e. `2.25·10⁻⁹` of the threshold — **65 536×**
smaller.  That recovers `7 727 068 562 … 7 727 068 586`, i.e. **all of clause
1**.

**(3) Clause 2 is false, and no accumulator width reaches it.**  At
`n = 7 727 068 587`,

```
|Σ_{m≤n} μ(m)/m| = 5.688085403150·10⁻⁶
      1/(2√n)    = 5.688039724193·10⁻⁶
```

so the majorant is exceeded by `4.57·10⁻¹¹`, a relative `8.0·10⁻⁶`.  This is
not a precision artifact.  `bench/ref_mob_margin.c` computes the sum at scale
`2⁹²`, where its own accumulated round-to-nearest budget is `≤ n/2` ulps —
nine orders below the gap — and the exact integer inequality

```
4·n·A²  ≤  2¹⁸⁴          (equivalent to |A/2⁹²| ≤ 1/(2√n))
```

fails by a relative `1.6·10⁻⁵`, and *still* fails when `A` is moved by the
full `±n/2` in either direction.  Clause 1 at `n = 7 727 068 586` — the same
inequality with `n+1` in place of `n` — holds with relative slack `2.9·10⁻⁵`,
and also survives `A ± n/2`.

So `PlattStrongerRangeNatFamily` **is false**, in its second conjunct, and so
is the real-variable statement it reduces to
(`∀ x ∈ [3, 7 727 068 587], |Σ_{m≤x} μ(m)/m| ≤ 1/(2√x)`), because at
`x = 7 727 068 587` the sum includes `m = 7 727 068 587`.  What is true is
clause 1 alone,

```
|Σ_{m≤n} μ(m)/m| ≤ 1/(2√(n+1))     for   3 ≤ n ≤ 7 727 068 586,
```

equivalently `|Σ_{m≤x} μ(m)/m| ≤ 1/(2√x)` for real `x < 7 727 068 587`.  The
off-by-one is the `x <` versus `x ≤` convention at the endpoint of Platt's
range; an axiom that closes the interval is false as encoded, and this is the
one thing in the gap that no amount of computation fixes.

`bench/ref_mob_margin.c` sweeps `[1, 7.7272·10⁹]` in 3 m 33 s on 18 cores and
prints, per integer, the true margin and the verdict of both scales:

```
per-integer test fails: S=62 21 162 times, S=78 18 475 times over [3, 7.7272·10⁹]
                        both first at n = 4, the tie discussed next;
                        first real failure S=62 at 7 727 068 562,
                                           S=78 at 7 727 068 587
min true margin = −1.597·10⁻⁸ at n = 7 727 085 914
```

The per-integer verdicts are exactly what the two artifacts report; the margins
are the mathematics, independent of either.

**The one place the `⌈·⌉` relaxation costs anything: `n = 4`.**  Replacing
`√(n+1)` by `c = ⌈√(n+1)⌉` makes the test stricter than the family by a
relative `1/√(n+1)`, which is `3·10⁻⁶` at the top and 34 % at `n = 4`.  There
`Σ_{m≤4} μ(m)/m = 1/6` exactly and `⌈√5⌉ = 3`, so `|V|` lands exactly on
`⌊2⁶¹/3⌋` and the `+1` for the shift's truncation tips it over — while the
family holds with enormous room (`1/6` against `1/(2√5) = 0.224`).  Swept
exhaustively, **`n = 4` is the only integer in `[3, 7.727·10⁹]` where the
relaxation costs anything**; `bench/seg_chain.sh plattstrong` covers it with an
exact emit-time threshold, and `bench/moblive_chain.sh` asserts the first
link's failure count to be exactly `3` (`n = 1, 2` where the family is
genuinely false, and `n = 4`).

### The per-integer `Σ μ(m)/m` artifact

```
lake env lean --run bench/ArraySegEmit.lean plattstronglive LO SEGLEN CNT OUT - [TLO THI]
bench/moblive_chain.sh HI SEGLEN LINKLEN [CC] [MANIFEST] [--corrupt K]
```

Body 161 instructions against the windowed residue's 130.  Agreement, exact,
on every one of the five numbers an artifact prints:

| range | failed tests | slot0 (limb lo) | slot1 (limb hi) | slot2 `⌈√(hi+1)⌉` | slot3 |
| --- | --- | --- | --- | --- | --- |
| `[1, 10⁵]` | 3 | 318441023180074197 | 32760 | 317 | 100489 |
| `[1, 2·10⁷]` | 3 | 3923701836270913649 | 32767 | 4473 | 20007729 |

against `bench/ref_moblive.py` (a Python linear sieve, same fixed point) at
`10⁵` and an independent C sieve at `2·10⁷`.  The three failures are `n = 1`
and `n = 2`, where the family is genuinely false, and `n = 4`, the `⌈·⌉` tie
above; a run that reported `0` there would mean the artifact was not testing
what it claims, so the chain driver **requires** the count to be `3` on the
first link and `0` on every later one.

Cost, measured at `lo = 10¹⁰` over `10⁸` integers, `375 739 392` iterations:

| residue | gcc | ccomp |
| --- | --- | --- |
| `plattstrong` (windowed) | 5.95 s = 15.84 ns/iter = **58.7 ns/integer** | 6.94 s = 18.47 ns/iter = **68.5 ns/integer** |
| `plattstronglive` (per integer, two limbs) | 6.34 s = 16.87 ns/iter = **62.6 ns/integer** | 8.00 s = 21.29 ns/iter = **78.9 ns/integer** |

so per-integer testing plus the wide accumulator costs **+6.6 % under gcc and
+15.3 % under CompCert**.  Projected over `[1, 7.727·10⁹]` — one artifact,
`28 646 119 488` iterations — that is **10.2 min** under `ccomp` and **8.1
min** under gcc on one core, against 8.8 / 7.6 min for the windowed residue.
The whole coverage gap is bought for about ninety seconds of CPU.

Shift counts in the emitted C are `1, 15, 16, 17, 48, 49` — all below 64, so
no shift is undefined; that is what pins `1 ≤ mobWideBits ≤ 15`.

### Why a chain driver must check more than the violation count

`bench/seg_chain.sh` accepts a window when its artifact reports zero
violations.  For a *chain* that is not sound: a link run with the wrong
carry-in computes a wrong accumulator, and a wrong accumulator can sit
comfortably under the threshold and report zero.  Measured, on a four-link
chain over `[1, 2·10⁷]` with the carry-in of link 3 moved by **one ulp**:

```
link 3: [10000001, 15000000] violations=0 slots=(12992314015720698035,...)
MANIFEST MISMATCH at link 3
  expected: ... 0 12992314015720698034 32768 3873 15000129
  got:      ... 0 12992314015720698035 32768 3873 15000129
link 4: [15000001, 20000000] violations=0 ...
MANIFEST MISMATCH at link 4
chain REJECTED   (exit 1)
```

Every link still reports zero violations — the old check passes, and the
chain would have been accepted having proved nothing.  `bench/moblive_chain.sh`
compares the violation count **and all four result slots** of every link
against a manifest, feeds link `i` literally the slots link `i−1` printed, and
clamps the last link so the walk stops at exactly `HI` rather than
overshooting past the range the family claims (the fourth hazard recorded in
`bench/seg_chain.sh.README`).

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

## The `10¹²` run of `residual_platt_2_11`

`bench/platt211_chain.py`, `bench/ArraySegBatch.lean`,
`bench/platt211_report.py`, manifest
`bench/results/manifests/platt211_1e12.json`.

The axiom is, verbatim
(`MathExtras/NumberTheory/Helfgott/Section24PlattFinite.lean`):

```lean
axiom residual_platt_2_11 :
    ∀ x : ℝ, 1 ≤ x → x ≤ (10 : ℝ) ^ (12 : ℕ) →
      |mobiusOverNSum x| ≤ Real.sqrt (2 / x)
```

`√(2/x)` is antitone, so on the real cell `[n, n+1)` the binding value is
`x → n+1`: the integer family is `|S(n)| ≤ √(2/(n+1))`, which is what the
`(n+1)` column of the table above says and what is tested here.

### Why one pass was not enough

A window's epilogue compares the running extrema of the accumulator, **seeded
with the carry-in `T(lo−1)`**, against one threshold literal.  Run a window
with the wrong carry-in and it computes wrong extrema — and wrong extrema can
sit comfortably under the threshold and report zero.  **For a chain the
violation count is not the check.**  So:

| phase | carry-in | compiler | what it gives |
| --- | --- | --- | --- |
| A | neutral `tBias`, every window independent, any order | `gcc -O2` | per window `(δ, max_rel, min_rel)`; a serial prefix pass then produces the true carry-in of every window, the true extrema, and applies every threshold |
| B | phase A's reconciled carry-in, baked in as the seed literal | `ccomp -O2` | the **artifact** applies its own threshold test; every slot must equal what phase A predicted and every carry-out must be the next window's seed |

Both phases covered **all 1092 windows**.  A chain is accepted only when every
phase-B window reproduces the phase-A reconciliation in all three slots, every
carry-out is the next seed, the violation counts are exactly the expected
ones, and the windows tile `[1, 10¹²]` with no gap, no overlap and no
overshoot.  `--corrupt K` perturbs one carry-in by one ulp; run against a good
chain the corrupted window **still reports `violations 0`** — the exit-code
check passes — and the manifest comparison rejects on three independent
grounds (`slot-mismatch`, `seed-mismatch`, `chain-break`).

### Result

```text
chain accepted: [1, 1000000000000], 1092 windows, every phase-B slot
reproduces the phase-A reconciliation, carry-outs chain, endpoint exact,
1 exempted window.
```

with

```text
T(10¹²) = 9 223 372 287 158 981 334      S(10¹²) = 5.427607268270948e-08
```

Three independent confirmations:

1. **An oracle that shares no code with the artifact.**  `bench/ref_seg.c`,
   run from `n = 1` to `n = 10 091 000 000` (162.90 s user), gives
   `T = 9 223 359 361 693 643 309`, which is **exactly** the chain's carry-out
   at window #858.  A wrong prefix anywhere below `10¹⁰` could not survive
   that.
2. **A published number.**  The separate axiom
   `residual_platt_10_pow_12_interval` records
   `S(10¹²) ∈ [5.42625·10⁻⁸, 5.42898·10⁻⁸]` from Platt's interval arithmetic.
   The computed `5.4276073·10⁻⁸` **is inside it**, at 50 % of the width.
3. **The strict `(n+1)` form.**  The artifact's literal is
   `platt211Threshold(hi) = ⌊2⁶²√(2/hi)⌋ − ⌈hi/2⌉`, the majorant at `hi`; the
   Nat family wants it at `hi+1`.  Below `hi ≈ 3.4·10⁷` that difference
   exceeds the `⌈hi/2⌉` the artifact already subtracts, so every window was
   **re-tested** from the same result cells against the stricter
   `⌊2⁶²√(2/(hi+1))⌋ − ⌈hi/2⌉`.  Every window clears it except the `n = 1`
   tie below.

The family is nowhere near tight: the worst window over `n > 2` is
`[3, 3]` at ratio `0.7071` against the strict threshold, and it is worst only
because a window's extrema are seeded with `T(lo−1)`.

### The one exact tie, at `n = 1`

`S(1) = 1` and `√(2/(1+1)) = 1`: the integer family is an **equality** at
`n = 1`, and no floored fixed-point test that subtracts a rounding budget can
certify an equality.  Concretely:

* window `[1,1]` is tested against `⌊2⁶²√2⌋ − 1 = 6 521 908 912 666 391 105`,
  which `2⁶²` clears with 41 % to spare — so `n = 1` **passes** under the
  artifact's own literal;
* window `[2,2]` inherits the tie, because its running extrema are seeded with
  `T(1)`.  It is the one exempted window, and the exemption is discharged from
  the same result cells: it covers a single integer, so `max = min = T(2)`,
  and `|T(2) − bias| = 2⁶¹ ≤ thr = 2⁶² − 1`.  Its violation count is asserted
  to be exactly `1` — a `0` there would mean the artifact was not testing what
  it claims;
* the **axiom** is unaffected.  It quantifies over reals, and on `x ∈ [1, 2)`
  it needs `|S(1)| ≤ √(2/x)` where `√(2/x) > 1 = |S(1)|` strictly.

### Cost

| | user/wall | ns/integer | vs projection |
| --- | --- | --- | --- |
| phase A, `gcc -O2`, 1092 windows | 167 354 s of summed per-window wall = 46.5 core-h | 167.4 | 17.3 h projected — but this phase ran while the shared cgroup was over its `memory.high`, so the figure is stall, not work |
| phase B, `ccomp -O2`, 1092 windows | 112 797 s = **31.3 core-h** | 112.8 | **20.4 h projected, +54 %** |
| emission, 2·1092 artifacts | 18.6 s wall in 4 Lean processes | — | — |
| compilation, 2·1092 artifacts | 8.5 s wall in 4 streams (unloaded) | — | — |

The `+54 %` is not all artifact: phase B ran with 14 concurrent windows on a
20-core box, so it includes shared-L3 contention, and the schedule adds a
`√hi`-integer root sieve per window (0.01 % of the range) plus the
`2·π(√hi)/L` mark term for windows whose span forces `L < 10⁶`.

**Two operational findings worth keeping**, both of which cost hours before
they were understood:

* *emit and compile in batches, not per window.*  One `lean --run` per
  artifact and one `gcc` per artifact are fine on an idle box (0.5 s and
  0.06 s).  Under memory pressure they are not: a single `gcc -O2` of a 16 kB
  translation unit was measured at **1166.36 s wall for 0.05 s of user time**
  — a 23 000× stall.  Batching 1092 emissions into 4 Lean processes and 1092
  compiles into 4 sequential streams took 18.6 s and 8.5 s respectively.
* *the stall was `memory.high`, not RAM.*  The host had 40 GB free the whole
  time.  The shared cgroup was at 57.4 GB against a `memory.high` of 55 GB
  with swap exhausted, so the kernel put every allocating task in it into
  forced direct reclaim: `/proc/pressure/memory` read `full avg10=93`.
  Compute-bound processes with a stable working set were unaffected — which is
  why the artifacts themselves kept running at full speed while every
  `fork`/`exec` crawled.

## Proved trial-division fallback for the live residue (2026-08-07)

`Ports/MobiusResidueTrial.lean` now closes the previously missing
producer-to-residue machine arrow without assuming the segmented sieve:

* `MertensCDEM.body` is the already-denoted fixed-round trial-division
  producer;
* ten proved scalar instructions materialize `(n, μ⁺, μ⁻, gate)`;
* `MobiusResidueScalar.residue` is extracted from the exact 50-instruction
  live array residue, and its denotation is inherited from
  `mobiusLiveResidue_denote`;
* `fullProgram_denote` proves the resulting rolled scalar program denotes the
  joint transparent fold; and
* `SafeRun`/`safeCheck` state the only run-time definedness condition as a
  finite Boolean computation.  `safeRun_append` proves that check can be
  split at any list boundary, with the first shard's concrete carry-out as
  the second shard's seed.

`Ports/MobiusResidueTrialWindow.lean` closes the next fold layer:
`fullBlock_spec` collapses every candidate's divisor rounds to one transparent
residue step, and `fullValue_eq_trialResAt` identifies the complete flat output
with the final trial-residue violation counter.  A fresh capped source build
completed in 0.31 s with 575,216 KiB peak RSS.  The downstream consumer then
identifies both emitted trial bits with Mathlib's Möbius function and proves
zero-result-to-source soundness from a proved canonical initial residue.  The
downstream root now supplies the exact paper-faithful stronger-range
configuration and proves its word admissibility.  A finite accepting receipt
and compiled checker for the remaining explicit arithmetic side conditions
are still required before that literature atom can be retired.  The `(2.11)`
row needs a distinct looser residue predicate; this stronger predicate is
known to fail beyond the stronger-range endpoint.

This is a semantics-complete fallback, not the production algorithm.  Its
work is `Θ(N·√N)` trial rounds for `[1,N]`, whereas the segmented route is
near-linear.  On the current aarch64 host, single core, `gcc -O2`:

| measurement | result |
| --- | --- |
| capped source build (`MemoryHigh=3G`, `MemoryMax=4G`, no swap) | 2.23 s wall, 576,364 KiB peak RSS |
| full 371-target repository build (one Lake job, no swap) | 12:21.91 wall, 17,011,432 KiB peak RSS; passed inside a 20 GiB hard cgroup |
| tiny rolled emission, 24 rounds | 0.27 s wall, 543,164 KiB peak RSS |
| emitted C / hosted executable | 12,820 B / 70,328 B |
| `gcc -O2` for the tiny artifact | 0.03 s wall, 25,536 KiB peak RSS |
| native 10 million rounds | 0.14 s user |
| native 100 million rounds | 1.38 s user |
| fitted rate | about **13.8 ns/trial round** |

The exact stronger-range configuration has 679,224,782,846,572 flat rounds.
At the measured rate, a single complete trial-division pass would cost
approximately 109 core-days through `7.727·10⁹`; using the same signal
producer with a future `(2.11)` predicate would cost 437 core-years through
`10¹²`, and `4.37·10⁸` core-years through `10¹⁶`.  These figures explain
why the proved fallback is valuable as a trust bridge and shard oracle but
does not replace the segmented sieve for the cited production ranges.

Kernel `#eval` is specifically not the execution route: a combined
`safeCheck`/`Program.denote`/`fullValue` probe at only 24 rounds was stopped
after 150 CPU-seconds.  The rolled native artifact completed immediately.

The memory incident that motivated the cap was also reproduced and
diagnosed: two compiler children orphaned by the earlier crashed run were
still outside any cgroup at roughly 5.5 GiB RSS each.  They were terminated.
The compositional proof initially attempted in this run briefly reached
4.8 GiB before being replaced by an opaque append lemma; the final source
build is below 600 MiB.  The full-build peak belongs to the pre-existing
`LeanCompCertTests.Attest` kernel string/hash test, not this port; that single
target took 738 seconds under memory reclaim.  All measurements above used
`MemorySwapMax=0`.

## Separate extrema residue for Helfgott (2.11) (2026-08-07)

The looser `(2.11)` predicate now has a distinct verified path rather than
reusing the stronger-range per-integer test:

* `MobiusExtremaScalar` extracts the original nineteen-instruction
  `mobiusOverNResidue` block and proves its exact accumulator/max/min step;
* `MobiusExtremaTrial` composes that block with the proved trial producer and
  proves a complete finite program with an explicit two-sided epilogue;
* `MobiusExtremaTrialWindow` collapses all divisor rounds to one true
  candidate update, preserving the ordered extrema invariant.

All three source checks ran with `MemoryHigh=3G`, `MemoryMax=4G`,
`MemorySwapMax=0`:

| source target | wall | peak RSS |
| --- | ---: | ---: |
| `MobiusExtremaScalar.lean` | 0.52 s | 566,336 KiB |
| `MobiusExtremaTrial.lean` | 0.74 s | 574,940 KiB |
| `MobiusExtremaTrialWindow.lean` | 0.24 s | 558,136 KiB |

This changes the proof route, not the asymptotic trial fallback cost: through
`10^12` the producer still performs about `10^18` trial rounds, or roughly
437 core-years at the measured 13.8 ns/round.  The completed segmented
campaign remains the production evidence (31.3 core-hours); proving its
sieve-to-Möbius refinement is therefore still the high-leverage route.

The root Mathlib bridge now completes the paper-facing half of this route.
`Platt211FixedPointReduction` proves that the integer sweep
`(n+1)(n+2|A_n|)^2 <= 8(2^62)^2` implies the exact all-real `(2.11)` claim.
`MobiusExtremaPaperBridge` proves zero extrema acceptance supplies that sweep,
including reciprocal-rounding equality and explicit exclusion of word wrap,
and composes it with `fullProgram_denote_mu`.  Direct capped source checks
used an 8 GiB hard limit and zero swap:

| root source target | wall | peak RSS |
| --- | ---: | ---: |
| `Platt211FixedPointReduction.lean` | 4.18 s | 6,849,388 KiB |
| `MobiusExtremaPaperBridge.lean` | 4.14 s | 6,919,936 KiB |

Fresh `#print axioms` for
`fullProgram_zero_implies_platt211` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The theorem is conditional on the
finite program returning zero; it does not misreport the 437-core-year trial
run as completed.

The first production-sieve refinement slice is now isolated as
`ArraySegMobiusSignal.signalBlock`: it is definitionally instructions 66--85
of the 111-instruction segmented core, not a reimplementation.  Its theorem
proves that on a main-phase accumulation iteration the four residue registers
are exactly `decodeCell n prod flag`; `CellRepresents` then leaves only the
pure statement that the two marked cells encode `mu(n)`.  The capped source
check used `MemoryHigh=3G`, `MemoryMax=4G`, no swap, and completed in 0.63 s
wall with 593,640 KiB peak RSS.  This is a partial denotation arrow, not yet a
proof that the whole segmented sieve establishes `CellRepresents`.

The follow-up `signalBlock_defined` proves the two product/parity loads are
in bounds in the two-bank layout, and `denote_signalBlock_readSig` composes
that fact with the generic array bridge.  Thus this slice now covers the
partial machine denotation, not merely the total helper evaluator.  Its capped
source rebuild completed in 0.83 s wall with 602,204 KiB peak RSS and no swap.

The complete 111-instruction core is now definitionally split into its
66-instruction prefix, the verified decoder, and its 25-instruction tail.
`readSig_arun_postSignal` proves the tail preserves all four observed
registers, and `readSig_arun_coreBody` lifts the decoder equation to the whole
core.  A first monolithic simplification of the tail climbed past the 3 GiB
soft limit and was stopped; replacing it by the reusable structural
`arun_reg_frame` proof brought the full source check back to 0.85 s wall and
601,168 KiB peak RSS under the unchanged 4 GiB hard cap, with no swap.
