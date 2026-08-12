# `R₂*`: the reduced family that needed a factorisation sieve

`bench/results/array_seg_folds.md` covers the families whose residue the
segmented Möbius sieve already produces; `bench/results/psi_fold.md` covers
`ψ`, which needed a logarithm and a fourth loop phase.  `R₂*` is the third
shape, and §5 of `psi_fold.md` named the obstruction exactly:

> The rest is a **Dirichlet convolution**, and that is the obstruction: the
> residue needs, per cell `k`, the classification "prime power / two distinct
> prime powers / more", together with both prime factors. […] `R₂*` is cheap;
> it is simply a sieve this repository does not have yet.

It has one now: `LeanCompCert/Ports/R2SegSieve.lean`.

| axiom | quantity | range | majorant |
| --- | --- | --- | --- |
| `ramare_zuniga_2024_lemma_6_2` | `\|R₂*(n)\|` | `[3, 2.1·10¹⁰]` | `1.93·√n·log n` |

Read from `claude_math`, branch `a7/triage-13-cone-axioms`:
`MathExtras/NumberTheory/Reductions/FiniteCiteFloorReductions.lean`
(`RamareZunigaLemma62NatFamily`), with `r2Star` and `r2Coeff` from
`MathExtras/NumberTheory/Mertens/RamareEq22.lean`.

## 1. What has to be computed

`r2Coeff(k) = (Λ∗Λ)(k) − Λ(k)·log k + 2γ`, and the convolution collapses:

```
(Λ∗Λ)(p^a)     = (a−1)·log²p        Λ(p^a)·log(p^a) = a·log²p
(Λ∗Λ)(p^a q^b) = 2·log p·log q      Λ(·)·log(·)     = 0
(Λ∗Λ)(k)       = 0                  for k with ≥ 3 distinct prime factors
```

so

```
R₂*(N) = 2γN − Σ_{p^a ≤ N} log²p + 2·Σ_{p^a q^b ≤ N, p≠q} log p·log q .
```

Per cell the loop needs `ω(k)`, and when `ω(k) ≤ 2` both prime factors —
a factorisation, not a primality bit.

## 2. The sieve: three planes, `p^j` for every `j`, four modes

The table is the primes `p ≤ ⌊√hi⌋`, one cell each; the higher powers the
loop generates itself — when the multiples of `p^j` run past the window it
tries `p^{j+1}` first and only steps the cursor when that would exceed `hi`,
eight instructions.  A cell divisible by `p^v` is therefore marked exactly `v`
times, and each mark writes three planes:

* `prod` — multiplied by the **base prime**, so it ends at `Π p^{v_p(n)}` over
  the small primes.  `prod ≠ n` is exactly "a prime factor above `⌊√hi⌋` is
  left", and for `n ≤ hi` there can be only one, to the first power;
* `lsum` — incremented by `lnFix p`, the fixed-point logarithm of `prod`;
* `W` — at a `j = 1` mark only: the first two distinct weights and a two-bit
  saturating count, `w1 | w2<<28 | d<<56`.

An entry is **one array cell**, `value | lnFix p <<35 | first <<63`, and
generating the powers in the loop rather than tabulating them is what keeps
the init block compilable: at `hi = 2.1·10¹⁰` the powers would be 14 006 of
27 421 entries, so the emitted C halves, from 82 277 init statements to
40 259 — and that is the difference between `ccomp` overflowing its stack and
`ccomp` compiling the artifact (§6).

| mode | cell | jump | rounds |
| --- | --- | --- | --- |
| 0 | `d = 0`, `prod ≠ n` | `−(log n)²` | `S` |
| 1 | `d = 1`, `prod ≠ n` | `+2·log p·log Q` | `S` |
| 2 | `d = 1`, `prod = n` | `−(log p)²` | 1 |
| 3 | `d = 2`, `prod = n` | `+2·log p·log q` | 1 |

`Q = n/prod` is the large prime and its logarithm is never computed directly:
`log Q = lnFix n − lsum`, one subtraction.  That is why the log phase runs on
`n`, which increases along the stream so `⌊log₂ n⌋` stays incremental, rather
than on `Q`, which jumps around and would need a `clz` the fragment lacks.
Modes 2 and 3 still go through the stream — the running extrema of `R₂*` are
only right if the jumps are applied in increasing `n` — but finish after one
round instead of `S`.

Costs, at `hi = 2.1·10¹⁰`: the mark budget goes from `L·Σ 1/p = 2.74·L` to
`L·Σ 1/(p−1) = 3.55·L`, 30% more marking, and the log phase runs on the
`22.4%` of cells that are mode 0 or 1.  The budget is now *checked*: the mark
phase's last iteration asserts that the cursor reached the end of the table,
so a `markSteps` too small — which truncates the sieve and makes the
classification wrong, not merely incomplete — is reported rather than
silently believed.

### The test points are the jumps, not the integers

Between consecutive jumps `R₂*` increases by `2γ` per integer and the majorant
increases too, so on `[prev, cur−1]` the maximum of `R₂*` is at `cur−1` and
the minimum of the majorant at `prev`.  **Clause 1** is therefore tested once,
at `cur−1`, against `thr(prev)`; **clause 2** at each test point right after
its jump, where `R₂*` is smallest and the majorant binds hardest from below.
Both bounds then hold at every integer of the cell.

The head `[1, lo−1]` is folded at emit time in Lean, with both clauses tested
at **every** integer — and it has to be.  At `n = 2` the majorant is
`1.93·√2·log 2 = 1.892` while `⌊√2⌋ = 1` gives `1.338`, below the true
`R₂*(2) = 1.828`: the artifact's floored `⌊√n⌋` cannot represent the bottom of
the range, exactly as `ψ`'s could not represent `n = 1`.

## 3. The error is carried, not assumed

`lnFix m` undershoots `2^S·ln m` by at most 4 ulps (`logFix_bracket`'s two,
plus two for the conversion to natural logarithm), and every jump is a
*product* of two such values, so a term is off by at most
`2·4·(log p + log q) ≤ 16·log n` ulps of `2^-S`.  A register accumulates
`16·(⌊log₂ n⌋+1)·ln 2 + 2` at every test point and both clause tests add it,
so a clean run bounds the **real** `R₂*`, not its fixed-point image.  The
`2γ` step is `⌊2γ·2^S⌋`, one ulp per integer low, which clause 1 adds back as
`n`.

`S = 24` is forced from above, not below: a jump is a `64×64` product of two
`lnFix` values, so `(2^S·log hi)² < 2⁶⁴` caps `S ≤ 27`.  At `S = 24` the
budget over `2.1·10¹⁰` reaches `8.4·10⁴` against a margin of `1.65·10⁶` —
twenty times inside — and `2^S·|R₂*| ≤ 1.1·10¹⁴` sits one word deep under the
`2⁴⁸` bias.  **`R₂*` is the case where a single 64-bit accumulator is enough**;
`ψ`, in `psi_fold.md` §2, is the case where it was not.

## 4. What the numbers are checked against

Four independent things, none of which shares code with the artifact.

**(a) The kernel, against trial division.**  `Ports/R2SegSieve.lean`'s `Check`
namespace evaluates the whole three-phase loop at `S = 4` over `[6, 14]` and
compares the accumulator, the term count and `⌊√n⌋` against a reference that
factors by dividing.  The window exercises all four modes: `6 = 2·3` and
`12 = 2²·3` are mode 3, `8 = 2³` and `9 = 3²` mode 2, `10 = 2·5` and `14 = 2·7`
mode 1, and `7, 11, 13` mode 0.  `[propext, Classical.choice, Quot.sound]`.

**(b) The artifact, against `bench/ref_r2.c`.**  All ten result cells agree
bit for bit at `10⁶`, `10⁷` and `10⁸`, and `ccomp -O2` and `gcc -O2` produce
identical output at all three sizes.

| `hi` | `D` | `err` | terms | violations |
| --- | --- | --- | --- | --- |
| `10⁶` | `281 645 378 686 395` | `77 256 339` | `367 460` | 0 |
| `10⁷` | `282 198 274 298 136` | `794 372 917` | `3 201 972` | 0 |
| `10⁸` | `282 520 779 687 361` | `8 128 272 114` | `28 487 468` | 0 |

**(c) The fixed point, against exact real arithmetic.**  `R₂*(N)` computed in
`mpmath` at 30 digits from the definition:

| `N` | artifact `(D − 2⁴⁸)/2²⁴` | exact | difference | carried enclosure |
| --- | --- | --- | --- | --- |
| `10⁶` | `10 156.749233` | `10 156.985365` | `0.2361` | `4.6048` |
| `10⁷` | `43 111.895769` | `43 114.412149` | `2.5164` | `47.3483` |
| `10⁸` | `62 334.714932` | — | — | `484.4828` |

The difference is `5%` of the budget at both sizes: the budget is a bound on a
one-sided per-term truncation whose signs then cancel, so it is honest and
loose by about `20×`, which is what §3 claims.

**(d) The only published numbers this quantity appears in.**  No table of
`R₂*` is printed anywhere — not in Ramaré–Zúñiga Alterman 2024, not in
Ramaré 2013, not in the companion papers.  What *is* printed, in
Ramaré 2013 Lemma 7.1 (Acta Arith. 157, p. 375) and Ramaré–Zúñiga Alterman
2024 Lemma 7.1 (arXiv:2408.05969v2, p. 11), is a bound on a quantity built
from the same summand:

```
Σ_{k≤K} |Λ∗Λ − Λ·log + 2γ|(k)/k  +  2|R₂*(K)|/K  ≤  4345·c
```

| `K` | published `c` | published bound | computed here | mpmath, exact |
| --- | --- | --- | --- | --- |
| `462 848` | `0.0374` | `162.503` | `161.677370` | `161.67736993` |
| `10⁶` | `0.0422` | `183.359` | `182.217151` | — |
| `10⁷` | `0.0579` | `251.576` | `250.763810` | — |
| `10⁸` | `0.0762` | `331.089` | `329.972960` | — |

All four sit just under the published bounds, by `0.3%` to `0.6%` — tight
enough that a wrong classification or a wrong logarithm would have shown — and
the one value re-computed in exact arithmetic agrees with the oracle to nine
significant figures.  These are upper bounds, so they can refute and not
confirm; they are nonetheless the only external check this quantity admits.
`bench/ref_r2.c` prints the sum as `lemma71`.

The observed worst ratio `|R₂*(n)|/(√n·log n)` is `1.2574` at `n = 59 753`
over `[3, 10⁷]` and `1.3657` at `n = 36 917 053` over `[3, 10⁸]`, against the
majorant's `1.93`.

## 5. Measurements

`bench/R2SegEmit.lean` emits; one core, `user` time, mean of three, `lo` is
`⌊√hi⌋ + 1` and the head `[1, lo−1]` is folded at emit time.  Body: **318**
instructions.

| `hi` | `L` | table | iters/integer | ccomp s | ns/int | gcc s | ns/int |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `10⁶` | 99 900 | 168 | 13.336 | 0.433 | 433.4 | 0.287 | 287.3 |
| `10⁷` | 99 968 | 446 | 12.565 | 4.067 | 406.8 | 2.670 | 267.1 |
| `10⁸` | 999 900 | 1 229 | 11.909 | 38.24 | 382.4 | 25.29 | 253.0 |

The repository's law is `ns/integer = (iterations/integer) × (body) × κ`.
Fitting `κ` on these three points:

| | `10⁶` | `10⁷` | `10⁸` | mean |
| --- | --- | --- | --- | --- |
| `κ` (ccomp) | 0.0997 | 0.0993 | 0.0985 | **0.0992 ns** |
| `κ` (gcc) | 0.0661 | 0.0652 | 0.0652 | **0.0655 ns** |

— consistent to `±0.6%`, and within 7% of the `0.1066`/`0.0655` that
`psi_fold.md` fitted on a different body.  Artifact size:

| `hi` | C bytes | init statements | ccomp `-O2` | gcc `-O2` |
| --- | --- | --- | --- | --- |
| `10⁶` | 67 581 | 518 | 0.18 s | 0.09 s |
| `10⁷` | 120 690 | 1 352 | 0.27 s | 0.15 s |
| `10⁸` | 271 525 | 3 701 | 0.78 s | 0.44 s |

## 6. The `2.1·10¹⁰` configuration, and one measurement at `10¹⁰`

The configuration is computed, not guessed.  At `hi = 2.1·10¹⁰`,
`⌊√hi⌋ = 144 913`, and the table is the **13 415** primes below it — one cell
each, the 14 006 higher powers generated in the loop.  With `L = 10⁶`:

```
mark budget   3.550 iterations/integer   (2.74 of it the primes, 0.81 the powers)
accumulation  1.000
log phase     4.14 at the bottom of the range, 6.15 at its peak near 1e9,
              5.90 at 1e10, 5.82 at the top
                                        ------
total         8.69 / 10.70 / 10.45 / 10.37 iterations per integer
memory        3L cells of planes + 0.5L of stream + the table = 44 MB
```

The log-phase density is *not* monotone, and neither budget may be taken from
the first window.  Mode-2/3 cells (both primes below the **fixed** `√hi`) thin
out as `n` grows, while mode-0/1 cells — the ones that cost `S` rounds — are
almost absent just above `lo ≈ √hi`, where a prime factor above `√hi` barely
fits, and rise to their asymptotic density.  The round count therefore peaks a
window or two in.  Sizing from the first window alone under-budgets the log
phase by 1.3% at `10⁷`; the drain guard caught it — a nonzero violation count,
not a wrong answer — and `R2Cfg.ofScale` now takes the maximum over seven
probe windows.

**A direct measurement at `n ≈ 10¹⁰`, not an extrapolation.**  A *chained*
artifact (`R2Cfg.ofChain`) carries the mark table and the budgets of the whole
sweep to `2.1·10¹⁰` but walks only a slice — which is what a production chain
looks like, since every link needs every prime.  One such link over
`[10¹⁰+1, 10¹⁰+2·10⁶]`, at `10.451` iterations per integer, `ccomp` and `gcc`
byte-identical, zero violations:

| | measured | `κ` implied | vs. the `≤10⁸` fit |
| --- | --- | --- | --- |
| ccomp `-O2` | **366.5 ns/integer** | 0.1076 | +8.5% |
| gcc `-O2` | **241.7 ns/integer** | 0.0709 | +8.2% |

The 8.5% is the three planes: at `L = 10⁶` they are 24 MB against 24 MB of L3.
A production run should measure `L = 2·10⁵` too, where they are 4.8 MB and the
mark budget rises only to 3.82 iterations per integer.

**Cost of the whole sweep**, `[144 914, 2.1·10¹⁰]`, on one core, from that
measurement rather than from the law:

| | ns/integer | `2.1·10¹⁰` |
| --- | --- | --- |
| gcc `-O2` | 241.7 | **1.41 core-hours** |
| ccomp `-O2` | 366.5 | **2.14 core-hours** |

The full-scale run has since been made; it is §8, and it came out **24 %**
(ccomp) / **31 %** (gcc) above these projections.

### The wall the table hit, and how it was removed

The first version tabulated every prime power: 27 421 entries, 82 277 init
statements, 5.3 MB of C.  `gcc -O2` compiled it in 22.4 s and 447 MB;
**`ccomp -O2` stack-overflowed** in `Env.IdentMap.add` at the default 8 MB
stack, and with an unlimited stack was still climbing past 27 GB after four
minutes when it was stopped — the same wall `ArraySegSieve`'s docstring
records at `10¹²` for the prime table it deleted, reached here at `2.1·10¹⁰`
because each entry carries a logarithm that a root phase could not have
computed.

Generating the `j ≥ 2` entries in the loop removes it.  Eight instructions in
the body — `p^{j+1} = rQ·rBp`, one comparison against `hi`, and the cursor
steps only when the bump does not fit — cost 2.5% of the run and halve the
init block:

| | entries | init statements | C bytes | ccomp `-O2` | gcc `-O2` |
| --- | --- | --- | --- | --- | --- |
| tabulated powers | 27 421 | 82 277 | 5 285 979 | stack overflow | 22.4 s, 447 MB |
| generated in the loop | 13 415 | 40 259 | 2 611 288 | **104.3 s, 9.3 GB** | 8.5 s, 224 MB |

`ccomp` compiles the production artifact.  Emission itself is 4 minutes and
0.5 GB of Lean.

## 7. What this establishes, and what it does not

Built and proved (`propext, Classical.choice, Quot.sound`, no `sorry`, no
`native_decide`, ten new `#print axioms` lines in `scripts/AxiomAudit.lean`):

* `Ports/R2SegSieve.lean` — `r2Program_wf` and `r2Program_compiled`, so
  `AProgram.evalCC_compile` applies and the emitted C computes exactly
  `denote`; plus the four-mode kernel check against trial division, which the
  in-loop power generation also exercises (the check's table is `2, 3`, and
  the loop produces `4`, `8` and `9` itself);
* `bench/R2SegEmit.lean`, `bench/ref_r2.c`, and the artifacts of §5.

Not proved, exactly as in `ArraySegSieve` and `PsiSegSieve`: that `denote`
*is* the residue — that the three planes compute the factorisation, that the
accumulator is `2^S·R₂*`, and that a zero output means the reduced family
holds.  That is an algorithmic-correctness statement, checked here by §4(a)–(d).

**And, most importantly: computing this family corroborates Lemma 6.2, it does
not discharge it.**  The trust question is about provenance, and the
computation cannot answer it:

* Ramaré–Zúñiga Alterman 2024 (arXiv:2408.05969v2, p. 10) states Lemma 6.2 for
  `3 ≤ X ≤ 2.1·10¹⁰` and introduces it with "Let us recall [13, Lemma 6.3]";
* [13] is Ramaré, Acta Arith. 157 (2013), whose Lemma 6.3 (p. 374) reads:
  `|R₂*(D)| ≤ 1.80·√D log D` for `3 ≤ D ≤ 1.1·10⁸`, and `≤ 1.93·√D log D` for
  `1.1·10⁸ ≤ D ≤ 1.8·10⁹`.  The cited range is **11.7× smaller**, and the
  cited constant below `1.1·10⁸` is `1.80`, not `1.93`;
* the paragraph after that lemma says the `10¹⁰` computation was *not* run
  ("On letting this script run longer (about twenty days), I would most
  probably be able to show that the bound `|R₂*(D)| ≤ 2√D log D` holds when
  `D ≤ 10¹⁰`") — and even hypothetically claims the constant `2`;
* arXiv v1 of the 2024 paper printed `1.8·10⁹` in Lemma 6.2; v2 changed that
  one number to `2.1·10¹⁰` and nothing else.  The paper's own use of the lemma
  needs only `2·10⁹`, so `2.1·10⁹` would have covered it.

A clean run of this artifact to `2.1·10¹⁰` would establish the *statement* on
the *stated* range by machine, independently of what the paper's citation
supports.  It would not make the paper's citation correct, and the axiom's
docstring on `claude_math` should keep saying so.

## 8. The full-scale run

`bench/results/manifests/r2star_2p1e10.json`.

### One artifact, not a chain

At two-and-a-bit core-hours the whole sweep fits in a single emitted, single
compiled, single executed program — so the one thing a chain can get wrong,
the carry-in, does not exist here.

```
lake env lean --run bench/R2SegEmit.lean 145000 1000000 21000 r2_prod.c
gcc   -O2 -o r2_prod_gcc r2_prod.c        #    8.74 s,  224 MB
ccomp -O2 -o r2_prod_cc  r2_prod.c        #  931.90 s, 9268 MB   (§6's wall, under load)
```

`lo = 145 000`, `L = 10⁶`, `N = 21 000`, hence `hi = 21 000 144 999`: the swept
range `[3, 21 000 144 999]` **contains** the axiom's `[3, 2.1·10¹⁰]` with
144 999 integers to spare.  `lo` has to exceed `⌊√hi⌋ = 144 914`; the head
`[1, 144 999]` is folded at emit time and reports `viol = 0`.

| | |
| --- | --- |
| emitted C | 2 611 275 bytes, 40 259 init statements, SHA-256 `47c92be0…` |
| emit | 4 min 21 s wall, 455 MB peak, `iterPerInteger = 10.531` |
| `loopCount` | 221 163 768 000 |
| array | 5 796 499 cells = 46 371 992 bytes |
| head carry-in | `d = 281 482 090 345 501`, `err = 10 983 953`, `terms = 61 171`, `viol = 0` |

### Result

**Zero violations, exit status 0, under both compilers, and all ten result
cells identical between `ccomp -O2`, `gcc -O2` and the oracle
`bench/ref_r2.c` run over the same range.**

```text
slot0 D     282 485 210 916 841      slot5 ⌊log₂⌋      34
slot1 err     1 781 404 027 878      slot6 2^…         34 359 738 368
slot2 prev   21 000 144 997          slot7 lnLo       398 757 432
slot3 terms   4 802 318 405          slot8 thr        111 525 658 352 741
slot4 ⌊√prev⌋   144 914              slot9 violations           0
```

so `R₂*(2.1·10¹⁰) = (D − 2⁴⁸)/2²⁴ = 60 214.651` with the carried enclosure
`err/2²⁴ = 106 179.954`, against a threshold `thr/2²⁴ = 6.648·10⁶`.  The
budget is 1.6 % of the threshold, so the run bounds the **real** `R₂*` with
two orders of magnitude to spare, exactly as §3 claims.

The oracle additionally reports the tightest point of the whole range:

```text
worst_ratio 1.452077   at   n = 110 102 617
```

— `|R₂*(n)|/(√n·log n) ≤ 1.4521` over `[3, 2.1·10¹⁰]`, against the axiom's
`1.93`.  (§4 saw `1.2574` over `[3, 10⁷]` and `1.3657` over `[3, 10⁸]`; the
sequence is still climbing, but slowly, and 1.93 is not close.)

### Cost, measured

The box was shared while these ran — load average 24–63 on 20 cores, swap
exhausted — so **wall time here is not a rate** and only `user` CPU is quoted.
Even `user` is inflated by shared-L3 contention, which is why the measured
figures sit above the projections rather than on them.

| | user CPU | ns/integer | ns/iteration | wall (under load) | peak RSS | exit |
| --- | --- | --- | --- | --- | --- | --- |
| `gcc -O2` | **6 628.08 s = 1.841 core-h** | 315.6 | 29.97 | 2:31:51 | 31 212 kB | 0 |
| `ccomp -O2` | **9 586.90 s = 2.663 core-h** | 456.5 | 43.35 | 3:57:15 | 30 552 kB | 0 |
| `bench/ref_r2.c` (oracle) | 1 019.60 s = 0.283 core-h | 48.6 | — | 50:24 | 27 956 kB | 0 |

against §6's projections of `241.7` ns/integer (1.41 core-h) for gcc and
`366.5` ns/integer (2.14 core-h) for ccomp: **+31 % and +24 %**.  The ratio
`ccomp/gcc = 1.446` is within 5 % of §6's `1.516`, which is the part of the
measurement that contention cannot distort, so the excess is the machine and
not the artifact.

The oracle is 6.5× faster than the CompCert-compiled artifact per integer.
That is the price of a data-independent straight-line body, and it is the
same 5–6× `array_seg_folds.md` records.

### What this establishes

The *statement* of Ramaré–Zúñiga Alterman 2024, Lemma 6.2, now holds by
machine over the whole of its stated range — `[3, 2.1·10¹⁰]` and 144 999
integers beyond it — with the loop body machine-checked (`r2Program_wf`,
`r2Program_compiled`) to be what `denote` says and the compilation performed
by CompCert.

§7's caveat is unchanged and is the important one: **this corroborates
Lemma 6.2, it does not discharge it.**  The paper's citation still does not
support the endpoint it prints, and the axiom's docstring on `claude_math`
should keep saying so.  What has changed is that the endpoint is no longer
merely asserted: it is computed.

## 9. Formal source classification

The paper repository now proves the real-valued mathematical seam in
`MathExtras/NumberTheory/Reductions/R2CoeffClassification.lean`.  Starting
from Mathlib's literal `vonMangoldt * vonMangoldt`, it proves:

* `r2JumpReal_one`: the initial cell has no sparse jump;
* `r2JumpReal_prime_pow`: every positive prime power contributes
  `-(log p)^2` (modes 0 and 2);
* `r2JumpReal_two_prime_pows_exact`: positive powers of two distinct primes
  contribute `2 log p log q` (modes 1 and 3);
* `r2JumpReal_eq_zero_of_three_le_card_primeFactors`: three or more distinct
  factors contribute zero (mode 4); and
* `r2Star_eq_linear_add_jumps`: the source summatory function is exactly the
  `2 gamma N` linear step plus those sparse jumps.

A direct source check completed in about 2.8 seconds under
`MemoryMax=1536M`, `MemorySwapMax=0`; the four printed closures contain only
`propext`, `Classical.choice`, and `Quot.sound`.  The aggregate `MathExtras`
consumer also builds with one Lean worker under a 2,304 MiB/no-swap cap.

This removes the Dirichlet-convolution/classification part of §7's gap.  The
remaining theorem is program-specific: prove that the three planes recover
the source factor count, bases, and exponents; telescope that invariant
through `r2Program.denote`; and transport the fixed-point/error tests to the
real source bound.  Until that theorem exists, the full run remains a
completed benchmark and not a discharge of the literature atom.

## 10. Formal compiled-selector refinement

`LeanCompCert/Ports/R2SegClassification.lean` now proves the next
program-specific layer.  The theorem `classSelectorBody_run` identifies the
literal 24-instruction production slice in `R2Cfg.classBody` with a pure
four-way classifier.  It covers the qualification bit, modes 0--3, active
round gating, packed stream payload, and the factors which `logBody` later
uses:

* mode 0 selects `(log n, log n)` with a negative sign;
* mode 1 selects `(log p, log n - lsum)` with a positive sign;
* mode 2 selects `(log p, log p)` with a negative sign; and
* mode 3 selects `(log p, log q)` with a positive sign.

The proof is deliberately split into flag, mode, and payload stages.  A
one-shot simplification of the same instruction list exceeded the 1,536 MiB
hard cap and was killed; the staged source check completes in under one
second under that cap and its fresh closure contains only `propext`,
`Classical.choice`, and `Quot.sound`.

This narrows the remaining denotation gap again.  The physical marking loop
must still prove that its product, logarithmic-sum, and packed-weight planes
satisfy the selector hypotheses at each live cell.  That invariant must then
be telescoped through windows, followed by the fixed-point enclosure and
real-bound transport.

## 11. Formal marking-cell refinement

`LeanCompCert/Ports/R2SegMarkingModel.lean` and the count-specific
`R2SegMarkingRaw0`--`Raw3` modules now formalize one complete logical marking
hit.  The model records the product plane, fixed-logarithm-sum plane, and the
packed distinct-count/weight plane.  It proves exact decoding of the count and
both 28-bit weights, the canonical empty-cell invariant, and preservation of
that invariant by every base-prime or higher-power hit.

The composite theorem `rawMark_encode` proves that the physical natural-word
update commutes with the logical update for every reachable cell.  Its four
packed-count cases live in separate modules: elaborating all transitions in
one broad arithmetic simplification exceeded the 1,536 MiB development cap,
whereas the split source checks and the composite check stay below it.  The
fresh composite source check takes about 0.2 seconds and peaks near 522 MiB;
its closure is `[propext, Quot.sound]`, with no `sorry` or `native_decide`.

`R2SegMarkingInstr.lean` and its staged `Weight*`, `CellRaw`, and `Cell`
consumers now discharge that literal instruction layer as well.
`markCellBody_eq_slice` identifies the helper definitionally with the
22-instruction production slice.  `markCellBody_rawMarkCount_run` proves the
exact three array writes made by that slice, with pairwise-distinct plane
addresses and all 64-bit headroom guards explicit.  The capstone
`markCellBody_markPower_run` then combines the machine theorem with
`rawMark_encode`: one actual load/scalar/store execution writes precisely the
encoding of `MarkCell.markPower`.

The packed-weight proof was split into flag, term, sum, add, commit, and
composition modules after a one-shot branch expansion exceeded the 1,536 MiB
hard limit.  With one Lean worker and swap disabled, representative fresh
direct source checks were:

| source check | elapsed | peak RSS | hard cap | result |
|---|---:|---:|---:|---|
| packed add composition | 0.20 s | 516,764 KiB | 1,536 MiB | success |
| packed full scalar calculation | 0.21 s | 531,484 KiB | 1,536 MiB | success |
| packed load/compute/store stage | 0.24 s | 539,684 KiB | 1,536 MiB | success |
| complete raw three-plane slice | 0.28 s | 537,652 KiB | 1,536 MiB | success |
| logical `markPower` capstone | 0.21 s | 539,608 KiB | 1,536 MiB | success |

Every new capstone prints `[propext, Quot.sound]`, with no `sorry` or
`native_decide`.  The production prefix has since been extended backward in
four further staged modules.  `R2SegMarkingAddress` proves that an active hit
selects `j`, `j+L`, and `j+2L`; `R2SegMarkingHit` composes that stage with the
cell theorem and is tied to the exact 30-instruction production slice.
`R2SegMarkingPhase` proves that every iteration inside the mark budget enables
that hit path, and `R2SegMarkingReset` proves both cursor-mux branches: window
start installs `q0`, `w0`, the first-power flag, and the least nonnegative
cell offset, while every non-start iteration preserves the complete
prime-power cursor.  Fresh checks of these modules remain near 530--552 MiB
under the same 1,536 MiB/no-swap cap.

The remaining marking proof is now the post-hit cursor/power advance and the
window telescope around these literal prefix theorems.  That will connect the
verified cell transition to all live cells before the selector and
fixed-point/error transport are composed.

The next LeanCompCert checkpoint after `b680dfe` completes the literal post-hit
suffix in seven memory-bounded stages.  `R2SegMarkingAdvanceFlags` proves the mutually
exclusive keep/bump/step decision; `R2SegMarkingAdvanceLoad` proves the
clamped table index and exact row load; `R2SegMarkingAdvanceDecode` proves the
packed prime/weight decoder; `R2SegMarkingAdvanceValue` proves all three
cursor-value mux branches; `R2SegMarkingAdvanceOffset` proves the retained,
new-power, and sentinel offsets with an explicit positive divisor;
`R2SegMarkingBudget` proves the final truncation guard; and
`R2SegMarkingAdvance.markAdvanceBody_eq_suffix` identifies their concatenation
with all 48 remaining production instructions.  Representative fresh direct
source peaks under the 1,536 MiB/no-swap profile are:

| staged source | peak RSS | result |
|---|---:|---|
| power decision | 562,920 KiB | success |
| index and load | 564,852 KiB | success |
| packed decoder | 556,152 KiB | success |
| value mux | 556,912 KiB | success |
| offset/remainder mux | 580,444 KiB | success |
| budget guard | 546,296 KiB | success |
| exact suffix capstone | 528,956 KiB | success |

All printed closures are foundational only (`propext` and, where required,
`Quot.sound`); the exact suffix equality itself has no axioms.  The remaining
work is composition of these staged contracts into the finite marking-window
telescope, followed by the directed fixed-point/error transport.

The complete 671-target LeanCompCert build passed in 4.85 seconds at a
1,817,416 KiB peak under the 2,304 MiB hard/no-swap aggregate profile, with
one Lean worker and zero swaps.

`R2SegMarkingAdvanceSelect.markAdvanceSelectBody_run` then composes the first
16 suffix instructions into one table-selection seam: it carries the
keep/bump/step decision through the clamped index, exact resident-row load,
and packed prime/weight decode.  Its fresh direct source check took 0.45
seconds at 548,400 KiB under the 1,536 MiB/no-swap profile, and its printed
closure is `[propext, Quot.sound]`.

With that capstone imported, the complete 673-target build passed in 4.84
seconds at 1,821,648 KiB under the 2,304 MiB/no-swap aggregate profile.

`R2SegMarkingAdvanceCursor.markAdvanceCursorBody_run` composes the 27
value-and-offset instructions into the actual next `(power, base, weight,
first-power flag, cell)` cursor.  It keeps the updated power nonzero as an
explicit premise before either remainder is evaluated.  The direct source
check took 0.29 seconds at 539,560 KiB under 1,536 MiB/no-swap, with closure
`[propext, Quot.sound]`.

The complete 675-target build passed in 4.96 seconds at 1,798,748 KiB under
the 2,304 MiB/no-swap aggregate profile.

`R2SegMarkingAdvanceTail.markAdvanceTailBody_run` joins the cursor theorem to
the five-instruction budget guard, yielding one theorem for the complete
32-instruction value/offset/budget suffix.  Its exact suffix equality has no
axioms; its semantic closure is `[propext, Quot.sound]`.  The direct check
took 0.32 seconds at 544,496 KiB under 1,536 MiB/no-swap.

The complete 677-target build passed in 4.55 seconds at 1,805,404 KiB under
the 2,304 MiB/no-swap aggregate profile.

`R2SegMarkingAdvanceStep.markAdvanceStepBody_run` composes the proved
16-instruction table-selection/decode prefix with the proved 32-instruction
cursor/budget tail.  It therefore covers the complete 48-instruction
production post-hit suffix, including derived exclusive keep/bump/step bits,
the positive updated-power guard, and both budget-failure counters.  Its exact
suffix equality has no axioms and its semantic closure is
`[propext, Quot.sound]`.  The direct check took 0.81 seconds at 567,772 KiB
under 1,536 MiB/no-swap.

The complete 679-target build passed in 5.35 seconds at 1,812,304 KiB under
the 2,304 MiB/no-swap aggregate profile.

`R2SegMarkingPrelude` begins the finite iteration layer by composing the
four-instruction phase selector with the nineteen-instruction reset mux.
Separate start and non-start theorems prove respectively the initial table
cursor installation and preservation of the live prime-power cursor.  The
exact 23-instruction prefix equality has no axioms; both semantic closures
are `[propext, Quot.sound]`.  The direct check took 0.34 seconds at
554,168 KiB under 1,536 MiB/no-swap.

The complete 681-target build passed in 4.75 seconds at 1,822,140 KiB under
the 2,304 MiB/no-swap aggregate profile.

`R2SegMarkingResident` identifies the prelude, address/cell block, and
post-hit step definitionally with all 101 instructions of `markBody`.  Since
the post-hit step is store-free, its start and non-start resident theorems
prove the exact logical `MarkCell.markPower` update across the complete body.
All exact-list equalities have no axioms and all semantic closures are
`[propext, Quot.sound]`.  The direct check took 0.32 seconds at 561,808 KiB
under 1,536 MiB/no-swap.

The complete 683-target build passed in 4.65 seconds at 1,809,916 KiB under
the 2,304 MiB/no-swap aggregate profile.

The complementary past-window path is now explicit too.
`markAddressBody_past_run` selects exactly the scratch cells at `3L`, `4L`,
and `5L`; `markAddressCellBody_past_run` proves their logical update; and
`markResidentBody_past_live_frame` proves every address below `3L` unchanged
across the complete 78-instruction resident suffix.  Fresh direct checks
peaked at 545,296, 535,144, and 562,008 KiB respectively under
1,536 MiB/no-swap, with semantic closures `[propext, Quot.sound]`.

The resulting 683-target rebuild passed in 8.15 seconds at 1,804,260 KiB
under the 2,304 MiB/no-swap aggregate profile.

`markFullBody_start_past_live_frame` and
`markFullBody_nonstart_past_live_frame` lift that sink separation through the
phase-selector/reset prelude.  Thus both window-start and later past-window
regimes frame every live plane address across all 101 `markBody`
instructions.  Their direct source check took 0.51 seconds at 579,612 KiB
process RSS.  The complete 683-target build passed in 3.74 seconds at
1,801,956 KiB process RSS.  Both ran in live transient units with
`MemoryAccounting=yes`, hard/high limits of 1,536/2,304 MiB respectively,
and `MemorySwapMax=0`; the units reported zero swap.  Process RSS is retained
alongside cgroup accounting because already-shared mapped build pages are not
newly charged to the transient unit.

The cursor seam now carries the production gate facts as well as the array
effect.  `markAddressBody_resident_pastBit` and
`markAddressBody_past_pastBit` prove the exact resident/past selector, while
`markAddressCellBody_cursor_frame` proves that the address/cell block frames
all persistent cursor and budget registers.  Fresh source checks for the
address and address/cell modules took 0.40 and 0.39 seconds at 572,628 and
576,384 KiB process RSS respectively under the 1,536 MiB/no-swap profile.

`markResidentBody_resident_cursor_run` composes those facts with the complete
48-instruction advance theorem.  On a resident hit it proves that the prime
power row is preserved, `j` advances by the current power, and the two budget
counters receive exactly the production `budgetFailure`.  Its direct source
check took 0.30 seconds at 540,292 KiB process RSS, with closure
`[propext, Quot.sound]`.  The complete 685-target build passed in 10.27
seconds at 1,816,776 KiB process RSS.  Both checks used live transient units
with their 1,536/2,304 MiB high and hard limits, `MemoryAccounting=yes`, one
Lean worker, and `MemorySwapMax=0`; both reported zero swap.

`R2SegMarkingCursorPast.markResidentBody_past_cursor_run` closes the
complementary cursor branch across the complete 78-instruction suffix.  It
exposes the exact production bump-or-step selection, clamped table cursor,
packed-row decode, selected next multiple, budget counters, and post-sink
array.  Its direct source check took 0.33 seconds at 546,560 KiB process RSS,
with closure `[propext, Quot.sound]`.  The complete 687-target build passed in
4.85 seconds at 1,816,596 KiB process RSS.  Both ran in live transient units
under the 1,536/2,304 MiB hard/no-swap profiles and reported zero swap.

The remainder of a marking round is now staged rather than reduced as one
large expression.  `R2SegMarkingClassFrame` covers the exact 62-instruction
classifier, its three scratch-sink clears, and its disabled stream push; its
direct source check took 2.03 seconds at 616,472 KiB process RSS.
`R2SegMarkingLogFrame` covers all 158 log instructions, including the five
zero failure commits, the zeroed log-round counter, and the framed read
cursor; its final direct check took 6.35 seconds at 644,412 KiB.
`R2SegMarkingTail` proves the exact non-boundary round increment and retained
window/cursors in 0.36 seconds at 576,212 KiB.  Finally,
`R2SegMarkingPost.markPostBody_run` composes class, log, and tail into the
complete post-mark schedule in 1.83 seconds at 594,288 KiB.  Every semantic
closure is `[propext, Quot.sound]`; the exact list equalities use no axioms.

With the new modules imported by the umbrella, the complete 695-target build
passed in 6.45 seconds at 1,809,576 KiB process RSS.  All source checks used
the 1,536 MiB hard/high limit; the aggregate used 2,304 MiB.  Every run used
one Lean worker, `MemorySwapMax=0`, and reported zero process swaps.

`R2SegMarkingFullCursor` lifts the resident suffix cursor contract through
the complete phase-selector/reset prelude.  Separate boundary-start and
ordinary-round theorems now cover all 101 `markBody` instructions: the first
installs the initial packed row before advancing its multiple, while the
second preserves the incoming row before the same exact resident advance.
Both transport the production budget failure into the aggregate and marking
counters and have closure `[propext, Quot.sound]`.  The direct source check
took 2.28 seconds at 551,028 KiB process RSS under the 1,536 MiB/no-swap cap.
The complete 697-target build passed in 6.84 seconds at 1,822,708 KiB under
the 2,304 MiB aggregate cap, again with one worker and zero swap.

`R2SegMarkingFullPastCursor.markFullBody_past_cursor_run` lifts the exact
past-window bump-or-step transition through the complete literal prelude
without duplicating its large word-readiness contract.  It names the
post-prelude state explicitly, which the proved start/non-start prelude APIs
supply, and identifies the resulting execution with all 101 `markBody`
instructions.  Its closure is `[propext, Quot.sound]`; the direct check took
0.23 seconds at 541,472 KiB under the 1,536 MiB/no-swap cap.  The complete
699-target build passed in 4.54 seconds at 1,818,604 KiB under the 2,304 MiB
aggregate cap with one worker and zero swap.

`R2SegMarkingScheduled` closes the exact one-body scheduling seam.  It proves
that executing `body` is executing `markBody` followed by `markPostBody`, and
provides a polymorphic postcondition transport so the large branch contracts
need not be restated or re-elaborated during finite induction.  Both closures
are `[propext]`.  The direct check took 0.15 seconds at 535,624 KiB; the live
326-job umbrella consumer passed in 0.94 seconds at 1,754,176 KiB under the
same one-worker, 1,536/2,304 MiB, no-swap profiles.

`R2SegMarkingRoundPosition` supplies the first size-independent finite
marking telescope over the literal production schedule.  A complete body
strictly inside the marking budget advances `rR` exactly once and preserves
`rW`; induction lifts this to an arbitrary index list and then to the exact
`List.range`/`List.foldl` schedule consumed by the denotational bridge.  The
semantic closures are `[propext, Quot.sound]`.  The direct source check took
1.00 seconds at 598,048 KiB process RSS under the 1,536 MiB/no-swap cap.  The
live 327-job umbrella consumer passed in 1.63 seconds at 1,752,632 KiB under
the 2,304 MiB aggregate cap, with one worker and zero process swaps.

`R2SegMarkingInit` now proves the exact finite seed-list execution and its
marking cursor position, while `R2SegMarkingDenotePrefix` carries that result
through the public program denotation.  Fresh direct source checks took 0.24
seconds at 558,876 KiB and 0.21 seconds at 553,156 KiB respectively.  Both
used the one-worker 1,536 MiB hard/high, no-swap profile and both have closure
`[propext, Quot.sound]`; no decision-procedure axiom is introduced.

`R2SegDenoteSegments` now extracts every arbitrary finite loop slice from one
successful program denotation and specializes that theorem to each complete
production window.  It separately exposes the literal epilogue, its total
`arun` state, and the exact observed output.  Thus the forthcoming
array/cursor invariant can telescope one opaque window at a time without
reducing the `2.1·10^10` source trace or assuming partial definedness again.
The direct source check peaked at **112,914,432 charged bytes** and the focused
85-job target at **130,691,072 charged bytes** under the one-worker 2/3 GiB
no-swap profile; both had zero pressure, hard-limit, OOM, or swap events.
Fresh axiom prints are `[propext, Quot.sound]` for the segment theorems and
`[propext]` for the epilogue theorems.

## 12. Fixed-point real telescope and dependency isolation

`LeanCompCert.Verified.LogFixedBounds` is a deliberately downstream structural
module.  It proves that the `S` emitted fractional bits are below `2^S` and
therefore that `logFix S n < 63·2^S` for every `n < 2^63`.  Keeping this
storage theorem out of `LogFixed` is important build engineering: changing the
circuit module invalidates the monolithic `PsiSegSieve` emitter, whereas a
change to `LogFixedBounds` does not.

The focused four-job target completed in **1.6 seconds** at **193,441,792
charged bytes** under one Lean worker, `MemoryHigh=2G`, `MemoryMax=3G`, and
`MemorySwapMax=0`, with zero pressure, hard-limit, OOM, or swap events.

The paper repository's downstream
`MathExtras.NumberTheory.Reductions.R2FixedPointSoundness` supplies the real
telescope at the actual `S = 24` production scale:

```
lnFix 24 n ≤ 2^24 log n ≤ lnFix 24 n + 4,
gammaStep 24 ≤ 2^24 (2γ),
a193 / 2^16 ≤ 1.93,
⌊√n⌋ ≤ √n.
```

It also transports the literal jump products through the program's final
right shift.  The single product used by modes 0/2 and the doubled product
used by modes 1/3 are each bracketed between the stored natural quotient and
the source-scaled real product, with the explicit four-ulp product width and
one final-division ulp.  Prime-power and two-distinct-prime-power corollaries
are stated directly in terms of the live `r2JumpReal`, so the remaining
whole-state induction need not reopen von Mangoldt convolution or real
multiplication.

The companion source proof now also verifies the exact production error
charge.  It proves that `ln2Up 24` is an upward fixed-point enclosure of
`log 2`, transports `n < 2^(log2 n + 1)` through the literal `>> (24 - 4)`
quotient, and shows that the following `+2` covers both the final product
division and the full four-ulp width in every single or doubled jump mode.
Thus the remaining induction can carry the program's existing `err` word
directly rather than introducing an analytic error oracle.

The source bridge now packages those inequalities into direct contracts for
negative prime-power events and positive two-prime-power events, followed by
generic signed accumulator-step lemmas.  The other running component is also
two-sided: a 64-term Euler--Maclaurin enclosure proves that the downward
`gammaStep 24` rounding loses strictly less than one accumulator ulp per
integer, exactly the slack supplied by the checker's literal `+ n`.

`R2SegLogAccumulator` supplies the machine-side composition.  It identifies
instructions 279--285 and 316--320 plus the term counter as literal slices of
`R2Cfg.logBody`, proves their exact total scalar semantics, and lifts the
results to `AState` with full array frames.  The 42 intervening instructions
are proved to preserve the event payload, sign, finish gate, error, count, and
array, and the complete 58-instruction interval is composed into one exact
signed carry transition.  The latest source check took **1.5 seconds /
139,628,544 charged bytes**; the focused live target took **1.6 seconds /
168,714,240 charged bytes** with its dependency cone cached (the preceding
cold 87-module build took 24.7 seconds / 172,363,776 bytes).  All memory-event
counters were zero.

`R2SegLogFactors` closes the adjacent classifier-to-product seam: the literal
13-instruction block 266--278 is proved to compute exactly
`ClassResult.jumpFactors`, with an array-state lifting theorem.  Its capped
source check took **1.1 seconds / 113,889,280 charged bytes**, with all memory
events zero.  Its focused live target took **1.1 seconds / 140,111,872
charged bytes**, also with zero events.

The two-sided natural-log result uses the exact 64-bit `L2` literal, an
ordinary-kernel 128-term near-one Taylor enclosure for `log 2`, the proved
two-ulp `logFix_bracket`, and an explicit final-division remainder.  Its
latest source check completed in **8.0 seconds** at **792,793,088 charged
bytes**, and its live consumer target completed in **10.9 seconds** at
**906,772,480 charged bytes**, under the same 2/3 GiB no-swap profile.  Every
memory event counter was zero.  No native evaluator or new trust declaration
is introduced.

As a regression control, placing the structural theorem in `LogFixed` was
tested and rejected: it triggered a rebuild of `PsiSegSieve`, crossed the 2
GiB soft threshold, and reached 2.9 GiB before the contained compile was
stopped.  The downstream-module layout is the retained route.

The same investigation found the larger cause: three closed whole-program
`by decide` examples were embedded at the bottom of each production emitter.
They were not proof dependencies, but every source edit forced their complete
kernel reduction.  Under the 2/3 GiB no-swap profile the isolated `ψ` check
reached **2,894,848,000 charged bytes** after ten minutes and was stopped
before the hard ceiling.  Those reductions are retired in favor of the proved
`AProgram` compiler/denotation chain and the existing CompCert/gcc/reference
accepting and rejecting controls recorded above.

The cheap, independent emit-time checks remain in
`PsiSegSieveChecks` and `R2SegSieveChecks`; fresh source checks peaked at
**110,145,536** and **95,125,504 charged bytes** respectively with zero memory
events.  With the reductions off the production path, `PsiSegSieve` compiled
from source in **1.7 seconds / 178,335,744 bytes**, and the live
`R2SegSieve` target in **3.5 seconds / 223,911,936 bytes**, both with every
memory event counter zero.  This is the retained memory-safe build layout.
