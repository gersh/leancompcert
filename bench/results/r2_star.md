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

The mark table is every prime power `q = p^j ≤ hi` with `p ≤ ⌊√hi⌋`, sorted by
`(p, j)`, so a cell divisible by `p^v` is marked exactly `v` times by `p`'s
entries.  Each mark writes three planes:

* `prod` — multiplied by the **base prime**, so it ends at `Π p^{v_p(n)}` over
  the small primes.  `prod ≠ n` is exactly "a prime factor above `⌊√hi⌋` is
  left", and for `n ≤ hi` there can be only one, to the first power;
* `lsum` — incremented by `lnFix p`, the fixed-point logarithm of `prod`;
* `W` — at a `j = 1` mark only: the first two distinct weights and a two-bit
  saturating count, `w1 | w2<<28 | d<<56`.

The base prime is never stored.  The table is sorted by `(p, j)` and the
`j = 1` entries carry a flag, so one register tracks it, and an entry is
**one array cell** — `value | lnFix p <<35 | first <<63`.

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
`L·Σ 1/(p−1) = 3.51·L`, 28% more marking, and the log phase runs on the
`22.4%` of cells that are mode 0 or 1.

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
| `10⁶` | 99 900 | 404 | 13.336 | 0.430 | 430.4 | 0.283 | 283.6 |
| `10⁷` | 99 968 | 1 001 | 12.565 | 4.023 | 402.4 | 2.603 | 260.4 |
| `10⁸` | 999 900 | 2 633 | 11.909 | 38.02 | 380.2 | 25.29 | 252.9 |

The repository's law is `ns/integer = (iterations/integer) × (body) × κ`.
Fitting `κ` on these three points:

| | `10⁶` | `10⁷` | `10⁸` | mean |
| --- | --- | --- | --- | --- |
| `κ` (ccomp) | 0.1015 | 0.1007 | 0.1004 | **0.1009 ns** |
| `κ` (gcc) | 0.0669 | 0.0652 | 0.0668 | **0.0663 ns** |

— consistent to `±0.6%`, and within 6% of the `0.1066`/`0.0655` that
`psi_fold.md` fitted on a different body.  Artifact size:

| `hi` | C bytes | init statements | ccomp `-O2` | gcc `-O2` |
| --- | --- | --- | --- | --- |
| `10⁶` | 112 001 | 1 226 | 0.25 s | 0.13 s |
| `10⁷` | 225 714 | 3 017 | 0.69 s | 0.29 s |
| `10⁸` | 539 252 | 7 913 | 3.02 s | 0.93 s |

## 6. The `2.1·10¹⁰` configuration, and one measurement at `10¹⁰`

The configuration is computed, not guessed.  At `hi = 2.1·10¹⁰`,
`⌊√hi⌋ = 144 913`, `π(⌊√hi⌋) = 13 415`, and the mark table is **27 421**
entries — every prime power `p^j ≤ hi` with `p ≤ 144 913`, one cell each.
With `L = 10⁶`:

```
mark budget   3.558 iterations/integer   (2.74 of it the primes, 0.79 the powers)
accumulation  1.000
log phase     4.14 at the bottom of the range, 6.15 at its peak near 1e9,
              5.90 at 1e10, 5.82 at the top
                                        ------
total         8.70 / 10.70 / 10.46 / 10.38 iterations per integer
memory        3L cells of planes + 0.6L of stream + the table = 44 MB
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
`[10¹⁰+1, 10¹⁰+2·10⁶]`:

| | measured | the law's prediction |
| --- | --- | --- |
| gcc `-O2` | **250 ns/integer** (0.50 s for `2·10⁶`) | 220 ns |
| ccomp `-O2` | 376 ns/integer (by the 1.503 ratio at `10⁸`) | 335 ns |

13% above the law, which is the three planes: at `L = 10⁶` they are 24 MB
against 24 MB of L3.  A production run should measure `L = 2·10⁵` too.

**Cost of the whole sweep**, `[144 914, 2.1·10¹⁰]`, on one core:

| | ns/integer | `2.1·10¹⁰` |
| --- | --- | --- |
| gcc `-O2` | 250 | **1.46 core-hours** |
| ccomp `-O2` | 376 | **2.19 core-hours** |

**No full-scale run was started.**

### The wall the table hits

The full-scale artifact is 5.3 MB of C with **82 266** init statements, one
per table cell write.  `gcc -O2` compiles it in 22.4 s and 447 MB.
`ccomp -O2` **stack-overflows** at the default 8 MB stack, in
`Env.IdentMap.add` — the same wall `ArraySegSieve`'s docstring records at
`10¹²` for the prime table it deleted, reached here at `2.1·10¹⁰` because each
entry carries a logarithm the root phase could not have computed.  Two exits,
neither taken here:

* raise the stack (`ulimit -s unlimited`) — see the note below;
* generate the `j ≥ 2` entries **in the artifact**: a fixed-length state
  machine walking the prime table, `v := v·p` while `v ≤ hi`, copying the
  weight, would halve the init block to the 13 415 `j = 1` entries, which is
  the size range `ArraySegSieve` already compiles.

Emission itself is 7 minutes and 0.5 GB of Lean; the earlier 54 GB was
`refR2`, the emit-time reference fold, being handed `hi = 2.1·10¹⁰` and
building a smallest-prime-factor table for it.  The driver now treats an empty
positional argument as absent.

## 7. What this establishes, and what it does not

Built and proved (`propext, Classical.choice, Quot.sound`, no `sorry`, no
`native_decide`, ten new `#print axioms` lines in `scripts/AxiomAudit.lean`):

* `Ports/R2SegSieve.lean` — `r2Program_wf` and `r2Program_compiled`, so
  `AProgram.evalCC_compile` applies and the emitted C computes exactly
  `denote`; plus the four-mode kernel check against trial division;
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
