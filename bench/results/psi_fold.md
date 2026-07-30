# `psi` and `R₂*`: the two reduced families that are not integer folds

`bench/results/array_seg_folds.md` covers the four families whose residue the
segmented Möbius sieve already produces — `M(n)`, `Q(n)`, `Σ μ(m)/m`.  Two of
the six on-cone reduced families are not of that shape, because they sum
**logarithms of primes**:

| axiom | quantity | range | majorant |
| --- | --- | --- | --- |
| `ch25_lemma_9_2_psi` | `(ψ(n) − n)/√n` | `[1, 10¹³]` | `(−√2, 0.79059276]` |
| `ramare_zuniga_lemma_6_2` | `\|R₂*(n)\|` | `[3, 2.1·10¹⁰]` | `1.93·√n·log n` |

Read from `claude_math`, branch `a7/triage-13-cone-axioms`:
`MathExtras/NumberTheory/Reductions/StepMinusLinearReductions.lean`
(`ChirreHelfgottLemma92NatFamily`) and
`MathExtras/NumberTheory/Reductions/FiniteCiteFloorReductions.lean`
(`RamareZunigaLemma62NatFamily`), with `r2Star` and `r2Coeff` from
`MathExtras/NumberTheory/Mertens/RamareEq22.lean`.

## 1. The logarithm

`LeanCompCert/Verified/LogFixed.lean` computes `logFix S n = ⌊2^S·log₂ n⌋`,
`LeanCompCert/Ports/LogFixPort.lean` realises it in the proved fragment in 21
instructions per round with **no division of any width**, and `bench/ref_psi.c`
is the same arithmetic in C.

The bound is an *integer* statement, and deliberately so.  This repository has
no Mathlib, so `Real.log` cannot be written here; but the natural statement of
what the algorithm computes needs no real number at all:

```
2 ^ logFix S n  ≤  n ^ (2 ^ S)  <  2 ^ (logFix S n + 2)          -- logFix_bracket
```

Take `log₂` of that line and divide by `2^S`: it says `logFix S n / 2^S ≤
log₂ n < (logFix S n + 2)/2^S`, i.e. two units in the last place, two-sided.
The two powers are astronomically large terms but they are never evaluated —
they occur only inside a proved inequality.  Converting to `Real.log` is a
one-line consequence on the `claude_math` side, where Mathlib exists.

Kernel checks: `logFix 20 n` is `⌊2²⁰·log₂ n⌋` **exactly** at
`n = 2, 3, 5, 7, 1000003, 999999937`; the last is `31 349 646`.

### The accumulated error is in the theorem

The bracket multiplies, so the accumulation is exact:

```
2 ^ (Σ logFix S p)  ≤  (Π p) ^ (2 ^ S)  ≤  2 ^ (Σ logFix S p + 2·#terms)
                                                              -- logFold_bracket
```

The width of the enclosure of `2^S·log₂(Π p)` is **exactly two ulps per
factor**, appearing as the literal subterm `2 * l.length`.  There is no hidden
`ε`, no independence assumption and no cancellation argument.  Two further
ulps come from the conversion to natural logarithm (one from the multiply by
`⌊2⁶⁴·ln 2⌋`, one from that constant's own truncation), so the per-term window
in the artifact is `4` ulps of `2^−S`.

The error budget inside a single `logFix` — the relative slack of the running
mantissa, which squaring doubles — is defined by its own recursion
`D ↦ 2D + D²/2⁶² + 9`, so the induction step is definitional and the whole
quantitative claim reduces to `errB 48 = 2 533 970 701 664 099 ≤ 2⁶²`, one
`decide`.  That is `5.5·10⁻⁴` of a mantissa unit at `S = 48`: three orders of
magnitude of slack under the `+2`.

## 2. A single 64-bit accumulator cannot carry `ψ` to `10¹³`

This is the load-bearing arithmetic, and the answer is negative.

`π*(10¹³) = 346 065 765 710` prime powers (`π(10¹³) = 346 065 536 839` primes
plus `228 871` proper prime powers).  The accumulator must be in **residual**
form `D(n) = Σ lnFix(p^k) − 2^S·n`, because the direct form `2^S·ψ(n)` reaches
`2^S·10¹³` and caps `S` at 20.  In residual form the family itself bounds
`|D| ≤ 2^S·√2·√n = 2^S·4.472·10⁶`:

| `S` | `\|D\|` max | fits one u64? | enclosure width, absolute | width `/√n` at `10¹³` |
| --- | --- | --- | --- | --- |
| 32 | `1.92·10¹⁶` | yes | `322.3` | `1.02·10⁻⁴` |
| **40** | `4.92·10¹⁸` | **yes** | `1.259` | `3.98·10⁻⁷` |
| 41 | `9.83·10¹⁸` | **no** | `0.630` | `1.99·10⁻⁷` |
| 46 | `3.15·10²⁰` | no | `0.0197` | `6.22·10⁻⁹` |
| **48** | `1.26·10²¹` | no | `4.92·10⁻³` | `1.56·10⁻⁹` |
| 64 | `8.25·10²⁵` | no | `7.50·10⁻⁸` | `2.37·10⁻¹⁴` |

The printed constant `0.79059276` is an outward rounding of the paper's
`0.79059275…`, so the margin the family leaves is **at most `10⁻⁸`** in the
ratio.  Requiring `4·π*(n)/2^S ≤ 10⁻⁸·√n` at the binding point `n = 10¹³`
gives `2^S ≥ 4.377·10¹³`, i.e.

> **`S ≥ 45.32` is required; one 64-bit residual word allows `S ≤ 40`.
> A single u64 is short by a factor of 2⁵·³ ≈ 40.**

At `S = 40` the artifact's own uncertainty is `4.0·10⁻⁷` in a quantity the
paper prints to eight decimals: it could not distinguish `0.79059276` from
`0.79059236`.  **`ψ` needs 128-bit accumulation.**  That is cheap — the
residual is 71 bits at `S = 48`, so two words and a carry, about six
instructions — but it is a representation decision, not an engineering
detail.  `S = 48` with two words gives `1.6·10⁻⁹`, one sixth of the last
printed digit; `S = 64` (the scale the GPU campaign uses) gives `2.4·10⁻¹⁴`
for `1.33×` the squaring rounds.

`R₂*` is the opposite case.  Its majorant at `n = 2.1·10¹⁰` is `6.65·10⁶` and
the observed worst ratio is `1.4519` against `1.93`, an absolute margin of
`1.65·10⁶`.  With `≈3.6·10⁹` terms and a per-term error of `4·log n` ulps
(each term is a *product* of two logarithms), `S = 24` gives a width of
`4.1·10⁴` — forty times inside the margin — and `2^24·6.65·10⁶ = 1.1·10¹⁴`
fits one word with room for another `2¹⁶`.  **Precision is not the obstruction
for `R₂*`; see §5.**

## 3. Prime powers are not droppable, and where they go

`ψ(n) = Σ_{p^k ≤ n} log p` runs over prime powers, and the segmented sieve
enumerates only primes.  They cannot be dropped and they cannot be deferred:

* over the whole range they contribute `Σ_{k≥2} θ(n^{1/k}) ≈ 2√n = 6.3·10⁶`
  at `n = 10¹³`, against a budget of `0.03`;
* within one segment of `L = 10⁸` at `n = 10¹³` there are about
  `L/(2√n) = 16` of them, contributing about `240` — still four orders of
  magnitude over budget, so pushing a segment's worth to the segment
  boundary is not sound either.

They must sit at their exact positions.  The mechanism costs almost nothing:
there are only `228 871` prime powers below `10¹³` in total, all with
`p ≤ √hi`, so a window's list is computed **at emit time** in Lean — value and
weight `logFix S p` (not `logFix S (p^k)`: `Λ(p^k) = log p`) — and merged into
the log phase's prime stream by one extra cursor and a comparison, about ten
instructions.  `bench/ref_psi.c` does exactly this and is the oracle for it.

## 4. The test points are the prime powers, not the integers

Between consecutive prime powers `ψ` is constant and `n` increases, so
`(ψ(n) − n)/√n` strictly decreases.  Clause 1 of the reduced family is
therefore worst immediately *after* a jump and clause 2 immediately *before*
the next one:

* clause 1 is tested at `n = q` for every prime power `q`;
* clause 2 is tested at `n = q − 1`, plus the range's right endpoint.

That is `2·π*(n)` test points, not `2n` — and every one of them is a point the
log phase already visits.  **No per-integer test phase is needed at all**,
which is what makes the fourth phase affordable.  `⌊√n⌋` is maintained
incrementally along the prime stream: consecutive squares are `2√n = 6.3·10⁶`
apart at `10¹³` while prime gaps there are `≈ 30`, so one conditional
increment per test point suffices for `lo ≥ 10⁶`.

The head `[1, 10⁶]` is left to an exact kernel computation, and it has to be:
clause 2 is *attained* at `n = 1`, where `(ψ(1) − 2)/√2 = −√2` exactly, and
the artifact's `⌊√n⌋` thresholds cannot represent equality there.  Above
`n = 1000` the observed worst is `−0.8032` at `n = 1423` — a factor `1.76`
of margin — so the flooring costs nothing in the checked range.

## 5. `R₂*` is a different computation, not a harder logarithm

`r2Coeff(k) = (Λ∗Λ)(k) − Λ(k)·log k + 2γ`.  Evaluating the convolution:

```
(Λ∗Λ)(p^a)      = (a−1)·log²p          Λ(p^a)·log(p^a) = a·log²p
(Λ∗Λ)(p^a q^b)  = 2·log p·log q        Λ(·)·log(·)     = 0
(Λ∗Λ)(k)        = 0  for k with ≥3 distinct prime factors
```

so

```
R₂*(N) = 2γN − Σ_{p^a ≤ N} log²p + 2·Σ_{p^a q^b ≤ N, p≠q} log p·log q .
```

The `2γN` term folds into the linear part of the residual exactly as
`c·n` does in the CDEM residue.  The rest is a **Dirichlet convolution**, and
that is the obstruction: the residue needs, per cell `k`, the classification
"prime power / two distinct prime powers / more", together with both prime
factors.  Against the current sieve that means

* marking multiples of `p^j` for every `j`, not just `p`, so that the small
  prime can be divided out to its full multiplicity — the mark budget goes
  from `L·Σ 1/p = 2.74·L` to `L·Σ 1/(p−1) ≈ 3.4·L` at `hi = 2.1·10¹⁰`, 24%
  more marking;
* a per-cell cofactor register and one `udiv` per mark step;
* one 64×64 multiply of two logarithms on the `≈13%` of cells that qualify.

`log p` for the small factor is free — `p ≤ √hi = 144 914`, so the `13 480`
values fit in a table the root phase can fill.  `log q` for the large factor
needs the squaring loop, on those 13% of cells, at `S = 24`: `3.2` extra
iterations per integer.

Cost: `≈ 7.6` iterations per integer against a body of `≈ 210`, i.e.
`205 ns/integer` under `ccomp`, over `2.1·10¹⁰` integers — **1.2 hours on one
core**.  `R₂*` is cheap; it is simply a sieve this repository does not have
yet.

## 6. Measurements

`bench/ref_psi.c`, one core, mean of three, with the `plattstrong` chain
running on another:

| `hi` | `L` | terms | `ψ(hi) − hi` | worst clause-1 ratio | width `/√hi` | s | ns/integer |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `10⁶` | `10⁶` | 78 734 | `−413.402504` | `0.7101614716` @ 24 137 | `1.1·10⁻¹²` | 0.0196 | 19.6 |
| `10⁷` | `10⁶` | 665 134 | — | `0.7101614716` @ 24 137 | `3.0·10⁻¹²` | 0.1245 | 12.5 |
| `10⁸` | `10⁶` | 5 762 859 | `−1757.203` | `0.7157274617` @ 30 909 673 | `8.2·10⁻¹²` | 0.9764 | 9.76 |

`ψ(10⁶) = 999 586.597496` and `ψ(10⁸) = 99 998 242.797` reproduce the
published values; both clauses pass over `[1000, 10⁸]` with no violations.

Isolating the log loop by varying `S` at `hi = 10⁸`:

| `S` | s | ns/integer |
| --- | --- | --- |
| 1 | 0.2477 | 2.48 |
| 24 | 0.5830 | 5.83 |
| 48 | 0.9683 | 9.68 |

so the `S = 48` logarithm is `7.2 ns/integer` of the `9.7`, and the marginal
cost is `0.153 ns/integer` per round of `S` at `hi = 10⁸` — i.e.
`2.7 ns` per round per prime.

### Extrapolation to `10¹³`

The fitted law is the repository's own, from
`bench/results/array_seg_folds.md`: an `AProgram` body is data-independent, so

```
ns/integer = (iterations/integer) × (body length) × κ,
  κ = 0.1283 ns  (ccomp),  κ = 0.1033 ns  (gcc)
```

both calibrated at `lo = 10¹⁰` where `3.76 × 138 × 0.1283 = 66.6 ns` against a
measured `66.5`.  For the `ψ` residue at `hi = 10¹³`:

* iterations/integer `= 3.97` (the documented sieve figure) `+ S/ln(10¹³)`
  `= 3.97 + 48/29.93 = 5.57`;
* body `≈ 193` — `93` core, `8` prime compaction into the main phase, `21`
  the log round, `12` stream advance and mantissa reset, `17` the `ln 2`
  multiply, `6` the two-word accumulate, `6` incremental `⌊√n⌋`, `20` two
  thresholds and two 128-bit compares, `10` the prime-power merge.

| | ns/integer | `10¹³` single core |
| --- | --- | --- |
| `M`,`Q` residue (measured law) | 70 | 8.1 days |
| `ψ` residue (this design) | **138** (ccomp), 111 (gcc) | **16.0 days**, 12.9 days |
| ratio | `1.97×` | |

Artifact size is set by the body length and the bootstrap table, not by `hi`:
at `L = 10⁶` the `M`,`Q` artifact is 45 474 B of C compiling in 0.06 s, so a
`193`-instruction body is `≈ 62 KB` and well inside the `ccomp` wall (the wall
was 235 000 *init* statements, and the root phase removed those).

`R₂*` at `2.1·10¹⁰`: `7.6 × 210 × 0.1283 = 205 ns/integer`, **1.2 hours**.

**No full-scale run was started.**

## 7. What is built and what is not

Built and proved (`propext, Classical.choice, Quot.sound`, no `sorry`, no
`native_decide`):

* `Verified/LogFixed.lean` — `sq62_eq`, `logIter_spec`, `logFix_bracket`,
  `logFold_bracket`, `errB_le_48`, plus six kernel checks;
* `Ports/LogFixPort.lean` — the 21-instruction round as a fragment `Program`,
  `logRoundProgram_wf`, `logRoundProgram_compiled`, five kernel checks tying
  `denote` to `logFrac` and `logFix`;
* `bench/ref_psi.c` — the complete residue including prime powers, validated
  against published `ψ` values, and the speed line.

Specified and costed here, not built: the compaction of the main phase's
primes into a stream, the fourth loop phase that drains it, and the two-word
accumulator inside `Ports/ArraySegSieve`.  `Ports/ArraySegSieve` is
**untouched**, so the `mertens` artifact still agrees with `bench/ref_seg.c`
slot for slot on all seven slots (`M(10⁷) = 1037`, `Q(10⁷) = 6 079 291`), and
`check-native` still passes.
