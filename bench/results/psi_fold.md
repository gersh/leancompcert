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

## 6. The artifact

`LeanCompCert/Ports/PsiSegSieve.lean` is the residue as an `AProgram` of the
proved fragment.  Against `Ports/ArraySegSieve` — which is **untouched** — it
changes three things.

**A fourth loop phase.**  A window's period is `markSteps + segLen + logSteps`.
The accumulation phase no longer decodes `μ`: it reads one plane, tests
`prod = 0` (never marked, hence prime, because `lo > ⌊√hi⌋`), merges the
emit-time prime-power table in by one cursor and one comparison, and
**compacts** the surviving test points into a stream of `(position, payload)`
pairs.  The log phase then drains that stream, one squaring round per
iteration, `S` rounds per entry, the entry boundary carried by a wrapping
counter rather than by a division.  At the `S`-th round it converts to natural
logarithm, advances the residual, and runs both clauses.

`logSteps = S · streamCap` is a **budget**, set at emit time to the exact
prime count of the *first* (densest) window plus `6%`.  Both ways it can be
wrong are checked in the loop: a push past `streamCap` clamps to a sink and
counts a violation, and a log phase that ends with the stream undrained counts
another.

**The two-word accumulator.**  `Verified/AddWide.lean` proves the four
instructions — `add`, `lt`, `add`, `add`, the carry by proved comparison —
and their one-word specializations, which are three instructions each and are
what the loop actually runs (`+ lnFix(p)` at a test point, `− 2^S·gap`
between two).  `Verified/LogAccum.lean` composes that with `logFold_bracket`:

```
2 ^ A  ≤  (Π p) ^ (2^S)  ≤  2 ^ (A + 2·#terms),    A = wval (sumWide …)
```

where `A` is the value of the **pair of `u64` registers**, not of an
idealized `Nat`.  The error term `2·#terms` is unchanged — the carry chain
contributes nothing to it, because `logFoldWide` says the accumulation is
exact rather than approximate.  The two side conditions are
`logFix_lt : logFix S n < 2^(S+6)` (one term is one word, which is why
`S ≤ 58`) and `#terms · 2^(S+6) < 2¹²⁸` (`2⁹²·⁴` at `S = 48` over
`π*(10¹³)` terms, so 35 bits of headroom).

**One-word comparisons.**  A clause reads `D + 4·terms ≤ ⌊0.79059276·2^S⌋·⌊√n⌋`
and the right-hand side is a 70-bit product.  Instead of a 128-bit multiply and
a 128-bit compare, both sides are shifted right by `16`:
`t = (D.lo >>> 16) + (D.hi <<< 48)` is exact because the overflow guard keeps
`D.hi < 2⁸`, and the constants are pre-shifted at emit time — **downward on
both sides**, so each test is strictly stronger than its clause.  Passing
clause 1 certifies

```
(ψ(n) − n)/√n  ≤  0.79059276 + 2¹⁶/(2⁴⁸·√n)  =  0.79059276 + 2.3·10⁻¹⁰/√n
```

against a margin of `10⁻⁸`: seven orders of magnitude of slack, for `7`
instructions instead of about `40`.  Clause 2 loses nothing at all
(`2¹⁶·⌊c/2¹⁶⌋ ≤ c`).

### What the loop checks, beyond the two clauses

Six guards, all gated to the finishing round and all summed into the same
counter, so a nonzero result is a failure of *something*:

| guard | what it rules out |
| --- | --- |
| `wcur < streamCap` | a window producing more test points than budgeted |
| `ecur = wcur` at turnover | a log phase that did not drain the stream |
| `n − prev < 2¹⁶` | a prime gap too large for the one-word `2^S·gap` |
| `n < (s+1)²` after the step | `⌊√n⌋` needing more than one increment |
| `n < 2^(ex+1)` after the step | `⌊log₂ n⌋` needing more than one increment |
| `D.hi < 2^(S+24−64)` | the accumulator leaving `[0, 2^(S+24))` |

The one precondition *not* checked in the loop is `lo > ⌊√hi⌋`, which is what
makes "never marked" mean "prime"; the emitter refuses to build an artifact
that violates it.

## 7. Measurements

`bench/PsiSegEmit.lean` emits; one core, `user` time, mean of three, with two
other jobs running.  `lo` is `⌊√hi⌋ + 1` in each case and the head `[1, lo−1]`
is folded at emit time with the same `logFix`.

| `hi` | `lo` | `L` | iters/integer | body | ccomp s | ns/int | gcc s | ns/int |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `10⁶` | 1 001 | 99 900 | 8.954 | 246 | 0.230 | 230.2 | 0.147 | 146.9 |
| `10⁷` | 3 201 | 99 968 | 8.328 | 246 | 2.180 | 218.1 | 1.323 | 132.3 |
| `10⁸` | 10 001 | 999 900 | 7.544 | 246 | 20.187 | 201.9 | 12.087 | 120.9 |

`ccomp` and `gcc` produce byte-identical output at all three sizes.  The
artifact agrees with `bench/ref_psi.c` **bit for bit** on the residual:

| `hi` | `D` (artifact, advanced to `hi`) | `D` (`ref_psi.c`) | terms | `ψ(hi)` |
| --- | --- | --- | --- | --- |
| `10⁶` | `−116 362 460 288 916 769` | same | 78 734 | `999 586.597496` |
| `10⁷` | `−411 121 409 175 809 375` | same | 665 134 | `9 998 539.403346` |
| `10⁸` | `−494 608 778 557 207 013` | same | 5 762 859 | `99 998 242.796627` |

and reproduces the published `ψ` values.  Violations are `0` in all three: both
clauses and all six guards hold over the checked range.  (`ref_psi.c` reports
three clause-2 violations because it starts at `n = 1`, where clause 2 is
*attained* — `(ψ(1) − 2)/√2 = −√2` exactly.  That is the head the artifact
leaves to the exact emit-time fold, for precisely this reason.)

Artifact size and compile time are set by the body and the emit-time tables,
not by `hi`:

| `hi` | C bytes | init statements | ccomp `-O2` |
| --- | --- | --- | --- |
| `10⁶` | 117 921 | 1 483 | 0.26 s |
| `10⁷` | 230 047 | 3 325 | 0.68 s |
| `10⁸` | 556 477 | 8 644 | 3.61 s |

At `10⁸` the init block is dominated by the prime-power table, which spans
`[10⁴, 10⁸]` and has 1 353 entries.  A *chained* window at `10¹³` contains
almost none of them — see below.

### The fitted law, and `10¹³`

The repository's law is `ns/integer = (iterations/integer) × (body) × κ`.
Fitting `κ` on this program's own three points:

| | `10⁶` | `10⁷` | `10⁸` | mean |
| --- | --- | --- | --- | --- |
| `κ` (ccomp) | 0.1045 | 0.1064 | 0.1088 | **0.1066 ns** |
| `κ` (gcc) | 0.0667 | 0.0646 | 0.0651 | **0.0655 ns** |

— consistent to `±2%`, and both below the `0.1283`/`0.1033` calibrated on the
Mertens body, because the log phase is pure register ALU with no memory
traffic.

The configuration at `10¹³` (`PsiCfg.ofScale 48 10¹³ 10⁶ 1000`, i.e. `10⁹`
integers per artifact) is computed, not guessed:

```
rootCap    = 3 162 435      tableLen   = 227 655      (computed by the root phase)
markSteps  = 3 309 034      3.309 iterations/integer
segLen     = 1 000 000      1.000
streamCap  = 35 591         logSteps = 1 708 368  ->  1.708
                                                     -------
                                              total  6.041 iterations/integer
primePowers in range = 8            memory = 9 MB
```

| | ns/integer | `10¹³` on one core |
| --- | --- | --- |
| `M`,`Q` residue (measured law) | 70 | 8.1 days |
| **`ψ` residue, two-word accumulator** | **158.4** (ccomp), 97.3 (gcc) | **18.3 days**, 11.3 days |
| ratio to `M`,`Q` | `2.26×` | |

The earlier §2 estimate was `138 ns` and `16.0 days` from a `193`-instruction
body.  The built body is `246`: the extra `53` are the eleven-instruction
`ln 2` multiply written out, the guards (which the estimate did not include at
all), and the stream's own bookkeeping.  The `6%` stream margin costs `0.10`
iterations per integer of the `6.041`; a tight budget would give `152 ns` and
`17.6 days`, and is available to anyone willing to re-run a window that
reports an overflow.

**No full-scale run was started.**

### 2026-08-14 proof-oriented multiplier update

The clause-1 products now use two instances of the library's proved generic
half-limb `u64 × u64 → u128` multiplier.  This replaces the two bespoke
optimized circuits and increases the body from 246 to 254 instructions without
changing the exact integer comparison.  Scaling the measured law above by
`254 / 246` gives **163.6 ns/integer**, or **18.9 CompCert core-days** through
`10¹³`; the corresponding gcc projection is about **100.5 ns/integer** or
**11.6 core-days**.  These are conservative projections from the existing
calibration, not a new full-range run.  The emitted multiplication and
comparison slices have exact denotation theorems in `PsiSegClauseCheck`.

## 8. What is built and what is not

Built and proved (`propext, Classical.choice, Quot.sound`, no `sorry`, no
`native_decide`):

* `Verified/LogFixed.lean` — `sq62_eq`, `logIter_spec`, `logFix_bracket`,
  `logFold_bracket`, `errB_le_48`, plus six kernel checks;
* `Verified/AddWide.lean` — `carry_bit`, `borrow_bit`, `addWide_spec`,
  `addWide_exact`, `subWide_exact`, `sumWide_spec`: the two-limb accumulator is
  `mod 2¹²⁸` arithmetic exactly, and a list of `u64`s whose total is below
  `2¹²⁸` accumulates with no hypothesis about how the carries interact;
* `Verified/LogAccum.lean` — `logFix_lt`, `logFold_le`, `logFoldWide`,
  `logFoldWide_bracket`: the bracket restated over the machine accumulator,
  error term intact;
* `Ports/AddWidePort.lean` — `addWideBody_denote`, `addWideLoBody_denote`,
  `subWideLoBody_denote`: the four (resp. three) fragment instructions compute
  those functions, stated in the form a loop body consumes (accumulator limbs
  out, every other register untouched); plus `accProgram_compiled` and kernel
  checks that the carry really crosses limbs;
* `Ports/LogFixPort.lean` — the 21-instruction round as a fragment `Program`;
* `Ports/PsiSegSieve.lean` — `psiProgram_wf` and `psiProgram_compiled`, so
  `AProgram.evalCC_compile` applies and the emitted C computes exactly
  `denote`; plus kernel checks of the whole four-phase loop at `S = 4`,
  `[25, 32]`, against a **trial-division** reference that shares no code with
  it — `lambdaFix` divides, where the artifact reads an unmarked sieve cell and
  a merged table.  Both the residual and the term count are checked, and the
  window's five test points `25 = 5²`, `27 = 3³`, `29`, `31`, `32 = 2⁵`
  exercise the prime stream and the prime-power merge together;
* `bench/PsiSegEmit.lean`, and the three artifacts of §7.

Not proved, exactly as in `ArraySegSieve`: that `denote` *is* the residue —
that the sieve computes primality, that the accumulator is `ψ(n) − n`, and
that a zero output means the reduced family holds on the range.  That is an
algorithmic-correctness statement about the sieve; it is checked here by kernel
evaluation against the trial-division reference at a tiny size, and by the
artifact against `bench/ref_psi.c` at `10⁶`, `10⁷` and `10⁸`, where the
residual agrees to the last bit.

`Ports/ArraySegSieve` is **untouched**, so the `mertens` artifact still agrees
with `bench/ref_seg.c` slot for slot on all seven slots (`M(10⁷) = 1037`,
`Q(10⁷) = 6 079 291`), and `check-native` still passes 10/10 with
`--force`.

### The one fragment question this raised, and how it was closed

The mantissa reset shifts by a **register**, `n <<< (62 − ⌊log₂ n⌋)`, and the
fragment's `shl` is total (`(a <<< b) mod 2⁶⁴` for every `b`) while C's is not
(undefined at a width of 64 or more).  `62 − ⌊log₂ n⌋` is provably in `[0, 62]`,
so the two agree — but only because of an invariant, not because of the types.
Rather than extend the fragment with a checked shift, the emitted amount is
masked with `& 63`: one instruction, a no-op under the invariant, and it makes
the emitted C total rather than merely correct.  `Ports/LogFixPort`'s own
register shift needs no mask, its amount being a comparison result.

Nothing else in the design wanted an instruction the fragment lacks.  The
two-limb add needed no carry flag (the comparison trick supplies it), the
`ln 2` conversion needed no 128-bit multiply (eleven instructions of 32-bit
halves suffice, because `logFix < 2⁵⁴`), and the clause comparisons needed no
128-bit compare (the shifted domain is one word).
