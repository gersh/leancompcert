# Helfgott Prop. 12.2.4: what the reduction is, and what a port would cost

This is a scoping note, not a port.  `Verified/ExpFixed.lean` and
`Ports/ExpFixPort.lean` landed the primitive the table needs — a proved
fixed-point `exp`/`rpow` — and this records what remains.

## The atom

There is no declaration named `finite_check_helfgott_prop_12_2_4`.  In
`claude_math` the two real names, both in
`ext/analytic_nt/AnalyticNT/LargeSieve/RamareProp1224FiniteCite.lean`, are

* `finite_check_helfgott_prop_12_2_4_computation_source` — the axiom,
* `finite_check_helfgott_prop_12_2_4_computation_cite` — a theorem with the
  identical statement, proved `exact` from the axiom; this is the
  consumer-facing name.

The checked predicate, per pair of naturals `(q, k)`.  Write
`G_q(R) = Σ_{r ≤ R, gcd(r,q)=1} μ(r)²/φ(r)`, `L(q) = Σ_{p | q} log p / p`,
`c_E = γ + Σ_p log p /(p(p−1))`,
`f₁(q) = ∏_{p|q} (1 + p^{−2/3})·(1 + (p^{1/3}+p^{2/3})/(p(p−1)))^{−1}`,
`κ*(q) = (1 − ω*)(log q − L(q)) + (1.36 − c_E)` with `ω* = 0.627312`,
`β* = 0.023111`, and `ϖ(q)` the window floor built from `q^τ`,
`τ = 0.4 e^{−γ}`.  Then for every `q ≥ 1`, `k ≥ 1` with
`q < 3.3·10⁹` or (`210 | q` and `q < 2.2·10¹⁰`), and with
`ϖ(q) ≤ k` and `k^{1/3}κ*(q) < (q/φ(q))·7.284·(1+β*)·f₁(q)`:

```
G_q(k) − (φ(q)/q)(log k + c_E + L(q))
        + ω*·7.284·(20000k)^{−1/3}·f₁(q)   ≤   (φ(q)/q)·κ*(q).
```

That is Helfgott's (12.31) with the far-error term already replaced by its
(12.32) envelope at the extreme `t = Q/Q₀ = 20000`.

## Is the reduction sound?

**Yes, in the sense that matters, and it is not vacuous — but it is a
trust-transfer, not a proof.**

Sound, as checked against the usual traps:

* **Directions are all conservative.**  `ω* ≥ ω(ρ)` on the admissible range and
  `κ` is decreasing in `ω`, so the right-hand side is shrunk; the far-error
  term is replaced by an *upper* envelope, so the left-hand side is grown.  The
  axiom asserts something stronger than (12.31), which is the safe direction.
* **No `∀env` / `∀N` trap.**  Both quantifiers are over `ℕ` and both are
  genuinely bounded — `q` by the range hypothesis, `k` above by the window
  hypothesis, which given `κ*(q) > 0` is exactly `k < λ(q)`.  A finite double
  family.
* **Not vacuous.**  The window is non-empty for ≈ 1.3 · 10⁶ values of `q`;
  `q = 1` alone admits ≈ 2 · 10⁷ values of `k`.
* **Range match is exact.**  The assembly case-splits on precisely the axiom's
  three hypotheses and discharges all three complementary branches.
* **One historical over-claim is already fixed on master.**  The older
  `ramareCSigmaStar := 0.9118` rounded `c(c₊)` *down*, which lowers `ϖ₀(q)` and
  makes the axiom claim more cells than the paper checked; master replaced it
  with the exact expression.  The rounded decimal survives on
  `codex/appendix-b25-retire`, which is stale — do **not** merge from there.

Not a proof: the Lean-side "reduction" turns the axiom into a hypothesis and
then supplies that hypothesis from an attested run certificate.  In
`gpu_prover`, `ExternalShardRealization`'s single field *is* the mathematical
claim, sharded; `Certificate.check` only verifies that the shard rank intervals
tile `[0, 3389047618)`.  So the chain moves trust from "Helfgott's paper reports
the computation" to "an attested run of an MPFR/GMP program returned true, and
the MPFR-to-exact-real refinement is correct".  The repo labels that boundary
explicitly and keeps `execution_attested`, `lean_realization_proved`,
`lean_atom_discharged` all `false`.  No branch anywhere proves the axiom.

## What needs merging in `claude_math`

The reduction is **not on master**.  It originates at commit `700178d06` and is
present identically on `a7/triage-13-cone-axioms`, `agent/leancompcert-ports`,
`prune/off-cone-development-axioms`, `wip/cert-shards-and-azure-bridges`,
`a7/build-perf-orphan-fix`, `a7/retire-arb-boundary-axiom`.  What master lacks:

* the `RamareProp1224FiniteComputation` abbrev and the three
  `…_of_inputs_and_finite` lemmas that make the finite check a hypothesis
  (+46 lines across `RamareProp1224FiniteCite.lean` and
  `RamareProp1224Assembly.lean`);
* `MathExtras/NumberTheory/Analysis/Prop1224GPUProverBridge.lean` (231 lines),
  whose `sourceClaim_iff_live_source_shape` is `by rfl` — the bridged
  proposition is definitionally the live one;
* `Math/Problems/TernaryGoldbach/AzureRegisteredSourceInputs.lean`,
  `MathExtras/…/GPUProverRegisteredBridgeAudit.lean`,
  `scripts/check_tg_registered_bridges.py`;
* a path dependency `SparkInterval → ../gpu_prover_wt_leanbridge` in
  `lake-manifest.json`.

The finite-computation content itself lives in a *different repo*
(`gpu_prover`, branch `agent/ramare-receipt-bridge`).

## The size of the job

| quantity | count |
| --- | ---: |
| `q` rows (`sourceRankCount`, proved to cover the range) | 3 389 047 618 |
| `q` rows with a non-empty window | ≈ 1.3 · 10⁶ |
| `(q,k)` margin cells | ≈ 6.7 · 10⁷ exact, ≈ 7.5–8 · 10⁷ with outward widening |
| `G_q` sieve `r`-steps | ≈ 1.2 · 10⁸ |

The cost is dominated by the `q` rows, **including the empty ones**: every row
needs its distinct-prime factorisation and `φ(q)`, then outward enclosures for
`log q`, `L(q)`, `f₁(q)` (three `rpow` per prime factor), `q^τ`, two
irrational-exponent `rpow` for `ϖ₀`, one for the `c₂*` floor, and the cube for
`λ(q)`.  With `ω(q) ≈ 3` on average that is `≈ 12 rpow` per row.

## Projection against the measured primitive

`bench/results/exp_fixed.md` measures the emitted exponential at `P = 30`,
`S = 24`: **1.28 µs per `expFix` under ccomp**, 1.13 µs under gcc, plus ≈ 0.06 µs
for the logarithm, so **≈ 1.34 µs per `rpow`**.

| phase | work | ccomp |
| --- | ---: | ---: |
| transcendentals on `q` rows | 3.389·10⁹ × 12 rpow | ≈ 15 core-hours |
| `(q,k)` margin cells | 7.5·10⁷ × 1 rpow + 1 log | ≈ 100 s |
| `G_q` accumulation | 1.2·10⁸ `r`-steps | ≈ 30 s |
| factorisation of 3.389·10⁹ rows | segmented, ≈ 1.5–2·10⁶ rows/s | ≈ 0.5 core-hours |

so **≈ 15–20 core-hours** for a full CompCert-compiled replay, against the
105–640 core-hours the MPFR campaign budgets — the gap is 30 bits of fixed
point against 192 bits of MPFR.  Per `(q,k)` cell the *cell* phase is ≈ 1.4 µs;
amortised over the whole run the cost per cell is ≈ 800 µs, because the run is
paying for 3.4·10⁹ empty rows, not for 7.5·10⁷ cells.

**Nothing has been run.**  These are projections from a measured primitive and
a published cell count, not from a sweep.

## Is 30 bits enough?

Probably, and it is checkable rather than a matter of taste, because every
rounding in the fixed-point layer is outward:

* the minimum observed margin is `0.0233` at `q = 1` and `1.156` at
  `q = 6 469 693 230`, against a relative enclosure width of `2.2·10⁻⁸`;
* widening `ϖ(q)` and `λ(q)` outward can only *add* cells to the check, which
  is conservative;
* `G_q(k)` is a sum of up to `2·10⁷` terms and must be accumulated at a wider
  scale than `2^30` — `Verified/AddWide.lean` and `Verified/LogAccum.lean` are
  the existing machinery for that, and at scale `2^62` the accumulated width is
  `2·10⁷ / 2^62 ≈ 4·10⁻¹²`.

So the port's precision budget is: `G_q` at `2^62` by wide accumulation, the
transcendentals at `2^30` by `ExpFixed`, and a final margin comparison with
both enclosures carried.  That is the design a port should start from.

## What is still missing

1. A `Ports/` module for the per-`q` row: three-plane marking to distinct prime
   factors and `φ(q)` (the `R2SegSieve` pattern, whose `prod ≠ n` test for "a
   prime above `√hi` remains" is directly reusable), then the `f₁`, `ϖ`, `λ`
   pipeline over `ExpFixPort`.  **Still missing.**
2. A `Ports/` module for the `(q,k)` cell: the coprime squarefree `1/φ(r)`
   accumulation and the margin.  **Landed** as
   `Ports/Prop1224Cell.lean`; see below.
3. The `claude_math` merge above, so the atom is a hypothesis and not a call.
   **Not done, deliberately** — the bridge file cannot compile on master
   without also merging the `SparkInterval → ../gpu_prover_wt_leanbridge` path
   dependency, which is entangled with in-flight `gpu_prover` consolidation.
4. The bridge from the artifact's integer margin back to the real-valued
   statement.  **Landed** as `Verified/Prop1224Margin.lean`.

None of these is blocked on the exponential any more.

## What the port revised in this note

Three things in the estimate above turned out to be wrong, all in the
favourable direction.

**`c_E` cancels out of the checked inequality.**  Substituting `κ*` and `err`
and collecting, the per-cell test is

```
(φ(q)/q)·[ log k + (1−ω*)·log q + ω*·L(q) + 1.36 ] ≥ G_q(k) + ω*·7.284·(20000k)^{−1/3}·f₁(q)
```

in which `c_E` does not appear.  It survives only inside the *window*, where it
is a hypothesis, so its proved bracket `1.3325822 ≤ c_E ≤ 1.3339` costs cells
(about `16 %` more at `q = 1`) rather than soundness.

**`λ(q)` needs no cube root, and the cell needs no exponential.**  The window
hypothesis is `k^{1/3}·κ*(q) < B(q)`; cubing gives `k·κ*³ < B³`, which is pure
integer monotonicity (`Prop1224Margin.lamHi_covers`).  And `(20000k)^{−1/3}`,
which looked like one `rpow` per cell at `1.34 µs`, is instead a register
`t = ⌊2^5(20000k)^{1/3}⌋` advanced over consecutive `k` and certified by
`t³ ≤ 2^15·20000k` (`Prop1224Margin.cbrtOK`).  Measured in the oracle, that
change alone cut the cell loop `3.0×`.

**The row needs ≈ 4 `rpow`, not 12.**  `f₁`'s per-prime factor depends only on
`p`, and the `5 820` primes below `⌊√(3.3·10⁹)⌋` fit in an emit-time table, so
only `q`'s single large prime costs an exponential — and only one, since for
`P > 57446` the factor is bounded above by `1 + P^{−2/3}`.  What is left is
`ϖ₀`'s three (`q^τ`, and two integer-base powers that replace fixed-point ones
via `x^a ≥ ⌊x⌋^a`), plus a fourth for `ϖ`'s third term on the `q < 2^17` rows
only.  Only `rpowLo` is ever called: `f₁` is wanted from above, and every
direction inverts to a lower bound on the exponentials.

## Revised projection

Measured on this box (20 cores, `ccomp` 3.17, `gcc -O2`):

| phase | work | measured | source |
| --- | ---: | ---: | --- |
| one `rpow` | | `1.34 µs` | `bench/results/exp_fixed.md`, unchanged |
| `q` rows, oracle C | `3.389·10⁹` | `3142 ns/row` ccomp, `2549` gcc | `bench/ref_p1224.c` |
| `(q,k)` cells, oracle C | `7.5·10⁷` | `118.9 ns/cell` ccomp, `96.4` gcc | `bench/ref_p1224.c` |
| `(q,k)` cells, **the artifact** | `4.3·10⁸` instructions | `915 ns/cell` ccomp, `610` gcc | `bench/Prop1224CellEmit.lean` |

The artifact's cell phase is `9.5×` the oracle's, which is the price of
branchlessness: every phase's instructions execute on every one of the `25`
loop iterations a cell costs (one accumulate pass and `S = 24` squaring
rounds), and none of them can be skipped.  It still sustains `7.2·10⁹`
register-machine instructions per second under `ccomp`, so the whole cell
phase — `1.2·10⁸` `r`-steps — is **under two minutes**.

The row phase has no artifact yet, so its number is a projection from the
measured primitive rather than a measurement: `4` `rpow` per row at the
measured `1.34 µs` is `≈ 5 core-hours` over `3.389·10⁹` rows, plus `≈ 0.5` for
the segmented factorisation at `R2SegSieve`'s measured `1.5–2·10⁶` rows/s.

| | ccomp artifact |
| --- | ---: |
| row transcendentals, `3.389·10⁹ × 4 rpow` | `≈ 5.0` core-hours (projected) |
| row factorisation | `≈ 0.5` core-hours (projected) |
| `(q,k)` cells, `1.2·10⁸` `r`-steps | `0.03` core-hours (**measured**) |
| **total** | **`≈ 5.6` core-hours** |

against the `105–640` core-hours the MPFR campaign budgets — a factor of `19`
to `115`.  **Still not run.**

## Two emit-time hazards met in practice

*Literal tables overflow `ccomp`.*  The note above records `27 421` entries
doing it at `27 GB`.  The cell module first initialised its two multiplicative
planes with `2·segLen` literal stores, which at the production `segLen = 2^16`
is `131 072` — five times over.  The fix costs two instructions per mark and
two per cell: the planes start at the array's own zero fill and a zero cell is
read as the neutral `1`, which is `R2SegSieve`'s `0`-means-`1` correction.

*Emission is quadratic in `arrayLen`.*  `5.9 s` at `16 433` cells, `78 s` at
`65 607`.  This is emit-time only and does not affect the artifact, but it does
bound how large a single window can usefully be.
