# Ternary-Goldbach finite-computation operation inventory — 2026-07-28

Source: the fully-elaborated `native_decide_manifest.json` of the
ternary-goldbach development (all 1,371 atoms, 15 families) plus its checker
engine sources. Every atom is `Decidable.decide P = true` for a closed `P`.
This inventory drives the operation set of the verified reflection compiler
(`LeanCompCert.Verified.Reflect`) and records what remains.

## Proposition-shape census (1,371 atoms)

| Count | Shape |
|---:|---|
| 940 | `ℚ` inequalities over interval-arithmetic kernels (`log_enclose_full`, `interval_bisect`, `adaptiveUpper`) |
| 148 | `Prod` equalities (`Nat × Nat`, `Int × Bool`) from fixed-point ladder folds |
| 145 | Boolean conjunctions over enumerated band cells |
| 65 | `f args = true` checker folds |
| 26 + 5 | `Nat` inequalities and equalities (scaled-fold accumulators) |
| 23 | `Option` results (early-exit folds) |
| 17 | bounded `∀` over `Finset.Icc` / `Fintype` enumerations |

## Scalar operations across all families

**Covered by the proved fragment and the reflection DSL today** (u64/u8
machine ops with a machine-checked bridge to restricted C):

- `Nat` add, sub, mul, floor division, remainder, ceiling division (as
  `(a + b − 1)/b`), all six comparisons, bitwise and/or/xor, shifts,
  width casts;
- fixed-point scaling at `2^20`–`2^62` where values stay under `2⁶⁴`;
- multi-word accumulation built from proved 64-bit steps (demonstrated at
  128 bits: carry = proved `<` comparison, widened by proved cast) — covers
  the `2⁶⁴`-scaled accumulators whose targets are 20-digit literals;
- branchless selection via comparison masks (demonstrated: parity and
  squarefree filters, totient factor selection over a fixed prime list).

**Proved limb foundation** (`LeanCompCert/Verified/Limb.lean`): statically
sized limb vectors with machine-checked value-denotation theorems for
ripple add-with-carry (`adc_val`), subtract-with-borrow (`sbb_val`), and
wide comparison as the borrow bit (`lt_iff`) — the induction cores every
wide operation reuses, realized per limb by already-proved `u64`
instructions. This is the "arbitrary arithmetic" core: certificate widths
are always statically known (max 143 kbit in this corpus), so
arbitrary-precision means limb vectors of static size.

**Expressible by composition over the limb layer, not yet packaged:**

- full 64×64→128 products (32-bit half-limb decomposition) and schoolbook
  wide multiplication — needed for `n²·2^48 ≈ 2^97` intermediates and the
  dyadic interval kernels;
- `Int` (sign-magnitude pairs) for the Möbius/CDEM accumulators and
  `Int.natAbs`;
- `Nat.log`/`Nat.log2` at bounded arguments (unrolled halving);
- outward-rounded reciprocal (fixed-round Newton) for interval division.

**Requiring data-dependent control flow (the branch/goto proof, planned):**

- `Nat.minFac` / `Nat.Prime` / `Squarefree` / `IsPrimePow` by trial
  division with data-dependent trip counts (bounded unrolling is sound and
  demonstrated at reduced heights, but production heights need loops);
- `Nat.sqrt` (Newton), `Nat.gcd` (Euclid), early-exit `Option` folds
  (`loop410`, `bandRun`), well-founded recursion (`muFast`), and the
  value-dependent `adaptiveUpper` bisection trees.

**Requiring bignum arithmetic (out of the machine-word fragment):**

- all `ℚ` arithmetic — 940 atoms; every ℚ operation normalizes with
  `Nat.gcd` at up to 43,288-digit widths (the RS62 primorial seeds);
  `Rat.num`/`Rat.den`, `Int.floor`/`Int.ceil`, `Nat.factorial`, `p^48`,
  `m^16`, `n·2^192` nested square roots;
- 382 atoms carry at least one ≥20-digit literal; the multi-word approach
  covers the accumulator side, but general bignum ℚ needs either a
  runtime-backed path (outside the proved fragment) or fixed-precision
  dyadic re-statement of the certificates (the `roundOut`-at-`2^48`
  kernels are already effectively dyadic).

**Requiring container semantics:**

- `Array` with in-place `set!`/`modify`/`push` at up to 1.4·10⁸ elements
  (sieve builders in the Ramaré engines) — needs heap/array proof coverage;
- `List`/`Finset` pipelines (`range`, `filter`, `foldl`, `all`, `prod`,
  nested double sums) — the fold shapes map onto `foldTrace`; filters map
  onto comparison masks; embedded literal tables (18-entry to 13,600-entry)
  map onto per-iteration constants or in-circuit data.

**Not needed anywhere:** floating point, `IO`, `String` (beyond metadata
leaves), unrestricted recursion.

## Iteration scales

Fuel-indexed folds up to 1.4·10⁸ steps (Ramaré `MStar140M`), 2.5·10⁷
(`cePrimeAux`), 10⁷ (`gFold1215`, ψ sweeps), 2.56·10⁶ (C.17 sieve),
60,793-element filtered folds (§14.1 Mertens). Fixed bisection trees to
`2^10` cells; adaptive trees to `2^16`.

## What this means for the verified pipeline

1. The **scalar op set of the proved fragment is complete** for the integer
   fixed-point families (ternary arithmetic, ChebyshevPsi, the ladder and
   Mertens folds, C.17, vmHead): everything else those families need is
   composition (limbs, masks, unrolled folds), which the reflection DSL
   packages with a structural correctness theorem.
2. The **binding constraint for production heights is control flow**
   (branch/goto proof coverage) and **kernel evaluation scale**, not
   missing scalar operations.
3. The **ℚ interval families** additionally need bignum; the practical
   route is their existing dyadic `roundOut` discipline, which turns ℚ
   kernels into bounded-width integer computations expressible in the
   fragment once multi-word libraries exist.
