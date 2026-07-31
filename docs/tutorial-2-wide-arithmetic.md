# Tutorial 2 — Wide arithmetic: beyond 64 bits

> **Vocabulary.** *Denotation* means what a program computes as ordinary
> Lean arithmetic, defined mathematically rather than by running anything;
> *reflection* means proving something by computing a `Bool` and appealing
> to a theorem that says the `Bool` being `true` implies the statement.
> [What is proved](what-is-proved.md) defines these, says what a *program*
> is and everything you can write in one, and separates what is proved from
> what is merely observed.

Certificate values routinely exceed the machine word (the goldbach
Mertens sums are `2⁶⁴`-scaled). This tutorial shows the proved patterns
for multi-word computation, all built from fragment instructions.

## The 128-bit accumulator pattern

A wide accumulator is a `lo`/`hi` pair of registers. The carry out of
the low word is a **proved comparison**: after `lo' := lo + term`
(mod 2⁶⁴), overflow occurred exactly when `lo' < lo`. In a `Program`
body (see `Testing/WideMertensCertificate.lean` for the full context):

```lean
.mov 18 (.reg 0),                    -- save old lo
.binop 0 .add (.reg 18) (.reg 17),   -- lo += term (wraps mod 2^64)
.binop 19 .lt (.reg 0) (.reg 18),    -- carry = (lo' < lo)  ∈ {0,1}
.binop 1 .add (.reg 1) (.reg 19)     -- hi += carry
```

To check a 128-bit result, compare both words in the epilogue and
output an acceptance flag:

```lean
.binop 20 .eq (.reg 0) (.lit expectedLo),
.binop 21 .eq (.reg 1) (.lit expectedHi),
.binop 22 .band (.reg 20) (.reg 21)   -- output register: 1 iff both match
```

## Terms that don't fit a u64 literal

`⌊2⁶⁴/q⌋` itself overflows a literal. Use the identity
`⌊2⁶⁴/q⌋ = ⌊(2⁶⁴−1)/q⌋ + [(2⁶⁴−1) mod q = q−1]`, with the increment
decided by a proved comparison and widened by the comparison's `0`/`1`
result — see `Testing/WideMertensCertificate.lean`.

## 128-bit products

`Testing/FixedPointCertificate.lean` computes full products `n·C` beyond
`2⁶⁴` with the half-limb circuit: split both factors at 32 bits, form
four partial products (each fits u64), and recombine with
comparison-detected carries. The underlying arithmetic identity is
proved once: `Verified.MulWide.hl_spec` — the circuit's `(lo, hi)`
satisfies `lo + 2⁶⁴·hi = a·b`.

## Arbitrary precision: the limb layer

For statically-known widths beyond 128 bits, `Verified.Limb` provides
little-endian limb vectors with machine-checked value theorems:

| Operation | Theorem |
|---|---|
| `adc` (ripple add + carry) | `adc_val` |
| `sbb` (guarded subtract + borrow) | `sbb_val` |
| `isLt` (compare = borrow bit) | `lt_iff` |
| `mulLimbs` (schoolbook, full precision) | `mulLimbs_val : val (mulLimbs xs ys) = val xs * val ys` |
| `divModMSB` (long division by a limb) | `divModMSB_val`, `divModMSB_rem_lt` |

Signed values are sign-magnitude pairs (`Verified.SignedLimb.SInt`) with
`add_val`/`sub_val`/`neg_val`; `Verified.Log2Fixed.log2Fixed` is a
fixed-64-round log2 equal to `Nat.log2` on the whole u64 range.

Each limb operation's per-limb step is exactly the fragment pattern
above (carry = comparison), so limb programs realize in `Program`
bodies the same way the 128-bit certificates do.

## Dyadic fixed-point intervals

For interval-arithmetic certificates (the ℚ-valued goldbach families,
restated at a static binary precision), `Verified.Dyadic` provides
directed-rounding `mulLo/mulHi/divLo/divHi` and the `DInt` interval type
with machine-checked enclosure theorems in cross-multiplied `Nat` form,
e.g. `mulLo_le : mulLo p a b * 2^p ≤ a * b`. Division is exact floor and
ceiling — no Newton reciprocal is needed, since wide division is already
proved (`divModMSB_val`).

## A warning learned the hard way

When a wide value's term equals the full scale (e.g. `⌊2⁶⁴/1⌋ = 2⁶⁴`),
it wraps to zero in a u64 register and silently loses a high-word unit.
Fold such terms into the accumulator's initialization (the wide Mertens
certificate initializes `(lo, hi) = (0, 1)` for its `q = 1` term) — and
always cross-check your expected constants with independent bignum
arithmetic before certifying.
