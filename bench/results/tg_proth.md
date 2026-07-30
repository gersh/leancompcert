# Stage (b) of the Helfgott–Platt prime ladder: the Proth test, ported

`bench/results/tg_goldbach.md` recorded stage (b) — `ProthTester::test` —
as **not expressible** in the proved fragment, and measured it at **75.1 %
of the reference producer's cost**.  The obstruction named there was
precise:

> `mpz_powm` needs `x·y mod N` with `N` about 90 bits.  The fragment's only
> division is `udiv`/`urem` at 64 ÷ 64 → 64.  Reducing a 128-bit product
> modulo a 90-bit modulus is a 128 ÷ 64 division, which the fragment cannot
> express.  `Verified/MulWide.lean` proves the 128-bit *product* circuit
> (`hl_spec`), but there is no counterpart for the reduction.

That counterpart now exists.  **Stage (b) is expressible.**

Everything below is measured on this box (aarch64, 20 cores, shared).
CPU (user) time throughout.

## The verdict, updated

| stage | expressible | share of reference cost | cost vs reference |
|---|---|---|---|
| (a) progression sieve | yes, as a different algorithm | 22.6 % | 792× (gcc), 3 422× (ccomp) |
| (b) **Proth test** | **yes, exactly** | 75.1 % | **1.57× (gcc), 2.25× (ccomp)** |
| (c) ladder assembly | yes, exactly | 2.4 % | ≈ 1× |

The stage that costs three quarters of the run is now the *cheapest* one to
check, relative to the reference.

## Why Montgomery, and not Barrett

Three candidate reductions were considered; the choice is forced by the
instruction set, not by taste.

* **Schoolbook 128 ÷ 64.** Not expressible: it is exactly the missing
  instruction.  Emulating it by 64 shift-subtract rounds costs ~64
  register operations *per multiplication step*, an order of magnitude
  more than the whole Montgomery reduction.
* **Barrett.** Replaces the division by a multiplication, but needs a
  precomputed `μ = ⌊2ᵏ/N⌋` — itself a wide division — plus a wide
  compare-and-correct.  When the modulus is an emission-time literal `μ`
  can be precomputed and *verified* by multiplication; when the modulus is
  runtime data (a rolled window over `k`) it cannot, and Barrett dies.
* **Montgomery.** Needs **no division at all**: one multiply mod `2⁶⁴`, one
  multiply-accumulate, one exact shift by `2⁶⁴`.  Its only precondition is
  an odd modulus, and Proth numbers `k·2ⁿ+1` are odd by construction.  It
  also has a closed-form multiplier for this family — see below — so it
  needs no Newton iteration either.

Montgomery wins on the criterion that matters: *nothing* it needs is
outside the fragment.  `Verified/Mont2.lean` was mechanically checked to
contain no `/` and no `%` in any machine-form definition beyond the fixed
`% 2⁶⁴` that *is* the machine's word semantics.

### One accident worth naming

For a Proth modulus `N = k·2ⁿ + 1` with `n ≥ 32`, the Montgomery multiplier
has a closed form:

    n′ = k·2ⁿ − 1   (mod 2⁶⁴)

because `N·n′ + 1 = (k·2ⁿ)²` is divisible by `2^{2n} ∣ 2⁶⁴`.  The usual
Newton iteration (five rounds of `x ← x(2 − N x)`) is not needed: the
inverse is **one instruction**.  This falls out of `(1+u)(u−1) + 1 = u²`
with `u = k·2ⁿ`, and it is the reason the whole setup fits in twelve `mov`s.

## What is proved

| theorem | content |
|---|---|
| `Montgomery.redcStep_mul` | the reduction's shift is *exact*: `redcStep N n′ T · 2⁶⁴ = T + m·N`. This is the reduction-side analogue of `MulWide.hl_spec`. |
| `Montgomery.redcIter_mul` | `s` steps divide by `2^{64s}` modulo `N` |
| `Montgomery.redcIter_lt` | `T < N·Bˢ + N` ⟹ output `< 2N` |
| `Montgomery.montMul_spec` | `montMul s N n′ a b · Bˢ ≡ a·b (mod N)`, output `< N` |
| `Montgomery.cancel_B_pow` | `Bˢ` cancels modulo an odd `N` — the Montgomery domain is a homomorphism |
| `Montgomery.montPow_rep` | square-and-multiply in the Montgomery domain computes the ordinary power |
| `Montgomery.montExp_spec` | end to end, in ordinary modular arithmetic: `montExp … = a^e mod N` |
| `Mont2.hlW_eq` | the 128-bit product with the half-limb split done by shift and mask — the last `/ 2³²` removed |
| `Mont2.redcStep2_val` | the two-limb machine block realizes one `Montgomery.redcStep` |
| `Mont2.montMul2_val` | **the deliverable**: two-limb Montgomery multiplication in the 64-bit instruction set |
| `Mont2.dblIter_val` | `x·2ᵏ mod N` by doubling — division-free entry into the Montgomery domain when the modulus is runtime data |
| `InstrBlock.srun_correct` | a division-free straight-line block always runs, to a *total* `Nat` state function |
| `Straight.block_correct` | the same at the expression layer |
| `TGProth.prothProgram_denote_fold` | the emitted program is a plain fold — no `Option`, no CCIR, no trace |
| `TGProth.body_step` | the 505-instruction loop body computes exactly two `Mont2.montMul2` applications and one branchless select |
| `TGProth.prothProgram_wf` | well-formedness, program-sized and decidable |
| **`TGProth.prothProgram_denote`** | **the bridge**: the program's denotation is `0` iff `a^((N−1)/2) mod N = N − 1` |

One precondition is worth naming because it was found the hard way, by the
statement being false without it: **`kbits ≤ 64`**.  Operand literals denote
modulo `2⁶⁴`, so a wider window would load `k mod 2⁶⁴` into the window
register and mask with `(2^kbits − 1) mod 2⁶⁴` — at `n = 32`, `kbits = 65`,
`k = 2⁶⁴ + 1` every other hypothesis holds and the loop exponentiates by
the wrong exponent.  The shipped certificate uses `kbits = 39`.  A ladder
needing `k ≥ 2⁶⁴` would need a two-limb window, not just a bigger literal.

All on `propext` / `Classical.choice` / `Quot.sound` or fewer.  No `sorry`,
no `native_decide`.  `scripts/AxiomAudit.lean` covers all of them.

The chain is closed end to end: `prothProgram_denote_fold` turns the
program into a `Nat` fold, `body_step` identifies one iteration with two
Montgomery multiplications, `Mont2.montMul2_val` identifies those with
`Montgomery.montMul 2`, and `Montgomery.montExp_spec` identifies the whole
loop with `a^e mod N`.  Nothing in it evaluates the computation.

A note on how it is proved, because the technique is reusable: a
505-instruction body is *never* unfolded.  Leaf blocks (18 instructions and
under, at literal register numbers) have one-line `rfl` specifications;
`InstrBlock.srun_append` glues them, and the intermediate register file is
`generalize`d away at every boundary so no term ever grows.  Unfolding even
the 95-instruction `mul2B` in one step does not terminate in practice.

## The artifact

`N = 274877906947·2⁵² + 1 = 1237940039298891073781235713`, 91 bits, witness
`a = 3`.  This is ladder scale: at `10²⁷` the producer's `k` is just under
`2³⁹` and `N` just under `2⁹¹`.

The exponent `(N−1)/2 = k·2⁵¹` has `k`'s 39 bits followed by 51 zeros, so
the loop runs 90 times with a uniform body: shift one bit out of a window
register, square, and multiply by `a` or by the Montgomery `1`, selected
**branchlessly** (two multiplications by a 0/1 flag — no comparison, no
jump, no data-dependent control flow anywhere).

| | |
|---|---|
| generated C | 33 467 bytes (rolled: size independent of the exponent length) |
| loop body | 505 instructions, of which 2 × 240 are the Montgomery multiply |
| registers | 272 |
| emission | 0.27 s |
| `ccomp -c` + `ld` | 73 ms |
| linked binary | **3 744 bytes**, statically linked, **0 undefined dynamic symbols** |
| divisions in the emitted C | **0** |

## Cost

Against GMP's `mpz_powm` on the **same** modulus, exponent and base —
200 000 repetitions, best of three:

| engine | µs per Proth test | vs GMP |
|---|---|---|
| GMP `mpz_powm` | **1.34** | 1× |
| this port, `gcc -O2` | **2.10** | **1.57×** |
| this port, `ccomp` (freestanding) | **3.00** | **2.25×** |

(`bench/results/tg_proth.csv`, produced by `bench/tg_proth.sh`.)

The reference producer's own end-to-end figure corroborates the GMP arm:
`tg_goldbach_ladder_native.cpp` at range 4·10²³ does 318 674 Proth tests in
0.56 s of total CPU (0.60 s wall), and `bench/results/tg_goldbach.md`
attributes 1.35 µs/test to stage (b) — within 1 % of the 1.34 µs measured
here directly.

**A proved, CompCert-compiled, division-free Proth test costs 2.25× GMP.**
That is not "10× slower but worth having"; it is close enough that the
proved artifact is a practical producer, not only a checker.

Two honest caveats on the ratio:

* The branchless multiply-always costs 51 redundant Montgomery
  multiplications out of 180 (the trailing zero bits multiply by the
  Montgomery `1`, which is a genuine no-op on the value). Unrolling the
  exponentiation would cut ~28 % of the work, at the price of an artifact
  whose size grows with the exponent.
* GMP's `mpz_powm` also does a *windowed* exponentiation, so it performs
  fewer multiplications than the naive ladder; the comparison is
  algorithm-to-algorithm, not instruction-to-instruction.

## Correctness cross-check

`bench/tg_proth.sh` emits, compiles (CompCert *and* `gcc -O2`), runs, and
compares the exit status against an independent Python
`pow(a,(N-1)//2,N) == N-1` for seven cases: four real 91-bit Proth primes
with genuine witnesses, one composite, and two non-witnesses of a prime.

| k | a | expected | ccomp | gcc | python |
|---|---|---|---|---|---|
| 274877906947 | 3 | pass | 0 | 0 | True |
| 274877906962 | 3 | pass | 0 | 0 | True |
| 274877906976 | 5 | pass | 0 | 0 | True |
| 274877907025 | 3 | pass | 0 | 0 | True |
| 274877906946 | 3 | **fail** | 1 | 1 | False |
| 274877906947 | 2 | **fail** | 1 | 1 | False |
| 274877906947 | 7 | **fail** | 1 | 1 | False |

7/7 agreement, in both directions.  The artifact is also registered as the
`proth` certificate of `lean-compcert check-native`, so it is compiled with
CompCert and run on every acceptance pass.

## What this does and does not certify

Proth's criterion is

    N = k·2ⁿ + 1,  2ⁿ > k:    N prime  ⟺  ∃a,  a^((N−1)/2) ≡ −1 (mod N)

The **producer** searches for the witness `a` — that is what the
reference's `mpz_jacobi` is for.  The **verifier** only checks the
congruence for the witness it is handed.  So the three secondary
obstructions listed in `tg_goldbach.md` — the Jacobi loop's
data-dependent trip count, the early exits, and the nested inner loops —
all disappear on the checking side.  What is left is one modular
exponentiation, and that is what this program is.

Proth's criterion itself is *not* formalized here.  It is classical (Proth
1878; Robinson, *Math. Comp.* **11** (1957) 21–22) and is used, like the
other literature facts in this package, at the level of the source
development.  What is formalized is the arithmetic — which is where the
obstruction was.

## What is not proved

Stated honestly, because the distinction matters:

* **Proth's criterion.** `prothProgram_denote` says the artifact decides
  the congruence `a^((N−1)/2) ≡ N−1 (mod N)`. That this congruence implies
  `N` prime is the classical theorem cited above, and it is *not*
  formalized here. The artifact is a proved decision procedure for the
  congruence, not a proved primality certificate.
* **The emitted C**, as everywhere in this package, is an emission choice,
  not a theorem. The theorems are about `Program.denote`. See
  `runtime/start/README.md` for the freestanding artifact's exact trusted
  surface.
* **Width.** `Mont2` is two limbs, so moduli up to `2¹²⁷`.
  `Verified/Montgomery.lean` is stated for an arbitrary number of
  reduction steps, so widening is a machine-layer exercise in the same
  proof shape — that is the route to `checkAllPsiLeMul`'s ~950-bit
  operands, and it is not done.

## Reproducing

```
bench/tg_proth.sh [path/to/tg_goldbach_ladder_native.cpp]
```

Emits the artifact, compiles it with CompCert (freestanding) and gcc,
cross-checks all seven cases against Python, measures both against GMP's
`mpz_powm` on the same modulus, and — if the reference source is given —
rebuilds and reruns the reference producer for corroboration.
