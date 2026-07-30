# The CDEM Abel increment scan

`LeanCompCert/Ports/CDEMAbelScan.lean`, its certificate
`LeanCompCert/Testing/AbelScanCertificate.lean`, its emitter
`bench/AbelEmit.lean`, and its oracle `bench/ref_abel.c`.

## 1. What is being computed

The residue is `MathExtras.Reductions.CDEMAbel.CDEMAbelNatFamily` on
`claude_math` — the `Nat` reduction of the last live external atom of the CDEM
replacement-table campaign, `reproducibleTable_abel_verifier_output`.  With
`W = 10¹⁸`, `K = 199330`, `N = 5·10⁹`:

```text
F(k)   = Σ_{d ≤ K} μ(d)·⌊k/d⌋            (an integer)
G(0)   = 0,   G(k) = |1 − F(k)|
dPos   = max(G(k) − G(k−1), 0)           dNeg = max(G(k−1) − G(k), 0)
uPos   = Σ_{k=1}^N dPos(k)·⌈W/k⌉         uNeg = Σ_{k=1}^N dNeg(k)·⌊W/k⌋
v      = Σ_{k=1}^N (dPos+dNeg)(k)·⌈W/√k⌉ tv   = Σ_{k=1}^N (dPos+dNeg)(k)
```

and the claim the reduction discharges is

```text
uPos ≤ uNeg + 324880457633740        v ≤ 48710223109607260068028 .
```

The artifact stores `uPos`, `uNeg` and `v` as limb pairs and `tv`, `F(N)`,
`G(N)`, `⌊√N⌋` and the divisor cursor as single words — twelve result cells —
and returns the number of failed guards in the output register.

Note that `F(k) = 1` identically for `k ≤ K` (it is `Σ_{n≤k} Σ_{d∣n} μ(d)`),
so every accumulator stays empty until the scan passes `K`.  Any test
configuration with `HI ≤ K` is vacuous.

## 2. Three things that are new relative to the sieves already here

**The mark table is the resident μ table.**  `ArraySegSieve` marks by primes,
`R2SegSieve` by prime powers; here the marks are indexed by every `d ≤ K` with
`μ(d) ≠ 0`, because `F(k) − F(k−1) = Σ_{d∣k, d≤K} μ(d)`.  The table is
`K + 1 = 199331` cells.  It cannot be emitted as literals — `storeLits` costs
three instructions per cell, and `27421` literal entries already needed 27 GB
of `ccomp` stack — so the program's first phase **builds** it by trial
division against the `86` primes `p ≤ ⌊√K⌋ = 446`, which is `(K+1)·86 =
17142466` iterations, once.

**Every product is 64×64→128.**  `v ≈ 4.9·10²²` and `uPos`, `uNeg ≈ 10²⁰`
exceed `2⁶⁴`, so the accumulators are `AddWide` limb pairs — but so do the
*addends*: `⌈W/k⌉ = 10¹⁸` at `k = 1` and `dPos` can reach
`1 + Σ_{d≤K}|μ(d)| = 121175`, giving single products near `10²³`.  All three
products therefore go through the half-limb circuit of `Verified/MulWide.lean`
inlined as `mulWideBody`.  Budget check: the largest accumulator is
`2.6·10⁵` times below `2¹²⁸`.

**`⌈W/√k⌉` has to be exact, and is.**  The trusted numeral
`48710223109607260068028` *is* the engine's `Σ|δ(k)|·⌈W/√k⌉`, and by
`v_reduction_tight` the exact ceiling already spends `tv/W` over the true `V`
— with `tv = 1678512305`, that is the entire margin.  An artifact rounding
`1/√k` even one ulp more generously than `⌈W/√k⌉` overshoots the numeral and
fails.  There is no slack.  So the artifact computes it exactly, with no
floating point, no 128-bit division and no `clz`:

* `t = ⌊√k⌋` incrementally along the stream (no division), giving the bracket
  `⌈W/(t+1)⌉ ≤ ⌈W/√k⌉ ≤ ⌈W/t⌉`;
* bisection on `P(s) ≡ s²k ≥ W²`, **one step per loop iteration** (the
  round-counter shape of `R2SegSieve`'s log phase), so the body stays one test
  wide — `378` instructions — instead of `bsSteps` tests wide;
* `P(s)` decided exactly from `W = a·s + b` (`a = ⌊W/s⌋`, `b = W mod s`) via
  `s²(k − a²) ≥ 2abs + b²`, which for the only hard case `1 ≤ k − a² ≤ 2a`
  becomes `s·(s·e − 2ab) ≥ b²` with **both** `s·e ≤ 2W` and `2ab < 2W` inside
  a `u64`.  That rearrangement is the whole trick; the two remaining products
  are the only 128-bit quantities, and `a ≤ 2³¹` is checked rather than
  assumed.

## 3. Guards

The output register is the number of failed guards; a correct run returns `0`.

| budget | guard |
| --- | --- |
| `markSteps` per window | the divisor cursor reached `K` before the phase ended |
| `bsSteps` per integer | the bisection bracket closed (`rSl = rSh`) |
| the incremental `⌊√k⌋` | one bump per integer sufficed |
| `a ≤ 2³¹` in the predicate | no `a·a` wrap |

## 4. Proved, and not proved

Proved at `[propext, Classical.choice, Quot.sound]` (`scripts/AxiomAudit.lean`,
eighteen new lines, no `sorry`, no `native_decide`): `abelProgram_wf` and,
through `AProgram.evalCC_compile`, `abelProgram_compiled` — the emitted C
computes exactly `denote`.

Not proved, exactly as in `ArraySegSieve`, `PsiSegSieve` and `R2SegSieve`:
that `denote` *is* the residue.  That is corroborated by §5.

## 5. Oracle agreement

`bench/ref_abel.c` shares nothing with the artifact: `μ` comes from a linear
smallest-prime-factor sieve rather than trial division against a small-prime
table; the reciprocal square root uses `long double` plus a `u128` fixup, which
is what `scripts/cdem_repro_table_fast.cpp` on `claude_math` does, rather than
bisection on the exact 64-bit predicate; and the accumulators are
`unsigned __int128` rather than limb pairs.

All twelve result slots, both compilers, zero violations:

| `W` | `K` | `HI` | body | loop | gcc | ccomp | vs oracle |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `10⁶` | `30` | `40` | 378 | `1478` | 0 viol | 0 viol | 12/12 |
| `10¹⁸` | `100` | `500` | 378 | `35374` | 0 viol | 0 viol | 12/12 |
| `10¹⁸` | `1000` | `5000` | 378 | `386391` | 0 viol | 0 viol | 12/12 |
| `10¹⁸` | `5000` | `20000` | 378 | `1554129` | 0 viol | 0 viol | 12/12 |
| `10¹⁸` | `199330` | `2·10⁶` | 378 | `158832782` | 0 viol | 0 viol | 12/12 |

The last row is at the **production** weight scale and Möbius prefix bound.
Its slots are

```text
uPos = 595788639320683480             (hi limb 0)
uNeg = 595462313982487501             (hi limb 0)
v    = 52·2⁶⁴ + 4326638605017328058
tv   = 868448      F = −61      G = 62      ⌊√HI⌋ = 1414
```

The Lean-side emit-time reference `Ports.CDEMAbelScan.Ref.fold` was separately
checked against the same oracle at `(W, K, HI) = (10⁶, 30, 40)`,
`(10⁶, 60, 120)` and `(10⁸, 200, 400)`; it is not usable above `W ≈ 10⁸`
because its `⌈W/√k⌉` is a deliberate linear descent.

Reproduce:

```bash
cc -O2 -o ref_abel bench/ref_abel.c -lm
lake env lean --run bench/AbelEmit.lean 1000000000000000000 199330 1000000 2 prod.c
gcc  -O2 -o prod_gcc prod.c
ccomp -O2 -o prod_cc  prod.c
./prod_gcc ; ./prod_cc ; ./ref_abel 1000000000000000000 199330 2000000 1
```

## 6. Cost

At the production configuration (`W = 10¹⁸`, `K = 199330`, `segLen = 10⁶`), the
period is `markSteps + segLen·(bsSteps+1) = 8845158 + 62·10⁶ = 70845158`
iterations per window, i.e. **`70.85` loop iterations per integer** — `8.85`
marks and `62` bisection rounds.  The whole body is `378` instructions with
eight `udiv`/`urem`, and the array is `1199430` cells (9.6 MB).

Measured on this machine at `HI = 2·10⁶` (`1.588·10⁸` iterations, of which
`1.714·10⁷` are the one-time μ sieve):

| | wall | per iteration | per integer |
| --- | --- | --- | --- |
| gcc `-O2` | 6.065 s | 38.2 ns | **2705 ns** |
| ccomp `-O2` | 7.709 s | 48.5 ns | **3440 ns** |

Compile wall for the production body: gcc `0.079 s`, ccomp `0.173 s`.  The
rolled emission keeps the body at one copy, so `ccomp` never sees the 27 GB
literal-table failure mode; the μ table is generated in the loop precisely to
avoid it.

**Projected full run, `N = 5·10⁹`, single core:**

```text
gcc    5·10⁹ × 2705 ns = 1.353·10¹³ ns = 13 530 s ≈ 3.8 hours
ccomp  5·10⁹ × 3440 ns = 1.720·10¹³ ns = 17 200 s ≈ 4.8 hours
```

plus `0.7 s` for the μ table, and 9.6 MB resident.  For comparison, the
unverified production engine `scripts/cdem_repro_table_fast.cpp` takes
`87.85 s` on eight threads (`≈ 442` core-seconds) and **19.5 GiB**, because it
materializes `delta[]` for all of `[1, N]`; the artifact is `≈ 31×` slower per
core and `2000×` smaller.  **No full run has been started.**

The single obvious lever, not taken here: the bisection runs for every integer,
but `s` is only consumed where `δ(k) ≠ 0`, which is about `27 %` of them
(`tv = 1.68·10⁹` increments over `5·10⁹` integers).  Streaming the test points
the way `R2SegSieve` streams its log phase would drop `62` rounds per integer
to `≈ 17` and the projection to roughly `1.1` hours.  That is a strictly
mechanical change to the phase schedule and changes nothing proved above.
