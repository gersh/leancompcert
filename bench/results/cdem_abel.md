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

`LeanCompCert/Ports/CDEMAbelPrimitives.lean` now also proves, against the
literal array-machine blocks used in this scan:

* `muxBody_arun`: the branchless selector returns the selected word;
* `mulWideBody_arun_exact`: the two output limbs recombine to the exact
  natural-number product;
* `addWideBody_arun_mod` and `addWideBody_arun_exact`: the accumulator is
  addition modulo `2^128`, and ordinary exact addition under the explicit
  no-wrap invariant;
* `okFormula_iff`: the predicate's large-`e` shortcut and fine 128-bit branch
  are equivalent in both directions to `W^2 <= s^2*k` after
  `W = a*s+b`, so the rearrangement loses no cases and adds none;
* `okQuot_arun`: the literal guard-plus-division prefix computes exactly
  `a = W/s` and `b = W%s` for the positive bisection candidates;
* `okClassify_run`: the next 17 production instructions compute `a^2`,
  `e = k-a^2`, and the equality and large-`e` branch flags exactly under the
  explicit word/no-underflow bounds;
* `okProductPrep_flags`, `wordGe_iff_wval`, and `okPost_run`: the scalar
  product guard, little-endian 128-bit comparison, and final Boolean postlude
  implement the residual formula, including the branch where the subtraction
  wraps but is gated off;
* `okAfterClassify_run`: both literal 64-by-64 multipliers and the complete
  product/comparison tail refine that residual formula;
* `productionOkS_run`: all 74 instructions at the live allocation
  (`rs=194`, gate `142`, result `197`) return exactly `okFormula`, including
  the `k < a^2` rejection path;
* `okBody_defined`: the exact reciprocal-square-root predicate's two
  register-valued divisions cannot divide by zero.

The array-level primitive theorems include the array frame, so these scalar
stages cannot silently modify the sieve plane.  A fresh source check under
`MemoryHigh=1536M`, `MemoryMax=2G`, `MemorySwapMax=0`, and
`LEAN_NUM_THREADS=1` took `1.72 s`, peaked at `708348 KiB` RSS, and used no
swap.  A module build under the same cap took `1.94 s` and peaked at
`730348 KiB`; fresh `#print axioms` checks report only `propext`,
`Classical.choice`, and `Quot.sound` (with `okPost_run` needing only
`propext`).

The predicate definedness proof is deliberately split after its two-instruction
divisor guard and two-instruction division stage.  A diagnostic one-shot
`simp` over all 74 instructions reached `3.77 GiB` RSS after 73 seconds and
was interrupted inside a 4 GiB hard cap.  The block-split source proof checked
in `0.33 s`, peaked at `572076 KiB`, and used no swap inside a stricter 2 GiB
hard cap.  This is also the required build shape for later predicate-value
and bisection proofs.

`LeanCompCert/Ports/CDEMAbelBisection.lean` now supplies the next refinement
layer.  The finite executable `exactRoot` is characterized as the least `s`
with `W² ≤ s²k`; the source-shaped initial bracket is proved to contain it;
the actual logarithmic `bsBudget` is proved sufficient; and `round_run`
composes the literal seven-instruction probe, complete 74-instruction
predicate, and four branchless updates.  `rounds_run` then proves any finite
sequence of those machine rounds refines the pure iterator, with the 64-bit
fit conditions kept explicit at each midpoint.  The production envelope now
discharges all of them for `1 ≤ k ≤ 5·10⁹`: quotient, square, residual,
remainder product, doubled product, and successor are proved below `2⁶⁴` for
every midpoint in every iterated sub-bracket.  `production_rounds_run`
therefore proves the complete central 61-round machine sequence closes at
`exactRoot` with no fit oracle.  `accBisect_decomp` identifies that sequence
inside the literal array program, while `open_run_initial` proves the actual
round-zero prefix installs the pure initial bracket.  The enlarged integrated
source check under the same 2 GiB, one-thread, zero-swap cap took `4.29 s` and
peaked at `669988 KiB` RSS; the module build took `4.54 s` and peaked at
`726076 KiB`.

The final consumer is now proved too. On a closed bracket, `close_run_mod`
shows the literal violation check, half-limb product, two-limb add, and advance
stage leave both violation counters unchanged and add exactly
`(dPos+dNeg)·exactRoot` modulo `2^128`; `close_run_exact` removes the modulus
under the explicit accumulator no-wrap invariant. With this addition the
integrated source check took `4.46 s` and peaked at `696108 KiB`.

`LeanCompCert/Ports/CDEMAbelAccumulation.lean` closes the next interleaved
stage.  `mulAdd_run_mod` proves the reusable literal 64-by-64 multiply followed
by two-limb addition, and `accProd_run_mod` instantiates it twice against the
actual array program: `uPos` gains `r169·r167`, `uNeg` gains `r170·r168`, both
modulo `2^128`, every unrelated register is framed, and the sieve array is
unchanged.  `accProd_run_exact` removes both moduli under the two explicit
no-wrap invariants.  Fresh source compilation under the same one-thread,
2 GiB, zero-swap cap took `0.49 s` and peaked at `592612 KiB`; the live module
build took `0.53 s` and peaked at `606240 KiB`.  Fresh axiom prints for all
four public refinement theorems report only `propext`, `Classical.choice`, and
`Quot.sound`.

Still not proved: preservation/composition through the `accHead` block
interleaved between bisection rounds, then the μ-table build, window marking,
full accumulators, and outer loop to
show that the complete `denote` *is* the residue.  That remaining refinement
gap is corroborated, but not discharged, by §5.

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

There is deliberately **no kernel-evaluation check** of `denote` here, unlike
`ArraySegSieve` and `R2SegSieve`.  `AProgram.denote` threads the register file
as a closure chain, one link per register write, and this body writes `378`
registers per iteration: even the smallest non-vacuous configuration (`W = 64`,
`K = 8`, `HI = 12`) needs `351` iterations and so a chain about `1.3·10⁵` deep,
which overflows the interpreter stack outright and does not reduce in the
kernel within any budget worth spending.  Both sieves above stay under
`3·10⁴`.  The check that replaces it is §5's oracle agreement, which is run at
the production parameters rather than at a toy configuration.

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
core and `2000×` smaller.  The full run is §7.

The single obvious lever, not taken here: the bisection runs for every integer,
but `s` is only consumed where `δ(k) ≠ 0`, which is about `27 %` of them
(`tv = 1.68·10⁹` increments over `5·10⁹` integers).  Streaming the test points
the way `R2SegSieve` streams its log phase would drop `62` rounds per integer
to `≈ 17` and the projection to roughly `1.1` hours.  That is a strictly
mechanical change to the phase schedule and changes nothing proved above.

## 7. The full run at `N = 5·10⁹`

### The oracle first, because it changes what the artifact has to do

`bench/ref_abel.c` now takes a fifth argument, the length of the marking
window.  The flat version allocates `int32_t[HI+1]` — 20 GB at `N = 5·10⁹`,
which on a shared box is not a thing to ask for — so the multiples of each
squarefree `d ≤ K` are walked window by window instead, at a cost of
`⌈HI/SEG⌉·K` extra cursor initialisations: `2.5·10⁸` against the `4·10¹⁰` the
marking already costs, i.e. 0.6 %.  At `SEG = 4·10⁶` the window is 16 MB, it
stays in cache, and the whole oracle runs in **605.91 s user and 19 MB**.  It
reproduces the flat version and §5's `HI = 2·10⁶` slots exactly.

Run at the production configuration `(W, K, N) = (10¹⁸, 199330, 5·10⁹)`:

```text
uPos = 2 037 368 965 713 732 597        tv        = 1 678 512 305
uNeg = 2 037 044 085 256 098 857        F(N)      = 112
v    = 2640·2⁶⁴ + 10 818 755 014 043 801 788   G(N) = 111
                                        ⌊√N⌋      = 70 710
```

and therefore

| the reduction's claim | computed | target | slack |
| --- | --- | --- | --- |
| `uPos ≤ uNeg + 324880457633740` | `uPos − uNeg = 324 880 457 633 740` | `324 880 457 633 740` | **0** |
| `v ≤ 48710223109607260068028` | `48 710 223 109 607 260 068 028` | `48 710 223 109 607 260 068 028` | **0** |

**Both hold, and both hold as exact equalities.**  §2 said this of `v` — "the
trusted numeral *is* the engine's `Σ|δ(k)|·⌈W/√k⌉`" — and it is now confirmed
of `uPos − uNeg` as well.  The numerals in
`MathExtras/NumberTheory/Analysis/CohenDressElMarrakiReproducibleSourceDefs.lean`
(`ReproducibleTableAbelVerifierOutput`) are not bounds with room in them; they
are the values.  Three consequences worth stating plainly:

* the artifact has **no margin at all**.  An implementation that rounded
  `⌈W/√k⌉` one ulp more generously anywhere in `5·10⁹` integers would exceed
  the numeral and the claim would read as false.  §2's "there is no slack" is
  literal;
* `tv = 1 678 512 305`, `F(N) = 112` and `G(N) = 111` independently reproduce
  the `mobiusPrefixFloorSum` and `reproducibleVerifierGseq` fields of
  `ReproducibleTableNativePrefixOutput` in the same file, which are separate
  atoms checked by a different route;
* the two inequalities are **not** tested by the artifact.  Its output
  register is the number of failed *guards* (§3).  `bench/abel_check.py`
  assembles the limb pairs from the twelve result cells and applies the two
  comparisons, and the manifest records them.

### The artifact, at `N = 5·10⁹`

```
lake env lean --run bench/AbelEmit.lean 1000000000000000000 199330 1000000 5000 abel_prod.c
```

`LOOP = 354 242 932 466`, `CELLS = 1 199 430`, body `378`, 44 975 bytes of C
(SHA-256 `831d4a84…`), emitted in 3.97 s.  The scan is **not** shardable —
`Cfg` has no `lo` and no carry-in, `F` and `G` are running quantities, and the
program always opens at `k = 1` — so this is one process, one core, start to
finish, under each compiler.

**Zero guard failures, exit status 0, and all twelve result cells identical
between `ccomp -O2`, `gcc -O2` and the oracle.**

| | user CPU | ns/iteration | ns/integer | wall | peak RSS | exit |
| --- | --- | --- | --- | --- | --- | --- |
| `gcc -O2` | **15 961.61 s = 4.434 core-h** | 45.1 | 3 192 | 10:03:57 | 12 796 kB | 0 |
| `ccomp -O2` | **19 897.29 s = 5.527 core-h** | 56.2 | 3 979 | 11:08:21 | 12 672 kB | 0 |
| `bench/ref_abel.c` | 605.91 s = 0.168 core-h | — | 121 | 32:39 | 18 952 kB | 0 |

against §6's projections of `3.8 h` (gcc) and `4.8 h` (ccomp): **+17 % and
+15 %**.  Both runs also carry about `2 000 s` of *system* time, which is not
work: for most of their wall clock the shared cgroup they ran in was over its
`memory.high`, so every allocation went through forced direct reclaim.  Wall
clock here is meaningless — `%CPU` was 49 % and 54 % — and even the user
figures are somewhat inflated by shared-L3 contention.  The `ccomp/gcc` ratio
`1.247` is the part contention cannot distort, and it is within 1 % of §6's
`1.271`.

The oracle is `26×` faster per integer, which is the usual price of a
data-independent straight-line body plus a bisection that runs for every
integer whether or not `δ(k) ≠ 0`.  §6's un-taken lever — streaming the test
points — would remove about two thirds of that.

Manifest: `bench/results/manifests/cdem_abel_5e9.json`.

### What this establishes

`reproducibleTable_abel_verifier_output` now has a complete computed result:
its two fields are true at `N = 5·10⁹`, computed twice by the artifact (once
through CompCert) and once by an oracle sharing no code with it, agreeing on
every one of the twelve cells.

What it does **not** establish is anything about `denote` being the residue —
that is still §4's gap, closed only by §5's and §7's agreement — and, because
the two claims are exact equalities, nothing here has any margin.  A future
change to the artifact's arithmetic cannot be validated by "it still passes";
it has to reproduce these twelve integers.

## 8. LeanCompCert production observation

`LeanCompCert/Ports/CDEMAbelProductionCertificate.lean` now represents the
completed execution by one exact compiled-trace proposition.  It states that
the returned aggregate guard count is zero and that the final memory contains
the twelve cells printed above, in their physical epilogue order.  The atom
does not assert source definedness or an Abel inequality; those remain
denotation/refinement obligations.

The certificate uses the literal configuration printed by the retained run,
so importing it does not re-evaluate the 199,330-row marking-budget fold.
An independent emitter comparison evaluated both the original `Cfg.ofRange`
configuration and the literal certificate configuration and found their
35,064-byte rolled function sources identical.  The comparison took 3.71 s,
peaked at 522,300 KiB RSS, and used no swap under a 4 GiB hard cap.  A fresh
source check of the certificate took 0.23 s, peaked at 528,460 KiB RSS, and
used no swap under the same cap.  The LeanCompCert umbrella build, including
this certificate and the Ramaré maximum-headroom slice, passed serialized
under a 10 GiB hard cap.
