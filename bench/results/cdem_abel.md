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

The complementary round-zero path is now verified as well.
`productionOkS_gate0_counters` proves that the full predicate preserves both
failure counters when the bisection gate is zero; `round_gate0_run` proves the
bracket is unchanged; and `close_gate0_run` proves the gated product is
exactly zero, the `V` accumulator and cell cursor are unchanged, and only the
round counter advances. `accBisectS_gate0_run` composes the literal open,
round, and close blocks and proves that the first iteration installs the pure
initial bracket without changing `V` or either counter. The source check took
`4.91 s` at `736304 KiB` RSS and the module build took `5.06 s` at
`776500 KiB`, with one worker, a 2 GiB hard cap, and no swap. Fresh axiom
prints contain only Lean's ordinary foundations.

A deliberately rejected array-state wrapper around the same theorem hit
Lean's deterministic heartbeat limit after about 95 seconds at `770632 KiB`.
It duplicated the large lifted equality but proved no additional semantics.
The retained route names the combined scalar block with an irreducible
interface, proves the production array block is its lift, and then uses
`arun_lift`; this keeps theorem types compact while the explicit defining
equation remains available to scalar proofs.

That interface now supports both array-level schedules.
`accBisect_gate0_run` is the first-iteration contract.
`open_gate0_run`, `productionOkS_safe_counters`, and
`round_safe_counters` separately prove that an interior iteration leaves the
open bracket untouched, satisfies the quotient guard, and preserves both
failure counters. `accBisect_middle_run` then composes one exact active
bisection step, the zero-product close, round advance, array frame, and exact
`V` frame. The enlarged source check took `5.40 s` at `760068 KiB` and the
module build took `5.74 s` at `790764 KiB`, under the same one-worker 2 GiB
zero-swap cap. Fresh axiom prints contain only Lean's ordinary foundations.
This compact lifted interface is the required composition shape for the
378-instruction body.

The final active schedule is now complete too. `closeAdvance_gate1_run`
proves the literal final selector resets the round counter and advances the
cell cursor; `close_final_frame` carries the closed bracket and division
counter through the product/add/advance suffix; and
`accBisect_final_run` combines that frame with `close_run_exact`.  Its
array-level result proves the singleton bracket, exact 128-bit addition of
`d·s`, unchanged violation counters, round reset, cell increment, and array
frame for the actual `accBisect` program.  The four-instruction advance was
split into two two-instruction blocks after a direct all-at-once `simp` ran
for minutes; the retained staged proof keeps the same instruction list and
compiles as part of the full source in `5.46 s` at `796552 KiB` RSS.  The live
module build took `5.92 s` at `839912 KiB`, with one worker, the 2 GiB hard
cap, and no swap.  Fresh axiom prints for all five new refinement theorems
contain only `propext`, `Classical.choice`, and `Quot.sound` (the two close
lemmas do not require `Classical.choice`).

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

`LeanCompCert/Ports/CDEMAbelHead.lean` then decomposes the actual mixed
array/scalar `accHead` block without expanding it as one proof term.  For every
non-first, non-final bisection iteration, `accHead_middle_run` proves that the
literal selector/load/clear/scalar sequence reads and clears the scratch sink
cell, preserves every other array cell, and leaves carried `F`, `k`, square-root, increment,
violation, bracket, cell, and round state unchanged, computes the exact
ceiling/floor reciprocals of `k`, and sets both `U` product gates to zero.
This is the complete head contract for the 60 interior production rounds.
`accHead_last_run` supplies the corresponding final-round contract: the
last selector is one, the bisection selector remains one, the sink clear is
again explicit, the carried state and bracket are preserved, and both `U`
product gates stay zero.  Thus only the first-round window-cell transition
remains.  The proof is split into pre-load, scalar front, latch, and reciprocal
stages.  After the final-round addition, a fresh source check under the
one-thread 2 GiB zero-swap cap took `7.46 s` and peaked at `630436 KiB`; its
module build took `7.94 s` and peaked at `656320 KiB`.  Fresh axiom prints use
only `propext` and `Quot.sound` (the structural and scalar-stage theorems use
only `propext`).

The first-round proof is now staged as well: `headPre_first_run` proves the
literal selector and live window address, `headFK_first_run` proves the loaded
cell is added to wrapped `F` and latches the exact integer `k`, and
`headSqrt_noBump_run`/`headSqrt_bump_run` prove both branches of the checked
single-step square-root update.  `headDelta_run` now proves the next literal
stage too: the two's-complement absolute-value selector computes
`G = |1-F|`, and the gated subtraction pair computes exactly the positive and
negative parts of `G-E`.  This stage is itself split into the three-instruction
sign prefix, five-instruction selector, and six-instruction increment tail so
the compiler never elaborates the full head as one simplifier term.  The
first-round latch and reciprocal tail are now verified too, including the
exact `tv`, ceiling/floor, and positive/negative product gates.  Finally,
`headPost_first_noBump_run` and `headPost_first_bump_run` compose the complete
literal scalar postlude for both checked square-root branches.  The enlarged
`accHead_first_run` now lifts that result through the actual selector, live
window-cell load, and zeroing store.  It proves exactly that one source cell
is cleared, exposes the new `F`, `k`, square-root, `G`, increments,
reciprocals, `tv`, and both live `U` product gates, and frames the bisection
and loop state.  Together with the interior and final contracts, every
production `accHead` regime is now verified.  The enlarged source check took
`13.93 s`, peaked at `671660 KiB`, and used no swap; the module build took
`13.95 s` and peaked at `693688 KiB` under the same cap.
Fresh axiom prints use only `propext` and `Quot.sound`.

`LeanCompCert/Ports/CDEMAbelBody.lean` starts the per-integer composition at
the 60 interior regimes. `accBody_middle_run` applies the verified head,
proves the two zero-gated product blocks leave both `U` accumulators exact,
then applies the verified active bisection schedule. Its contract covers the
array frame, exact pure bracket step, both `U` and `V` values, all three
failure counters, round advance, and unchanged cell cursor for the literal
`accHead ++ accProd ++ accBisect` block. A dedicated four-register bisection
frame prevents normalization of the lifted array list. The fresh source check
took `4.43 s`, peaked at `601832 KiB` RSS, and used no swap under the
one-thread 2 GiB cap.
The live module build, including a rebuilt 13-second head dependency, took
`18.79 s` at `689016 KiB`. Fresh axiom prints contain only Lean's ordinary
foundations.

The final regime is now composed in the same module. `LastHeadSpec` exposes
the already-computed `dPos+dNeg` register; `accProd_zero_run` proves both
final zero-gated `U` stages are exact no-ops; and `accBody_final_run` feeds
that value to the verified consuming bisection. The literal body therefore
adds exactly `d·s` to `V`, closes the singleton bracket, increments the cell,
resets the round, and preserves the array, both `U` values, and all failure
counters. The enlarged source check took `8.17 s` at `628840 KiB`; the module
build took `8.36 s` at `617296 KiB`, under the one-thread 2 GiB zero-swap cap.

The first regime is now composed too. `accProd_exact_frame_run` packages both
exact nonzero `U` additions with the register and array frames, while
`accBody_first_run` connects the live-cell head, both products, and the
gate-zero initial bisection. The square-root handoff is an explicit executable
invariant: the checked head result must equal `Nat.sqrt (W+cell)` before the
initial bracket is opened. The body contract proves the one-cell clear, both
exact `U` increments, initial bracket, unchanged `V` and failure counters,
round advance, and fixed cell cursor. The enlarged source check took `13.15 s`
at `689356 KiB`; the module build took `13.35 s` at `693572 KiB`, with one
worker, the 2 GiB hard cap, and no swap. Thus all first, 60 interior, and final
`accBody` regimes now have LeanCompCert execution contracts.

`LeanCompCert/Ports/CDEMAbelSchedule.lean` now performs the finite scheduler
composition. `accIter_middle_ready` turns any finite family of explicit
`MiddleStepReady` machine states into one trace theorem, telescoping the pure
bracket, both `U` values, `V`, all failure counters, array, cell, and round
counter. `accSchedule_from_ready_middle` then composes the first contract,
that interior trace, and the final contract into `FullAccSpec`.
`final_step_exact` independently proves that `bsSteps = bsBudget` makes the
last active step close at `exactRoot`; the singleton final premise is not an
oracle. The source check took `0.16 s` at `584064 KiB` and the live module
build took `0.30 s` at `596164 KiB`, with one worker, the 2 GiB hard cap, and
no swap.

The production readiness envelope is now partly discharged rather than
postulated per round. `production_iter_quotient_guard` proves the checked
`W/midpoint ≤ 2^31` condition throughout every production sub-bracket, and
`production_forward_roundFit`, `production_forward_quotient_guard`, and
`production_forward_bracket` transport the complete arithmetic, quotient,
ordering, and word bounds to the scheduler's forward iterator.  The bisection
block also has an explicit latch frame for `k`, `dPos`, `dNeg`, gate, and zero;
`accBody_middle_latch_of_head` composes it through the actual head and both
product blocks.  A fresh bisection source/build check took `5.67/6.04 s` at
`767264/819720 KiB`.  The enlarged scheduler still checks in `0.35 s` at
`576576 KiB`.  The companion body proof is intentionally isolated because
normalizing its five carried projections together is expensive: its fresh
source check took `62.13 s` at `651648 KiB`, and its module build took
`76.72 s` at `708784 KiB` including rebuilt dependencies.  Every run used one
worker, a 2 GiB hard cap, and no swap; no native evaluator is used.

The finite production schedule is now closed. `FirstBodySpec` exposes the
latched key, signed increments, gate, and zero in addition to its accumulator
contract. `ProductionMiddleCore` carries those values together with the exact
round/cell counters, zero sink, and all register/array word bounds.
`accIter_production_ready` inductively constructs every interior
`MiddleStepReady` state from the actual first body; no family of 60 readiness
hypotheses remains. `accBody_final_of_production_core` derives the final
literal body from that endpoint and `final_step_exact`.
`accSchedule_production` composes the actual first body, all
`bsSteps - 1` interior bodies, and the final body into one `FullAccSpec` whose
bracket is the singleton `exactRoot`, whose `U` and `V` changes are exact, and
whose round/cell, failure-counter, and array effects match the program. Its
only terminal arithmetic premise is the explicit 128-bit `V` no-wrap bound.
Fresh axiom prints contain only `propext`, `Classical.choice`, and
`Quot.sound`. The enlarged body source/build checks took `110.90/111.68 s` at
`712556/734196 KiB`; the schedule source/build checks took `0.48/0.63 s` at
`600212/594072 KiB`. All four ran with one worker, a 2 GiB hard cap, and no
swap.

The accumulator array contract has since been strengthened to match the
literal outer loop. `SinkClearSpec` states that the head sets `c.sink` to zero
and preserves every other cell without assuming the incoming scratch value.
`MiddleBodyLiveSpec` and `FinalBodyLiveSpec` carry that fact through the
literal product and bisection blocks; the prior exact-array contracts are
derived only when an actual zero-sink premise is available. The refactored
body source/build checks took `111.36/112.59 s` at `710076/702300 KiB`, with
one worker, a 2 GiB hard cap, and no swap. The schedule consumer still checks
in `0.50 s` at `616048 KiB`. Fresh axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

`LeanCompCert/Ports/CDEMAbelOuter.lean` starts the literal outer-loop layer.
`selectors_acc_run` proves the five selector instructions set the sieve and
mark gates to zero and the accumulation gate to one in the live accumulation
range. `tail_continue_run` proves the six-instruction tail increments the
period cursor without moving the window base, while `tail_wrap_run` proves the
terminal cursor resets to zero and advances the window base by exactly
`segLen`; all three preserve the array. The source check took `0.25 s` at
`588812 KiB`, and the module build took `0.33 s` at `596492 KiB`, with one
worker, the 2 GiB hard cap, and no swap. Fresh axiom prints use only `propext`
and `Quot.sound`.

The outer layer now also proves the two inactive array stages rather than
silently treating them as no-ops. `sieve_inactive_live_frame` and
`mark_inactive_live_frame` split each emitted block around its single store,
prove the inactive selector routes that store to `c.sink`, and frame every
other cell. This matters because the sieve deliberately writes a nonzero
squarefree code to the sink during accumulation rounds. A rejected one-shot
symbolic simplification expanded the unrelated trial-division arithmetic and
was interrupted; the retained store-local proofs compile with the full outer
source in `1.89 s` at `617116 KiB`, and the live module build takes `2.54 s`
at `641848 KiB`, under the same cap and with no swap. Their axiom prints use
only `propext` and `Quot.sound`.

Still not proved: composition of this now-complete 62-iteration accumulator
schedule with the μ-table build and window marking, the global accumulator
no-wrap invariant, and the outer loop to
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

## 9. Literal outer-body accumulation proof

`LeanCompCert/Ports/CDEMAbelOuter.lean` now composes the actual emitted body,
not an isolated model of the accumulator.  In an accumulation round it proves
that the selector enables the accumulator, the inactive sieve and marking
stages can write only to the scratch sink, the marking stage preserves the
live cell and violation counters, and the middle accumulator step satisfies
its arithmetic contract before the tail executes.  The resulting theorem is
`body_middle_live_run`; its array contract deliberately says that the scratch
sink is cleared while every live cell is preserved.

A fresh `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
`body_middle_live_run` and `[propext, Quot.sound]` for its prefix-latch lemma.
There is no computation oracle or project trust declaration in either proof.

The proof is intentionally isolated behind local heartbeat and recursion-depth
options so importing the module does not relax limits elsewhere.  With one
Lean worker, no swap, `MemoryHigh=1536M`, and a hard `MemoryMax=2G`:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| fresh source compilation | 36.18 s | 678,552 KiB | 0 |
| `lake build LeanCompCert.Ports.CDEMAbelOuter` | 36.87 s | 689,964 KiB | 0 |

The next checkpoint adds `body_final_live_run`, which composes the same literal
prefix with the last accumulator round and tail.  It proves singleton bracket
closure, the exact `d * s` addition to the wide `V` accumulator, round reset,
cell advance, live-cell preservation, and scratch clearing.  Its fresh axiom
print is again `[propext, Classical.choice, Quot.sound]`.

Because the module now checks both complete literal-body theorems, its current
fresh source/build measurements under the same cap are:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| fresh source compilation | 64.88 s | 688,292 KiB | 0 |
| `lake build LeanCompCert.Ports.CDEMAbelOuter` | 65.24 s | 726,364 KiB | 0 |

`body_first_live_of_acc` now supplies the remaining literal composition seam:
given the already verified `FirstBodySpec` for the accumulator sub-block, it
composes the actual selector, inactive sieve, inactive mark, accumulator, and
tail.  Its `WindowClearLiveSpec` records the real first-round behavior: the
current live window cell is cleared and all other live cells are preserved,
but scratch is not falsely claimed to be zero.  A fresh axiom print reports
only `[propext, Quot.sound]` for this composition theorem.

With all three emitted-body compositions present, the current capped checks
are:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| fresh source compilation | 65.46 s | 746,564 KiB | 0 |
| `lake build LeanCompCert.Ports.CDEMAbelOuter` | 65.22 s | 737,888 KiB | 0 |

The finite outer iterator and the production invariant that supplies the first
accumulator contract remain before the retained production trace has a
complete denotation proof.

`LeanCompCert/Ports/CDEMAbelOuterSchedule.lean` now supplies that finite
iterator layer without re-elaborating the expensive body proofs.
`bodyIter_middle_contracts` telescopes any finite family of literal middle-body
contracts, including live-array preservation and scratch clearing after every
nonempty trace. `bodySchedule_of_contracts` then composes literal first,
middle, and final contracts into `OuterFullAccSpec`, with the exact two wide
`U` additions, exact wide `V` addition, cleared window cell, cleared sink,
round reset, and cell advance.

Fresh axiom prints are `[propext, Quot.sound]` for the iterator and `[propext]`
for the final contract composition. Under the one-worker 2 GiB zero-swap cap:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| fresh scheduler source | 0.28 s | 579,444 KiB | 0 |
| scheduler module build | 0.34 s | 565,872 KiB | 0 |

The remaining local scheduling obligation is now readiness: derive each
literal body contract from a production invariant that also tracks the period
cursor and window base. The denotation proof must then connect the resident
Möbius table and streamed floor convolution to that invariant.

The prefix contract now also exposes the accumulation phase gate, period
cursor, and window base, and `body_acc_run_decomp` seals the large emitted-body
decomposition behind a compiled lemma. In the scheduler module,
`accBody_cursor_frame` proves that the accumulator sub-block preserves those
three registers. `body_cursor_continue_run` and `body_cursor_wrap_run` then
compose the literal body with the six-instruction tail to prove the two cursor
branches: advance within the period, or reset the cursor and advance the
window base by `segLen`.

The repeated literal-list framing that initially exhausted local heartbeat
limits was replaced by the prefix contract and one reusable accumulator frame.
Only the two cursor theorems have a local three-million-heartbeat allowance;
the global setting remains unchanged. Current capped measurements are:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| outer module build after sealed frames | 67.31 s | 742,764 KiB | 0 |
| scheduler source with cursor branches | 71.75 s | 640,420 KiB | 0 |
| scheduler module build | 71.42 s | 636,960 KiB | 0 |

Fresh axiom prints use `[propext]` for the accumulator frame and `[propext,
Quot.sound]` for both literal cursor branches. The next readiness step can now
track exact cursor/window movement without unfolding the emitted body.

`LeanCompCert/Ports/CDEMAbelOuterReady.lean` packages the corresponding finite
trace arithmetic. `bodyIter_succ_start` and `bodySchedule_eq_bodyIter` prove
that a cell schedule is exactly `middleCount + 2` literal body iterations.
`bodyIter_cursor_contracts` telescopes per-step continue contracts, and
`bodySchedule_cursor_of_contracts` concludes exact cursor advance with an
unchanged window base. This module imports the compiled cursor semantics and
therefore remains cheap:

| check | elapsed | peak RSS | swap |
| --- | ---: | ---: | ---: |
| fresh readiness source | 0.30 s | 594,740 KiB | 0 |
| readiness module build | 0.43 s | 612,536 KiB | 0 |

Fresh axiom prints use only `[propext]` or `[propext, Quot.sound]`. What remains
is to discharge each per-step contract from the production arithmetic
invariant, selecting continue for all nonterminal iterations and wrap at the
end of a full window.

After adding the readiness module to the umbrella import, a serialized
`lake build LeanCompCert` completed in 0.63 s with zero swap under the same
2 GiB hard cap. GNU `time` reported 1,730,380 KiB RSS, but a later run that
also sampled the enclosing cgroup recorded only 216,588,288 bytes at the
kernel boundary (0.73 s, GNU `time` 1,729,056 KiB). The disparity comes from
the imported/shared mappings counted by `time`; cgroup `memory.peak` is the
authoritative hard-limit measurement.

The production readiness gap is now closed at the literal cell-schedule
level. `FirstStepReady` lists the finite word, square-root-step, and wide-product
guards consumed by the emitted first accumulator round, and
`body_first_ready_run` derives the first literal-body contract from those
guards instead of assuming that contract. `ProductionOuterMiddleCore` carries
the key, signed increments, round and cell counters, cursor/window position,
and machine-word invariants. `bodyIter_production_middle_ready` proves every
middle literal-body contract and threads that core through the actual tail
continue branch.

Finally, `bodySchedule_production_ready` composes the first, all middle, and
final literal bodies into `OuterFullAccSpec`. Its accompanying
`ProductionCellCursorSpec` selects the real tail branch: an interior cell
advances the cursor, while the last cell resets it and advances the window by
`segLen`. The proof uses the definitional production period
`markSteps + segLen * (bsSteps + 1)`; no cursor outcome is supplied as a
semantic assumption. A fresh axiom print for the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

The kernel cgroup peak is the authoritative memory measurement here; GNU
`time` includes imported/shared mappings and reported a larger RSS. With one
Lean worker, no swap, `MemoryHigh=1536M`, and `MemoryMax=2G`:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh readiness source | 61.12 s | 644,860 KiB | 210,149,376 B | 0 |
| readiness consumer build | 2 min 15.90 s | 682,880 KiB | 270,831,616 B | 0 |
| fresh capstone axiom print | 0.14 s | 524,472 KiB | 85,983,232 B | 0 |

The remaining production proof is below this scheduler boundary: establish
`FirstStepReady` and the named first-round values from the resident Möbius
table and streamed floor-convolution invariant, then telescope the proven
cell theorem across all windows.

`LeanCompCert/Ports/CDEMAbelSourceReady.lean` now discharges the first half of
that boundary in source-shaped terms. `SqrtStreamInv` records that the current
root square is at most the next integer, the stored `rT2` is the next square,
and the square after one bump is strictly above the integer. From those three
facts, `sqrtStream_step` proves that the literal branch is exactly `Nat.sqrt`
and `sqrtStream_key_closed` proves its one-bump guard.

`FirstEntryInv` names the next streamed floor-convolution cell through
`nextF`, and states the signed deltas, reciprocals, and wide no-wrap bounds in
those source values. `firstStepReady_of_entry` transports this invariant
through the actual selector/inactive sieve/inactive mark prefix and derives
`FirstStepReady`. `firstValues_of_entry` proves that the five machine outputs
are precisely `nextKey`, `nextDPos`, `nextDNeg`, `nextCeil`, and `nextFloor`.
The source-facing capstone `bodySchedule_production_of_entry` then invokes the
complete literal scheduler, with no preassembled first-body contract or opaque
post-head values. Its fresh axiom print is `[propext, Classical.choice,
Quot.sound]`.

Under one worker, the 2 GiB hard cgroup, and zero swap:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh source-readiness source | 9.45 s | 636,176 KiB | 200,507,392 B | 0 |
| source-readiness module build | 9.67 s | 622,068 KiB | 197,959,680 B | 0 |
| fresh source capstone axiom print | 0.15 s | 524,804 KiB | 85,995,520 B | 0 |

The remaining denotation work is now the finite window invariant itself:
prove that the resident Möbius marking phase installs the `nextF` cell, carry
`FirstEntryInv` and the exact wide accumulator values between cells/windows,
and telescope the source-facing cell theorem across the 5,000 windows.

The cell capstone now carries that finite invariant's persistent stream state,
not only the Abel sums. `FirstBodySpec` proves the literal first round updates
`rF`, the square-root cursor `rT`/`rT2`, the sign latch `rE`, and total
variation `rTv`. `accBody_stream_frame_of_head` proves directly from the
emitted product and bisection blocks that the middle and final rounds preserve
those registers. The outer first/middle/final contracts and their finite
middle telescope expose the same equations, so `OuterFullAccSpec` and
`bodySchedule_production_of_entry` now report the complete post-cell stream
state. The first outer proof requires the source-true guard `rC < segLen` to
show that `rC + winBase` is a live address rather than the sink.

All runs below used one requested Lean worker, `MemoryHigh=1536M`,
`MemoryMax=2G`, `MemorySwapMax=0`, and no concurrent compiler. Kernel cgroup
peaks are authoritative:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh accumulator-body source | 2 min 9.55 s | 739,420 KiB | 353,476,608 B | 0 |
| accumulator-body module build | 2 min 9.27 s | 757,928 KiB | 402,632,704 B | 0 |
| fresh strengthened outer source | 3 min 44.77 s | 750,392 KiB | 365,830,144 B | 0 |
| fresh middle telescope source | 1 min 13.85 s | 637,972 KiB | 204,304,384 B | 0 |
| readiness source | 1 min 0.65 s | 647,332 KiB | 216,190,976 B | 0 |
| source-facing capstone source | 9.51 s | 621,340 KiB | 179,593,216 B | 0 |
| cached-chain capstone build | 2 min 22.93 s | 659,272 KiB | 251,199,488 B | 0 |
| fresh source capstone axiom print | 0.15 s | 524,852 KiB | 86,536,192 B | 0 |
| cached LeanCompCert umbrella build | 0.74 s | 1,727,444 KiB | 215,973,888 B | 0 |

The source capstone still prints exactly
`[propext, Classical.choice, Quot.sound]`. The strengthened outer source is a
known expensive elaboration unit, but its 349 MiB kernel peak is safely below
the hard cap; it is therefore built serially and benchmarked rather than
replaced by an opaque or native decision shortcut.

`LeanCompCert/Ports/CDEMAbelSourceTelescope.lean` now closes the interior-cell
source-state handoff. `interior_stream_step_of_full` combines the literal full
cell and cursor contracts to prove that an interior cell keeps the next
resident marked array value, advances `rF`, `rE`, and `rTv` exactly, and
re-establishes `SqrtStreamInv` for the next integer. In particular its
`nextF` equation is the source recurrence using the next pre-marked cell; no
array value is supplied as a postcondition.

The same module proves generic word and untouched-register frames for
`bodyIter` and `bodySchedule`. `InteriorNextBounds` contains only the genuinely
numerical next-cell guards (word-sized square cursor, deltas, reciprocals, and
wide no-wrap bounds). `interior_firstEntry_of_full` combines that compact
envelope with the code-derived stream/cursor/array facts to reconstruct the
complete `FirstEntryInv` for the actual next interior cell. The remaining
source denotation is consequently concentrated at window-start marking and at
proving `InteriorNextBounds` from global production bounds.

Under the same serialized one-worker 2 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh interior telescope source | 6.43 s | 660,460 KiB | 218,357,760 B | 0 |
| interior telescope module build | 6.65 s | 696,952 KiB | 278,249,472 B | 0 |
| fresh two-theorem axiom print | 0.14 s | 525,268 KiB | 86,261,760 B | 0 |
| cached umbrella consumer build | 0.73 s | 1,729,924 KiB | 217,202,688 B | 0 |

Both new capstones print only `[propext, Classical.choice, Quot.sound]`.

`LeanCompCert/Ports/CDEMAbelMark.lean` begins the active window-marking
denotation. `markBody_first_active` is a theorem about the complete literal
emitted `markBody`: at `rR = 0` it proves the resident update
`window[0] := window[0] + μ(1)` modulo the machine word, with `μ(1) = +1`,
and the exact following cursor `(d, sign, multiple, cell) = (1, +1, 1, 0)`.
The proof factors the instruction list into reset, store, divisor head,
store-free table lookup, cursor commit, and budget suffix. This replaces an
initial monolithic normalization that remained memory-safe but repeated the
same tail work for minutes.

Under the serialized one-worker 2 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh active-first-mark source | 1.87 s | 611,256 KiB | 171,847,680 B | 0 |
| active-first-mark module build | 1.94 s | 627,536 KiB | 201,203,712 B | 0 |
| fresh capstone axiom print | 0.15 s | 525,572 KiB | 88,100,864 B | 0 |
| cached umbrella consumer build | 0.63 s | 1,729,988 KiB | 217,079,808 B | 0 |

The capstone prints only `[propext, Quot.sound]`. The next marking step is to
give the active non-start mark/cursor transition a source state and telescope
it over the finite `markSteps` budget.

The same module now proves the arbitrary active resident-store case.
`markBody_active_resident_store` states that whenever a non-start marking
cursor has `cell < segLen`, the complete emitted body performs exactly
`window[cell] := window[cell] + sign (mod 2^64)` and preserves every other
array cell. The theorem accepts any word-sized signed code, so later source
refinement can specialize it to the resident Möbius codes `1` and `2^64-1`
without rebuilding the instruction semantics.

Under the same serialized one-worker 2 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh extended mark source | 2.45 s | 650,156 KiB | 215,531,520 B | 0 |
| extended mark module build | 2.54 s | 681,908 KiB | 262,750,208 B | 0 |
| fresh two-capstone axiom print | 0.17 s | 535,960 KiB | 98,861,056 B | 0 |
| cached umbrella consumer build | 0.63 s | 1,729,928 KiB | 217,788,416 B | 0 |

Both marking capstones print only `[propext, Quot.sound]`. Remaining marking
work is the out-of-range divisor-advance transition, cursor telescoping, and
the source identification of the resulting resident convolution window.

The live out-of-range transition is now proved as well.
`markBody_active_cursor_advance` follows the complete literal emitted
`markBody` when `cell ≥ segLen` and `d < kBound`: the suppressed array write
lands only in the sink, `d` advances to `d+1`, the resident table entry at
`muBase+d+1` is loaded, codes `0/1/2` are decoded to `0/+1/-1`, the first
multiple `(d+1 - W % (d+1)) % (d+1)` is selected (or `segLen` for code zero),
and the final cursor mux commits those values. The proof splits the emitted
middle at literal instruction boundaries into a six-instruction load/decode
block and a thirteen-instruction offset/parking block; this avoids the
recursive term expansion encountered by the initial monolithic proof.

Under the same serialized one-worker 2 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh extended cursor source | 10.62 s | 739,648 KiB | 323,117,056 B | 0 |
| extended cursor module build | 10.86 s | 694,128 KiB | 295,129,088 B | 0 |
| fresh three-theorem axiom print | 0.16 s | 524,184 KiB | 87,564,288 B | 0 |
| cached umbrella consumer build | 0.64 s | 1,732,332 KiB | 217,268,224 B | 0 |

The prefix, middle, and complete transition each print only
`[propext, Quot.sound]`. Remaining marking work is the terminal cursor case,
the finite `markSteps` telescope, and identification of the finished resident
window with the source divisor convolution.

The terminal branch is now complete too. `markBody_active_cursor_terminal`
proves that an active non-start cursor at `d = kBound` with an out-of-window
multiple leaves the divisor at `kBound`, parks `(sign,multiple)` at
`(0,segLen)`, and frames every non-sink array cell. The first direct terminal
normalization was stopped when its term expansion approached the memory cap.
The successful proof instead frames the arbitrary eight-instruction offset
calculation and normalizes only the final five-instruction exhausted-parking
block.

These checks used an even stricter serialized one-worker cgroup:
`MemoryHigh=1G`, `MemoryMax=1536M`, `MemorySwapMax=0`.

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh terminal cursor source | 15.57 s | 793,204 KiB | 378,474,496 B | 0 |
| terminal cursor module build | 15.86 s | 830,464 KiB | 445,353,984 B | 0 |
| fresh three-theorem axiom print | 0.15 s | 524,356 KiB | 88,109,056 B | 0 |
| cached umbrella consumer build | 0.63 s | 1,730,524 KiB | 219,435,008 B | 0 |

All three terminal theorems print only `[propext, Quot.sound]`. Every active
out-of-window branch now has literal semantics. The in-window cursor handoff
was the remaining per-iteration component.

`markBody_active_resident_transition` now strengthens the resident-store
contract to the complete in-window transition: after the exact modular array
write, the divisor and wrapped sign are unchanged and the next multiple is
`cell+d`. The nine-instruction cursor head is represented by exact literal
2/1/2/4-instruction blocks so no simplifier invocation expands the whole
head. These checks used the same one-worker 1.5 GiB zero-swap cap:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh complete resident transition source | 13.60 s | 716,212 KiB | 313,102,336 B | 0 |
| complete resident transition module build | 14.16 s | 759,888 KiB | 379,219,968 B | 0 |
| fresh capstone axiom print | 0.16 s | 528,652 KiB | 89,399,296 B | 0 |
| cached umbrella consumer build | 0.63 s | 1,730,888 KiB | 215,240,704 B | 0 |

The new capstone prints only `[propext, Quot.sound]`. Every active mark-body
branch now has complete literal array and cursor semantics; remaining marking
work is the finite `markSteps` telescope and source identification of the
completed resident divisor-convolution window.

`CDEMAbelMarkSchedule.lean` now lifts the first active resident mark through
the literal selector, inactive sieve, inactive accumulator, and period tail.
The proof records two scheduler details that syntactic register/array framing
would miss: the inactive accumulator clears the designated sink cell, and its
cell-cursor instruction writes `rC + 0` rather than leaving `rC` untouched.
Dedicated LeanCompCert lemmas prove the correct non-sink array frame and the
semantic zero-cursor preservation.  The scheduler proof is split at the
before-accumulator and before-tail boundaries; this reduced a monolithic
heartbeat timeout to a short bounded build.

These checks used one requested Lean worker and the strict cgroup
`MemoryHigh=1G`, `MemoryMax=1536M`, `MemorySwapMax=0`:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh first-mark scheduler source | 22.15 s | 650,752 KiB | 230,064,128 B | 0 |
| first-mark scheduler module build | 22.60 s | 656,388 KiB | 251,432,960 B | 0 |
| fresh six-theorem axiom print | 0.16 s | 544,076 KiB | 106,668,032 B | 0 |
| cached umbrella consumer build | 0.64 s | 1,735,796 KiB | 222,011,392 B | 0 |

The public scheduler capstones print only `[propext, Quot.sound]` (the
cell-zero helper needs only `propext`).  The actual first scheduled marking
iteration now has a code-derived live-array update, exact divisor/sign/
multiple/cell state, period cursor `1`, and unchanged window base.  The next
marking task is to lift the three non-start mark transitions through the same
scheduler and telescope the finite `markSteps` interval.

`CDEMAbelMarkScheduleStep.lean` completes that scheduler lift. A common
`markPrelude_run` proves the active selector and inactive-sieve state, while
`markSuffix_run` carries an arbitrary proved mark effect through the real
inactive accumulator and continuing period tail. The three public
instantiations cover an in-window resident update, a live divisor advance and
resident-code decode, and the terminal divisor park. Each preserves the zero
accumulation cell and advances the period cursor by exactly one.

Under the same serialized one-worker 1.5 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh non-start scheduler source | 4.21 s | 654,880 KiB | 225,173,504 B | 0 |
| non-start scheduler module build | 4.84 s | 605,532 KiB | 189,763,584 B | 0 |
| fresh five-theorem axiom print | 0.17 s | 532,144 KiB | 91,197,440 B | 0 |
| cached umbrella consumer build | 0.63 s | 1,731,792 KiB | 217,022,464 B | 0 |

All scheduler-step capstones print only `[propext, Quot.sound]`. Every active
marking branch now has both complete literal `markBody` semantics and an
actual scheduled-body theorem. The remaining marking proof is the finite
cursor trace/telescope and its identification with the source resident
divisor convolution.

`CDEMAbelMarkTelescope.lean` adds the executable finite cursor used for that
trace. `MarkState.step` has exactly the resident-update, divisor-advance, and
terminal-park branches; `body_markState_step` refines one literal scheduled
body to that function. `bodyIter_markState_refines` telescopes any finite
ready trace, while `body_first_markState_rep` and
`bodyIter_markState_from_start` connect it to the actual first `mu(1)` body.
The machine theorem therefore starts from emitted code rather than an
assumed post-reset surrogate.

Under the serialized one-worker 1.5 GiB zero-swap cgroup:

| check | elapsed | GNU time peak RSS | cgroup `memory.peak` | swap |
| --- | ---: | ---: | ---: | ---: |
| fresh finite mark telescope source | 20.48 s | 653,192 KiB | 210,993,152 B | 0 |
| finite mark telescope module build | 18.62 s | 698,960 KiB | 276,439,040 B | 0 |
| fresh four-theorem axiom print | 0.14 s | 526,188 KiB | 88,313,856 B | 0 |
| cached umbrella consumer build | 0.73 s | 1,732,180 KiB | 215,953,408 B | 0 |

All telescope capstones print only `[propext, Quot.sound]`. The remaining
source refinement is now purely finite arithmetic over `MarkState`: prove
the production resident table makes every iterated cursor `MarkStepReady`,
use the explicit `markBudget` bound to reach the terminal cursor, and identify
the completed executable plane with `Ref.deltaF` on each window cell.
