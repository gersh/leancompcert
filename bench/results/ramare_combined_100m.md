# Ramaré combined 100-million port: measured costs

Measured 2026-08-06 on the repository host (`aarch64`, Cortex-X925 up to
3.9 GHz), with CompCert 3.17 and GCC 13.3.  Times are `/usr/bin/time` user
times; all runs exited `0` and used under 1 MiB RSS.

## Word-sized psi transition

`bench/RamarePsiQREmit.lean` emits exactly
`RamareCombined100M.PsiQRBlock.program`, whose compiler correspondence is
`PsiQRBlock.program_compiled`.  Its loop body is 22 scalar instructions.  The
timing harness calls the emitted one-step function 100,000,000 times through a
volatile accumulator.

| compiler | user time | ns/call |
| --- | ---: | ---: |
| CompCert 3.17 `-O2` | 0.78 s | 7.8 |
| GCC 13.3 `-O2` | 0.16 s | 1.6 |

The suffix contains `100,000,000 - 10,001 + 1 = 99,990,000` candidates and
updates two psi endpoints per candidate.  At the CompCert rate the two exact
quotient transitions therefore cost about **1.56 core-seconds** in total.
They are not the runtime bottleneck.

Reproduction:

```bash
lake env lean --run bench/RamarePsiQREmit.lean 100000000 /tmp/ramare_psi_qr.c
ccomp -O2 -o /tmp/ramare_psi_qr.ccomp /tmp/ramare_psi_qr.c
gcc -O2 -o /tmp/ramare_psi_qr.gcc /tmp/ramare_psi_qr.c
/usr/bin/time /tmp/ramare_psi_qr.ccomp
/usr/bin/time /tmp/ramare_psi_qr.gcc
```

## Flat factor-classification baseline

The current source model intentionally uses two fixed bounded divisor scans
per candidate.  `bench/TrialDivisionEmit.lean` emits the already-proved
trial-division fold.  A 100,000,000-round calibration (`fuel=10,000`,
`div=10,000`) measured:

| compiler | user time | ns/trial round |
| --- | ---: | ---: |
| CompCert 3.17 `-O2` | 0.95 s | 9.5 |
| GCC 13.3 `-O2` | 0.61 s | 6.1 |

The literal reference route performs

```text
2 · 99,990,000 candidates · 10,000 rounds
  = 1,999,800,000,000 trial rounds.
```

Its measured CompCert projection is therefore **18,998 s = 5.28 core-hours**
before the much cheaper strip, interval, and checkpoint arithmetic.  This is
a baseline, not the final implementation target: the segmented-sieve route
removes the `10,000`-round factor and is expected to be orders of magnitude
faster.

The flat route is nevertheless operationally shardable.  Splitting the
candidate interval into 20 contiguous shards gives about **16 minutes wall
time** at ideal 20-way utilization, plus checkpoint/merge overhead.  Each
shard must carry and verify its exact entry and exit state; independent shards
with guessed seams would not prove the source fold.

Reproduction of the calibration:

```bash
lake env lean --run bench/TrialDivisionEmit.lean \
  10001 10000 10000 18446744073709551615 /tmp/ramare_trial.c
ccomp -O2 -o /tmp/ramare_trial.ccomp /tmp/ramare_trial.c
gcc -O2 -o /tmp/ramare_trial.gcc /tmp/ramare_trial.c
/usr/bin/time /tmp/ramare_trial.ccomp
/usr/bin/time /tmp/ramare_trial.gcc
```

## Segmented shape classifier

`Ports/RamareCombined100MShapeSieve.lean` replaces the two bounded divisor
scans with a seven-plane prime-power segmented sieve.  The planes retain the
first two distinct prime bases, their exponents and their exact prime-power
products, so the classification phase produces the six `Shape` fields without
an exponentiation loop.  `ShapeSieve.program_compiled` instantiates the
verified array/CCIR compiler bridge.  A kernel smoke covers primes, prime
powers, two-prime cells and a three-distinct-prime cell.

The exact production suffix `[10001, 100000000]` was run as 100 windows of
999,900 cells with the complete 1,229-prime table for `sqrt(10^8)`.  The
positive artifact classified all 99,990,000 candidates and returned zero in
both failure classes.  A control with the mark budget halved failed the mark
coverage guard in every window.

| artifact | emit user / RSS | CompCert `-O2` user / RSS | run user / RSS | result |
| --- | ---: | ---: | ---: | --- |
| positive | 0.33 s / 532,296 KiB | 0.31 s / 79,452 KiB | 9.61 s / 55,996 KiB | guards 0; seen 99,990,000 |
| half-budget control | 0.26 s / 534,460 KiB | 0.28 s / 79,592 KiB | 5.43 s / 55,996 KiB | guards 100; mark 100 |

The program has a 207-instruction body, 426,020,600 loop iterations, and a
111,998,672-byte static array.  Exact hashes:

```text
positive C      aa222123bc751266392d65d92b99fbc02c82fb36cb674b8610bcd704f99fb224
positive binary c5f9952dad6d292b6012e1236d2b577e32fe8ffdf5da70075767c73a6f7b3a5a
control C       0b83ee1673351a85c77034e36561a5492406551769dcb344679250204d317d6b
control binary  a358c42199c500abbedd7ef2d31c1b868614a20967fd4c6ff9bfc3460e9c8167
```

Reproduction, with no swap and hard memory caps around each phase:

```bash
lake env lean --run bench/RamareCombined100MShapeEmit.lean \
  positive 10001 999900 100 100000000 /tmp/ramare_shape_full.c
ccomp -O2 -o /tmp/ramare_shape_full /tmp/ramare_shape_full.c
/tmp/ramare_shape_full

lake env lean --run bench/RamareCombined100MShapeEmit.lean \
  control 10001 999900 100 100000000 /tmp/ramare_shape_full_control.c
ccomp -O2 -o /tmp/ramare_shape_full_control \
  /tmp/ramare_shape_full_control.c
/tmp/ramare_shape_full_control
```

This retires the factorisation runtime bottleneck.  It does not by itself
retire the combined run axiom: the remaining work is to append the Ramaré
candidate arithmetic and quotient-state carry to the classification phase,
then prove the seven-plane number-theoretic refinement at the consumer
boundary.

The classifier instruction list is now definitionally factored into
kernel-small index, plane-address, sink, load, normalization, first/second
shape, tail, two exact-product guard, commit, and clear stages without changing
the emitted program.  Exact run theorems cover every stage, including the
seven load/store bounds, nonzero normalized divisors, all six decoded `Shape`
registers, both product checks, both violation counters, and the seen counter.
`classBody_candidate_run` composes the full mixed block and proves that the
candidate register is exactly `windowBase + liveOffset` and that the live gate
remains one.  The reusable `Verified/ArrayRegFrame.lean` framing theorem makes
that composition inspect only instruction destinations, so it never
normalizes the decoder arithmetic.  The leading mark/class phase selector is
also isolated and proved exact; destination framing carries it through the
remaining mark instructions and the loop tail, so `body_candidate_run`
derives the live gate and exact candidate for the complete loop body rather
than assuming the gate at classifier entry.  The expanded capped source
compile took **78.07 wall-seconds**, **3,345,568 KiB peak RSS**, and zero swap.

The physical mark loop is now split, with the emitted order unchanged, into
cursor reset, address selection, seven loads, all-product, first-prime,
second-prime, and cursor-advance blocks.  The separate
`RamareCombined100MMarkRefinement.lean` proves exact reset/preservation,
seven live addresses and loads, all-product writeback, first-prime
selection/exponent/product updates, and second-prime flag/commit/exponent
updates.  The second exact-product update, power-vs-prime cursor choice,
clamped table index, exact next-row load, selected power/base values,
next-multiple offset (including the sentinel), and budget-failure accounting
are now exact as well.  The selector, clamped load, value, offset, and budget
lemmas are composed into an exact theorem for the emitted
`Cfg.markAdvanceBody`; it preserves the round, word, and array while proving
the new cursor and both failure counters.  The all-product, first-prime, and second-prime blocks
are then composed into one exact `PlaneCell.markPower` transition: seven
physical plane writes and a positive-width read-after-write theorem establish
the complete cell update without normalizing the combined 43-instruction
stream.  Its expanded capped direct source check took **3.20 wall-seconds**,
**781,208 KiB peak RSS**, and zero swap.  The deliberately split proof avoids
normalizing the full 120-instruction mark core.

The separate `RamareCombined100MMarkInvariant.lean` then proves the
number-theoretic row fold.  It identifies the first, second, and later-prime
power-event modes; proves that a complete positive-power block is exactly
`RamareCombined100MSeg.markPrime`; and folds distinct active rows from the
seven zero planes to `RamareCombined100MSeg.markCell`.  `Cfg.ofChain` now uses
the extensionally identical bounded-trial table, whose entries are
definitionally at least two and whose filtered range is proved duplicate-free;
this specializes the row-fold theorem to the exact production table.  Its
expanded capped direct source check took **0.38 wall-seconds**, **552,136 KiB
peak RSS**, and zero swap.

`RamareCombined100MCursorInvariant.lean` now closes that obligation at the
selected-cell level.  It reuses the audited segmented-Möbius residue-cursor
arithmetic to prove that each finite live progression reaches an offset
exactly when its translated integer is divisible by the represented power.
It then proves that the divisible powers among the fixed exponents `1..32`
form a prefix, identifies their length with `exponent32`, folds every power
cursor to `markRange`, and folds every production-table row to `markCell`.
The theorem is specialized to the exact `Cfg.ofChain` table at every live
window offset.  Its expanded capped direct source check took **0.54
wall-seconds**, **597,176 KiB peak RSS**, and zero swap.

`RamareCombined100MCursorMachine.lean` adds the finite power-aware state
machine needed for the emitted marking loop.  It proves exact live-prefix,
power-bump, next-table-row, terminal-sentinel, and slack behavior, then
composes those cases over an explicit phase chain.  It also proves that the
complete emitted advance block implements one pure power-cursor transition,
with its table and word-safety premises explicit.  It now also composes the
live-hit, live-other-offset, and exhausted cases through the complete emitted
address/load/cell/advance iteration; proves that the mark-phase classifier
clears only sink cells; frames the classifier and loop tail around the
selected cell and cursor; and proves the emitted phase/reset semantics.  This
expanded generic source check took **7.01 wall-seconds**, **768,776 KiB peak
RSS**, and zero swap.  The separate
`RamareCombined100MProductionPhases.lean` checker evaluates only the
few-thousand closed production descriptors; it does not reduce the
3.26-million-round mark loop.  Its capped module build took **46.89
wall-seconds**, **12,051,732 KiB peak RSS**, and zero swap.  This is the
intentionally isolated high-water kernel check and remains below the
documented 20/22 GiB build limits.
Regenerating the production C
after this refactor gives the same SHA-256 `aa222123bc751266392d65d92b99fbc02c82fb36cb674b8610bcd704f99fb224`;
the full run still reports `guards 0 seen 99990000 mark 0 shape 0`.

### Exact log-ladder carry

`Ports/RamareCombined100MLogSweep.lean` appends the two word-safe RS62
increment formulas to the classifier and carries `logL`/`logU` across segment
boundaries.  Its `program_compiled` theorem covers the extended program, while
kernel controls compare both carried outputs against direct folds of
`incLWord` and `incUWord` over `[11,30]`.

The physical suffix is factored without changing its emitted instruction
sequence into the named `lowerScalarBody`, `upperScalarBody`, and
`commitScalarBody` blocks.  The lower block is further split into arithmetic
stages of at most four instructions.  `lowerNumeratorBody_run`,
`lowerCorrectionBody_run`, and `lowerFinalizeBody_run` compose kernel-small
per-instruction proofs, and `lowerScalarBody_run` proves that all nine emitted
instructions compute exactly `incLWord` while preserving the candidate and
array.  The upper path now uses the same method: `upperScalarBody_run` proves
all thirteen instructions compute exactly `incUWord`.  Four single-instruction
commit proofs compose into `commitScalarBody_run`, and `candidateBody_run`
joins both increments with the exact classification-gated updates of the two
carried log endpoints.  The theorem preserves the candidate and complete
array and keeps every no-wrap condition explicit.  No instruction in the
26-instruction suffix remains semantically opaque.

A capped source compile of the complete candidate semantics took **71.99
wall-seconds**, **2,536,088 KiB peak RSS**, and zero swap; its live lambda/psi
consumer compiled in **40.09 wall-seconds** at **3,095,376 KiB** and zero swap
under a 20/22-GiB physical-memory cgroup.  During development, one
unresolved simplifier goal involving the literal `1 % 2^64` grew to
**20,021,928 KiB RSS** before Lean reported its internal out-of-memory
condition.  The virtual-memory cap contained that failure.  Supplying the
one-line modular fact explicitly restored the 2.49-GiB source compile; this is
the concrete failure mode behind the earlier high-memory behavior.  A later
six-instruction upper proof similarly reached **19,251,208 KiB RSS** and a
kernel-recursion error; splitting it into one- and two-instruction lemmas
restored the 2.51-GiB compile without changing emitted code.

The exact production run starts from the kernel-certified `prefixState10`
endpoints and returns:

```text
logL 5184959831595253
logU 5184961464486049
```

The 233-instruction program completed the full suffix in 10.69 user seconds
(10.72 wall) at 55,996 KiB RSS, with zero classifier guards and exactly
99,990,000 commits.  Emitting the zero-seed variant took 0.27 user seconds at
533,228 KiB; CompCert 3.17 `-O2` took 0.29 user seconds at 82,652 KiB.  The
production-seed hashes are:

```text
C      a9bd629f96f1aed98f8414a934a93470d75ac7e7077d489343e5eb3e4396064c
binary a3e1c57210491657fa9ce13a2d1e387dfbe3a65f6c9ca7970f4953a3fed79814
```

Reproduction:

```bash
lake env lean --run bench/RamareCombined100MLogEmit.lean \
  positive 10001 999900 100 100000000 \
  2592507685042803 2592509215128426 /tmp/ramare_log_production.c
ccomp -O2 -o /tmp/ramare_log_production /tmp/ramare_log_production.c
/tmp/ramare_log_production
```

### Composed lambda and psi carry

`Ports/RamareCombined100MLambdaPsiSweep.lean` composes the classifier and
log-ladder carry with the exact prime-power lambda selection and two carried
psi quotient/remainder transitions.  Only the 2,459 active log-ladder cells
are stored; all inactive table rows are omitted.  The compiler theorem is
`LambdaPsiSweep.program_compiled`.  The two embedded 22-instruction quotient
blocks now have source-refinement theorems
`advanceBody_lower_denote`/`advanceBody_upper_denote`: every successful
array-machine denotation returns exactly `PsiQR.advance`, while decidable
frame theorems show that the blocks preserve their candidate/lambda inputs
and the complete array.  These theorems reuse the word-level arithmetic proof
from `RamarePsiQRBlock.lean`; they do not trust the measured output values.
The surrounding seven-instruction quotient-sum stage is now also isolated and
proved exact by `sumBody_run`: under explicit no-wrap and positive-denominator
hypotheses it returns the model's floor and ceiling updates, using the proved
`ceilDiv_eq_div_add_modBit` identity.  `sumBody_inputs` proves the candidate,
both lambda endpoints, and the full array are unchanged.  The 30-instruction
selection prefix is isolated as `selectionBody`; `selectionBody_run` proves
that its emitted instructions recover both old log endpoints, perform both
clamped table reads, choose the exact prime-power/table lambda endpoints, and
preserve the complete array.  The endpoint copies and both quotient commits
are likewise named blocks with exact run theorems
`copyLowerEndpointBody_run`/`copyUpperEndpointBody_run` and
`commitLowerEndpointBody_run`/`commitUpperEndpointBody_run`.  Their explicit
word and remainder guards are the invariants required by the future
whole-loop refinement.  `lowerEndpointBody_run` and
`upperEndpointBody_run` compose each copy/advance/commit shell.  Finally,
`candidateBody_run` composes the selector, both sums, and both endpoint shells
into one source-shaped `candidateArithmetic` transition.  It proves all four
output components and the complete array frame under explicit word,
initialized-table, no-wrap, and quotient-transition hypotheses; no emitted
arithmetic is left opaque inside the candidate suffix.  `arithmeticBody_run`
now composes this theorem with the complete 26-instruction log suffix.  It
derives the selector's old-endpoint subtraction guards from the proved log
update and returns both carried logs, the four candidate projection fields,
and the complete array frame in one theorem.
`classifiedArithmeticBody_run` closes the next seam as well: it composes the
complete seven-plane classifier with `arithmeticBody_run`, exposes the exact
candidate and live gate, and returns the two logs, full candidate projection,
and cleared-array frame.  Its assumptions are packaged as the explicit
`ArithmeticPre` word/table/no-wrap invariant on the concrete
post-classification state.

The production artifact used the exact `[10001, 100000000]` configuration,
the certified prefix-through-10 state, and denominator `100000001`.  It
processed every one of the 99,990,000 candidates with no guard, mark, or shape
failure:

```text
sumL       5022482397001815
sumU       5022484809383406
psiL.q     281469980046829
psiL.r     8827400
psiU.q     281470071170241
psiU.r     53687095
```

Thus the two exact carried numerators are respectively
`28146998286152888874229` and `28147007398494224857336`.  A control with every
mark budget halved reports exactly 100 mark-coverage failures.

| artifact | emit user / RSS | CompCert `-O2` user / RSS | run user / RSS | result |
| --- | ---: | ---: | ---: | --- |
| positive | 5.37 s / 3,154,580 KiB | 1.93 s / 439,664 KiB | 18.75 s / 56,212 KiB | guards 0; seen 99,990,000 |
| half-budget control | 5.35 s / 3,152,332 KiB | 1.75 s / 439,960 KiB | 11.09 s / 56,224 KiB | guards 100; mark 100 |

The program has a 334-instruction body, 426,020,600 loop iterations, and a
112,158,760-byte static array.  Exact hashes:

```text
positive C      2a611c13281b9574c2d1889d96678defd7f8dd436998ce1f7426b9b15a815f5d
positive binary 4ce60d4db4ac5144082bc167ef56505244b59c68c427fb3289787176d39846ba
control C       f5a41c7559d586226bf84d6ed7565923cf42211573d9c32d8ca79667dcfc5784
control binary  3a5f3bbd1d035556861e5631004d02b2f41532d9d3def0b13813c525f4633815
```

All phases were run without swap.  Emission used `MemoryHigh=9G` and
`MemoryMax=10G`, CompCert used `4G`/`5G`, and execution used `768M`/`1G`.
The source file containing the embedded-block, sum-stage, lambda-selection,
copy, commit, endpoint-shell, whole-candidate, composed-log, and
classifier-to-arithmetic semantics compiled from source in **40.93
wall-seconds** with **3,431,708 KiB peak
RSS**, serialized under a **20/22 GiB physical-memory cgroup**, with zero
swap.

This completes the production runtime composition and the exact
whole-candidate semantics of the lambda selector, quotient sums, both quotient
sub-blocks, and their endpoint commits.  It does not yet retire the closed
carrier: the remaining proof obligation is the whole-loop number-theoretic
refinement from the seven sieve planes to the unchanged source fold, including
discharge of the composed theorem's explicit word/table invariants.

## Build-memory measurements

The new quotient block compiles from source in under one second inside a
6 GiB hard cgroup (`MemoryHigh=5 GiB`, no swap).  The sibling LeanCompCert
umbrella build completed serialized under an 8 GiB hard cap; its peak was
7,517,138,944 bytes and came from the pre-existing segmented-psi module, not
this block.  The full Goldbach statement build completed serialized under a
14 GiB hard cap, with a recorded cgroup peak of 12,929,568,768 bytes.
