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

## Build-memory measurements

The new quotient block compiles from source in under one second inside a
6 GiB hard cgroup (`MemoryHigh=5 GiB`, no swap).  The sibling LeanCompCert
umbrella build completed serialized under an 8 GiB hard cap; its peak was
7,517,138,944 bytes and came from the pre-existing segmented-psi module, not
this block.  The full Goldbach statement build completed serialized under a
14 GiB hard cap, with a recorded cgroup peak of 12,929,568,768 bytes.
