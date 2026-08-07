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

## Build-memory measurements

The new quotient block compiles from source in under one second inside a
6 GiB hard cgroup (`MemoryHigh=5 GiB`, no swap).  The sibling LeanCompCert
umbrella build completed serialized under an 8 GiB hard cap; its peak was
7,517,138,944 bytes and came from the pre-existing segmented-psi module, not
this block.  The full Goldbach statement build completed serialized under a
14 GiB hard cap, with a recorded cgroup peak of 12,929,568,768 bytes.

