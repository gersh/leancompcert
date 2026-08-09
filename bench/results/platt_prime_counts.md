# Literal Platt root-table prime counts

Measured 2026-08-08 on Linux/aarch64 with Lean 4.32.1 and CompCert 3.17.
These are the physical runs named by
`ArraySegMobiusPlattFiniteEvidence.plattPrimeCount_compcert_run` and
`plattCrossingPrimeCount_compcert_run`.

The emitter lowers the proved `ArraySieveCount.sieveCountProgram` directly;
there is no separately implemented prime-count algorithm.  Its symbolic
denotation theorem identifies the returned word with `primeCount len`, and the
literal schedule proofs use that fact to establish root-table capacity.

| bound | len | machine iterations | expected/returned | emit wall | emit peak RSS | `ccomp -O2` wall | run wall | run peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 295 | 87,904 | 26,019,584 | 8,534 | 0.21 s | 532,656 KiB | 0.03 s | 0.10 s | 1,912 KiB |
| 170 | 29,301 | 5,010,471 | 3,183 | 0.21 s | 526,444 KiB | 0.03 s | 0.01 s | 1,416 KiB |

Both generated C files were about 1.9 KiB; the rolled loop keeps source size
independent of the iteration count.  Both executables printed the expected
count and exited 0.

Commands:

```bash
lake env lean --run bench/ArraySieveCountEmit.lean 295 87904 8534 /tmp/platt-prime-count-87904.c
ccomp -O2 -o /tmp/platt-prime-count-87904 /tmp/platt-prime-count-87904.c
/tmp/platt-prime-count-87904

lake env lean --run bench/ArraySieveCountEmit.lean 170 29301 3183 /tmp/platt-prime-count-29301.c
ccomp -O2 -o /tmp/platt-prime-count-29301 /tmp/platt-prime-count-29301.c
/tmp/platt-prime-count-29301
```

Every command was run under a no-swap user cgroup.  Lean emission and CompCert
compilation used `MemoryHigh=2G`, `MemoryMax=3G`, and one Lean worker.  Runtime
used `MemoryHigh=256M`, `MemoryMax=512M`.

## Weighted marking-budget receipts

The two final root-table marking budgets use
`ArraySieveWeightedSum.sieveWeightedProgram`, whose symbolic denotation theorem
proves that the compiled result is
`Σ_{p < 87904} (weight / p + 2)`.  Its inactive rows divide through an explicit
positive clamp, so neither receipt relies on division-by-zero behavior.

| weight | bonus | machine iterations | expected/returned | emit wall | emit peak RSS | `ccomp -O2` wall | run wall | run peak RSS | C bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 29,301 | 2 | 26,019,584 | 91,668 | 0.22 s | 521,224 KiB | 0.02 s | 0.12 s | 1,896 KiB | 2,250 |
| 3 | 2 | 26,019,584 | 17,070 | 0.24 s | 531,560 KiB | 0.03 s | 0.12 s | 1,896 KiB | 2,234 |

These totals are only 16 below the production budgets 91,684 and 17,086.
They replace a direct kernel reduction that was stopped after 3 minutes 33
seconds under a 2 GiB hard cap without producing a result.

```bash
lake env lean --run bench/ArraySieveWeightedSumEmit.lean 295 87904 29301 2 91668 /tmp/platt-first-budget.c
ccomp -O2 -o /tmp/platt-first-budget /tmp/platt-first-budget.c
/tmp/platt-first-budget

lake env lean --run bench/ArraySieveWeightedSumEmit.lean 295 87904 3 2 17070 /tmp/platt-tail-budget.c
ccomp -O2 -o /tmp/platt-tail-budget /tmp/platt-tail-budget.c
/tmp/platt-tail-budget
```
