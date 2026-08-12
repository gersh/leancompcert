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

## Production root-only cursor campaign

The pinned `10^12` manifest also has a direct certificate using the actual
production segmented root loop.  `Platt211RootBatch.lean` sets the following
main-window count to zero, gives the root table the structurally roomy capacity
`rootCap + bootCount`, and returns the persistent table cursor; the paired
audit program checks every source guard.  This avoids replaying the completed
main sweep merely to inspect the root table, while ensuring that the table-fit
proof does not assume the recorded prime count it is intended to verify.
When a one-window root interval ends exactly on its segment boundary, the
certificate adds one inert cell beyond `rootCap`; the cap gate prevents that
cell from changing the table and makes the proved final transition uniform.

All 1,092 rows completed, with one ordinary and one audit receipt per row:

| rows | receipts | emit wall | CompCert wall | run wall | campaign peak RSS | swaps |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1,092 | 2,184 | 51.194 s | 44.157 s | 8.487 s | 609,424 KiB | 0 |

The compact summary is `platt211_root_1e12.json`.  It pins manifest SHA-256
`3ed737cb9ad2dd5a107d46c08d179e351850c199482ec487443c35d998f4cb3e`
and aggregate receipt SHA-256
`970c545d4fd929a456b7d6617c3285300dceb43caf6d5f3b0f1848ca36dfb787`.
The run used CompCert 3.17, twelve runtime workers and four compiler workers
inside a no-swap cgroup with `MemoryHigh=1536M` and `MemoryMax=2560M`.

```bash
LEAN_NUM_THREADS=1 python3 bench/platt211_root_certificate.py \
  --outdir runs/platt211_root --workers 12 --compile-workers 4
```
