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
