# Platt (2.11) scalar prefix observations

Measured 2026-08-12 on Linux/aarch64 with Lean 4.32.1 and CompCert 3.17.
These are the physical runs named by
`ArraySegMobiusPlatt211Prefix100Certificate.platt211PrefixObservations_compcert_run`.

The batch emitter lowers the proved `tProgram` once for each prefix
`n = 1, ..., 100`.  Each executable returns the accumulator word at exactly
that prefix and its driver compares the result to the retained observation.
The mathematical bridge proves that these words are the true-Möbius
round-to-nearest accumulators; Lean does not execute the prefix recurrence.

| observations | emit wall | emit peak RSS | CompCert compile + run wall | peak compiler/runtime RSS | failures |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 100 | 0.77 s | 542 MiB | 4.33 s | 16,956 KiB | 0 |

All commands ran with one Lean worker.  Every emitted source compiled with
`ccomp -O2`, every executable exited zero, and the aggregate source hash
(the SHA-256 of the sorted per-file SHA-256 listing) is
`687997c3d5eb68f4af193ba0481f07090eadddca5b4722a2d4d281182681a800`.

Representative commands:

```bash
lake env lean --run bench/Platt211Prefix100Emit.lean observations /tmp/platt211-prefix
for n in $(seq 1 100); do
  ccomp -O2 -o /tmp/platt211-prefix/prefix_${n}.x \
    /tmp/platt211-prefix/prefix_${n}.c
  /tmp/platt211-prefix/prefix_${n}.x
done
```

The emitting Lean process was run in a no-swap cgroup.  The generated C and
executables are temporary build products and are intentionally not versioned.
