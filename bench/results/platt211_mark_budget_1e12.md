# Platt (2.11) post-prefix marking budgets

Measured 2026-08-12 on Linux/aarch64 with Lean 4.32.1 and CompCert 3.17.
These are the physical runs named by
`ArraySegMobiusPlatt211MarkBudgetCertificate.platt211MarkBudget_compcert_run`.

For every retained manifest row after the separately certified prefix through
candidate 100, the batch emitter lowers the proved
`sieveWeightedBudgetProgram`.  The program enumerates the prime table and
checks the exact weighted marking sum against that row's literal production
budget.  Its self-checking driver exits zero only when the returned verdict is
zero.  Lean checks the manifest's scalar bounds and consumes these opaque run
receipts; it does not enumerate primes or reduce the weighted sums.

| rows | machine iterations | emit wall | emit peak RSS | `ccomp -O2` wall | run wall | run CPU | run peak RSS | failures |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1,017 | 102,342,149,675 | 1.18 s | 609,716 KiB | 8.69 s | 49.16 s | 576.42 s | 8,536 KiB | 0 |

Compilation used four workers and execution used twelve workers.  Every
emitted source compiled with CompCert and every executable exited zero.  The
SHA-256 of the lexically sorted per-file source-hash listing is
`57a3523cfe82326698d65e176a47f454e4c84ac883f9ad09f690bfd5044a3c94`.
The analogous executable-list hash is
`72591e65867dc54aafa998f6beba8e0b7ac489b0aebaf037f88fa8b04fe3fbcd`.

Representative scale checks before the batch run were row 75 (44 loop
iterations), row 500 (885,381 iterations), and row 1,091
(1,001,001,001 iterations).  The final row ran in 5.37 seconds at 8,712 KiB
RSS, consistent with the complete campaign's 576.42 CPU-seconds.

Commands:

```bash
lake env lean --run bench/Platt211MarkBudgetBatch.lean \
  all /tmp/platt211-mark-budget

find /tmp/platt211-mark-budget -name 'row_*.c' -print0 | sort -z | \
  xargs -0 -P4 -n1 sh -c \
    'ccomp -O2 -o "${1%.c}.x" "$1"' _

find /tmp/platt211-mark-budget -name 'row_*.x' -print0 | sort -z | \
  xargs -0 -P12 -n1 sh -c '"$1"' _
```

All three stages ran in no-swap cgroups.  Emission used one Lean worker; the
hard memory limit was 1,900 MiB throughout.  Generated C and executables are
temporary build products and are intentionally not versioned.
