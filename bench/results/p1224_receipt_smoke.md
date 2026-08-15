# Proposition 12.2.4 compiled-receipt smoke

This benchmark exercises both programs used by the retained-receipt bridge,
including the mechanically generated fail-safe variants.  It is deliberately
small but non-vacuous: the row program computes `q = 1,...,32`; the exact
reported `q = 30` constants seed the cell program over the complete prefix
`r = 1,...,20`.  It starts with the exact zero `G_q` carry and tests all
thirteen cells `k = 8,...,20` in the computed window `[8,9322)`.

Run under the repository's 64 GiB/no-swap ceiling:

```bash
systemd-run --user --wait --collect --pipe --quiet \
  --working-directory=/home/gersh/leancompcert \
  -p MemoryAccounting=yes -p MemoryMax=64G -p MemorySwapMax=0 \
  bench/p1224_receipt_smoke.sh
```

Observed on 2026-08-13:

| artifact | CompCert compile wall / max RSS | run wall | run max RSS |
| --- | ---: | ---: | ---: |
| row, 32 rows | 1.03 s / 61,856 KiB | < 0.01 s | 1,268 KiB |
| row fail-safe audit | 0.90 s / 69,660 KiB | < 0.01 s | 1,268 KiB |
| cell, thirteen tested margins | 0.09 s / 22,176 KiB | < 0.01 s | 1,252 KiB |
| cell fail-safe audit | 0.15 s / 25,184 KiB | < 0.01 s | 1,260 KiB |

The positive cell run reports thirteen tested cells, zero violations, and zero in
all five failure classes.  Both fail-safe programs report `audit 0`.  The
control starts the `G_q` accumulator one Q44 unit (`2^44`) too high; all
thirteen margins then fail and the executable returns the margin-specific status
6.  Thus the smoke does not merely exercise an empty window or a constant
success path.  A second control supplies the deliberately invalid cube-root
seed `2^21`; all thirteen tested cells trip `guard_cuberoot_lower`, none trip
the margin class, and the executable returns status 5.  This specifically
guards the anti-conservative direction in which an over-large cube root would
make the reciprocal envelope too small.

The cell input now uses the compiled compact-row conversion
`afHi = ceil(306643258 * 45879730 / 2^26) = 209640114`; the previous smoke
incorrectly supplied the unscaled `f1Hi = 45879730`.  The corrected smoke and
both failure controls pass.

This benchmark is evidence for the executable behavior.  The Lean theorems
in `Ports/Prop1224{Row,Cell}ReceiptBridge.lean` separately transport retained
compiled executions to exact source executions and result cells.  The
paper-facing real-enclosure/source-semantics theorem and the production sweep
are still required before retiring the literature atom.
