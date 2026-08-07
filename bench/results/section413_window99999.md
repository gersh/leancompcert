# Section 4.1.3 99,999-point window certificate

Measured 2026-08-06 on Linux/aarch64 (20-core Cortex-X925) from the tree
based on commit `315339d` plus the compact rolled-lowering context recorded
with this receipt. Every command ran in a systemd cgroup with
`MemorySwapMax=0`; generated artifacts are local benchmark products and are
not proof inputs.

The emitted runtime program checks all 199,998 source-derived `g₁`/`g₂`
event words against `commonBound`. It does not evaluate `windowOK` or bake
its answer into the generated C. The rejecting control replaces exactly the
first event word by `commonBound + 1`.

| Phase | Wall time | Peak RSS | Hard memory limit | Result |
|---|---:|---:|---:|---|
| Emit positive C | 10.20 s | 1,562,080 KiB | 6 GiB | `some 0` |
| CompCert 3.17 `-O0`, positive | 55.64 s | 1,424,272 KiB | 6 GiB | success |
| Run positive | <0.01 s | 3,664 KiB | 1 GiB | `flag=0`, exit 0 |
| Emit one-word-over-bound control | 10.29 s | 1,560,324 KiB | 6 GiB | `some 1` |
| CompCert 3.17 `-O0`, control | 59.44 s | 1,383,256 KiB | 6 GiB | success |
| Run control | <0.01 s | 3,664 KiB | 1 GiB | `flag=1`, exit 1 |

The emitted program contains 199,998 epilogue comparisons. CompCert needed
the same bounded 512 MiB parser stack used for the full table artifacts; all
process memory remained inside the 6 GiB cgroup and swap stayed disabled.

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 24,999,409 | `d4bc575d7888a403230b9b3ee8e9e2d2ea435c22471e307e663ac411d91bc836` |
| control C | 24,999,447 | `20a5b0a241c87355dec2c007aa88cbafe901816a9a5a1df16656c73a7c83c818` |
| positive executable | 2,429,880 | `e64957d895a65a4f83cd41d399503294b4e68f1a3c4220da16a35a04504d9a63` |
| control executable | 2,429,888 | `2c38435ff7669880824a205b57984c8468bdcc567ebff0c850a14f438f2afb5a` |

`TotalWordBounds.all_le_of_returns_zero` proves that an accepted compiled
result bounds every emitted word. The generated K-trace proofs identify those
words with the source recurrences, the separate full G1/G2 table runs prove
all 99,999 source table rows, and `windowOK_of_tables` derives the unchanged
Section 4.1.3 window predicate. Thus the physical positive/control pair tests
the same runtime path used by the admitted `Returns 0` proposition.
