# Section 4.1.3 G2 table certificate benchmark

Measured 2026-08-05 on Linux/aarch64 (20-core Cortex-X925), leancompcert
commit `856beb6fa01889cfc8b7a9c55ebc67dd323746ac`.  Every command ran in a
systemd cgroup with `MemorySwapMax=0`; the emitted artifacts remain local
build products and are not source inputs.

Configuration: `cap=10000`, `R=999`, `checkLo=33`, `arrayLen=50005`,
`loopCount=12009001`, 1,456 body instructions and 80,000 table-check
epilogue instructions.

| Phase | Wall time | Peak RSS | Hard memory limit | Result |
|---|---:|---:|---:|---|
| Generate 100 local tables and aggregate | 31.77 s | 584,128 KiB | 3 GiB | success |
| Direct-check aggregate source | 4.24 s | 849,196 KiB | 6 GiB | success |
| Emit positive C | 95.25 s | 660,576 KiB | 6 GiB | success |
| CompCert 3.17 `-O2`, positive | 260.25 s | 390,264 KiB | 4 GiB | success |
| Run positive | 1.89 s | 6,528 KiB | 2 GiB | `flag=0`, exit 0 |
| Emit one-cell corruption control | 73.94 s | 639,612 KiB | 6 GiB | success |
| CompCert 3.17 `-O2`, control | 259.96 s | 390,196 KiB | 4 GiB | success |
| Run control | 1.88 s | 6,528 KiB | 2 GiB | `flag=1`, exit 1 |

Artifact identities:

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 3,344,364 | `ec60f597d8140f9f1c9edc01fbe22c59990efafde088ba23798b747d554c09f4` |
| control C | 3,344,349 | `8cc1f59524d886f1af46cf4a7018e675f2d95799f9e8eadaf65a76cd55b9242d` |
| positive executable | 857,072 | `4095a262a28a0f362508665553092d9c64f72b446088af6642e118ac5ca7b2cc` |
| control executable | 857,080 | `5ab3de3f06f9d5c36887a6fd1568d072ab8989bc08e2e412f4c5c8afab517559` |

The positive table aggregate is
`(47734020464052231290564355, 1442305040177257056)`.  Its local arithmetic
is proved in 100 kernel-checked chunks; the physical `flag=0` result is
connected to the source model through `compiled_zero_expected_g2`.  The
control changes expected cell 1 to zero and demonstrates that the compiled
comparison path rejects a mismatched table.

## Full 99,999-row campaign

Measured 2026-08-06 on the same Linux/aarch64 host from the tree based on
commit `315339d` plus the compact rolled-lowering context recorded with this
receipt. Every phase ran with `MemorySwapMax=0`. The C compiler used
CompCert 3.17 at `-O0`; the generated 799,992-statement epilogue required a
512 MiB parser stack (`ulimit -s 524288`) inside the stated memory cgroup.

Configuration: `cap=99999`, `R=999`, 99,999 rows, `arrayLen=500000`,
`loopCount=163297368`, 1,456 loop-body instructions, and 799,992 table-check
epilogue instructions.

| Phase | Wall time | Peak RSS | Hard memory limit | Result |
|---|---:|---:|---:|---|
| Emit positive C | 32.97 s | 1,182,832 KiB | 6 GiB | success |
| CompCert `-O0`, positive | 3:00.59 | 3,190,708 KiB | 6 GiB | success |
| Run positive | 34.49 s | 13,776 KiB | 1 GiB | `flag=0`, exit 0 |
| Emit one-cell corruption control | 32.83 s | 1,221,768 KiB | 6 GiB | success |
| CompCert `-O0`, control | 3:02.02 | 3,190,968 KiB | 6 GiB | success |
| Run control | 34.46 s | 13,684 KiB | 1 GiB | `flag=1`, exit 1 |

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 32,202,548 | `c6759f6b8c711133787641a3a3d7e2c7bead2c4a026c86ee0e74bf2db6f4a621` |
| control C | 32,202,533 | `573d190295fce8198fd7b7b564d88b5918e124a7c8e3e805a0283fb29fff74ac` |
| positive executable | 8,852,464 | `8e8f7ea14b66b0cdf559bf3b0d96a3fe7fde48c66da2513978e33ce1c1c4b4a2` |
| control executable | 8,852,472 | `d6a896cd285b908044cffe209511c056e4b10f31ca1675457d16ecd42f07ee79` |

The same compact typing context removes quadratic emitter allocation without
changing the generated recurrence, comparison program, or proof chain.
