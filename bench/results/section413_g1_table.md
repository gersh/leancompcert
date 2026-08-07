# Section 4.1.3 G1 table certificate benchmark

Measured 2026-08-05 on Linux/aarch64 (20-core Cortex-X925), leancompcert
commit `856beb6fa01889cfc8b7a9c55ebc67dd323746ac`.  Every command ran in a
systemd cgroup with `MemorySwapMax=0`; emitted artifacts are local build
products and are not proof inputs.

Configuration: `cap=10000`, `R=999`, `checkLo=33`, `arrayLen=50005`,
`loopCount=12009001`, 1,456 body instructions and 80,000 table-check
epilogue instructions.

| Phase | Wall time | Peak RSS | Hard memory limit | Result |
|---|---:|---:|---:|---|
| Generate 100 local tables and aggregate | 33.01 s | 574,848 KiB | 3 GiB | success |
| Direct-check aggregate source | 4.51 s | 868,036 KiB | 6 GiB | success |
| Emit positive C | 75.78 s | 648,700 KiB | 6 GiB | success |
| CompCert 3.17 `-O2`, positive | 323.21 s | 488,508 KiB | 4 GiB | success |
| Run positive | 1.90 s | 6,520 KiB | 2 GiB | `flag=0`, exit 0 |
| Emit one-cell corruption control | 96.47 s | 667,176 KiB | 6 GiB | success |
| CompCert 3.17 `-O2`, control | 199.14 s | 423,212 KiB | 4 GiB | success |
| Run control | 1.89 s | 6,528 KiB | 2 GiB | `flag=1`, exit 1 |

Artifact identities:

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 3,311,703 | `0ce8f035edfda9a5794e81482ec55720bf43269c3157023465206eac440d397e` |
| control C | 3,311,688 | `ce48e64f6328e3d1408723ac681fd07a180383630acc33413333d668956bc843` |
| positive executable | 857,072 | `96465427d15458cb7ab23726c3d1d3e70479a05370d7e27eb64dd381cfef2667` |
| control executable | 857,080 | `6b4df779ee0e2b28c2c4150732f907e0dabdc676961f9602cfdf108b0311cdad` |

The positive table aggregate is
`(37224399391489426675474563, 724965793909164307)`.  Its arithmetic is
proved in 100 kernel-checked chunks.  The specialized ungated-weight
machine has a complete denotation and source-soundness proof, so
`compiled_zero_expected_g1` connects the physical `flag=0` result to every
source table cell.  The control changes expected cell 1 to zero and is
rejected by the compiled comparison path.

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
| Emit positive C | 32.63 s | 1,228,756 KiB | 6 GiB | success |
| CompCert `-O0`, positive | 2:51.17 | 3,223,516 KiB | 6 GiB | success |
| Run positive | 34.52 s | 13,684 KiB | 1 GiB | `flag=0`, exit 0 |
| Emit one-cell corruption control | 32.70 s | 1,231,724 KiB | 6 GiB | success |
| CompCert `-O0`, control | 2:54.07 | 3,248,956 KiB | 6 GiB | success |
| Run control | 34.51 s | 13,684 KiB | 1 GiB | `flag=1`, exit 1 |

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 32,667,957 | `e5c37b550ff295590c11a5591f678f46ac9f3f6bdff8952bd2af701d2d495b8a` |
| control C | 32,667,942 | `a5ca34cdbc4114261b281063324577fad4ddf92af707424c7d780faf6f8519e0` |
| positive executable | 8,852,464 | `85cb5501f2c057bd57ede32a428ceeec9fa5767cb49c719e7642cf5b3f45382a` |
| control executable | 8,852,472 | `a56c7a3226824f3e4ad8c430d4da4367bb0125c7b644ef92ea94c1d7ffb92008` |

The compact context changes only how operand types are supplied to the
proved lowerer. A 10,000-row epilogue-lowering probe fell from 73.713 s to
1.815 s; the emitted program, denotation theorem, and pointwise source
soundness statement are unchanged.
