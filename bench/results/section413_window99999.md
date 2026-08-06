# Section 4.1.3 99,999-point window certificate

Measured 2026-08-05 on Linux/aarch64 (20-core Cortex-X925), leancompcert
commit `856beb6fa01889cfc8b7a9c55ebc67dd323746ac`. Every command ran in a
systemd cgroup with `MemorySwapMax=0`; generated artifacts are local benchmark
products and are not proof inputs.

The source Boolean is `Section413Sweep.windowOK 999 99999`. It performs both
complete `g₁`/`g₂` table sweeps and both Section 4.1.3 window-event scans.
`ClosedBoolCarrier.computation_returns_zero_iff` proves that the packaged
LeanCompCert computation returns zero exactly when that Boolean is true.

| Phase | Wall time | Peak RSS | Hard memory limit | Result |
|---|---:|---:|---:|---|
| Direct certificate source check | 0.13 s | 512,952 KiB | 3 GiB | success |
| Emit positive C, including closed-model evaluation | 13:35.12 | 545,336 KiB | 3 GiB | `some 0` |
| CompCert 3.17 `-O2`, positive | 0.02 s | 15,548 KiB | 2 GiB | success |
| Run positive | <0.01 s | 1,256 KiB | 1 GiB | `flag=0`, exit 0 |
| Emit false-Boolean control | 0.35 s | 697,148 KiB | 3 GiB | `some 1` |
| CompCert 3.17 `-O2`, control | 0.03 s | 15,548 KiB | 2 GiB | success |
| Run control | <0.01 s | 1,256 KiB | 1 GiB | `flag=1`, exit 1 |

Artifact identities:

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| positive C | 495 | `41a164964d177f0c481ebb74676b370bda5639ea42b1aed70f550fad074013ae` |
| control C | 516 | `4a9ff1ec7e7b33bdd23447c6927ddb0d60502b6596b99ef24d043c780d2f89bc` |
| positive executable | 70,584 | `1b7e3d525b7ea51ecf9fcc16827995dc064ff1bad449c83016c0c27f50894d3c` |
| control executable | 70,592 | `b889bd8bd6d5c15c77a4ac9456d8f6fd0ff161a21bc94a40f6b4a59348b6d6d3` |

As an independent source-model cross-check, the expected `g₁` and `g₂`
tables through 99,999 were generated in 100 kernel-checked chunks each. The
`g₁` generation took 6:42.77 / 586,516 KiB and `g₂` took 6:30.12 /
595,240 KiB; all 200 chunks and their aggregate modules then built under a
16 GiB hard cap with eight workers. Those large tables are deliberately not
embedded in the final carrier: the direct source Boolean is the exact model
used by the theorem, and omitting a 33 MB literal-table epilogue keeps both
emission and CompCert compilation bounded.

The sole non-foundational atom, `section413Window99999_compcert_run`, is the
packaged computation's exact `Returns 0` proposition. The generic packaging
theorem proves the CCIR/generated-C lowering, and the source bridge
`section413Window431_of_model` derives the unchanged project certificate.
