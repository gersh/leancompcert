# Appendix A.34 fixed-width certificate

The production checker covers `[1/10, 36]` with `2^20 = 1,048,576`
outward-rounded dyadic cells at precision `2^-24`.  Each row checks four
square-root brackets, the positive divisor, three subtraction guards, and

```
(υ² - υ) ≤ ρ · Υ · ((29888/100000) · W - 1/2).
```

The original exact-rational adaptive proof was stopped after 20:34 at about
16.4 GiB RSS.  The fixed-width model gives two bounded validation routes:

| route | work | wall | peak RSS | result |
| --- | ---: | ---: | ---: | --- |
| model exploration (`#eval`) | depth 18 |  — | — | reject |
| model exploration (`#eval`) | depth 20 | 23.77 s | 515,336 KiB | accept |
| kernel shard | 1,024 rows | 5.04 s | 1,740,724 KiB | accept |
| kernel group | 16 × 1,024 rows | 81.76 s | 2,579,228 KiB | accept |
| complete certificate build | 64 groups / 1,048,576 rows | 12:33 | 18.1 GiB cgroup peak | accept |
| root theorem source compile | complete bridge and A.34 theorem | 4.68 s | 4,458,052 KiB | success |
| rolled artifact emission | 1,048,576 rows | 0.25 s | 511,988 KiB | emitted |
| CompCert 3.17, `-O2` | 844-line C file | 0.09 s | 21,600 KiB | compiled |
| artifact run | 1,048,576 rows | 0.25 s | 700 KiB | output `0` |
| rejecting control | depth 3, expected `1` | 0.25 s | 692 KiB | output `1` |

Every Lean measurement ran with `MemorySwapMax=0` and a cgroup hard limit.
The production kernel build uses two to four workers only for homogeneous
2.58-GiB groups, with a total hard limit; broad project builds use the
repository's `tools/safe_lake_build.sh` wrapper instead.

## Reproducibility

Emitter: `bench/A34BisectEmit.lean`.

Production artifact:

* generated C: 26,198 bytes, SHA-256
  `795e4ce94841d8ef06b870c39a2efb71c793aa62a8e1bc58f287becfa04fe8dc`;
* CompCert binary SHA-256
  `7cdee5b43a9a570d2907a068e0bd6bb68cf5583cfbf84e99a1de4708c00cc5dd`.

Rejecting control:

* generated C SHA-256
  `dec7c3da13237e4e2e112a48fe5b08cf0e1787e4d6eace29a469d556c9d8518c`;
* CompCert binary SHA-256
  `809173576bb2340a8f596cbf3e8fd45b218520181d3eea905baf83f7db409e69`.

## Trust status

The shipped A.34 theorem uses the kernel-sharded fixed-width model, so it adds
no run axiom.  `A34BisectProgram.program_wf` and the emitted-C compiler theorem
are proved, and the accepting and rejecting artifacts above benchmark the
same row expression graph.  The universal register-program/`leafOK`
simulation is not yet claimed; consequently the artifact measurements are
cross-checks, not the proof of the A.34 theorem.
