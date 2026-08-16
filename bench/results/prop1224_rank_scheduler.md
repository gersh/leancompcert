# Proposition 12.2.4 source-rank scheduler

The two CompCert-generated loops in
`LeanCompCert/Ports/Prop1224RankScheduler.lean` enumerate exactly the paper's
dense and `210`-spaced source ranges.  The symbolic source theorems are
`denseBody_q` and `extensionBody_q`; the checksum is only a benchmark output.

## Full-domain run

Date: 2026-08-13

Memory policy: systemd user scope with `MemoryMax=64G` and
`MemorySwapMax=0`.

Emitter:

    lake env lean --run bench/Prop1224RankSchedulerEmit.lean \
      /tmp/prop1224_rank_scheduler.c

Generated C SHA-256:

    08eebd281992f33402928841d783a310127c0d53996faaa550ad6e900e7af840

Generated C size: 1,757 bytes.  `ccomp -O` took 0.03 seconds and 15,552 KiB
maximum RSS.

The complete compiled run reported:

    dense_rows 3299999999 extension_rows 89047619 last_q 21999999840 \
    dense_checksum 5444999998350000000 \
    extension_checksum 1126452375897619050

Timing (`/usr/bin/time -v`):

| metric | value |
| --- | ---: |
| user time | 1.35 s |
| wall time | 1.36 s |
| maximum RSS | 1,272 KiB |
| exit status | 0 |

This benchmark covers all `3,389,047,618` source ranks.  It does not by
itself discharge Proposition 12.2.4; the same verified blocks are inputs to
the row arithmetic producer.
