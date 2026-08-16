# Proposition 12.2.4 shared phi/squarefree table

Date: 2026-08-14

The compiled table covers every `r = 1 ... 23,278,719`.  Its configuration is
segment length `8,192`, `2,842` segments, exact loop count `104,287,087`, and
array length `46,623,641` words.

The positive generated C has SHA-256
`3fec3f82c6a0dc987b70ca56506cd7d0dcc5ccd6e904ad548ab787e1d09e587c`
and size 1,342,922 bytes.  CompCert took 17.39 wall-s and about 3.86 GiB peak
RSS.  The complete execution returned `violations 0` in 1.73 user-s / 1.85
wall-s, at 365,540 KiB peak RSS.

The fail-safe audit C has SHA-256
`dd7e5d75a51bd8fe7829624587cbfeb0297b9b5adcdab3e5407c5015c79d2eae`
and size 4,122,976 bytes.  With a 64 MiB parser stack, CompCert took 72.83
wall-s and about 14.6 GiB peak RSS.  The complete audit returned `audit 0` in
2.08 user-s / 2.24 wall-s, at 365,316 KiB peak RSS.

All commands ran with `MemoryMax=64G` and `MemorySwapMax=0`.  The smaller
smoke artifact was independently checked for recognizable exact phi and
squarefree values.  `Prop1224PhiSquarefreeTable.tableProgram_compiled` has
the fresh trust print `[propext, Quot.sound]`.
