# The array bridge, measured

All numbers: aarch64, single core, `/usr/bin/time -v`, **user** time in
seconds, best of two runs.  Every artifact exits `0`, i.e. it agrees with the
expected value of `L + Σ_{n<L} μ(n)`.

Three programs compute the same number:

* **array** — `Ports.ArrayMobius.mobiusProgram L`, an `AProgram`, emitted
  rolled by `AProgram.emitRolled` (`bench/ArrayMobiusEmit.lean array`).  One
  `uint64_t` array; `O(L log log L)` work.
* **trial** — the memoryless equivalent, a `Reflect.Program` whose loop body
  recomputes `μ(n)` by trial division over the same prime table, unrolled
  (`bench/ArrayMobiusEmit.lean trial`).  This is what the proved fragment
  could express before the array bridge existed.
* **ref** — a hand-written plain C segmented Möbius sieve
  (`bench/ref_mobius.c`), gcc -O2.  The "how fast can this
  possibly go" line.

| L      | array gcc | array ccomp | trial gcc | trial ccomp | ref gcc | array max RSS |
| ------ | --------- | ----------- | --------- | ----------- | ------- | ------------- |
| 1e5    | 0.00      | 0.00        | 0.02      | 0.03        | 0.00    | 2.4 MB        |
| 1e6    | 0.015     | 0.030       | 0.57      | 1.00        | 0.00    | 16 MB         |
| 1e7    | 0.19      | 0.26        | 14.94     | 27.28       | 0.11    | 157 MB        |
| 3e7    | 0.62      | 0.85        | —         | —           | 0.39    | 470 MB        |
| 1e8    | 2.52      | 3.23        | —         | —           | 1.64    | 1.56 GB       |

`—` means the *emitter* runs out of interpreter stack: `Proof.lowerSequence`
is not tail-recursive and the trial body is `12·π(√L)+11` instructions, which
overflows somewhere between 5 363 (L = 1e7, fine) and 8 651 (L = 3e7, fails).
That is a pre-existing emitter limitation, unrelated to the array path — the
array body is a constant 60 instructions at every L.

## What the numbers say

**Array vs. memoryless.**  79× (gcc) and 103× (CompCert) at L = 1e7; 38× and
33× at L = 1e6.  The ratio grows like `π(√L) / log log L`, because the
memoryless body costs one modulo per small prime per `n` while the array body
is constant.  Extrapolating from the L = 1e7 point, at L = 1e12
(`π(√L) = 78 498` against `446`) the ratio is of order 10⁴.

**Array vs. hand-written C.**  1.7× (gcc) / 2.4× (CompCert) at L = 1e7,
falling to 1.5× / 2.0× at L = 1e8.  The residual factor is the price of the
fragment's shape, not of the bridge: an `AProgram` body is *data-independent*,
so the sieve phase and the accumulation phase both execute on every iteration
with the inactive one multiplied by zero, and suppressed stores are redirected
to a scratch cell rather than skipped.

**Per element.**  At L = 1e8, gcc: 2.52 s over 3.48e8 iterations = 7.2
ns/iteration, 25.2 ns per integer `n`.  The reference sieve is 16.4 ns per
`n`; the memoryless artifact is 1 494 ns per `n` at L = 1e7.

## Reproducing

```
lake env lean --run bench/ArrayMobiusEmit.lean array 10000000 arr.c 10001037
lake env lean --run bench/ArrayMobiusEmit.lean trial 10000000 tri.c 10001037
gcc -O2 -o arr.gcc arr.c ; ccomp -O2 -o arr.cc arr.c
/usr/bin/time -v ./arr.gcc
```

The expected value is `L + Σ_{n<L} μ(n)`; the `mobius-array` entry of
`lake exe lean-compcert check-native` runs the L = 1e5 instance through
CompCert with the freestanding link on every check.
