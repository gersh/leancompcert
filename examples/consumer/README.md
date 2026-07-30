# Consumer example

An external Lake project that depends on `leancompcert` (by path) and
states its **own** bounded computation using only the public API — no
edits to the parent repository.

## What it proves

`Consumer.lean` authors a fresh `Verified.Reflect.Program` computing

```
Σ_{k < 64} (m(k) + [m(k) < 512]),   m(k) = ((k+1)³ mod 2⁶⁴) &&& 1023
```

— for each `k`, the low ten bits of the cube plus an extra `1` whenever
that masked value is below `512` (multiplication, bitwise masking, and a
proved unsigned comparison in one loop body). The certificate

```lean
theorem demo_certificate : referenceSum = expectedValue   -- 28707
```

is discharged by `Decision.prove` through the structural
`Program.toComputation` packaging: the kernel evaluates only the
program's denotation and the reference fold. `#print axioms` reports the
standard `propext`, `Classical.choice`, `Quot.sound` — nothing else.
`generated_c_model_returns` carries the same value to the CCIR/C model,
and `foldP_accepts_total_step` exercises the `Verified.EarlyExit`
equivalence surface.

## Trust chain

The Lean kernel checks that the register program's denotation equals the
independently computed reference value; the package's proved fragment
carries that result structurally to the emitted C model; CompCert's
verified compilation carries the C to assembly. As in the parent
project, the CCIR-to-C emission step is validated rather than
machine-checked end-to-end — the claim is a kernel-checked certificate
whose native artifact is compiled by a verified C compiler, not a fully
verified Lean-to-machine-code pipeline.

## Commands

```console
cd examples/consumer
lake build                       # proves the certificate; zero errors expected
./.lake/build/bin/consumer demo.c   # write the emitted C (function + main)
ccomp -c -o demo.o demo.c        # no -I needed: only <stdint.h>/<stddef.h>
as -o start.o ../../runtime/start/$(uname -m).S
ld -o demo start.o demo.o        # freestanding: no libc, static, 0 undef syms
./demo; echo $?                  # 0: the native run reproduces 28707
                                 # 1 would mean a value disagreement;
                                 # anything else is abnormal termination
```

Or let the cached pipeline do the emit/compile/run loop (this is the
recommended way to keep a fast native cross-check in CI — see
[use case 1](../../docs/use-case-1-verified-native-decide.md)):

```console
./.lake/build/bin/consumer check-native
# [run] demo: compiled with CompCert, native check passed
./.lake/build/bin/consumer check-native
# [cached] demo: C unchanged since last passing run
```

The second invocation re-runs nothing: results are cached by content
hash of the generated C, so rebuilding the project or editing unrelated
files never repeats the native run. The wiring is five lines in
`Main.lean` (`LeanCompCert.NativeCheck.run` over a list of
certificates).
