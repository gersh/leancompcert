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
ccomp -I../../runtime/include -I"$(lean --print-prefix)/include" -o demo demo.c
./demo; echo $?                  # 0: the native run reproduces 28707
```
