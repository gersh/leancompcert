# Proposition 12.2.4 shared log/cube-root table

The compiled producer computes, for every `1 <= r <= 23,278,719`, the shared
fixed-point lower logarithm and exact scaled integer cube root consumed by the
Proposition 12.2.4 margin checker.  The numerical loop runs in CompCert output;
Lean proves the source program well formed and transports its execution through
the verified compiler.

All commands ran in systemd user scopes with `MemoryMax=64G`,
`MemorySwapMax=0`, and a 64 MiB stack limit.

## Production result

- rows: `23,278,719`
- array words: `46,557,442`
- positive result: `violations 0 stored 0`
- fail-safe instruction audit: `audit 0`
- positive run: 2.50 user-s, 2.65 wall-s, 364,956 KiB maximum RSS
- audit run: 2.57 user-s, 2.67 wall-s, 364,956 KiB maximum RSS
- CompCert positive compile: 0.07 wall-s, 21,532 KiB maximum RSS
- CompCert audit compile: 0.08 wall-s, 20,568 KiB maximum RSS

The generated positive C source is 30,136 bytes with SHA-256
`a5e4be4e4ceede29ca4308d0ff9f32d15b81f9219f904601592c0094915cbb93`.
The audited source is 30,545 bytes with SHA-256
`17e2fa28c4a5a64a41dd3727af7485100046017da9488abf286d2a952beff392`.

As an independent implementation check, the first 256 printed cube-root
entries were checked with arbitrary-precision host integers and all satisfied
`t^3 <= (20000*r)*2^15 < (t+1)^3`.  This check is supplemental; soundness is
provided by the emitted program's endpoint guards and compiled-code theorem.

Fresh `#print axioms` for
`LeanCompCert.Ports.Prop1224LogCbrtTable.program_compiled` reports only
`[propext, Quot.sound]`.
