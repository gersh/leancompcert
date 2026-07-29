import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.RS62LoopE

/-!
Benchmark support: emit the rolled C artifact for the **RS62 log-ladder
increment kernel** in its word-safe form.

The body computes, at ladder index `m`,

```
incLWord m = (fpD − ((3·fpD + 2m) + (fpD−1)/m) / (2m)) / (m−1)
incUWord m = ((fpD + m − 1) − ((3·fpD + 2m) − (3·fpD + m − 1)/m) / (2m)) / (m−1)
```

and accumulates both into registers 0 and 1. `LeanCompCert.Ports.RS62`
proves these equal the development's `incL`/`incU` for every `m ≥ 2`, so this
is the ladder's per-step arithmetic exactly — in the *source* form the
per-step numerator is a 106-bit number and no `u64` machine can run it.

Only the unguarded arithmetic is emitted here; the ladder's primality guard
is hoisted out of the loop (`Ports.RS62.loopE_eq_filter_foldl`) and is not
part of the register fragment.

Run with `lake env lean --run bench/RS62Emit.lean START COUNT OUTFILE VALUE`.
Emission only; no proof obligations are discharged.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect

namespace Bench.RS62Emit

/-- `2⁴⁸`, the ladder's fixed-point denominator. -/
def fpD : Nat := 281474976710656

/-- One ladder step at `m = start + idx`, word-safe throughout. -/
def body (start : Nat) : List Instr := [
  -- m, 2m, m−1
  .binop 2 .add .idx (.lit start),
  .binop 3 .mul (.reg 2) (.lit 2),
  .binop 9 .sub (.reg 2) (.lit 1),
  -- lower increment
  .binop 4 .udiv (.lit (fpD - 1)) (.reg 2),
  .binop 5 .add (.lit (3 * fpD)) (.reg 3),
  .binop 6 .add (.reg 5) (.reg 4),
  .binop 7 .udiv (.reg 6) (.reg 3),
  .binop 8 .sub (.lit fpD) (.reg 7),
  .binop 10 .udiv (.reg 8) (.reg 9),
  .binop 0 .add (.reg 0) (.reg 10),
  -- upper increment
  .binop 11 .add (.lit (3 * fpD)) (.reg 2),
  .binop 12 .sub (.reg 11) (.lit 1),
  .binop 13 .udiv (.reg 12) (.reg 2),
  .binop 14 .sub (.reg 5) (.reg 13),
  .binop 15 .udiv (.reg 14) (.reg 3),
  .binop 16 .add (.lit fpD) (.reg 2),
  .binop 17 .sub (.reg 16) (.lit 1),
  .binop 18 .sub (.reg 17) (.reg 15),
  .binop 19 .udiv (.reg 18) (.reg 9),
  .binop 1 .add (.reg 1) (.reg 19)
]

def prog (start count : Nat) : Program := {
  regCount := 20
  loopCount := count
  init := []
  body := body start
  epilogue := []
  output := 0
}

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.RS62Emit

open Bench.RS62Emit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [startStr, countStr, out, valueStr] =>
      let some start := startStr.toNat? | do IO.eprintln "bad start"; return 1
      let some count := countStr.toNat? | do IO.eprintln "bad count"; return 1
      let some value := valueStr.toNat? | do IO.eprintln "bad value"; return 1
      let p := prog start count
      let name := s!"RS62Ladder{start}x{count}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{start} {count} ok"
          return 0
  | _ => do IO.eprintln "usage: START COUNT OUT VALUE"; return 1
