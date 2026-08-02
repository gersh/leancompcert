import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.TrialDivisionFold

/-!
Benchmark support: emit the rolled C artifact for the **trial-division fold**
of `LeanCompCert.Ports.TrialDivisionFold`.

The emitted function is exactly `tdProgram ⟨START, FUEL, DIV, BOUND⟩` — the
same `Reflect.Program` whose denotation `Ports/TrialDivisionFold.lean` proves
is the flat fold of `tdRound`.  There is no second, hand-written C reference:
the artifact and the theorem are about the same object.

The loop is `FUEL · DIV` iterations, so emission must be rolled; unrolled it
would be terabytes of C.

Usage:

```
lake env lean --run bench/TrialDivisionEmit.lean START FUEL DIV BOUND OUT
```

The generated `main` returns `0` exactly when the program's output register
holds `1`, which by `tdProgram`'s epilogue means *no accumulator step wrapped
and the accumulated total is `≤ BOUND`*.  Emission only; no proof obligation
is discharged here, and `Program.denote` is never evaluated.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.TrialDivisionFold

namespace Bench.TrialDivisionEmit

/-- The accepting machine value: `tdProgram`'s output register is
`ok · (acc ≤ bound)`. -/
def acceptingValue : Nat := 1

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.TrialDivisionEmit

open Bench.TrialDivisionEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [startStr, fuelStr, divStr, boundStr, out] =>
      let some start := startStr.toNat? | do IO.eprintln "bad start"; return 1
      let some fuel := fuelStr.toNat? | do IO.eprintln "bad fuel"; return 1
      let some dv := divStr.toNat? | do IO.eprintln "bad div"; return 1
      let some bound := boundStr.toNat? | do IO.eprintln "bad bound"; return 1
      let P : Params := ⟨start, fuel, dv, bound⟩
      let p := tdProgram P
      let name := s!"TrialDivision{start}x{fuel}x{dv}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{start} {fuel} {dv} {bound} {p.loopCount} ok"
          return 0
  | _ => do
      IO.eprintln "usage: START FUEL DIV BOUND OUT"
      return 1
