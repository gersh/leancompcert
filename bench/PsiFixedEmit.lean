import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.PsiFixedCheckClaim

/-!
Benchmark support: emit the rolled C artifact for the **ψ fixed-point slope
check** of `LeanCompCert.Ports.PsiFixedCheck`.

The emitted function is exactly `psProgram ⟨START, FUEL, TD, K, LO⟩` — the
same `Reflect.Program` whose denotation `Ports/PsiFixedCheckRound.lean`
proves is the flat fold of `psRound`.  There is no second, hand-written C
reference: the artifact and the theorem are about the same object.

The loop is `FUEL · (TD + 67)` iterations, so emission must be rolled.

Usage:

```
lake env lean --run bench/PsiFixedEmit.lean START FUEL TD K LO OUT
```

The generated `main` returns `0` exactly when the program's output register
holds `1`, which by `psProgram`'s epilogue means *every masked slope test
held and no guard fired*.  Emission only; no proof obligation is discharged
here, and `Program.denote` is never evaluated.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.PsiFixedCheck

namespace Bench.PsiFixedEmit

/-- The accepting machine value: `psProgram`'s output register is
`pass · ok`. -/
def acceptingValue : Nat := 1

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.PsiFixedEmit

open Bench.PsiFixedEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [startStr, fuelStr, tdStr, kStr, loStr, out] =>
      let some start := startStr.toNat? | do IO.eprintln "bad start"; return 1
      let some fuel := fuelStr.toNat? | do IO.eprintln "bad fuel"; return 1
      let some td := tdStr.toNat? | do IO.eprintln "bad td"; return 1
      let some kv := kStr.toNat? | do IO.eprintln "bad K"; return 1
      let some lo := loStr.toNat? | do IO.eprintln "bad lo"; return 1
      let P : Params := ⟨start, fuel, td, kv, lo⟩
      let p := psProgram P
      let name := psName P
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{start} {fuel} {td} {kv} {lo} {p.loopCount} ok"
          return 0
  | _ => do
      IO.eprintln "usage: START FUEL TD K LO OUT"
      return 1
