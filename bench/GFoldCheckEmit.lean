import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.GFoldCheck

/-!
Benchmark support: emit the rolled C artifact for the **running Ramaré
`G`-bound check** of `LeanCompCert.Ports.GFoldCheck`.

The emitted function is exactly `gfProgram ⟨LO, LEN, TDIV, BMAX, SPLIT, M0⟩`
— the same `Reflect.Program` whose denotation `Ports/GFoldCheck.lean` proves
is the flat fold of `gfRound`.  There is no second, hand-written C reference:
the artifact and the theorem are about the same object.

The loop is `LEN · (TDIV + BMAX)` iterations, so emission must be rolled.

Usage:

```
lake env lean --run bench/GFoldCheckEmit.lean LO LEN TDIV BMAX SPLIT M0 OUT
```

The generated `main` returns `0` exactly when the program's output register
(the good flag) holds `1`, which means *every candidate passed some
exponent-pair threshold check with the accumulator below the cap*.  Emission
only; no proof obligation is discharged here, and `Program.denote` is never
evaluated.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.GFoldCheck

namespace Bench.GFoldCheckEmit

/-- The accepting machine value: the good flag. -/
def acceptingValue : Nat := 1

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.GFoldCheckEmit

open Bench.GFoldCheckEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loStr, lenStr, tdivStr, bmaxStr, splitStr, m0Str, out] =>
      let some lo := loStr.toNat? | do IO.eprintln "bad lo"; return 1
      let some len := lenStr.toNat? | do IO.eprintln "bad len"; return 1
      let some tdiv := tdivStr.toNat? | do IO.eprintln "bad tdiv"; return 1
      let some bmax := bmaxStr.toNat? | do IO.eprintln "bad bmax"; return 1
      let some split := splitStr.toNat? | do IO.eprintln "bad split"; return 1
      let some m0 := m0Str.toNat? | do IO.eprintln "bad m0"; return 1
      let c : Params := ⟨lo, len, tdiv, bmax, split, m0⟩
      let p := gfProgram c
      let name := s!"GFoldCheck{lo}x{len}x{tdiv}x{bmax}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{lo} {len} {tdiv} {bmax} {split} {m0} {p.loopCount} ok"
          return 0
  | _ => do
      IO.eprintln "usage: LO LEN TDIV BMAX SPLIT M0 OUT"
      return 1
