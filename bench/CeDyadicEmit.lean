import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.CeDyadicFold

/-!
Benchmark support: emit the **rolled** C artifact for a `CeDyadicFold`
instance.

The emitted function is exactly `ceProgram ⟨LO, LEN, R, K0, UP, LFX, BOUND⟩` —
the same `Reflect.Program` whose denotation `Ports/CeDyadicFold.lean` reasons
about.  There is no second, hand-written C reference: the artifact and the
theorem are about the same object.

The loop is `LEN · R` iterations (6.25·10¹⁰ for the `ce` instance), so emission
must be rolled.

Usage:

```
lake env lean --run bench/CeDyadicEmit.lean LO LEN R K0 UP LFX BOUND OUT
```

The generated `main` returns `0` exactly when the program's output register
holds `1`, which means *no accumulator step wrapped and the total is on the
certified side of `BOUND`*.  Emission only; no proof obligation is discharged
here, and `Program.denote` is never evaluated.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CeDyadicFold

namespace Bench.CeDyadicEmit

/-- The accepting machine value. -/
def acceptingValue : Nat := 1

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.CeDyadicEmit

open Bench.CeDyadicEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loStr, lenStr, rStr, k0Str, upStr, lfxStr, boundStr, out] =>
      let some lo := loStr.toNat? | do IO.eprintln "bad lo"; return 1
      let some len := lenStr.toNat? | do IO.eprintln "bad len"; return 1
      let some r := rStr.toNat? | do IO.eprintln "bad R"; return 1
      let some k0 := k0Str.toNat? | do IO.eprintln "bad k0"; return 1
      let some up := upStr.toNat? | do IO.eprintln "bad up"; return 1
      let some lfx := lfxStr.toNat? | do IO.eprintln "bad lfx"; return 1
      let some bnd := boundStr.toNat? | do IO.eprintln "bad bound"; return 1
      let c : Params := ⟨lo, len, r, k0, up, lfx, bnd⟩
      let p := ceProgram c
      let name := s!"CeDyadic{lo}x{len}x{r}x{up}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{lo} {len} {r} {k0} {up} {lfx} {bnd} {p.loopCount} ok"
          return 0
  | _ => do
      IO.eprintln "usage: LO LEN R K0 UP LFX BOUND OUT"
      return 1
