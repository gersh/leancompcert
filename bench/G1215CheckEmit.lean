import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.G1215Check

/-!
Benchmark support: emit the rolled C artifact for the **two-sided Helfgott
(12.15) running check** of `LeanCompCert.Ports.G1215Check`.

The emitted function is exactly
`gProgram ⟨LO, LEN, TDIV, BMAX, ESPLIT, FINU, FINL⟩` — the same
`Reflect.Program` whose denotation `Ports/G1215Check*.lean` proves is the flat
fold of `gRound`.  There is no second, hand-written C reference: the artifact
and the theorem are about the same object.

The loop is `LEN · (TDIV + BMAX)` iterations, so emission must be rolled.

Usage:

```
lake env lean --run bench/G1215CheckEmit.lean LO LEN TDIV BMAX ESPLIT FINU FINL OUT
```

The generated `main` returns `0` exactly when the program's output register
(the good flag, after the epilogue's two final-sum tests) holds `1`.  Emission
only; no proof obligation is discharged here, and `Program.denote` is never
evaluated.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.G1215Check

namespace Bench.G1215CheckEmit

/-- The accepting machine value: the good flag. -/
def acceptingValue : Nat := 1

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.G1215CheckEmit

open Bench.G1215CheckEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loStr, lenStr, tdivStr, bmaxStr, esplitStr, finUStr, finLStr, out] =>
      let some lo := loStr.toNat? | do IO.eprintln "bad lo"; return 1
      let some len := lenStr.toNat? | do IO.eprintln "bad len"; return 1
      let some tdiv := tdivStr.toNat? | do IO.eprintln "bad tdiv"; return 1
      let some bmax := bmaxStr.toNat? | do IO.eprintln "bad bmax"; return 1
      let some esplit := esplitStr.toNat? | do IO.eprintln "bad esplit"; return 1
      let some finU := finUStr.toNat? | do IO.eprintln "bad finU"; return 1
      let some finL := finLStr.toNat? | do IO.eprintln "bad finL"; return 1
      let c : Params := ⟨lo, len, tdiv, bmax, esplit, finU, finL⟩
      let p := gProgram c
      let name := s!"G1215Check{lo}x{len}x{tdiv}x{bmax}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{lo} {len} {tdiv} {bmax} {esplit} {finU} {finL} {p.loopCount} ok"
          return 0
  | _ => do
      IO.eprintln "usage: LO LEN TDIV BMAX ESPLIT FINU FINL OUT"
      return 1
