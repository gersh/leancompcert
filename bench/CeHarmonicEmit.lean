import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.CeHarmonicFold

/-! Emit a rolled harmonic-ceiling artifact.

Usage:
`lake env lean --run bench/CeHarmonicEmit.lean LEN NUMERATOR BOUND OUT`
-/

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CeHarmonicFold

private def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++
    "() == UINT64_C(1) ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [lenStr, numeratorStr, boundStr, out] =>
      let some len := lenStr.toNat? | do IO.eprintln "bad len"; return 1
      let some numerator := numeratorStr.toNat? |
        do IO.eprintln "bad numerator"; return 1
      let some bound := boundStr.toNat? | do IO.eprintln "bad bound"; return 1
      let c : Params := ⟨len, numerator, bound⟩
      let p := harmProgram c
      let name := s!"CeHarmonic{len}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{len} {numerator} {bound} {p.loopCount} ok"
          return 0
  | _ =>
      IO.eprintln "usage: LEN NUMERATOR BOUND OUT"
      return 1
