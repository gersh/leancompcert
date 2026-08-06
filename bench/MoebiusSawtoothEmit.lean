import LeanCompCert.Testing.MoebiusSawtoothCertificate

/-!
Emit the fixed production Möbius-sawtooth checker.

Usage: `lake env lean --run bench/MoebiusSawtoothEmit.lean EXPECTED OUT`
The production receipt uses `EXPECTED=0`; `EXPECTED=1` is the rejecting
control with an otherwise identical checker.
-/

open LeanCompCert.Ports.MoebiusSawtooth
open LeanCompCert.Testing.MoebiusSawtoothCertificate

set_option maxRecDepth 1000000

private def driver (expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString program.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    return l_MoebiusSawtooth_head11815(cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [expectedStr, out] =>
      let some expected := expectedStr.toNat? |
        do IO.eprintln "bad expected value"; return 1
      match program.emitRolled symbolName with
      | .error errors =>
          for e in errors do IO.eprintln e
          return 1
      | .ok source =>
          IO.FS.writeFile out (source ++ driver expected)
          IO.println s!"{program.loopCount} {program.arrayLen} {expected} ok"
          return 0
  | _ =>
      IO.eprintln "usage: EXPECTED OUT"
      return 1
