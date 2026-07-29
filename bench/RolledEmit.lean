import LeanCompCert.Verified.Rolled
import LeanCompCert.Testing.FixedPointCertificate

/-!
Benchmark support: emit the rolled C artifact for the 128-bit fixed-point
fold at a caller-chosen loop count, so CompCert compile time and native run
time can be measured as a function of iteration count.

Run with `lake env lean --run bench/RolledEmit.lean COUNT OUTFILE`.
No proof obligations are discharged here; this is emission only.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Testing.FixedPointCertificate (body)

namespace Bench.RolledEmit

def prog (n : Nat) : Program := {
  regCount := 20
  loopCount := n
  init := []
  body := body
  epilogue := []
  output := 0
}

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.RolledEmit

open Bench.RolledEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | countStr :: out :: rest =>
      let some count := countStr.toNat? | do
        IO.eprintln "bad count"; return 1
      let p := prog count
      -- The reference value may be supplied so that emission cost can be
      -- measured without the (much larger) interpreter evaluation of `denote`.
      let value ← match rest with
        | [v] => match v.toNat? with
                 | some v => pure v
                 | none => do IO.eprintln "bad value"; return 1
        | _ => match p.denote with
               | some v => pure v
               | none => do IO.eprintln "denote failed"; return 1
      let name := s!"BenchRolled{count}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{count} {value}"
          return 0
  | _ => do IO.eprintln "usage: COUNT OUT"; return 1
