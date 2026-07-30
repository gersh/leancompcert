import LeanCompCert.Ports.TGSieve

/-!
Benchmark support: emit the **rolled** C artifact for stage (a) of the
Helfgott–Platt prime ladder — the progression sieve of
`tg_goldbach_ladder_native.cpp` (arXiv:1305.3062v2, sections 2--4).

The program counts the survivors of the window `[START, START + COUNT)` of
the progression `k · 2⁵² + 1` against every odd prime below `16000`.
`LeanCompCert.Ports.TGSieve.sieveProgram_denote` proves that count equal to
the reference's, for every window.

The loop is rolled, so the emitted C is a fixed-size `while` loop whose
body is the 1861-row table compiled once; only the loop bound changes with
`COUNT`.

Run with `lake env lean --run bench/TGSieveEmit.lean START COUNT OUT VALUE`.
Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.TGSieve

namespace Bench.TGSieveEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.TGSieveEmit

open Bench.TGSieveEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [startStr, countStr, out, valueStr] =>
      let some start := startStr.toNat? | do IO.eprintln "bad start"; return 1
      let some count := countStr.toNat? | do IO.eprintln "bad count"; return 1
      let some value := valueStr.toNat? | do IO.eprintln "bad value"; return 1
      let p := sieveProgram sieveTable start count
      let name := s!"TGSieve{start}x{count}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{start} {count} ok"
          return 0
  | _ => do IO.eprintln "usage: START COUNT OUT VALUE"; return 1
