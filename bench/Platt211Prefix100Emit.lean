import LeanCompCert.Ports.ArraySegMobiusPlatt211Prefix100Certificate
import LeanCompCert.Verified.Rolled

/-!
Emit either rolled CompCert artifact for the trial-division prefix through
candidate 100.

Usage:

```
lake env lean --run bench/Platt211Prefix100Emit.lean word-safety OUT
lake env lean --run bench/Platt211Prefix100Emit.lean accumulator OUT
lake env lean --run bench/Platt211Prefix100Emit.lean observations JOBS
```
-/

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MobiusExtremaTrial
open LeanCompCert.Ports.ArraySegMobiusPlatt211Prefix100Certificate

namespace Bench.Platt211Prefix100Emit

def driver (symbol : String) (expected : Nat) : String :=
  "\nint main(void)\n{\n    return " ++ LeanCompCert.ABI.mangle symbol ++
    "() == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emit (program : Program) (symbol : String) (expected : Nat)
    (out : String) : IO UInt32 := do
  match emitRolled program symbol with
  | .error errors =>
      for error in errors do IO.eprintln error
      return 1
  | .ok source =>
      IO.FS.writeFile out (source ++ driver symbol expected)
      IO.println s!"{symbol} loops={program.loopCount} expected={expected} out={out}"
      return 0

def emitObservation (n : Nat) (out : String) : IO Bool := do
  let some row := prefixObservations[n - 1]? | do
    IO.eprintln s!"prefix candidate out of range: {n}"
    return false
  if row.n != n then
    IO.eprintln s!"prefix table mismatch at {n}: {row.n}"
    return false
  let p := tProgram (prefixCfgAt row.n) prefixExt
  let symbol := s!"platt211_prefix_{row.n}_accumulator"
  return (← emit p symbol row.t out) == 0

end Bench.Platt211Prefix100Emit

open Bench.Platt211Prefix100Emit in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["word-safety", out] =>
      emit prefixWordSafetyProgram "platt211_prefix_100_word_safety" 0 out
  | ["accumulator", out] =>
      emit prefixTProgram "platt211_prefix_100_accumulator"
        9366940894763051949 out
  | ["observations", jobs] =>
      let input ← IO.FS.readFile jobs
      let mut ok := true
      for line in input.splitOn "\n" do
        let fields := (line.splitOn " ").filter (· ≠ "")
        match fields with
        | [] => pure ()
        | [nS, out] =>
            let some n := nS.toNat? | do
              IO.eprintln s!"bad candidate: {nS}"
              ok := false
              continue
            unless ← emitObservation n out do ok := false
        | _ =>
            IO.eprintln s!"bad job line: {line}"
            ok := false
      return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: (word-safety|accumulator) OUT | observations JOBS"
      return 1
