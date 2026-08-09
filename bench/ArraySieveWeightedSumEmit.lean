import LeanCompCert.Ports.ArraySieveWeightedSum
import LeanCompCert.Verified.Rolled

/-!
Emit the proved weighted-prime-sieve computations used by the Platt marking
budgets.

```
lake env lean --run bench/ArraySieveWeightedSumEmit.lean BOUND LEN WEIGHT BONUS EXPECTED OUT
```
-/

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySieveWeightedSum

namespace Bench.ArraySieveWeightedSumEmit

def driver (name : String) (cells expected : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    printf(\"weighted-sum %llu\\n\", (unsigned long long)r);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.ArraySieveWeightedSumEmit

open Bench.ArraySieveWeightedSumEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [boundStr, lenStr, weightStr, bonusStr, expectedStr, out] =>
      let some bound := boundStr.toNat? | do IO.eprintln "bad BOUND"; return 1
      let some len := lenStr.toNat? | do IO.eprintln "bad LEN"; return 1
      let some weight := weightStr.toNat? | do IO.eprintln "bad WEIGHT"; return 1
      let some bonus := bonusStr.toNat? | do IO.eprintln "bad BONUS"; return 1
      let some expected := expectedStr.toNat? |
        do IO.eprintln "bad EXPECTED"; return 1
      let p := sieveWeightedProgram bound len weight bonus
      let name := s!"SieveWeighted{bound}x{len}w{weight}b{bonus}"
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver name p.arrayLen expected)
          IO.println s!"bound={bound} len={len} weight={weight} bonus={bonus} expected={expected}"
          IO.println s!"loopCount={p.loopCount} arrayLen={p.arrayLen} bodyLen={p.body.length}"
          return 0
  | _ => do
      IO.eprintln "usage: BOUND LEN WEIGHT BONUS EXPECTED OUT"
      return 1
