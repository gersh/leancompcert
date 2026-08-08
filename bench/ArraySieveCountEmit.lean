import LeanCompCert.Ports.ArraySieveCount
import LeanCompCert.Verified.Rolled

/-!
Emit the proved array-backed prime-count computation used by the literal
Platt root schedules.

```
lake env lean --run bench/ArraySieveCountEmit.lean BOUND LEN EXPECTED OUT
```

The generated process exits successfully exactly when the compiled program
returns `EXPECTED`.  It also prints the returned value for the run receipt.
-/

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySieveCount

namespace Bench.ArraySieveCountEmit

def driver (name : String) (cells expected : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    printf(\"count %llu\\n\", (unsigned long long)r);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.ArraySieveCountEmit

open Bench.ArraySieveCountEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [boundStr, lenStr, expectedStr, out] =>
      let some bound := boundStr.toNat? | do IO.eprintln "bad BOUND"; return 1
      let some len := lenStr.toNat? | do IO.eprintln "bad LEN"; return 1
      let some expected := expectedStr.toNat? |
        do IO.eprintln "bad EXPECTED"; return 1
      let p := sieveCountProgram bound len
      let name := s!"SieveCount{bound}x{len}"
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver name p.arrayLen expected)
          IO.println s!"bound={bound} len={len} expected={expected}"
          IO.println s!"loopCount={p.loopCount} arrayLen={p.arrayLen} bodyLen={p.body.length}"
          return 0
  | _ => do
      IO.eprintln "usage: BOUND LEN EXPECTED OUT"
      return 1
