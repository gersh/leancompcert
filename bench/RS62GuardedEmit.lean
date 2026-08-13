import LeanCompCert.Ports.RS62LadderEncoding

/-!
Guarded emission driver for an RS62 ladder window.

Unlike the historical `RS62Emit`, this program does not add the ladder
increment at every integer.  Each candidate receives exactly `BOUND` compiled
trial-divisor rounds, and the increment is committed only if no divisor
`d <= sqrt(n)` was found.  The driver refuses a bound that does not cover the
entire requested window.

```
lake env lean --run bench/RS62GuardedEmit.lean \
  START COUNT BOUND SL0 SU0 OUT EXPECTED_L EXPECTED_U
```

This is a correctness-oriented flat guarded route.  It is suitable for
controls and modest shards; the source documentation records that a full
`3.24e8` ladder needs a segmented prime-table route to be affordable.
-/

open LeanCompCert
open LeanCompCert.Ports.RS62Ladder

namespace Bench.RS62GuardedEmit

def driver (loName hiName : String) (expectedL expectedU : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[1];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t lo = l_" ++ loName ++ "((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t hi = l_" ++ hiName ++ "((uint64_t *)(uintptr_t)cells);\n" ++
  "  printf(\"lower %llu\\nupper %llu\\n\",\n" ++
  "    (unsigned long long)lo, (unsigned long long)hi);\n" ++
  "  return lo == UINT64_C(" ++ toString expectedL ++ ") &&\n" ++
  "         hi == UINT64_C(" ++ toString expectedU ++ ") ? 0 : 1;\n" ++
  "}\n"

end Bench.RS62GuardedEmit

open Bench.RS62GuardedEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [startS, countS, boundS, slS, suS, out, expectedLS, expectedUS] =>
      let some start := startS.toNat? | do IO.eprintln "bad START"; return 1
      let some count := countS.toNat? | do IO.eprintln "bad COUNT"; return 1
      let some bound := boundS.toNat? | do IO.eprintln "bad BOUND"; return 1
      let some sl0 := slS.toNat? | do IO.eprintln "bad SL0"; return 1
      let some su0 := suS.toNat? | do IO.eprintln "bad SU0"; return 1
      let some expectedL := expectedLS.toNat? |
        do IO.eprintln "bad EXPECTED_L"; return 1
      let some expectedU := expectedUS.toNat? |
        do IO.eprintln "bad EXPECTED_U"; return 1
      if start < 3 then
        IO.eprintln "START must be at least 3 for the word-safe RS62 increments"
        return 1
      if bound = 0 then
        IO.eprintln "BOUND must be positive"
        return 1
      let top := start + count
      if (bound + 2) * (bound + 2) < top then
        IO.eprintln s!"BOUND={bound} does not cover [START,START+COUNT): \
need {top} <= (BOUND+2)^2"
        return 1
      let pL := ladderProgram start count bound sl0 su0 rSL
      let pU := ladderProgram start count bound sl0 su0 rSU
      let loName := s!"RS62GuardedL{start}x{count}b{bound}"
      let hiName := s!"RS62GuardedU{start}x{count}b{bound}"
      match pL.emitRolled loName, pU.emitRolled hiName with
      | .ok lo, .ok hi =>
          IO.FS.writeFile out (lo ++ hi ++ driver loName hiName expectedL expectedU)
          IO.println s!"start={start} count={count} bound={bound} \
loopCount={pL.loopCount} body={pL.body.length}"
          return 0
      | .error errs, _ | _, .error errs =>
          for e in errs do IO.eprintln e
          return 1
  | _ =>
      IO.eprintln "usage: START COUNT BOUND SL0 SU0 OUT EXPECTED_L EXPECTED_U"
      return 1
