import LeanCompCert.Ports.RamareCombined100MShapeSieve

/-!
Emission driver for the segmented Ramaré shape classifier.

```
lake env lean --run bench/RamareCombined100MShapeEmit.lean \
  positive|control LO SEGLEN SEGCOUNT TABLEHI OUT.c
```

The control shortens every window's mark budget by one iteration.  The
artifact must then report a nonzero guard count; accepting it would mean that
a truncated factor table could silently pass.
-/

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

namespace Bench.RamareCombined100MShapeEmit

def driver (name mode : String) (c : Cfg) : String :=
  let expectedSeen := c.segLen * c.segCount
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    uint64_t seen = cells[" ++ toString (c.resultBase + 1) ++ "];\n" ++
  "    uint64_t mark = cells[" ++ toString (c.resultBase + 2) ++ "];\n" ++
  "    uint64_t shape = cells[" ++ toString (c.resultBase + 3) ++ "];\n" ++
  "    printf(\"guards %llu seen %llu mark %llu shape %llu\\n\",\n" ++
  "           (unsigned long long)r, (unsigned long long)seen,\n" ++
  "           (unsigned long long)mark, (unsigned long long)shape);\n" ++
  (if mode = "positive" then
    "    return r == UINT64_C(0) && seen == UINT64_C(" ++
      toString expectedSeen ++ ") ? 0 : 2;\n"
   else
    "    return r != UINT64_C(0) ? 0 : 2;\n") ++
  "}\n"

end Bench.RamareCombined100MShapeEmit

open Bench.RamareCombined100MShapeEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, loS, lenS, countS, hiS, out] =>
      if mode != "positive" && mode != "control" then
        IO.eprintln "MODE must be positive or control"
        return 1
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some count := countS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let some tableHi := hiS.toNat? | do IO.eprintln "bad TABLEHI"; return 1
      let base := Cfg.ofChain lo len count tableHi
      if len = 0 || count = 0 || base.table.isEmpty then
        IO.eprintln "SEGLEN, SEGCOUNT and the prime table must be nonempty"
        return 1
      if lo <= Nat.sqrt tableHi || base.hi > tableHi then
        IO.eprintln s!"need sqrt(TABLEHI) < LO and swept hi <= TABLEHI; got root={Nat.sqrt tableHi}, swept hi={base.hi}"
        return 1
      let c := if mode = "control" then
        { base with markSteps := base.markSteps / 2 }
      else base
      let p := program c
      let name := "RamareCombinedShape"
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver name mode c)
          IO.println s!"mode={mode} lo={c.lo} hi={c.hi} L={c.segLen} segments={c.segCount}"
          IO.println s!"primes={c.tableLen} markSteps={c.markSteps} period={c.period}"
          IO.println s!"loopCount={p.loopCount} bodyLen={p.body.length} arrayLen={p.arrayLen} memoryBytes={8 * p.arrayLen}"
          return 0
  | _ =>
      IO.eprintln "usage: positive|control LO SEGLEN SEGCOUNT TABLEHI OUT.c"
      return 1
