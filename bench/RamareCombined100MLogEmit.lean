import LeanCompCert.Ports.RamareCombined100MLogSweep

/-!
Emission driver for the segmented Ramaré classifier plus its exact RS62
log-ladder carry.

```
lake env lean --run bench/RamareCombined100MLogEmit.lean \
  positive|control LO SEGLEN SEGCOUNT TABLEHI LOGL LOGU OUT.c
```
-/

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.RamareCombined100M.LogSweep

private def driver (name mode : String)
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg) : String :=
  let expectedSeen := c.segLen * c.segCount
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString (c.arrayLen + 2) ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    uint64_t seen = cells[" ++ toString (c.resultBase + 1) ++ "];\n" ++
  "    uint64_t mark = cells[" ++ toString (c.resultBase + 2) ++ "];\n" ++
  "    uint64_t shape = cells[" ++ toString (c.resultBase + 3) ++ "];\n" ++
  "    uint64_t logl = cells[" ++ toString (c.resultBase + 4) ++ "];\n" ++
  "    uint64_t logu = cells[" ++ toString (c.resultBase + 5) ++ "];\n" ++
  "    printf(\"guards %llu seen %llu mark %llu shape %llu logL %llu logU %llu\\n\",\n" ++
  "      (unsigned long long)r, (unsigned long long)seen,\n" ++
  "      (unsigned long long)mark, (unsigned long long)shape,\n" ++
  "      (unsigned long long)logl, (unsigned long long)logu);\n" ++
  (if mode = "positive" then
    "    return r == UINT64_C(0) && seen == UINT64_C(" ++
      toString expectedSeen ++ ") ? 0 : 2;\n"
   else "    return r != UINT64_C(0) ? 0 : 2;\n") ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, loS, lenS, countS, hiS, logLS, logUS, out] =>
      if mode != "positive" && mode != "control" then
        IO.eprintln "MODE must be positive or control"
        return 1
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some count := countS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let some tableHi := hiS.toNat? | do IO.eprintln "bad TABLEHI"; return 1
      let some logL := logLS.toNat? | do IO.eprintln "bad LOGL"; return 1
      let some logU := logUS.toNat? | do IO.eprintln "bad LOGU"; return 1
      let base :=
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg.ofChain
          lo len count tableHi
      if len = 0 || count = 0 || base.table.isEmpty then
        IO.eprintln "SEGLEN, SEGCOUNT and the prime table must be nonempty"
        return 1
      if lo <= Nat.sqrt tableHi || base.hi > tableHi then
        IO.eprintln "need sqrt(TABLEHI) < LO and swept hi <= TABLEHI"
        return 1
      let c := if mode = "control" then
        { base with markSteps := base.markSteps / 2 }
      else base
      let seed : Seed := ⟨logL, logU⟩
      let p := program c seed
      let name := "RamareCombinedLogSweep"
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver name mode c)
          IO.println s!"mode={mode} lo={c.lo} hi={c.hi} L={c.segLen} segments={c.segCount}"
          IO.println s!"loopCount={p.loopCount} bodyLen={p.body.length} arrayLen={p.arrayLen} memoryBytes={8 * p.arrayLen}"
          return 0
  | _ =>
      IO.eprintln "usage: positive|control LO SEGLEN SEGCOUNT TABLEHI LOGL LOGU OUT.c"
      return 1
