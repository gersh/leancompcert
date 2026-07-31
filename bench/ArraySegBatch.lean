import LeanCompCert.Ports.ArraySegSieve

/-!
Batch emitter for `Ports.ArraySegSieve`: the same artifacts
`bench/ArraySegEmit.lean` emits, but many of them from one Lean process.

```
lake env lean --run bench/ArraySegBatch.lean JOBS
```

`JOBS` is a text file, one job per line:

```
IDX MODE LO SEGLEN SEGCOUNT OUTPATH [SEED]
```

and one line is printed per job,

```
job IDX hi=H thr211=T thrstrong=T'
```

A chained sweep is thousands of artifacts, and a `lean --run` per artifact
pays the interpreter's start-up — which, when the machine is under memory
pressure and the `.olean` page cache has been evicted, is minutes rather than
the half-second the emission itself costs.  Everything else here is
`ArraySegEmit`'s code, unchanged; only the driver loop is new.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

namespace Bench.ArraySegBatch

def hostedDriver (name : String) (cells slots : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < " ++ toString slots ++ "; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 8 + i]);\n" ++
  "    return 0;\n}\n"

def emitOne (idx mode loS lenS cntS : String) (out : String)
    (seed : Option Nat) : IO Bool := do
  let some lo := loS.toNat? | do IO.eprintln s!"job {idx}: bad LO"; return false
  let some len := lenS.toNat? | do IO.eprintln s!"job {idx}: bad SEGLEN"; return false
  let some cnt := cntS.toNat? | do IO.eprintln s!"job {idx}: bad SEGCOUNT"; return false
  let c := Cfg.ofRange lo len cnt
  let name := s!"Seg{mode}L{lo}S{len}N{cnt}"
  let p ←
    match mode with
    | "platt211" => pure (mobiusProgram c (seed.getD tBias) (platt211Threshold c.hi))
    | "plattstrong" => pure (mobiusProgram c (seed.getD tBias) (plattStrongerThreshold c.hi))
    | _ => do IO.eprintln s!"job {idx}: bad MODE {mode}"; return false
  match p.emitRolled name with
  | .error errs => (for e in errs do IO.eprintln e); return false
  | .ok src =>
      IO.FS.writeFile out (src ++ hostedDriver name p.arrayLen 7)
      IO.println s!"job {idx} lo={lo} hi={c.hi} thr211={platt211Threshold c.hi} thrstrong={plattStrongerThreshold c.hi} arrayLen={p.arrayLen} loopCount={p.loopCount} bodyLen={p.body.length}"
      return true

end Bench.ArraySegBatch

open Bench.ArraySegBatch in
def main (args : List String) : IO UInt32 := do
  match args with
  | [jobs] => do
      let text ← IO.FS.readFile jobs
      let mut ok := true
      for line in text.splitOn "\n" do
        let f := (line.splitOn " ").filter (· ≠ "")
        match f with
        | [] => pure ()
        | [idx, mode, lo, len, cnt, out] =>
            unless ← emitOne idx mode lo len cnt out none do ok := false
        | [idx, mode, lo, len, cnt, out, sd] =>
            unless ← emitOne idx mode lo len cnt out (sd.toNat?) do ok := false
        | _ => do IO.eprintln s!"bad job line: {line}"; ok := false
      return (if ok then 0 else 1)
  | _ => do
      IO.eprintln "usage: ArraySegBatch JOBS"
      return 2
