import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.ArrayAudit

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

Each emitted `main` carries the same verdict `bench/ArraySegEmit.lean`'s does:
exit `0` only when no threshold test failed, `1` if the two clause counters do
not sum to the aggregate, `2` for `mobius_upper` and `3` for `mobius_lower`.

A chained sweep is thousands of artifacts, and a `lean --run` per artifact
pays the interpreter's start-up — which, when the machine is under memory
pressure and the `.olean` page cache has been evicted, is minutes rather than
the half-second the emission itself costs.  Everything else here is
`ArraySegEmit`'s code, unchanged; only the driver loop is new.

Modes `platt211audit` and `plattstrongaudit` emit the mechanically transformed
fail-safe program.  Their driver exits zero exactly when every source
division and array access was defined.  Emission only; no proof obligation is
discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.ArraySegSieve

namespace Bench.ArraySegBatch

/-- One failure class: its label, its offset inside the class block, and the
exit status the driver returns when it is the first nonzero one.  The list is
given in **scan order**, so the classes that invalidate a run come before the
classes that are a result. -/
abbrev Class := String × Nat × Nat

/-- A hosted driver that prints the result cells and then **decides**.

`base` is the first result cell, `slots` how many of them the chain reads, and
`classBase` the slot at which the class counters start.  The emitted `main` returns `0` only when every
class counter is zero, `1` when the classes do not sum to the aggregate (a
split that has come adrift is a reason to trust neither number), and otherwise
the status of the first nonzero class in scan order. -/
def verdictDriver (name : String) (cells base slots classBase : Nat)
    (classes : List Class) (diags : List (String × Nat)) (sumIsExact : Bool) :
    String :=
  let cell (i : Nat) : String := "cells[" ++ toString (base + i) ++ "]"
  let classLine (x : Class) : String :=
    "    printf(\"class " ++ x.1 ++ " %llu\\n\", (unsigned long long)" ++
      cell (classBase + x.2.1) ++ ");\n" ++
    "    sum += " ++ cell (classBase + x.2.1) ++ ";\n"
  let diagLine (x : String × Nat) : String :=
    "    printf(\"diag " ++ x.1 ++ " %llu\\n\", (unsigned long long)" ++
      cell x.2 ++ ");\n"
  let verdictLine (x : Class) : String :=
    "    if (" ++ cell (classBase + x.2.1) ++ " != UINT64_C(0)) {\n" ++
    "        printf(\"verdict FAIL " ++ x.1 ++ "\\n\");\n" ++
    "        return " ++ toString x.2.2 ++ ";\n    }\n"
  let consistency :=
    if sumIsExact then
      "    if (sum != r) {\n" ++
      "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
      "               (unsigned long long)sum, (unsigned long long)r);\n" ++
      "        return 1;\n    }\n"
    else
      -- the aggregate collapses several conditions per row, so the classes
      -- bound it from above rather than equalling it; what must hold is that
      -- they vanish together
      "    if ((sum == UINT64_C(0)) != (r == UINT64_C(0)) || sum < r) {\n" ++
      "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
      "               (unsigned long long)sum, (unsigned long long)r);\n" ++
      "        return 1;\n    }\n"
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    uint64_t sum = 0;\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < " ++ toString slots ++ "; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString base ++ " + i]);\n" ++
  String.join (classes.map classLine) ++
  String.join (diags.map diagLine) ++
  consistency ++
  String.join (classes.map verdictLine) ++
  "    printf(\"verdict PASS\\n\");\n" ++
  "    return 0;\n}\n"


/-- The two clauses of the `Σ μ(m)/m` residue, in scan order.  Identical to
`bench/ArraySegEmit.lean`'s, because this file emits the same artifacts. -/
def classes : List Class := [ ("mobius_upper", 0, 2), ("mobius_lower", 1, 3) ]

/-- Minimal self-checking driver for a fail-safe audit program. -/
def auditDriver (name : String) (cells : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(0) ? 0 : 1;\n" ++
  "}\n"

def emitOne (idx mode loS lenS cntS : String) (out : String)
    (seed : Option Nat) : IO Bool := do
  let some lo := loS.toNat? | do IO.eprintln s!"job {idx}: bad LO"; return false
  let some len := lenS.toNat? | do IO.eprintln s!"job {idx}: bad SEGLEN"; return false
  let some cnt := cntS.toNat? | do IO.eprintln s!"job {idx}: bad SEGCOUNT"; return false
  let c := Cfg.ofRange lo len cnt
  let name := s!"Seg{mode}L{lo}S{len}N{cnt}"
  let source ←
    match mode with
    | "platt211" => pure (mobiusProgram c (seed.getD tBias) (platt211Threshold c.hi))
    | "platt211audit" => pure (mobiusProgram c (seed.getD tBias) (platt211Threshold c.hi))
    | "plattstrong" => pure (mobiusProgram c (seed.getD tBias) (plattStrongerThreshold c.hi))
    | "plattstrongaudit" => pure (mobiusProgram c (seed.getD tBias) (plattStrongerThreshold c.hi))
    | _ => do IO.eprintln s!"job {idx}: bad MODE {mode}"; return false
  let audited := mode == "platt211audit" || mode == "plattstrongaudit"
  let p := if audited then auditProgram source else source
  match p.emitRolled name with
  | .error errs => (for e in errs do IO.eprintln e); return false
  | .ok src =>
      IO.FS.writeFile out (src ++
        if audited then auditDriver name p.arrayLen
        else verdictDriver name p.arrayLen (p.arrayLen - 16) 3 8 classes []
          true)
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
