import LeanCompCert.Ports.ArraySegSieve

/-!
Emission driver for the offset segmented sieve of `Ports.ArraySegSieve`.

```
lake env lean --run bench/ArraySegEmit.lean MODE LO SEGLEN SEGCOUNT OUT [EXPECTED]
```

`MODE` is one of

* `mertens`  — the Mertens / squarefree residue, thresholds from Hurst
               (`|M| ≤ 0.571√n`) and CDEM (`b = 755/10⁴`), compared **once**
               in the epilogue against the majorant at the window's worst
               endpoint;
* `mertens2` — the same with the second CDEM threshold `b = 285/10⁴`;
* `mertenslive`, `mertenslive2` — the same two, with all four clauses tested
               **at every integer** against `⌊α·⌊√n⌋⌋`, so no window schedule
               and no `√(hi/lo) − 1` weakening.  Result slots are
               `M, Q, G, ⌊√hi⌋`;
* `platt211` — the `Σ μ(m)/m` residue against `√(2/(n+1))`;
* `plattstrong` — the same against `1/(2√(n+1))`;
* `plattstronglive` — the same against `1/(2√(n+1))` tested **at every
               integer**, on a two-limb accumulator at scale
               `2^(63+mobWideBits)`.  No window schedule, and a rounding budget
               `2^(mobWideBits+1)` times smaller.  Result slots are the two
               accumulator limbs, `⌈√(hi+1)⌉` and its square; the seeds are the
               two limbs.

## The emitted `main` carries a verdict

Both drivers exit `0` **exactly when** the artifact's own acceptance condition
held: no threshold test failed.  The hosted driver additionally prints the
result cells a chained run needs, and one line per **clause**, so a failure
names itself instead of arriving as a total:

| exit | class | modes |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the classes do not sum to the aggregate |
| `2` | `hurst_upper` / `mobius_upper` | the residue above its majorant |
| `3` | `hurst_lower` / `mobius_lower` | the residue below its majorant |
| `4` | `cdem_upper` | `Q(n) − (6/π²)n > b√n` |
| `5` | `cdem_lower` | `(6/π²)(n+1) − Q(n) > b√n` |

With `EXPECTED` the driver is *freestanding*: no `printf`, same acceptance
condition.  `EXPECTED` is an **additional** demand — exit `1` if the artifact
did not reproduce it — and never a substitute for acceptance: a run that
reproduces a nonzero violation count exits `2`, because reproducing a failure
is not passing.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

namespace Bench.ArraySegEmit

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

/-- The freestanding driver.  Acceptance is `r == 0`; a supplied `EXPECTED` is
an **additional** demand (exit `1` if the artifact did not reproduce it), never
a substitute for it — reproducing a nonzero count exits `2`. -/
def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    if (r != UINT64_C(" ++ toString expected ++ ")) return 1;\n" ++
  "    return r == UINT64_C(0) ? 0 : 2;\n}\n"

/-- The classes each mode's residue keeps, in scan order.

Every one of them is a **clause**: this file's residues carry no budgets and no
in-loop guards, so there is nothing here that says "the run was invalid", only
statements that failed.  `plattstronglive` has a single class because
`mobiusLiveResidue` folds the two sides into `|V|` before it compares; there is
nothing to separate, and the block has a realisation theorem proved about it. -/
def classesOf : String → List Class
  | "mertens" | "mertens2" | "mertenslive" | "mertenslive2" =>
      [ ("hurst_upper", 0, 2), ("hurst_lower", 1, 3)
      , ("cdem_upper", 2, 4), ("cdem_lower", 3, 5) ]
  | "platt211" | "plattstrong" =>
      [ ("mobius_upper", 0, 2), ("mobius_lower", 1, 3) ]
  | "plattstronglive" => [ ("mobius_majorant", 0, 2) ]
  | _ => []

/-- How many of the result cells the chain reads, per mode. -/
def slotsOf : String → Nat
  | "mertens" | "mertens2" => 7
  | "mertenslive" | "mertenslive2" => 4
  | "platt211" | "plattstrong" => 3
  | _ => 4

end Bench.ArraySegEmit

open Bench.ArraySegEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: loS :: lenS :: cntS :: out :: rest => do
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some cnt := cntS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let c := Cfg.ofRange lo len cnt
      let name := s!"Seg{mode}L{lo}S{len}N{cnt}"
      -- rest = [EXPECTED] ++ [seed...]; EXPECTED = "-" means the hosted driver
      let expected := rest.head?
      let seeds := (rest.drop 1).filterMap String.toNat?
      let seedA := seeds[0]?.getD mertensBias
      let seedB := seeds[1]?.getD 0
      let seedC := seeds[2]?.getD gBias
      let seedT := seeds[0]?.getD tBias
      let p ←
        match mode with
        | "mertens" =>
            pure (mertensProgram c ⟨seedA, seedB, seedC⟩ 755 10000)
        | "mertens2" =>
            pure (mertensProgram c ⟨seedA, seedB, seedC⟩ 285 10000)
        | "mertenslive" =>
            pure (mertensLiveProgram c (Nat.sqrt (lo - 1))
              ⟨seedA, seedB, seedC⟩ 755 10000)
        | "mertenslive2" =>
            pure (mertensLiveProgram c (Nat.sqrt (lo - 1))
              ⟨seedA, seedB, seedC⟩ 285 10000)
        | "platt211" =>
            pure (mobiusProgram c seedT (platt211Threshold c.hi))
        | "plattstrong" =>
            pure (mobiusProgram c seedT (plattStrongerThreshold c.hi))
        | "plattstronglive" =>
            -- carry-in: the two accumulator limbs.  Absent, the walk is
            -- assumed to open at n = 1 and the accumulator is the bare bias.
            let k := mobWideBits
            let dflt := mobLiveSeedStart k
            let s : MobLiveSeed :=
              (mobLiveSeed lo (seeds[0]?.getD dflt.tLo) (seeds[1]?.getD dflt.tHi))
            pure (mobiusLiveProgram c k s)
        | _ => do IO.eprintln "bad MODE"; return 1
      let base := p.arrayLen - 16
      let driver :=
        match expected.bind String.toNat? with
        | some n => exitDriver name p.arrayLen n
        | none =>
            verdictDriver name p.arrayLen base (slotsOf mode) 8
              (classesOf mode) [] true
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"mode={mode} lo={lo} L={len} S={cnt} hi={c.hi}"
          IO.println s!"  primes={c.tableLen} markSteps={c.markSteps} period={c.period}"
          IO.println s!"  rootCount={c.rootCount} rootLen={c.rootLen} rootCap={c.rootCap} boot={c.bootCount} initLen={c.coreInit.length}"
          IO.println s!"  loopCount={p.loopCount} arrayLen={p.arrayLen} bodyLen={p.body.length}"
          IO.println s!"  memoryBytes={8 * p.arrayLen}"
          IO.println s!"  cdemC={cdemC} hurstThr={hurstThreshold c.lo}"
          IO.println s!"  cdemThr755={cdemThreshold 755 10000 c.lo} cdemThr285={cdemThreshold 285 10000 c.lo}"
          IO.println s!"  platt211Thr={platt211Threshold c.hi} plattStrongThr={plattStrongerThreshold c.hi}"
          return 0
  | _ => do
      IO.eprintln "usage: MODE LO SEGLEN SEGCOUNT OUT [EXPECTED|-] [SEED...]"
      return 1
