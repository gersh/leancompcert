import LeanCompCert.Ports.Prop1224Cell
import LeanCompCert.Verified.ArrayAudit

/-!
Emission driver for the per-cell margin of `Ports.Prop1224Cell`.

```
lake env lean --run bench/Prop1224CellEmit.lean Q PHILO CONSTLO AF KLO KHI LO SEGLEN SEGCOUNT G EX TH T PRIMES OUT [audit]
```

`PRIMES` is a comma-separated list of the distinct primes of `Q` (empty for
`Q = 1`).  `G`, `EX`, and `TH` are the carry-in at `LO − 1`: the running `G_q`
at scale `2^C`, `⌊log₂(LO−1)⌋`, and `2^(⌊log₂(LO−1)⌋+1)` (use `EX=0`,
`TH=2` when `LO=1`).  `T` may instead be seeded at
`⌊2^5·(20000k₀)^{1/3}⌋`, where `k₀` is the first tested cell.  Production
rows can start at `LO = 1` with `G = 0`; marking every prime through
`⌊√hi⌋` makes the factor classification valid over the entire sweep.  Seeding
the cube-root cursor at the first tested cell is safe because earlier cells do
not use the margin, and avoids a costly unverified prefix computation.

The driver prints the six result cells:

```
slot0 G   slot1 cells   slot2 minMargin+2^(C+6)   slot3 cubeRoot
slot4 ⌊log₂⌋            slot5 violations
```

followed by the five failure classes in `slot6 … slot10`, which sum to `slot5`.

## The emitted `main` carries a verdict

It exits `0` **exactly when** the aggregate is `0`, and otherwise names the
class:

| exit | class | meaning |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the five classes do not sum to the aggregate |
| `2` | `budget_marktable` | the mark cursor had not finished: the sieve was truncated |
| `3` | `guard_log2` | one `⌊log₂ r⌋` increment did not suffice |
| `4` | `budget_cuberoot` | the certified cube root was still advanceable |
| `5` | `guard_cuberoot_lower` | the current cube root was not a valid lower bound |
| `6` | `margin` | the per-cell margin went negative — the clause failed |

The four budgets and guards come first because they retract the run: on those
cells the margin was not tested at all.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Prop1224Cell

namespace Bench.Prop1224CellEmit

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
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
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

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    printf(\"audit %llu\\n\", (unsigned long long)r);\n" ++
  "    return r == UINT64_C(0) ? 0 : 1;\n}\n"


/-- The five classes, in scan order: the four that retract the run, then the
margin.  Slot offsets follow `Ports.Prop1224Cell.violRegs`,
`[Margin, Mark, Log2, Cbrt-too-low, Cbrt-too-high]`. -/
def classes : List Class :=
  [ ("budget_marktable", 1, 2)
  , ("guard_log2", 2, 3)
  , ("budget_cuberoot", 3, 4)
  , ("guard_cuberoot_lower", 4, 5)
  , ("margin", 0, 6) ]

def parsePrimes (s : String) : List Nat :=
  (s.splitOn ",").filterMap (fun t => t.trimAscii.toString.toNat?)

end Bench.Prop1224CellEmit

open Bench.Prop1224CellEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | qS :: plS :: clS :: afS :: kloS :: khiS :: loS :: lenS :: cntS ::
    gS :: exS :: thS :: tS :: psS :: out :: rest => do
      let nat (s : String) (nm : String) : IO Nat := do
        match s.toNat? with
        | some v => pure v
        | none => do IO.eprintln s!"bad {nm}"; pure 0
      let q ← nat qS "Q"
      let pl ← nat plS "PHILO"
      let cl ← nat clS "CONSTLO"
      let af ← nat afS "AF"
      let klo ← nat kloS "KLO"
      let khi ← nat khiS "KHI"
      let lo ← nat loS "LO"
      let len ← nat lenS "SEGLEN"
      let cnt ← nat cntS "SEGCOUNT"
      let g ← nat gS "G"
      let ex ← nat exS "EX"
      let th ← nat thS "TH"
      let t ← nat tS "T"
      let c := CellCfg.ofRow q pl cl af klo khi (parsePrimes psS) lo len cnt
      let s : CellSeed := { g := g, ex := ex, th := th, t := t, cells := 0 }
      let p := cellProgram c s
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram p else p
      let name := s!"P1224CellQ{q}L{len}N{cnt}{if auditMode then "Audit" else ""}"
      match emitted.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          let driver := if auditMode then auditDriver name emitted.arrayLen
            else verdictDriver name p.arrayLen (p.arrayLen - 12) 6 6 classes
              [] true
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"q={q} lo={lo} hi={c.hi} root={c.root} name={name}"
          IO.println s!"  tableLen={c.tableLen} markSteps={c.markSteps} period={c.period}"
          IO.println s!"  bodyLen={p.body.length} arrayLen={p.arrayLen} loopCount={p.loopCount}"
          IO.println s!"  instructions={p.body.length * p.loopCount}"
          return 0
  | _ => do
      IO.eprintln "usage: Q PHILO CONSTLO AF KLO KHI LO SEGLEN SEGCOUNT G EX TH T PRIMES OUT [audit]"
      return 1
