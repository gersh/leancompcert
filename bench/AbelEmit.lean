import LeanCompCert.Ports.CDEMAbelScan

/-!
Emission driver for the CDEM Abel increment scan of `Ports.CDEMAbelScan`.

```
lake env lean --run bench/AbelEmit.lean W K SEGLEN SEGCOUNT OUT [EXPECTED] [ref]
```

The scan covers `[1, SEGLEN·SEGCOUNT]` with weight scale `W` and Möbius
prefix bound `K`.

## The emitted `main` carries a verdict

Both drivers exit `0` **exactly when** the artifact's own acceptance condition
held: every guard clear, i.e. the aggregate violation count is `0`.  The hosted
driver also prints the twelve result slots the comparison against
`bench/ref_abel.c` reads, and one line per guard:

| exit | class | meaning |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the four classes do not sum to the aggregate |
| `2` | `guard_weightquotient` | `⌊W/s⌋` exceeded `2³¹` |
| `3` | `budget_marktable` | the divisor cursor had not finished |
| `4` | `guard_sqrt` | one `⌊√k⌋` increment did not suffice |
| `5` | `budget_bisection` | the bisection bracket had not closed |

With `EXPECTED` the driver is *freestanding*: same acceptance condition, and
`EXPECTED` is an **additional** demand rather than a substitute — a run that
reproduces a nonzero violation count exits `2`.

A third argument `ref` additionally prints the Lean-side reference fold, so
the emitter, the Lean reference and the C oracle can be compared without
leaving the shell.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan

namespace Bench.AbelEmit

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


/-- The four classes, in scan order.  All four are guards: the scan states no
inequality of its own, it produces the increments a later Abel summation
consumes, so every failure here retracts the run rather than reporting a
result.  Slot offsets follow `Ports.CDEMAbelScan.violRegs`. -/
def classes : List Class :=
  [ ("guard_weightquotient", 0, 2)
  , ("budget_marktable", 1, 3)
  , ("guard_sqrt", 2, 4)
  , ("budget_bisection", 3, 5) ]

end Bench.AbelEmit

open Bench.AbelEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | w :: k :: segLen :: segCount :: out :: rest => do
      let W := w.toNat!
      let K := k.toNat!
      let L := segLen.toNat!
      let C := segCount.toNat!
      if W == 0 || K == 0 || L == 0 || C == 0 then
        IO.eprintln "require W, K, SEGLEN, SEGCOUNT >= 1"
        return 2
      let cfg := Cfg.ofRange W K L C
      let p := abelProgram cfg
      let name := "CDEMAbel.scan"
      let sym := "CDEMAbel_scan"
      IO.println s!"W={W}"
      IO.println s!"K={K}"
      IO.println s!"HI={cfg.hi}"
      IO.println s!"PRIMES={cfg.pn}"
      IO.println s!"BS_STEPS={cfg.bsSteps}"
      IO.println s!"MARK_STEPS={cfg.markSteps}"
      IO.println s!"SIEVE_LEN={cfg.sieveLen}"
      IO.println s!"PERIOD={cfg.period}"
      IO.println s!"LOOP={p.loopCount}"
      IO.println s!"CELLS={cfg.arrayLen}"
      IO.println s!"BODY={cfg.body.length}"
      if rest.length ≥ 2 && rest[1]! ≠ "" then
        let r := Ref.fold W K cfg.hi
        IO.println s!"REF_UPOS={r.uPos}"
        IO.println s!"REF_UNEG={r.uNeg}"
        IO.println s!"REF_V={r.v}"
        IO.println s!"REF_TV={r.tv}"
      let hosted :=
        verdictDriver sym cfg.arrayLen (cfg.arrayLen - 16) 12 12 classes [] true
      let driver :=
        match rest.head? with
        | some e =>
            match e.toNat? with
            | some n => exitDriver sym cfg.arrayLen n
            | none => hosted
        | none => hosted
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"wrote {out}"
          return 0
  | _ =>
      IO.eprintln
        "usage: AbelEmit W K SEGLEN SEGCOUNT OUT [EXPECTED] [ref]"
      return 2
