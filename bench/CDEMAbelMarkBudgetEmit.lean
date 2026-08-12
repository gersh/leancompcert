import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckCompile

/-!
Emit the rolled CompCert artifact for the production CDEM Abel marking-budget
check.  This is the same `Reflect.Program` whose source denotation and verified
compiler bridge are proved in `CDEMAbelMarkBudgetCheck{Fold,Compile}`.

Usage:

```
lake env lean --run bench/CDEMAbelMarkBudgetEmit.lean OUT
```

The generated `main` returns success exactly when the output is the production
budget `8723967`.  Emission does not evaluate the 88-million-round denotation.
-/

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

namespace Bench.CDEMAbelMarkBudgetEmit

def acceptingValue : Nat := 8723967
def symbolName : String := "CDEMAbelMarkBudgetProduction"

def mainC : String :=
  "\nint main(void)\n{\n    return l_" ++ symbolName ++
    "() == UINT64_C(" ++ toString acceptingValue ++ ") ? 0 : 1;\n}\n"

end Bench.CDEMAbelMarkBudgetEmit

open Bench.CDEMAbelMarkBudgetEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [out] =>
      match emitRolled program symbolName with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC)
          IO.println s!"{program.loopCount} {acceptingValue} ok"
          return 0
  | _ =>
      IO.eprintln "usage: OUT"
      return 1
