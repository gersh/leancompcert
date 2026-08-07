import LeanCompCert.Ports.Section413G1Full99999Certificate

/-! Emit the verified complete Section 4.1.3 99,999-cell table checker.

`positive` uses the proved generated table. `control` changes its first
expected cell to zero, so the same machine computation must reject it.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413G1Generated99999Chunks
open LeanCompCert.Ports.Section413G1Full99999Certificate

def driver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    printf(\"flag=%llu\\n\", (unsigned long long)r);\n" ++
  "    return r == 0 ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  let [mode, out] := args | do
    IO.eprintln "usage: positive|control OUT.c"
    return 1
  let some expected :=
      if mode = "positive" then some expected99999
      else if mode = "control" then some (expected99999.set! 1 czero)
      else none
    | do
      IO.eprintln "mode must be positive or control"
      return 1
  let p := tableProgram fullCfg expected
  let name := if mode = "positive" then "S413G1Table99999" else
    "S413G1Table99999Control"
  match p.emitRolled name with
  | .error errs =>
      for e in errs do IO.eprintln e
      return 1
  | .ok src =>
      IO.FS.writeFile out (src ++ driver name p.arrayLen)
      IO.println s!"mode={mode} arrayLen={p.arrayLen} loops={p.loopCount} \
        body={p.body.length} epilogue={p.epilogue.length} out={out}"
      return 0
