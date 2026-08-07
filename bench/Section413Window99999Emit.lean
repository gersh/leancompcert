import LeanCompCert.Ports.Section413Window99999Certificate
import LeanCompCert.Verified.Rolled

/-! Emit production and rejecting-control artifacts for the 99,999 window. -/

open LeanCompCert.Ports.Section413Window99999Certificate
open LeanCompCert.Ports.Section413WindowRuntime

def driver (name : String) : String :=
  "\n#include <stdio.h>\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "();\n" ++
  "    printf(\"flag=%llu\\n\", (unsigned long long)r);\n" ++
  "    return r == 0 ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  let [mode, out] := args | do
    IO.eprintln "usage: positive|control OUT.c"
    return 1
  let control := mode = "control"
  if mode != "positive" && !control then
    IO.eprintln "mode must be positive or control"
    return 1
  let words := if control then (commonBound + 1) :: windowWords.tail else windowWords
  let lp := LeanCompCert.Ports.TotalWordBounds.boundsProgram commonBound words
  let p := lp.flatten
  let name := if control then "S413Window99999Control" else "S413Window99999"
  match LeanCompCert.Verified.Reflect.emitRolled p name with
  | .error errs =>
      for e in errs do IO.eprintln e
      return 1
  | .ok src =>
      IO.FS.writeFile out (src ++ driver name)
      IO.println s!"mode={mode} words={words.length} result={lp.denote} out={out}"
      return 0
