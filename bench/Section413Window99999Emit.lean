import LeanCompCert.Ports.Section413Window99999Certificate
import LeanCompCert.Verified.Rolled

/-! Emit production and rejecting-control artifacts for the 99,999 window. -/

open LeanCompCert.Ports.Section413Window99999Certificate

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
  let p := if control then
      LeanCompCert.Ports.ClosedBoolCarrier.program false
    else windowCarrier
  let name := if control then "S413Window99999Control" else "S413Window99999"
  match LeanCompCert.Verified.Reflect.emitRolled p name with
  | .error errs =>
      for e in errs do IO.eprintln e
      return 1
  | .ok src =>
      IO.FS.writeFile out (src ++ driver name)
      IO.println s!"mode={mode} result={p.denote} out={out}"
      return 0
