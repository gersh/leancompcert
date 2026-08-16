import LeanCompCert.Ports.Prop1224RankScheduler

/-!
Emit the two full-domain compiled Proposition 12.2.4 rank campaigns.

    lake env lean --run bench/Prop1224RankSchedulerEmit.lean OUT.c
-/

open LeanCompCert.Ports.Prop1224RankScheduler

def driver (denseName extensionName : String) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[1];\n" ++
  "int main(void) {\n" ++
  "  uint64_t dense_checksum = l_" ++ denseName ++ "(cells);\n" ++
  "  uint64_t extension_checksum = l_" ++ extensionName ++ "(cells);\n" ++
  "  printf(\"dense_rows %llu extension_rows %llu last_q %llu dense_checksum %llu extension_checksum %llu\\n\",\n" ++
  "    (unsigned long long)UINT64_C(3299999999),\n" ++
  "    (unsigned long long)UINT64_C(89047619),\n" ++
  "    (unsigned long long)UINT64_C(21999999840),\n" ++
  "    (unsigned long long)dense_checksum,\n" ++
  "    (unsigned long long)extension_checksum);\n" ++
  "  return 0;\n}\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] =>
      let denseName := "p1224rankdense"
      let extensionName := "p1224rankextension"
      match denseProgram.emitRolled denseName,
          extensionProgram.emitRolled extensionName with
      | .ok denseSource, .ok extensionSource =>
          IO.FS.writeFile out
            (denseSource ++ extensionSource ++ driver denseName extensionName)
          IO.println s!"denseRows={denseRankEnd} extensionRows={extensionRankCount}"
          return 0
      | .error errors, _ | _, .error errors =>
          for error in errors do IO.eprintln error
          return 1
  | _ =>
      IO.eprintln "usage: OUT.c"
      return 1
