import LeanCompCert.Ports.Prop1224LogCbrtTable
import LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Ports.Prop1224LogCbrtTable

namespace Bench.Prop1224LogCbrtTableEmit

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? |
    throw <| IO.userError s!"bad {label}: {value}"
  return n

def cfg (rows : Nat) : Cfg :=
  let lnBase := 1
  let cbrtBase := lnBase + rows + 1
  let resultCell := cbrtBase + rows + 1
  { rows, lnBase, cbrtBase, resultCell, arrayLen := resultCell + 1 }

def positiveDriver (name : String) (c : Cfg) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void) { uint64_t v = l_" ++ name ++ "(cells);\n" ++
  "  for (uint64_t n = 1; n <= UINT64_C(" ++ toString (min c.rows 256) ++ "); ++n)\n" ++
  "    printf(\"%llu %llu %llu\\n\", (unsigned long long)n,\n" ++
  "      (unsigned long long)cells[" ++ toString c.lnBase ++ " + n],\n" ++
  "      (unsigned long long)cells[" ++ toString c.cbrtBase ++ " + n]);\n" ++
  "  printf(\"violations %llu stored %llu\\n\", (unsigned long long)v,\n" ++
  "    (unsigned long long)cells[" ++ toString c.resultCell ++ "]);\n" ++
  "  return v == UINT64_C(0) ? 0 : 1; }\n"

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) { uint64_t v = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"audit %llu\\n\", (unsigned long long)v);\n" ++
  "  return v == UINT64_C(0) ? 0 : 1; }\n"

end Bench.Prop1224LogCbrtTableEmit

open Bench.Prop1224LogCbrtTableEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | rowsS :: out :: rest => try
      let rows ← parseNat "rows" rowsS
      if rows = 0 then
        IO.eprintln "ROWS must be positive"
        return 1
      let c := cfg rows
      let sourceProgram := program c
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram sourceProgram else sourceProgram
      let name := s!"p1224logcbrt{rows}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name c
          IO.FS.writeFile out (source ++ host)
          IO.println s!"rows={rows} loopCount={sourceProgram.loopCount} arrayLen={sourceProgram.arrayLen}"
          IO.println s!"lnBase={c.lnBase} cbrtBase={c.cbrtBase} resultCell={c.resultCell}"
          return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
      IO.eprintln "usage: ROWS OUT [audit]"
      return 1
