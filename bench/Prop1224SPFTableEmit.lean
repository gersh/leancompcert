import LeanCompCert.Ports.Prop1224SPFTable
import LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Ports.Prop1224SPFTable

namespace Bench.Prop1224SPFTableEmit

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? |
    throw <| IO.userError s!"bad {label}: {value}"
  return n

def cfg (rows len : Nat) : Cfg :=
  let pre := Cfg.production rows len 0 0
  let dest := pre.tableBase + pre.tableLen + 2
  { pre with destBase := dest, arrayLen := dest + pre.hi + 2 }

def positiveDriver (name : String) (c : Cfg) (rows : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void) { uint64_t v = l_" ++ name ++ "(cells);\n" ++
  "  for (uint64_t n = 1; n <= UINT64_C(" ++ toString (min rows 256) ++ "); ++n)\n" ++
  "    printf(\"%llu %llu\\n\", (unsigned long long)n,\n" ++
  "      (unsigned long long)cells[" ++ toString c.destBase ++ " + n]);\n" ++
  "  printf(\"violations %llu stored %llu\\n\", (unsigned long long)v,\n" ++
  "    (unsigned long long)cells[" ++ toString c.resultCell ++ "]);\n" ++
  "  return v == UINT64_C(0) ? 0 : 1; }\n"

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) { uint64_t v = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"audit %llu\\n\", (unsigned long long)v);\n" ++
  "  return v == UINT64_C(0) ? 0 : 1; }\n"

end Bench.Prop1224SPFTableEmit

open Bench.Prop1224SPFTableEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | rowsS :: lenS :: out :: rest => try
      let rows ← parseNat "rows" rowsS
      let len ← parseNat "segLen" lenS
      if rows = 0 || len = 0 then
        IO.eprintln "ROWS and SEGLEN must be positive"
        return 1
      let c := cfg rows len
      let p := program c rows
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram p else p
      let name := s!"p1224spf{rows}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name c rows
          IO.FS.writeFile out (source ++ host)
          IO.println s!"rows={rows} segLen={len} segCount={c.segCount} paddedHi={c.hi}"
          IO.println s!"tableLen={c.tableLen} markSteps={c.markSteps} loopCount={p.loopCount} arrayLen={p.arrayLen}"
          return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
      IO.eprintln "usage: ROWS SEGLEN OUT [audit]"
      return 1
