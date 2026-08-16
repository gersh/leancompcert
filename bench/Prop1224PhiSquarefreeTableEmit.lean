import LeanCompCert.Ports.Prop1224PhiSquarefreeTable
import LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Ports.Prop1224Cell
open LeanCompCert.Ports.Prop1224PhiSquarefreeTable

namespace Bench.Prop1224PhiSquarefreeTableEmit

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? |
    throw <| IO.userError s!"bad {label}: {value}"
  return n

def positiveDriver (name : String) (cells pbase sbase result rows : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) {\n" ++
  "  uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  for (uint64_t n = 1; n <= UINT64_C(" ++ toString (min rows 256) ++ "); ++n)\n" ++
  "    printf(\"%llu %llu %llu\\n\", (unsigned long long)n,\n" ++
  "      (unsigned long long)cells[" ++ toString pbase ++ " + n],\n" ++
  "      (unsigned long long)cells[" ++ toString sbase ++ " + n]);\n" ++
  "  printf(\"violations %llu stored %llu\\n\", (unsigned long long)r,\n" ++
  "    (unsigned long long)cells[" ++ toString result ++ "]);\n" ++
  "  return r == UINT64_C(0) ? 0 : 1;\n" ++
  "}\n"

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) { uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"audit %llu\\n\", (unsigned long long)r);\n" ++
  "  return r == UINT64_C(0) ? 0 : 1; }\n"

end Bench.Prop1224PhiSquarefreeTableEmit

open Bench.Prop1224PhiSquarefreeTableEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | rowsS :: lenS :: out :: rest => try
      let rows ← parseNat "rows" rowsS
      let len ← parseNat "segLen" lenS
      if rows = 0 || len = 0 then
        IO.eprintln "ROWS and SEGLEN must be positive"
        return 1
      let count := (rows + len - 1) / len
      let c := CellCfg.ofRow 1 0 0 0 0 0 [] 1 len count
      let sourceProgram := tableProgram c rows
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram sourceProgram
      else sourceProgram
      let name := s!"p1224phitable{rows}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name sourceProgram.arrayLen (phiBase c)
              (squarefreeBase c rows) (outputResult c rows) rows
          IO.FS.writeFile out (source ++ host)
          IO.println s!"rows={rows} segLen={len} segCount={count} paddedHi={c.hi}"
          IO.println s!"markSteps={c.markSteps} loopCount={sourceProgram.loopCount} arrayLen={sourceProgram.arrayLen}"
          return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
      IO.eprintln "usage: ROWS SEGLEN OUT [audit]"
      return 1
