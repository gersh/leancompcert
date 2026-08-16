import LeanCompCert.Ports.Prop1224Row
import LeanCompCert.Verified.ArrayAudit

/-!
Emit an exact-row-count prefix of padded Proposition 12.2.4 row windows.

    lake env lean --run bench/Prop1224RowPrefixEmit.lean \
      LO SEGLEN SEGCOUNT TABLEHI UNROLL ROWCOUNT OUT [audit]

`SEGCOUNT` allocates and schedules enough padded windows; `ROWCOUNT` stops
the final window at the exact paper boundary.
-/

open LeanCompCert
open LeanCompCert.Ports.Prop1224Row

namespace Bench.Prop1224RowPrefixEmit

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? |
    throw <| IO.userError s!"bad {label}: {value}"
  return n

def positiveDriver (name : String) (cells resultBase expectedRows : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) {\n" ++
  "  uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  uint64_t rows = cells[" ++ toString (resultBase + 1) ++ "];\n" ++
  "  printf(\"violations %llu rows %llu expected_rows %llu\\n\",\n" ++
  "    (unsigned long long)r, (unsigned long long)rows,\n" ++
  "    (unsigned long long)UINT64_C(" ++ toString expectedRows ++ "));\n" ++
  "  printf(\"result\");\n" ++
  "  for (int i = 0; i < 20; ++i)\n" ++
  "    printf(\" %llu\", (unsigned long long)cells[" ++
    toString resultBase ++ " + (uint64_t)i]);\n" ++
  "  printf(\"\\n\");\n" ++
  "  return (r == UINT64_C(0) && rows == UINT64_C(" ++
    toString expectedRows ++ ")) ? 0 : 1;\n" ++
  "}\n"

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) {\n" ++
  "  uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"audit %llu\\n\", (unsigned long long)r);\n" ++
  "  return r == UINT64_C(0) ? 0 : 1;\n" ++
  "}\n"

end Bench.Prop1224RowPrefixEmit

open Bench.Prop1224RowPrefixEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | loS :: lenS :: cntS :: hiS :: unrollS :: rowsS :: out :: rest => try
      let lo ← parseNat "lo" loS
      let len ← parseNat "segLen" lenS
      let count ← parseNat "segCount" cntS
      let tableHi ← parseNat "tableHi" hiS
      let unroll ← parseNat "unroll" unrollS
      let rows ← parseNat "rowCount" rowsS
      if len = 0 || rows = 0 || len * count < rows then
        IO.eprintln "require 0 < ROWCOUNT <= SEGLEN*SEGCOUNT"
        return 1
      if unroll = 0 || 24 % unroll != 0 then
        IO.eprintln "UNROLL must be a positive divisor of 24"
        return 1
      let c := RowCfg.ofChain lo len count tableHi unroll
      let sourceProgram := rowPrefixProgram c rows
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram sourceProgram
      else sourceProgram
      let name := s!"p1224rowprefix{lo}n{rows}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name sourceProgram.arrayLen c.resultBase rows
          IO.FS.writeFile out (source ++ host)
          IO.println s!"lo={lo} rows={rows} paddedHi={c.hi} name={name}"
          IO.println s!"segLen={len} segCount={count} markSteps={c.markSteps}"
          IO.println s!"body={sourceProgram.body.length} loopCount={sourceProgram.loopCount} arrayLen={sourceProgram.arrayLen}"
          return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
      IO.eprintln "usage: LO SEGLEN SEGCOUNT TABLEHI UNROLL ROWCOUNT OUT [audit]"
      return 1
