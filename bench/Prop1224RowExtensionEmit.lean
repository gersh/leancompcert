import LeanCompCert.Ports.Prop1224RowExtension
import LeanCompCert.Verified.ArrayAudit

/-!
Emit the sparse `q = 210*m` Proposition 12.2.4 row producer.

    lake env lean --run bench/Prop1224RowExtensionEmit.lean \
      SEGLEN SEGCOUNT UNROLL OUT [audit]
-/

open LeanCompCert
open LeanCompCert.Ports.Prop1224Row
open LeanCompCert.Ports.Prop1224RowExtension

namespace Bench.Prop1224RowExtensionEmit

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? |
    throw <| IO.userError s!"bad {label}: {value}"
  return n

def positiveDriver (name : String) (cells rowBase segLen resultBase mLo
    expectedRows printRows : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) {\n" ++
  "  uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  uint64_t rows = cells[" ++ toString (resultBase + 1) ++ "];\n" ++
  "  for (uint64_t i = 0; i < UINT64_C(" ++ toString printRows ++ "); ++i) {\n" ++
  "    printf(\"%llu\", (unsigned long long)(UINT64_C(210) * (UINT64_C(" ++
    toString mLo ++ ") + i)));\n" ++
  "    for (int j = 0; j < 10; ++j)\n" ++
  "      printf(\" %llu\", (unsigned long long)cells[" ++ toString rowBase ++
    " + (uint64_t)j*UINT64_C(" ++ toString segLen ++ ") + i]);\n" ++
  "    printf(\"\\n\");\n" ++
  "  }\n" ++
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

end Bench.Prop1224RowExtensionEmit

open Bench.Prop1224RowExtensionEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | lenS :: countS :: unrollS :: out :: rest => try
      let len ← parseNat "segLen" lenS
      let count ← parseNat "segCount" countS
      let unroll ← parseNat "unroll" unrollS
      let rows ← match rest.head? with
        | some value => match value.toNat? with
          | some n => pure n
          | none => pure extensionRows
        | none => pure extensionRows
      let auditMode := rest.any (fun value => value = "audit")
      if len = 0 || rows = 0 || extensionRows < rows || len * count < rows then
        IO.eprintln "require 0 < ROWCOUNT <= extensionRows and ROWCOUNT <= SEGLEN*SEGCOUNT"
        return 1
      if unroll = 0 || 24 % unroll != 0 then
        IO.eprintln "UNROLL must be a positive divisor of 24"
        return 1
      let c := RowCfg.ofChain firstM len count lastM unroll
      let sourceProgram := extensionPrefixProgram c rows
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram sourceProgram
      else sourceProgram
      let name := s!"p1224rowextension{rows}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name sourceProgram.arrayLen c.rowBase c.segLen
              c.resultBase firstM rows (if count = 1 then rows else 0)
          IO.FS.writeFile out (source ++ host)
          IO.println s!"mLo={firstM} rows={rows} paddedMHi={c.hi} name={name}"
          IO.println s!"segLen={len} segCount={count} markSteps={c.markSteps}"
          IO.println s!"body={sourceProgram.body.length} loopCount={sourceProgram.loopCount} arrayLen={sourceProgram.arrayLen}"
          return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
      IO.eprintln "usage: SEGLEN SEGCOUNT UNROLL OUT [ROWCOUNT] [audit]"
      return 1
