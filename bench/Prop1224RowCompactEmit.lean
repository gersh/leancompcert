import LeanCompCert.Ports.Prop1224RowCompact
import LeanCompCert.Verified.ArrayAudit

/-!
Emit one of the three compact nonempty-row campaigns:

    lake env lean --run bench/Prop1224RowCompactEmit.lean \
      small|large|extension OUT [audit]
-/

open LeanCompCert
open LeanCompCert.Ports.Prop1224Row
open LeanCompCert.Ports.Prop1224RowCompact

namespace Bench.Prop1224RowCompactEmit

structure Campaign where
  label : String
  cfg : RowCfg
  rows : Nat
  capacity : Nat
  extension : Bool

def campaign? : String → Option Campaign
  | "small" => some {
      label := "small"
      cfg := RowCfg.ofChain 1 65536 2 3_300_000_000 4
      rows := 131_071
      capacity := 131_071
      extension := false }
  | "large" => some {
      label := "large"
      cfg := RowCfg.ofChain 131_072 65536 50353 3_300_000_000 4
      rows := 3_299_868_928
      capacity := 1_500_000
      extension := false }
  | "extension" => some {
      label := "extension"
      cfg := RowCfg.ofChain
        LeanCompCert.Ports.Prop1224RowExtension.firstM 65536 1359
        LeanCompCert.Ports.Prop1224RowExtension.lastM 4
      rows := LeanCompCert.Ports.Prop1224RowExtension.extensionRows
      capacity := 1_500_000
      extension := true }
  | _ => none

def positiveDriver (name : String) (cells resultBase compactResult rows : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) { uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"violations %llu rows %llu compact_rows %llu\\n\",\n" ++
  "    (unsigned long long)r,\n" ++
  "    (unsigned long long)cells[" ++ toString (resultBase + 1) ++ "],\n" ++
  "    (unsigned long long)cells[" ++ toString compactResult ++ "]);\n" ++
  "  return (r == UINT64_C(0) && cells[" ++ toString (resultBase + 1) ++
    "] == UINT64_C(" ++ toString rows ++ ")) ? 0 : 1; }\n"

def auditDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void) { uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "  printf(\"audit %llu\\n\", (unsigned long long)r);\n" ++
  "  return r == UINT64_C(0) ? 0 : 1; }\n"

end Bench.Prop1224RowCompactEmit

open Bench.Prop1224RowCompactEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: out :: rest =>
      let some campaign := campaign? mode |
        IO.eprintln "mode must be small, large, or extension"
        return 1
      let p := if campaign.extension then
        extensionCompactPrefixProgram campaign.cfg campaign.rows campaign.capacity
      else denseCompactPrefixProgram campaign.cfg campaign.rows campaign.capacity
      let auditMode := rest.head? = some "audit"
      let emitted := if auditMode then
        LeanCompCert.Verified.ArrayAudit.auditProgram p else p
      let name := s!"p1224compact{campaign.label}{if auditMode then "audit" else ""}"
      match emitted.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          let host := if auditMode then auditDriver name emitted.arrayLen
            else positiveDriver name p.arrayLen campaign.cfg.resultBase
              (compactResult campaign.cfg campaign.capacity) campaign.rows
          IO.FS.writeFile out (source ++ host)
          IO.println s!"campaign={campaign.label} rows={campaign.rows} capacity={campaign.capacity}"
          IO.println s!"loopCount={p.loopCount} arrayLen={p.arrayLen} body={p.body.length}"
          return 0
  | _ =>
      IO.eprintln "usage: small|large|extension OUT [audit]"
      return 1
