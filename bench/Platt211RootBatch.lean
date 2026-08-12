import LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

/-!
Batch emitter for the root-only Platt (2.11) count and fail-safe audit
receipts.  Each emitted driver compares the compiled return word against the
literal expected by the formal manifest and exits nonzero on disagreement.
-/

namespace Bench.Platt211RootBatch

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

def driver (name : String) (cells expected : Nat) (label : String) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"" ++ label ++ " %llu\\n\", (unsigned long long)r);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n" ++
  "}\n"

def emitOne (idx : Nat) (mode out : String) : IO Bool := do
  let some row := rows[idx]? | do
    IO.eprintln s!"row index out of range: {idx}"
    return false
  if row.idx != idx then
    IO.eprintln s!"manifest index mismatch at {idx}: {row.idx}"
    return false
  let source := rootOnlyProgram row
  let audited := mode == "audit"
  if mode != "root" && !audited then
    IO.eprintln s!"bad mode at {idx}: {mode}"
    return false
  let p := if audited then auditProgram source else source
  let name := s!"Platt211Root{if audited then "Audit" else "Count"}{idx}"
  let expected := if audited then 0 else (rootOnlyCfg row).primeBase + row.mainCount
  match p.emitRolled name with
  | .error errs =>
      for e in errs do IO.eprintln e
      return false
  | .ok src =>
      IO.FS.writeFile out (src ++ driver name p.arrayLen expected
        (if audited then "audit" else "write_cursor"))
      IO.println s!"job {idx} mode={mode} rootCap={row.rootCap} segLen={row.segLen} rootCount={row.rootCount} loopCount={p.loopCount} expected={expected}"
      return true

end Bench.Platt211RootBatch

open Bench.Platt211RootBatch in
def main (args : List String) : IO UInt32 := do
  match args with
  | [jobs] =>
      let input ← IO.FS.readFile jobs
      let mut ok := true
      for line in input.splitOn "\n" do
        let fields := (line.splitOn " ").filter (· ≠ "")
        match fields with
        | [] => pure ()
        | [idxS, mode, out] =>
            let some idx := idxS.toNat? | do
              IO.eprintln s!"bad index: {idxS}"
              ok := false
              continue
            unless ← emitOne idx mode out do ok := false
        | _ =>
            IO.eprintln s!"bad job line: {line}"
            ok := false
      return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: Platt211RootBatch JOBS"
      return 2
