import LeanCompCert.Ports.CDEMAbelProductionAuditCertificate

/-!
Emission driver for the fail-safe audit of the exact production CDEM Abel
program.

```
lake env lean --run bench/CDEMAbelAuditEmit.lean OUT
```

The emitted program is `auditComputation productionComputation` itself.  Its
driver exits zero exactly when no source division-by-zero or out-of-bounds
array access was encountered during the complete production scan.
-/

open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelProductionCertificate

private def exitDriver (name : String) (cells : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(0) ? 0 : 1;\n" ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  let emit (program : LeanCompCert.Verified.ArrayState.AProgram)
      (out : String) : IO UInt32 := do
      let audited := auditProgram program
      let name := "CDEMAbel.audit"
      let symbol := "CDEMAbel_audit"
      IO.println s!"LOOP={audited.loopCount}"
      IO.println s!"CELLS={audited.arrayLen}"
      IO.println s!"BODY={audited.body.length}"
      match audited.emitRolled name with
      | .error errors =>
          for error in errors do IO.eprintln error
          return 1
      | .ok source =>
          IO.FS.writeFile out
            (source ++ exitDriver symbol audited.arrayLen)
          IO.println s!"wrote {out}"
          return 0
  match args with
  | [out] => emit productionComputation.program out
  | [w, k, segLen, segCount, out] =>
      let W := w.toNat!
      let K := k.toNat!
      let L := segLen.toNat!
      let C := segCount.toNat!
      if W == 0 || K == 0 || L == 0 || C == 0 then
        IO.eprintln "require W, K, SEGLEN, SEGCOUNT >= 1"
        return 2
      emit (abelProgram (Cfg.ofRange W K L C)) out
  | _ =>
      IO.eprintln
        "usage: CDEMAbelAuditEmit OUT | W K SEGLEN SEGCOUNT OUT"
      return 2
