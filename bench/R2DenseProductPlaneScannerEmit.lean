/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCompCert.Ports.R2DenseProductPlaneScanner

/-!
Emit a positive or fail-safe-audit rolled product-plane shard scanner.

The emitted function accepts caller-owned memory, so it can be invoked on the
exact final array of the dense producer without serializing or regenerating
that array.

```
lake env lean --run bench/R2DenseProductPlaneScannerEmit.lean \
  positive|audit ARRAYLEN SEGLEN WINDOWBASE ILO IHI OUT.c
```
-/

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.R2DenseProductPlaneScanner

def main (args : List String) : IO UInt32 := do
  let (mode, arrayLen, segLen, windowBase, iLo, iHi, outPath) :=
    match args with
    | [mode, arrayLen, segLen, windowBase, iLo, iHi, outPath] =>
        (mode, arrayLen.toNat!, segLen.toNat!, windowBase.toNat!,
          iLo.toNat!, iHi.toNat!, outPath)
    | _ => ("", 0, 0, 0, 0, 0, "")
  if mode != "positive" && mode != "audit" then
    IO.eprintln "usage: positive|audit ARRAYLEN SEGLEN WINDOWBASE ILO IHI OUT.c"
    return 1
  if arrayLen = 0 || segLen > arrayLen || iLo > iHi || iHi > segLen then
    IO.eprintln "require 0 < ARRAYLEN, ILO <= IHI <= SEGLEN <= ARRAYLEN"
    return 2
  let c : Cfg := { arrayLen, segLen, windowBase, iLo, iHi }
  let p := if mode = "audit" then auditProgram (program c) else program c
  let name := if mode = "audit" then "r2dense_product_audit"
    else "r2dense_product"
  match p.emitRolled name with
  | .error errors =>
      for error in errors do IO.eprintln error
      return 3
  | .ok source =>
      IO.FS.writeFile outPath source
      IO.println s!"mode={mode} arrayLen={arrayLen} iLo={iLo} iHi={iHi} loopCount={p.loopCount}"
      return 0
