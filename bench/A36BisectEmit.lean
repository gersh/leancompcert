import LeanCompCert.Ports.A36BisectProgram

/-!
Emit the A.36 low-branch leaf sweep as rolled C.

    lake env lean --run bench/A36BisectEmit.lean DEPTH OUT

The program returns `0` exactly when every one of the `2^DEPTH` cells of
`[1, 6.2]` passes its three root checks and its residual comparison.  Emission
is rolled, so the C size does not depend on `DEPTH` — only the loop bound in
the emitted `while` does.

`DEPTH = 8` is the certificate: it is the depth
`MathExtras/Analysis/HelfgottThm31/C1Bound/A36Bisection.lean` uses, and
`LeanCompCert.Ports.A36Bisect.sweep_ok` proves the same sweep passes in Lean's
kernel.  Larger depths are cost measurements; they are also *stronger*
statements (a finer grid gives a tighter enclosure), but no Lean theorem is
attached to them until the body/`leafOK` simulation is proved.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.A36BisectProgram

namespace Bench.A36BisectEmit

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++
    "() == UINT64_C(0) ? 0 : 1;\n}\n"

end Bench.A36BisectEmit

open Bench.A36BisectEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [depthStr, out] =>
      let some d := depthStr.toNat? | do IO.eprintln "bad DEPTH"; return 1
      let p := programAt d
      let name := s!"A36Bisect{d}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"depth = {d}, leaves = {p.loopCount}, \
body = {p.body.length} instructions"
          return 0
  | _ => do
      IO.eprintln "usage: DEPTH OUT"
      return 1
