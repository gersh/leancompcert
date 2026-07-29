import LeanCompCert.Verified.Rolled
import LeanCompCert.Testing.FixedPointCertificate

/-!
# M4 demonstration: rolled emission at 10⁷ iterations

The fixed-point program of `Testing.FixedPointCertificate`, scaled to ten
million iterations and emitted as a **rolled** loop: the C artifact is
kilobytes instead of the multi-gigabyte unrolled form. The native binary
checks the expected value independently (its exit status is not a
theorem); the proved theorems remain those of the unrolled semantics.
-/

namespace LeanCompCert.Testing.RolledFixedPoint

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Testing.FixedPointCertificate (body)

def bigCount : Nat := 10000000
def expectedBig : Nat := 177635701698593418

def program : Program := {
  regCount := 20
  loopCount := bigCount
  init := []
  body := body
  epilogue := []
  output := 0
}

theorem program_wf : program.WF := by decide

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_FixedPoint_rolled10M() == UINT64_C(177635701698593418) ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let source ← emitRolled program "FixedPoint.rolled10M"
  pure (source ++ mainC)

end LeanCompCert.Testing.RolledFixedPoint
