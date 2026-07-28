import Mathlib
import LeanCompCert.Testing.VerifiedDecide

open LeanCompCert
open LeanCompCert.Verified

/--
The no-argument mode is a direct, axiom-free replacement for mathlib's closed
arithmetic linter fixture (outside the fixture itself, whose purpose is to
diagnose the literal `native_decide` syntax).
-/
example : 1 + 1 = 2 := by
  verified_decide

/--
An adapted `verified_decide` invocation typechecks in a mathlib environment
once the computation and its lowering certificate have been packaged.
-/
example :
    Testing.VerifiedDecide.computation.Returns 42 := by
  verified_decide using Testing.VerifiedDecide.decision
