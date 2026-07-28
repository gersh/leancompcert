import Mathlib.Algebra.Polynomial.Basic
import LeanCompCert.Verified.Decide

open Polynomial
open LeanCompCert.Verified

def p0 : ℕ[X] :=
  ⟨⟨{}, Pi.single 0 0,
    by intro; simp [Pi.single, Function.update_apply]⟩⟩

/--
Expected not to elaborate: `reprStr` reaches `Std.Format.prettyM`, whose
renderer is a private opaque `partial def`.  This fixture ensures the
kernel-only tactic never silently falls back to native evaluation.
-/
example : reprStr p0 = "0" := by
  verified_decide
