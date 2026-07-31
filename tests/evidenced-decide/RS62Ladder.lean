import LeanCompCert.Trusted.EvidencedDecide
import LeanCompCert.Testing.RS62LadderCertificate

/-!
One segment of the RS62 anchor ladder, admitted as an execution.

Not a default build target: the tactic reads evidence produced out of band, and
a fresh checkout has none.  See `README.md` in this directory.
-/

open LeanCompCert.Testing.RS62LadderCertificate

/-- The lower-accumulator artifact ran and reported its certified value. -/
theorem rs62LadderSL_ran : programSL.denote = some expectedSL := by
  evidenced_decide "rs62-ladder-sl"

/-- The upper-accumulator artifact ran and reported its certified value. -/
theorem rs62LadderSU_ran : programSU.denote = some expectedSU := by
  evidenced_decide "rs62-ladder-su"

#print axioms rs62LadderSL_ran
#print axioms rs62LadderSU_ran
