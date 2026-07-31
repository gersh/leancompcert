import LeanCompCert.Trusted.EvidencedDecide
import LeanCompCert.Testing.ArraySegCertificate

/-!
One admitted execution, end to end.  See `README.md` in this directory; this
file does not build in a fresh checkout, and is deliberately not a default
target.

The obligation is the offset segmented sieve certificate: eight windows of 4096
cells over `[1, 32768]`, whose artifact reports `4`.  The kernel cannot evaluate
`denote` on it — the register file is a chain of updates — which is exactly the
situation the bridge exists for.
-/

open LeanCompCert.Testing.ArraySegCertificate

/-- The artifact ran and reported `4`.  Resolution mode comes from
`leancompcert-evidence.cfg`; the proof term does not depend on which. -/
theorem mobiusSeg_ran : program.denote = some expected := by
  evidenced_decide "mobius-seg"

#print axioms mobiusSeg_ran
