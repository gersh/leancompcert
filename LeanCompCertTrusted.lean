import LeanCompCert.Trusted.Evidence
import LeanCompCert.Trusted.ArtifactRun
import LeanCompCert.Trusted.Resolve
import LeanCompCert.Trusted.EvidencedDecide
import LeanCompCert.Trusted.Demo

/-!
# `LeanCompCertTrusted` — the opt-in artifact-run bridge

Nothing in the `LeanCompCert` library imports anything under
`LeanCompCert/Trusted/`, and nothing under `LeanCompCert/Trusted/` is reachable
from `import LeanCompCert`.  **Depending on this package still adds nothing to
your axiom list.**  You get the axiom only by importing
`LeanCompCert.Trusted.ArtifactRun` (or this root) yourself, which is the point:
admitting an execution should be visible and deliberate.

This root exists so `lake build` compiles and audits the opt-in modules
alongside everything else.  See `docs/incorporating-a-computation.md`.
-/

namespace LeanCompCert.Trusted

/-- Version of the evidence record format this build reads and writes. -/
def evidenceFormat : String := "lean-compcert-evidence/1"

end LeanCompCert.Trusted
