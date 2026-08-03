import LeanCompCert.Attest.Crypto
import LeanCompCert.Attest.Receipt
import LeanCompCert.Attest.Admission
import LeanCompCert.Attest.Tool
import LeanCompCert.Attest.Ledger

/-!
# `LeanCompCert.Attest` — the run-receipt standard

The axiom-free half of the attested-run story.  Importing this adds **nothing**
to anybody's `#print axioms`: it defines what a receipt is (`RunReceipt`), what
it means for one to bind to a computation (`receiptBinds`), proves what a
passing check forces (`receiptBinds_sound` and the failure theorems), names the
single empirical premise (`RunAdmission`), and composes the two into
`returns_of_receipt`.

Discharging `RunAdmission` is a separate, opt-in step with its own named axiom:

* `LeanCompCert.Trusted.LocalReceipt` — a key generated on, and resident on,
  the machine that ran the binary.  Tamper-evident bookkeeping for a
  trusted-machine setting.  **Not** equivalent to hardware attestation.
* `gpu_prover` — a hardware-attested enclave, rooted in a pinned CA.

The two are distinguishable mechanically: they require different
`AttestationKind`s, they are different axioms with different names, and a
`#print axioms` on a downstream theorem says which was used.

The guide is `docs/use-case-3-attested-run-receipts.md`.

## The ledger

`LeanCompCert/Attest/Ledger.lean` adds the *bookkeeping* half: a registry of
compiled programs, what is in each, and which have actually been run.  It is
also axiom-free, and it keeps three facts visibly apart — **compiled**, **run**,
and **chain proved** — so that a green run can never be read as a green proof.
See `docs/program-ledger.md`.
-/

namespace LeanCompCert.Attest

/-- Version of the receipt format this build reads and writes. -/
def receiptFormat : String := schemaVersion

end LeanCompCert.Attest
