import LeanCompCert.Attest
import LeanCompCert.Verified.Package

/-!
# The receipt standard, exercised

What is tested here, and what deliberately is not.

**Tested in the kernel.**  The failure behaviour of `receiptBinds` on mutated
receipts — wrong value, replayed nonce, abnormal termination, disagreement,
regime confusion, route confusion, a substituted digest, a field edited after
signing, and an artifact that does not emit — and that the toy `ReceiptCrypto`
used below is *not* self-tested, so it cannot be mistaken for a deployment.

**Not tested here, because the kernel cannot do it.**  `receiptBinds … = true`
on a real artifact.  Evaluating it requires evaluating `Artifact.source?`, and
the C emitter is `partial` — see the warning on `Artifact.source?`.  The
positive direction therefore appears below as a *hypothesis*, which is exactly
the shape a consumer is in today: they discharge it with one named axiom per
artifact and check it out of band with `lean-compcert verify-receipt`.

The mutation tests use the library's proved failure theorems rather than
`decide`, for the same reason — and they are stronger for it: they hold for
every artifact, not for one.
-/

namespace LeanCompCertTests.Attest

open LeanCompCert
open LeanCompCert.Attest
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

set_option maxRecDepth 10000

/-! ## A small artifact -/

/-- `Σ_{k < 8} (k+1)² = 204`. -/
def program : Program := {
  regCount := 3
  loopCount := 8
  init := []
  body := [
    .binop 1 .add .idx (.lit 1),
    .binop 2 .mul (.reg 1) (.reg 1),
    .binop 0 .add (.reg 0) (.reg 2)
  ]
  epilogue := []
  output := 0
}

theorem program_wf : program.WF := by decide

def expected : Nat := 204

def computation : Computation :=
  program.toComputation "Attest.squareSum" program_wf

/-- The kernel's half of the chain, unchanged by any of this. -/
theorem returns_expected : computation.Returns ((expected : Nat) : Int) :=
  (toComputation_returns program "Attest.squareSum" program_wf expected).mpr
    (by decide +kernel)

/-- The self-checking `main`, built from `expected` rather than a literal —
the discipline `Attest.selfCheckMain` exists to enforce. -/
def mainC : String := selfCheckMain "l_Attest_squareSum" expected

/-- Pure data: no proof obligation, and the C text is not something the author
supplies.  See `Artifact`. -/
def artifact : Artifact := {
  computation
  route := EmissionRoute.provedStraightLine
  mainC
}

/-! ## A toy `ReceiptCrypto`

⚠ Not cryptography.  It exercises the shape of the interface and nothing
else. -/

private def hexChar (n : Nat) : Char :=
  "0123456789abcdef".toList.getD (n % 16) '0'

/-- A rolling hash rendered as 64 hex characters.  Deterministic, cheap, and
not collision-resistant in any sense. -/
def toyHash (text : String) : String :=
  let h := text.toList.foldl (fun acc c => (acc * 131 + c.toNat) % (2 ^ 64)) 7
  String.ofList ((List.range 64).map fun i => hexChar (h >>> (i % 16 * 4) + i))

def toyCrypto : ReceiptCrypto := {
  digest := { name := "sha256", hashHex := toyHash }
  signature := {
    name := "ecdsa-p256-sha256"
    verify := fun _ message signature => signature == toyHash message }
}

/-- **The toy crypto is not self-tested**, so no discharger would accept it:
`Trusted.localSignedRun_admits` takes `ReceiptCrypto.SelfTested` as a premise.
This is the mechanical version of "do not ship the test double". -/
theorem toyCrypto_not_selfTested : ¬ ReceiptCrypto.SelfTested toyCrypto := by
  intro h
  exact absurd h.digestAbc (by decide)

/-! ## A receipt, and what refuses it -/

def nonce : String :=
  "0000000000000000000000000000000000000000000000000000000000000001"

def toolchain : ToolchainId := {
  ccompVersion := "The CompCert C verified compiler, version 3.17"
  binaryDigest :=
    "0000000000000000000000000000000000000000000000000000000000000002"
  linkDescription := "freestanding test"
}

def unsigned : RunReceipt := {
  schema := schemaVersion
  attestation := AttestationKind.localSignature
  routeLabel := EmissionRoute.provedStraightLine.label
  campaign := "leancompcert-tests"
  digestName := "sha256"
  programHash :=
    "1111111111111111111111111111111111111111111111111111111111111111"
  paramsHash := toyHash ""
  toolchain
  value := ((expected : Nat) : Int)
  verdict := RunVerdict.agrees
  machine := "machine test-harness"
  nonce
  recordedAt := "2026-08-01T00:00:00Z"
  publicKey := "04" ++ String.ofList (List.replicate 128 '0')
  signature := ""
}

def receipt : RunReceipt :=
  { unsigned with signature := toyHash unsigned.payload }

/-! ### The mutations

Each names one field, changes it, and the check refuses.  These hold for
*every* artifact and every crypto, which is stronger than exhibiting them on
one instance. -/

theorem wrong_value_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce 205 receipt = false :=
  receiptBinds_false_of_value_ne (by decide)

theorem replayed_nonce_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      (String.ofList (List.replicate 64 'a')) ((expected : Nat) : Int) receipt
      = false :=
  receiptBinds_false_of_nonce_ne (by decide)

theorem abnormal_termination_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int)
      { receipt with verdict := RunVerdict.abnormal } = false :=
  receiptBinds_false_of_verdict_ne (by decide)

theorem disagreement_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int)
      { receipt with verdict := RunVerdict.disagrees } = false :=
  receiptBinds_false_of_verdict_ne (by decide)

/-- An enclave-grade claim cannot be met by a locally signed receipt. -/
theorem local_receipt_refused_for_enclave :
    receiptBinds toyCrypto artifact AttestationKind.enclaveQuote ""
      nonce ((expected : Nat) : Int) receipt = false :=
  receiptBinds_false_of_kind_ne (by decide)

/-- A receipt filed under the rolled route does not bind to a straight-line
artifact. -/
theorem wrong_route_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int)
      { receipt with routeLabel := "rolled-loop" } = false :=
  receiptBinds_false_of_route_ne (by decide)

/-- A receipt naming another hash function does not bind. -/
theorem wrong_digest_name_refused :
    receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int)
      { receipt with digestName := "blake3" } = false :=
  receiptBinds_false_of_digestName_ne (by decide)

/-! **Tampering** is covered by the library theorem
`receiptBinds_false_of_badSignature`, which holds for every receipt, and end to
end by `scripts/test-compcert.sh`, which edits one field of a real signed
receipt and requires `verify-receipt` to reject it.  Exhibiting it here would
mean evaluating the toy hash over the whole payload inside `isDefEq`, which was
measured at tens of gigabytes for no additional coverage. -/

/-- **An artifact that does not emit cannot be attested.** -/
theorem no_emission_refused (a : Artifact) (h : a.source? = none) :
    receiptBinds toyCrypto a AttestationKind.localSignature "" nonce
      ((expected : Nat) : Int) receipt = false :=
  receiptBinds_false_of_noEmission h

/-! ### The positive direction, as a hypothesis

This is the shape a consumer writes today: `bound` is discharged by one named
axiom per artifact and checked out of band by `lean-compcert verify-receipt`;
`admitted` is discharged by `Trusted.localSignedRun_admits` or by
`gpu_prover`'s enclave axiom.  Both premises are visible in `#print axioms`
downstream; this theorem itself carries none. -/
theorem returns_of_admitted_receipt
    (bound : receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int) receipt = true)
    (admitted : RunAdmission toyCrypto artifact receipt) :
    artifact.computation.Returns ((expected : Nat) : Int) :=
  returns_of_receipt bound admitted

/-! ## The tool's byte surgery

Round-tripping DER ↔ SEC1, DER ↔ `r ‖ s` and the receipt file is checked at
**run time**, in `LeanCompCertTests.testAttestTool`, not by `decide` here.
That is a deliberate placement: `ByteArray.foldl` and the string builders these
go through are not cheap for the kernel's evaluator (a `decide` over the
64-byte signature round trip was measured at tens of gigabytes), and nothing
about a receipt's *soundness* rests on them — a tool that mis-encodes produces
a signature the verifier rejects, so the failure is loud and is caught by
`receiptBinds`.
-/

end LeanCompCertTests.Attest
