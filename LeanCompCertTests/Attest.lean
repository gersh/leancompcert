import LeanCompCert.Attest
import LeanCompCert.Verified.Package
import LeanCompCert.Testing.RolledFixedPoint

/-!
# The receipt standard, exercised

What is tested here, and what deliberately is not.

**Tested in the kernel.**  The failure behaviour of `receiptBinds` on mutated
receipts — wrong value, replayed nonce, abnormal termination, disagreement,
regime confusion, route confusion, a substituted digest, a field edited after
signing, and an artifact that does not emit — and that the toy `ReceiptCrypto`
used below is *not* self-tested, so it cannot be mistaken for a deployment.

**Also tested in the kernel, and this is the part that used to be an axiom.**
That `Artifact.source?` evaluates at all, and that the receipt's `programHash`
is the digest of the emitted C — the *join*.  `decide +kernel` reduces the
emitter and both validators now; see `Artifact.source?` for the five kinds of
non-reducing definition that had to go.

**Not tested here, and why.**  The whole `receiptBinds … = true` in one goal.
It does close by `decide +kernel` — measured 54 s and 12.3 GB on this artifact
— but the cost is almost entirely the toy hash applied to `RunReceipt.payload`
(reducing `payload.length` alone is 28 s and 4.9 GB, because `payload` is built
by `String.intercalate` and Lean 4.32's `String` is UTF-8 bytes, so every
character read walks an append chain).  That is the receipt format's cost and
the crypto instance's, not the emitter's, and it does not grow with the size of
the computation.  Paying it on every build would buy no coverage the join test
below does not already give, so the shipped test stops at the join.

The mutation tests use the library's proved failure theorems rather than
`decide`.  They are stronger for it: they hold for every artifact, not for one.
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
  body := .straightLine computation
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

/-- A 128-hex-character stand-in for an `r ‖ s` signature.  The width matters:
`receiptBinds` requires `isP256Signature`, so a 64-character toy would make the
positive direction unreachable and the refusals would be passing for the wrong
reason. -/
def toySign (message : String) : String :=
  let h := toyHash message
  h ++ h

def toyCrypto : ReceiptCrypto := {
  digest := { name := "sha256", hashHex := toyHash }
  signature := {
    name := "ecdsa-p256-sha256"
    verify := fun _ message signature => signature == toySign message }
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
  -- The toy digest of the exact C this artifact emits, written out rather than
  -- computed, so that `binds_programHash` below is a real check on the emitted
  -- bytes: change the emitter and this test fails.
  programHash :=
    "8472955648989d3d8472955648989d3d8472955648989d3d8472955648989d3d"
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
  { unsigned with signature := toySign unsigned.payload }

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

/-! ### The positive direction, in the kernel

The two facts that used to need an axiom.  `bound` in
`returns_of_admitted_receipt` below is now something a consumer writes as
`by decide +kernel`; only `admitted` — the empirical premise — is still
discharged by a named axiom, and that one is the point of the whole design. -/

/-- **The emitter runs in the kernel.**  This is the exact reproducer the
ROADMAP recorded as *not* reducing. -/
theorem compiles_in_kernel :
    (Lower.compileProgram .portable
      { functions := #[computation.fn] }).toOption.isSome = true := by
  decide +kernel

/-- …and so does the whole of `Artifact.source?`, `main` included. -/
theorem source_in_kernel : artifact.source?.isSome = true := by
  decide +kernel

/-- **The join, checked by the kernel.**  The receipt's `programHash` is the
digest of the C text *this* artifact emits — not of some text lying around, and
not asserted by anybody. -/
theorem binds_programHash :
    (decide (receipt.programHash
      = toyCrypto.digest.hashHex (artifact.source?.getD ""))) = true := by
  decide +kernel

/-! ### Composition

`admitted` is the one premise that is not a theorem; see `RunAdmission`. -/
theorem returns_of_admitted_receipt
    (bound : receiptBinds toyCrypto artifact AttestationKind.localSignature ""
      nonce ((expected : Nat) : Int) receipt = true)
    (admitted : RunAdmission toyCrypto artifact receipt) :
    artifact.body.Returns ((expected : Nat) : Int) :=
  returns_of_receipt bound rfl admitted

/-! ## The rolled route, covered end to end

The 10⁷-iteration rolled fixed-point certificate — the artifact that exists
because its unrolled form is multi-gigabyte C — accepted by
`receiptBindsProved`, whose extra clause is now a real coverage condition
rather than a route tag.  What comes out is a statement about the
counter-augmented program's ordinary Lean denotation. -/

namespace Rolled

open LeanCompCert.Testing.RolledFixedPoint

/-- The rolled artifact.  Note that no `Computation` is supplied: the rolled
form carries the program, and everything else is derived. -/
def artifact : Artifact := {
  body := .rolled program "FixedPoint.rolled10M"
  mainC := LeanCompCert.Testing.RolledFixedPoint.mainC
}

/-! This is the *same* C the `rolled-10m` certificate emits and `check-native`
compiles: `emitFor_rolled` says `emitFor (.rolled p e) m` is
`emitRolled p e >>= (· ++ m)`, which is `RolledFixedPoint.emittedC` written
out.  It is not asserted as a theorem here because identifying the two closed
terms sends the *elaborator* (not the kernel) into evaluating the emitted
string; `scripts/test-compcert.sh` checks the same identity on the bytes. -/

/-- **The coverage condition, decided.**  Program well-formedness and a trip
count below `2⁶⁴`; both program-sized, neither growing with the 10⁷
iterations. -/
theorem rolled_covered : artifact.coveredByProvedChain = true := by decide

/-- **The strict check imposes nothing extra on this artifact.**  On a rolled
artifact `receiptBindsProved` used to be identically `false`; here it reduces
to `receiptBinds`, so anything the plain check accepts the strict one accepts
too. -/
theorem rolled_proved_is_binds (crypto : ReceiptCrypto)
    (kind : AttestationKind) (params nonce : String) (value : Int)
    (receipt : RunReceipt) :
    receiptBindsProved crypto artifact kind params nonce value receipt =
      receiptBinds crypto artifact kind params nonce value receipt := by
  simp only [receiptBindsProved, rolled_covered, Bool.true_and]

/-- **The rolled route is inside the proved C model.**  The model of the
emitted `while`-loop function returns the counter-augmented program's
denotation. -/
theorem rolled_model_preserved :
    artifact.body.modelResult = artifact.body.sourceResult :=
  artifact.body.modelResult_eq_sourceResult rolled_covered

/-- **The emitter runs in the kernel for the rolled route too**, so the join
clause of `receiptBinds` is a `decide +kernel` here exactly as it is for the
straight-line artifact. -/
theorem rolled_source_in_kernel : artifact.source?.isSome = true := by
  decide +kernel

/-- **The acceptance.**  `receiptBindsProved` — the strict form, demanding
coverage by the proved chain — applied to a rolled artifact, giving a fact
about the program's Lean-level denotation.  Before this change the strict form
refused every rolled artifact by construction. -/
theorem denote_of_admitted_rolled_receipt
    (crypto : ReceiptCrypto) (receipt : RunReceipt) (nonce : String)
    (bound : receiptBindsProved crypto artifact AttestationKind.localSignature
      "" nonce ((expectedBig : Nat) : Int) receipt = true)
    (admitted : RunAdmission crypto artifact receipt) :
    (program.counterAugment).denote = some expectedBig :=
  (ArtifactBody.rolled_Returns_iff_denote program "FixedPoint.rolled10M"
    expectedBig).mp (returns_of_receipt_proved bound admitted)

end Rolled

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
