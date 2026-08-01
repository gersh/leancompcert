/-!
# The crypto interface the receipt standard is stated over

This module contains **no cryptography**.  It declares the two operations a
receipt check needs — a 256-bit digest and a signature verifier — as ordinary
Lean data, and it states the known-answer tests a supplied implementation must
satisfy.  Implementations are supplied by the consumer.

## Why an interface rather than an implementation

`leancompcert` has **zero package dependencies** and a standing commitment not
to acquire Mathlib.  The audited, `native_decide`-free, executable Lean
implementations of SHA-256 and ECDSA P-256 that already exist in the
`gpu_prover` deployment (`SparkInterval/Certificate/SHA256.lean`,
`.../P256.lean`) begin with `import Mathlib`, transitively for all of them
(`P256 → RSA → SHA256 → Mathlib`).  Moving them here would either drag Mathlib
into a dependency-free package or mean rewriting their proofs — and a rewritten
copy of an audited signature verifier is a *fork*, which is exactly the
soundness hazard to avoid.  Parameterising instead keeps **one** implementation
of each primitive in the whole system, and adds no dependency edge in either
direction.

The price is that this package cannot, on its own, close a receipt check in the
kernel.  That is stated rather than hidden: `ReceiptCrypto` is an argument to
every definition and theorem below, and to `RunAdmission`.

## The vacuous-instance hazard, and the structural answer

An interface invites a garbage instance.  `⟨fun _ => "00…0", fun _ _ _ => true⟩`
inhabits `ReceiptCrypto` and makes `receiptBinds` accept anything.  Prose is not
a defence against that, so `ReceiptCrypto.SelfTested` is a `Prop` carrying
known-answer tests — three FIPS 180-4 SHA-256 vectors, one accepting ECDSA
P-256 vector and three rejecting ones — and **the dischargers require it**
(`LeanCompCert.Trusted.localSignedRun_admits` takes it as a hypothesis).  A
consumer discharges it by `decide +kernel` against its own implementation, so
the kernel, not the reader, checks that the digest and the verifier are the
ones the standard names.

`SelfTested` is a **sanity gate, not a proof of correctness**.  It rules out the
constant functions and the obvious mistakes; it does not establish that
`hashHex` is SHA-256 on every input, and no finite set of vectors could.  What
it buys is that the failure mode has to be deliberate rather than accidental.

## Conventions

* Digests are written as **64 lowercase hexadecimal characters**.  Uppercase is
  rejected, so a signed wire representation has a unique spelling — the same
  convention `gpu_prover`'s `CanonicalHex` uses.
* `SignatureScheme.verify publicKey message signature` takes the *message
  string*, not its digest; the scheme hashes internally.  This matches
  `SparkInterval.Certificate.P256.verifySha256` exactly, so the shim a consumer
  writes is one line.
* Public keys are SEC1 uncompressed (`04 || X || Y`, 130 hex characters);
  signatures are the fixed-width `r || s` form (128 hex characters).  DER is
  not accepted.
-/

namespace LeanCompCert.Attest

/-! ## Small string predicates, kernel-computable

Everything goes through `String.toList` — the raw `List Char` — rather than the
byte-position API, so the kernel reduces it by ordinary list recursion.

These are three-line boolean predicates, not cryptography; a near-identical set
lives in `LeanCompCert/Trusted/Evidence.lean`, which is in the *other* library
and predates this one.  They are kept separate rather than shared because
`Attest` must live in the axiom-free core while `Trusted` must not be imported
by it. -/

/-- A lowercase hexadecimal digit.  Uppercase is deliberately excluded. -/
def isHexDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9') || decide ('a' ≤ c ∧ c ≤ 'f')

/-- Exactly `n` lowercase hexadecimal characters. -/
def isHexOfLength (n : Nat) (s : String) : Bool :=
  decide (s.toList.length = n) && s.toList.all isHexDigit

/-- A 256-bit digest, written as 64 lowercase hex characters. -/
def isDigest256 (s : String) : Bool := isHexOfLength 64 s

/-- A SEC1 uncompressed P-256 public point: `04 || X || Y`, 130 hex
characters. -/
def isP256PublicKey (s : String) : Bool :=
  isHexOfLength 130 s && decide (s.toList.take 2 = ['0', '4'])

/-- A fixed-width `r || s` ECDSA signature: 128 hex characters. -/
def isP256Signature (s : String) : Bool := isHexOfLength 128 s

/-- A bounded, non-empty identity label.  The upper bound keeps the checker's
kernel cost fixed: identity strings are digests and short version labels, never
the full text of a configuration file. -/
def isLabel (s : String) : Bool :=
  decide (1 ≤ s.toList.length) && decide (s.toList.length ≤ 256)

/-! ## The two operations -/

/-- A named 256-bit digest over a string, producing lowercase hex.

The `name` field is part of the receipt's binding: a receipt records which
digest was used, and `receiptBinds` refuses a receipt naming a different one.
That is what stops a receipt produced under one hash from being re-presented
under another. -/
structure DigestScheme where
  /-- Algorithm identifier, e.g. `"sha256"`. -/
  name : String
  /-- The digest, as 64 lowercase hex characters. -/
  hashHex : String → String

/-- A named signature verifier.

`verify publicKey message signature` is **total and fail-closed**: it returns a
`Bool`, and every malformed input — wrong length, uppercase hex, an off-curve
point, an out-of-range scalar — must yield `false` rather than an error or a
default `true`. -/
structure SignatureScheme where
  /-- Algorithm identifier, e.g. `"ecdsa-p256-sha256"`. -/
  name : String
  /-- `verify publicKey message signature`. -/
  verify : String → String → String → Bool

/-- The pair a receipt check is stated over. -/
structure ReceiptCrypto where
  digest : DigestScheme
  signature : SignatureScheme

/-! ## Known-answer tests

The vectors below are constants of the standard.  The SHA-256 ones are the
three published in FIPS 180-4 Appendix B.  The P-256 ones were generated with
OpenSSL 3.0 and re-verified with an independent from-scratch ECDSA
implementation (curve arithmetic written out, no OpenSSL involved in the
check), so a consumer that fails them has a bug rather than a stale vector. -/

/-- FIPS 180-4 B.1: `SHA-256("")`. -/
def sha256KatEmptyOut : String :=
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

/-- FIPS 180-4 B.1: `SHA-256("abc")`. -/
def sha256KatAbcOut : String :=
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

/-- FIPS 180-4 B.2 input: the 448-bit two-block message. -/
def sha256KatLongIn : String :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

/-- FIPS 180-4 B.2 output.  This vector matters because it is the one that
crosses a block boundary, so an implementation whose padding or message
schedule is wrong fails here and not on the first two. -/
def sha256KatLongOut : String :=
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

/-- KAT signing key, SEC1 uncompressed. -/
def p256KatPublicKey : String :=
  "047baa3c88e86a0d4dc2a828ce66e84cec4c1045b015b581ace8622467685f6a3b" ++
  "4aece70bacf8e5eba80c623bf5985465a0ab62cdb0cd53bac30b9241bab76421"

/-- A *different* P-256 public key, for the wrong-key rejection vector. -/
def p256KatOtherPublicKey : String :=
  "04f6fe833f4b10b0be64962a10149d9cbfd8db48b32db40add7866eb598aa10372" ++
  "26f965082856805a715182f21dc6b9f6e91a2f5db7220b90d2c0c08bf043aedf"

/-- The signed message. -/
def p256KatMessage : String := "leancompcert-receipt-kat/1"

/-- A message differing from `p256KatMessage` in one character. -/
def p256KatOtherMessage : String := "leancompcert-receipt-kat/2"

/-- `ECDSA-P256-SHA256(p256KatMessage)` under the KAT key, as `r || s`. -/
def p256KatSignature : String :=
  "865ad0552080050429193a80ac84937bab1518b18e83d48f3ff2974186525bb2" ++
  "1aa726710fb726402c1d177947b60627d85022c442c6fdf158cb88aed1e173f8"

/-- `p256KatSignature` with its last nibble changed. -/
def p256KatTamperedSignature : String :=
  "865ad0552080050429193a80ac84937bab1518b18e83d48f3ff2974186525bb2" ++
  "1aa726710fb726402c1d177947b60627d85022c442c6fdf158cb88aed1e173f0"

/-- **The obligation a supplied `ReceiptCrypto` must meet.**

Discharge it by `decide +kernel` against your implementation.  It is required
by every admission discharger, so an instance that skips it cannot be used to
admit a run.

The three rejection clauses are the load-bearing ones.  A verifier that
returns `true` unconditionally passes `signatureAccepts` and fails all three;
a verifier that ignores the message passes two of them and fails
`rejectsWrongMessage`; a verifier that ignores the key fails
`rejectsWrongKey`. -/
structure ReceiptCrypto.SelfTested (c : ReceiptCrypto) : Prop where
  /-- The digest names itself `"sha256"`. -/
  digestNamed : c.digest.name = "sha256"
  /-- FIPS 180-4 B.1, empty message. -/
  digestEmpty : c.digest.hashHex "" = sha256KatEmptyOut
  /-- FIPS 180-4 B.1, `"abc"`. -/
  digestAbc : c.digest.hashHex "abc" = sha256KatAbcOut
  /-- FIPS 180-4 B.2, the two-block message. -/
  digestLong : c.digest.hashHex sha256KatLongIn = sha256KatLongOut
  /-- The verifier names itself `"ecdsa-p256-sha256"`. -/
  signatureNamed : c.signature.name = "ecdsa-p256-sha256"
  /-- A genuine signature is accepted. -/
  signatureAccepts :
    c.signature.verify p256KatPublicKey p256KatMessage p256KatSignature = true
  /-- A signature over a different message is rejected. -/
  rejectsWrongMessage :
    c.signature.verify p256KatPublicKey p256KatOtherMessage p256KatSignature
      = false
  /-- A signature checked against a different key is rejected. -/
  rejectsWrongKey :
    c.signature.verify p256KatOtherPublicKey p256KatMessage p256KatSignature
      = false
  /-- A signature altered by one nibble is rejected. -/
  rejectsTamperedSignature :
    c.signature.verify p256KatPublicKey p256KatMessage
      p256KatTamperedSignature = false

/-! ### What `SelfTested` rules out, stated as theorems

These are not decoration.  They are the reason `SelfTested` is a hypothesis of
the dischargers: without them the interface would be inhabited by functions
that make `receiptBinds` meaningless, and nothing would say so. -/

/-- A verifier that accepts everything is not self-tested. -/
theorem not_selfTested_of_alwaysTrue (d : DigestScheme) (name : String) :
    ¬ ReceiptCrypto.SelfTested ⟨d, ⟨name, fun _ _ _ => true⟩⟩ := by
  intro h
  exact Bool.noConfusion h.rejectsWrongMessage

/-- A verifier that rejects everything is not self-tested either, so
`SelfTested` cannot be met by simply refusing to work. -/
theorem not_selfTested_of_alwaysFalse (d : DigestScheme) (name : String) :
    ¬ ReceiptCrypto.SelfTested ⟨d, ⟨name, fun _ _ _ => false⟩⟩ := by
  intro h
  exact Bool.noConfusion h.signatureAccepts

/-- A verifier that ignores the message — the classic mistake of checking a
signature against a payload it was not computed over — is not self-tested. -/
theorem not_selfTested_of_messageIgnoring (d : DigestScheme) (name : String)
    (f : String → String → Bool) :
    ¬ ReceiptCrypto.SelfTested ⟨d, ⟨name, fun k _ s => f k s⟩⟩ := by
  intro h
  have haccept := h.signatureAccepts
  have hreject := h.rejectsWrongMessage
  simp only [] at haccept hreject
  rw [haccept] at hreject
  exact Bool.noConfusion hreject

/-- A constant digest is not self-tested: the three vectors have three
different answers. -/
theorem not_selfTested_of_constantDigest (name : String) (v : String)
    (s : SignatureScheme) :
    ¬ ReceiptCrypto.SelfTested ⟨⟨name, fun _ => v⟩, s⟩ := by
  intro h
  have h1 := h.digestEmpty
  have h2 := h.digestAbc
  simp only [] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

end LeanCompCert.Attest
