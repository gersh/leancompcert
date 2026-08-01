import LeanCompCert.Attest

/-!
# Local-key run attestation — what a signature you made yourself is worth

**Importing this module puts a named axiom in your axiom list.  That is the
point.**  `LeanCompCert.Attest` is axiom-free and stays that way; this module
is one of the two supplied ways to discharge its `RunAdmission` hypothesis, and
it is the *weak* one.

## Read this before using it

A locally-generated signing key sits on the same machine that ran the binary.
Anyone who can read that key can sign any value at all, and the machine that
signs is the machine whose honesty is in question.  So:

**What a local receipt buys.**  It makes the record **tamper-evident**.  A
receipt binds, in one signed blob: the digest of the exact C text compiled, the
digest of the inputs, the identity of the CompCert install (version *and* a
digest of the `ccomp` binary), the machine identity, a challenge nonce, a
timestamp, and the value reported.  Consequences that follow, and that are
worth having:

* a receipt cannot be silently edited after the fact — change any field and
  the signature stops verifying, and `receiptBinds` refuses it;
* a receipt for one program cannot be presented for another, because
  `programHash` is checked against the digest of *this* artifact's emitted C;
* a stale receipt cannot be passed off as fresh, because the nonce is fixed
  before the run and checked after it;
* a receipt produced against one CompCert install cannot be re-used to claim a
  run under a different one;
* a disagreeing or abnormally terminated run produces no admissible receipt at
  all, and the two are distinguished.

That is real: it turns "some file in `.lake/build` says the check passed" into
an auditable record that an accidental copy, a stale cache, a rebuilt
toolchain, or a post-hoc edit will visibly break.

**What a local receipt does not buy.**  It does **not** establish that the
computation was performed, that the machine was honest, or that the value is
what the binary really printed.  A compromised or merely careless host can sign
whatever it likes, and this scheme will accept it.  A local receipt is
*auditable bookkeeping for a trusted-machine setting*.  It is **not**
equivalent to enclave attestation and must never be described as such, in code,
in docs, or in a paper.

The distinction is structural, not editorial.  A local receipt carries
`AttestationKind.localSignature`; `receiptBinds` refuses it wherever
`AttestationKind.enclaveQuote` was demanded, and the reverse.  The two
dischargers are different axioms in different modules with different names, so
`#print axioms` on a downstream theorem says which one a result rests on:

* `LeanCompCert.Trusted.localSignedRun_admits` — this module;
* `gpu_prover`'s own axiom — hardware attestation, rooted in a pinned CA.

Grep for the first name in an axiom listing and you have found every theorem
whose evidence is a signature the running machine made about itself.

## Why a self-test hypothesis

The axiom takes `ReceiptCrypto.SelfTested crypto` as a premise.  Without it the
axiom would be applicable with `⟨fun _ => "0…0", fun _ _ _ => true⟩`, under
which `receiptBinds` accepts every receipt and the whole check is theatre.  The
premise is decidable and the kernel checks it, so that failure mode is closed
mechanically rather than by a warning in a docstring.

## What is still not admitted

The conclusion is `RunAdmission`, and `RunAdmission` gives you
`artifact.computation.Returns value` — a fact about the *computation*, not
about your mathematics.  The step from there to the statement you care about is
the encoding gap, it is yours, and it is deliberately not smuggled in here.  An
admitted run gives you a number; it does not give you a theorem about number
theory.
-/

namespace LeanCompCert.Trusted

open LeanCompCert.Attest LeanCompCert.Verified

/-- **The local-key admission schema.**

Read it as: *if the supplied digest and signature verifier pass their
known-answer tests, and a receipt of kind `localSignature` binds to this
artifact, these inputs, this nonce and this value, then the run it describes
may be admitted.*

Every premise but the last word is decidable and re-checked by the kernel.  The
leap — the entire leap — is that a receipt signed by a key resident on the
machine that ran the binary corresponds to a real execution on that machine.
Nothing proves that, and on a compromised host it is false. -/
abbrev LocalRunAdmitted : Prop :=
  ∀ (crypto : ReceiptCrypto) (artifact : Artifact) (params nonce : String)
    (value : Int) (receipt : RunReceipt),
    ReceiptCrypto.SelfTested crypto →
    receiptBinds crypto artifact AttestationKind.localSignature params nonce
      value receipt = true →
    RunAdmission crypto artifact receipt

/-- The schema, exhibited once as a named axiom.

This is the **weak** discharger.  See the module docstring for exactly what a
locally-generated key does and does not establish.

A consumer that wants one axiom per admitted run rather than one collapsed
entry mints its own constant of type `LocalRunAdmitted` at each site, exactly
as the `evidenced_decide` tactic does for `EvidencedRun`
(`LeanCompCert/Trusted/EvidencedDecide.lean`).  Both are instances of the same
statement, so an auditor checks the surface by listing the names and
type-checking each against this schema. -/
axiom localSignedRun_admits : LocalRunAdmitted

/-- **The whole loop, for a locally-attested run.**

```text
ReceiptCrypto.SelfTested crypto
receiptBinds crypto artifact .localSignature params nonce value receipt = true
  ⟹  artifact.computation.Returns value
```

Carries `localSignedRun_admits`, and nothing else.  The step from
`Computation.Returns` to a statement about the consumer's own reference
function is the consumer's equivalence lemma, which is an ordinary theorem. -/
theorem returns_of_localReceipt {crypto : ReceiptCrypto} {artifact : Artifact}
    {params nonce : String} {value : Int} {receipt : RunReceipt}
    (selfTested : ReceiptCrypto.SelfTested crypto)
    (bound : receiptBinds crypto artifact AttestationKind.localSignature
      params nonce value receipt = true) :
    artifact.computation.Returns value :=
  returns_of_receipt bound
    (localSignedRun_admits crypto artifact params nonce value receipt
      selfTested bound)

/-- The same, restricted to the emission route the package's proved C model
covers, so that no unmechanised step sits between the compiled text and the
computation.  See `Attest.EmissionRoute`. -/
theorem returns_of_localReceipt_proved {crypto : ReceiptCrypto}
    {artifact : Artifact} {params nonce : String} {value : Int}
    {receipt : RunReceipt}
    (selfTested : ReceiptCrypto.SelfTested crypto)
    (bound : receiptBindsProved crypto artifact AttestationKind.localSignature
      params nonce value receipt = true) :
    artifact.route = EmissionRoute.provedStraightLine
      ∧ artifact.computation.Returns value :=
  ⟨(receiptBindsProved_sound bound).1,
    returns_of_localReceipt selfTested (receiptBindsProved_sound bound).2⟩

/-- Consumer-facing form: a locally-attested run discharges a `Decision`, and
hence the proposition it decides. -/
theorem decide_of_localReceipt {proposition : Prop} {crypto : ReceiptCrypto}
    {artifact : Artifact} {params nonce : String} {receipt : RunReceipt}
    (decision : Decision proposition)
    (same : decision.computation = artifact.computation)
    (selfTested : ReceiptCrypto.SelfTested crypto)
    (bound : receiptBinds crypto artifact AttestationKind.localSignature
      params nonce decision.acceptingValue receipt = true) : proposition :=
  decision.prove (same ▸ returns_of_localReceipt selfTested bound)

end LeanCompCert.Trusted
