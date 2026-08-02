import LeanCompCert.Attest.Receipt

/-!
# `RunAdmission` — the one thing this package never proves

Everything else in `leancompcert` is a theorem.  This module names the single
empirical premise that separates a checked receipt from a mathematical fact,
declares it as a hypothesis, and composes it with the proved forward chain.

**This module adds no axiom.**  `#print axioms` on anything below shows
`[propext, Classical.choice, Quot.sound]`.  `RunAdmission` is an *assumption*
here; it is discharged elsewhere, by a named axiom in a module a consumer opts
into, so a downstream `#print axioms` names which discharger was used.

## What a discharger is asserting

Read this paragraph before writing or accepting one.

> Let `A` be an `Artifact`: an `ArtifactBody` — a `Computation`, or a
> `Reflect.Program` to be emitted rolled — and a string `A.source` together
> with a kernel-checked proof that `A.source` is exactly the C text this
> package's emitter produces for that body.  Let `R` be a `RunReceipt` for which
> `receiptBinds crypto A kind params nonce value R = true` — so, in particular,
> `R.programHash` is `crypto.digest.hashHex A.source`, `R.value` is `value`,
> `R.verdict` is `agrees`, `R.nonce` is the challenge nonce, and `R`'s
> signature verifies over `R.payload` under `R.publicKey`.
>
> To discharge `RunAdmission crypto A R` you are asserting, of the world and
> not of Lean:
>
> 1. **that a machine really executed** a binary produced by compiling the C
>    text whose `crypto.digest` is `R.programHash`, with the CompCert install
>    identified by `R.toolchain`, on the inputs whose digest is `R.paramsHash`;
> 2. **that the execution terminated normally** and reported the value
>    `R.value`, rather than being killed, truncated, or reported from a cache;
> 3. **that `R.publicKey` is a key you are willing to treat as speaking for
>    that execution**, on whatever grounds your regime supplies — a hardware
>    attestation rooted in a pinned CA, or the far weaker grounds of a key you
>    generated on a machine you administer;
> 4. and — because `MachineExecuted` is not a statement Lean can relate to the
>    C model on its own — **that the value the binary reported is the value the
>    proved C model returns**, i.e. `A.body.modelResult = some R.value`.
>
> Clause 4 is where the residual risk sits, and it is now the same claim on
> both routes: that CompCert compiled the emitted text faithfully and the
> hardware ran the result — the thing CompCert's Coq proof is about.
> `A.body.modelResult` is the model of the statements *actually emitted*: the
> lowered straight-line statements on `provedStraightLine`, and the
> declarations, prologue, counted `while` loop and epilogue on `rolledLoop`.
> The rolled route no longer bundles an extra unmechanised step; see
> `ArtifactBody.modelResult_eq_sourceResult` and
> `Reflect.rolledResult_eq_denote`.

Nothing in that list is provable in Lean, and no amount of cryptography makes
it so.  A signature establishes who is speaking, never that what they said is
true.

## Why the premise is opaque, and what that does and does not buy

`MachineExecuted` is `opaque`: it has no content Lean can use, so a discharger
cannot derive a contradiction from it and cannot be *refuted* by it either.
That is a deliberate safety property — a false discharger makes your theorem
meaningless, not your logic inconsistent — but it is also the thing to be
careful about.  **The obligation on a discharger is not logical; it is
editorial.**  Nothing in the kernel will catch a discharger whose docstring
says one thing and whose deployment does another.  What the kernel does give
you is the *name*: an axiom carrying the discharge appears in `#print axioms`,
and the two supplied regimes have different names in different modules, so a
reviewer can tell mechanically which one a theorem depends on.
-/

namespace LeanCompCert.Attest

open LeanCompCert.Verified

/-- **The empirical premise: a machine ran this artifact and reported this
value.**

Deliberately without content.  Lean has no model of a machine, a process, or a
clock, so any formalisation of "this really happened" is a name and nothing
more.  Making that explicit — rather than encoding some proxy that looks like
content — is the honest option, and it is the same stance `gpu_prover` takes
with `PhalaTdxAttestedEmission`.

Because it is opaque, it cannot be proved and cannot be disproved.  Its purpose
is to appear in `RunAdmission`'s type, so that a reader of the structure sees
the empirical claim spelled out instead of inferring it. -/
opaque MachineExecuted (crypto : ReceiptCrypto) (artifact : Artifact)
    (receipt : RunReceipt) : Prop := True

/-- **The admission interface.**  What a discharger must supply, and the only
thing this package takes on faith.

The two fields are the two halves of the claim, and they are separate on
purpose:

* `executed` is the empirical fact, which is outside logic;
* `reported` is its consequence for the object the proved chain is about — the
  restricted-C model of the emitted statements.

A discharger that supplies `reported` alone would be asserting a mathematical
statement with no stated connection to any run; a discharger that supplied
`executed` alone would assert something Lean could do nothing with.  Both are
required, and the docstring of this module says exactly what asserting them
commits you to. -/
structure RunAdmission (crypto : ReceiptCrypto) (artifact : Artifact)
    (receipt : RunReceipt) : Prop where
  /-- A machine really executed the CompCert compilation of this artifact's C
  text, on these inputs, and reported this value. -/
  executed : MachineExecuted crypto artifact receipt
  /-- …and therefore the proved restricted-C model of that text returns it. -/
  reported : artifact.body.modelResult = some receipt.value

/-! ## The composition

This is the theorem the whole module exists for: a checked receipt plus an
admitted run gives a fact about the `Computation`, and hence — through the
consumer's own equivalence lemma — about the consumer's mathematics. -/

/-- **The join, at the C model.**  A checked receipt plus an admitted run says
the proved model of the *emitted text* returns the claimed value.  No coverage
hypothesis: this is true on any route, because `modelResult` is by definition
about the statements that were emitted. -/
theorem modelResult_of_receipt {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {receipt : RunReceipt}
    (bound : receiptBinds crypto artifact kind params nonce value receipt = true)
    (admitted : RunAdmission crypto artifact receipt) :
    artifact.body.modelResult = some value := by
  have hvalue : receipt.value = value := (receiptBinds_sound bound).2.2.2.2.2.2.1
  rw [admitted.reported, hvalue]

/-- **The join.**

```text
receiptBinds crypto artifact kind params nonce value receipt = true
  →  artifact.coveredByProvedChain = true
  →  RunAdmission crypto artifact receipt
  →  artifact.body.Returns value
```

The first hypothesis is decidable and the kernel checks it; it is what makes
the third hypothesis *about this artifact* rather than about some unspecified
binary.  The second is the decidable, program-sized coverage condition — `rfl`
on the straight-line route.  The step from the C model back to the source
meaning is `ArtifactBody.modelResult_eq_sourceResult`, which is proved.

Axiom-free: `#print axioms` shows only the standard three. -/
theorem returns_of_receipt {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {receipt : RunReceipt}
    (bound : receiptBinds crypto artifact kind params nonce value receipt = true)
    (covered : artifact.coveredByProvedChain = true)
    (admitted : RunAdmission crypto artifact receipt) :
    artifact.body.Returns value := by
  show artifact.body.sourceResult = some value
  rw [← artifact.body.modelResult_eq_sourceResult covered]
  exact modelResult_of_receipt bound admitted

/-- The same, with the coverage condition taken from `receiptBindsProved`
rather than supplied separately.  This is the form with no unmechanised step
between the compiled text and the source meaning — available on **both**
routes; see `ArtifactBody`. -/
theorem returns_of_receipt_proved {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {receipt : RunReceipt}
    (bound :
      receiptBindsProved crypto artifact kind params nonce value receipt = true)
    (admitted : RunAdmission crypto artifact receipt) :
    artifact.body.Returns value :=
  returns_of_receipt (receiptBindsProved_sound bound).2
    (receiptBindsProved_sound bound).1 admitted

/-- Consumer-facing form: an admitted run discharges a `Decision`, and hence
the proposition it decides.

`Decision.specification` is the consumer's own equivalence lemma — the step
from "the computation returns `v`" to "my theorem holds" — and it is an
ordinary proved statement.  This corollary just chains it, so that a campaign
site reads as one application rather than three. -/
theorem decide_of_receipt {proposition : Prop} {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {receipt : RunReceipt}
    (decision : Decision proposition)
    (same : artifact.body.sourceResult = decision.computation.sourceResult)
    (bound : receiptBindsProved crypto artifact kind params nonce
      decision.acceptingValue receipt = true)
    (admitted : RunAdmission crypto artifact receipt) : proposition :=
  decision.prove (by
    have h := returns_of_receipt_proved bound admitted
    show decision.computation.sourceResult = some decision.acceptingValue
    rw [← same]
    exact h)

end LeanCompCert.Attest
