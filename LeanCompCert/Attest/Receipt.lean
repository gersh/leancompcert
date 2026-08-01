import LeanCompCert.Attest.Crypto
import LeanCompCert.Verified.Decide
import LeanCompCert.Verified.Rolled

/-!
# Run receipts, and the fact that binds one to a computation

## The gap this closes

`leancompcert` proves a **forward** chain, all of it machine-checked and
axiom-free:

```text
reference Lean function
  ↕ consumer equivalence lemma
Program.denote
  ↕ Program.evalCC_compile
CCIR trace
  ↕ lowerSequence_correct  →  Computation.result_preserved
restricted-C model of the emitted statements
  ↕ CompCert (Coq)
assembly
```

Separately, an attestation service can sign a statement that *some* binary ran
and reported *some* value.  Neither half holds the join: nothing said that the
binary whose run was attested is the compilation of the C whose semantics were
proved.  A signed receipt over the full range of a real computation therefore
discharged nothing at all.

The join is a **decidable, kernel-checkable** fact:

> `receipt.programHash = digest (the emitted C of this Artifact)`

`receiptBinds` below is that check, plus the well-formedness and freshness
clauses around it, and `receiptBinds_sound` is what it forces.  Composing it
with the forward chain gives `Attest.returns_of_receipt`
(`LeanCompCert/Attest/Admission.lean`) with **no new axiom in this package**.

## Why this is affordable in the kernel

Because of `emitRolled`.  A 10⁷-iteration loop is a ~2 KB C artifact
(`LeanCompCert/Testing/RolledFixedPoint.lean`), not a gigabyte of unrolled
statements, and a 256-bit digest of 2 KB is a few dozen compression-function
blocks — comfortable.  The check's cost is the *source* size, and is
independent of how long the artifact ran.

## The two emission routes, and which one the proved chain covers

Read `EmissionRoute` before using this.  One of the two routes is fully covered
by the proved chain and the other is not, and the difference is recorded in the
data rather than left to prose.
-/

namespace LeanCompCert.Attest

open LeanCompCert.Verified

/-! ## Emission routes -/

/-- How the C text handed to `ccomp` was produced from the computation.

**`provedStraightLine`** — the translation unit is `Lower.compileProgram`'s
output for `computation.fn`, i.e. the emission of exactly the statements the
`Computation` carries.  `Computation.result_preserved` is about *those*
statements, so the chain from "the C model returns `v`" back to "the CCIR
computation returns `v`" is proved end to end.

**`rolledLoop`** — the translation unit is `emitRolled`'s `while`-loop form for
a `Reflect.Program`.  This is the route that makes a 10⁷-iteration computation
a 2 KB artifact, and it is the one you want at scale.  ⚠ **It is not covered by
the proved C model.**  `Proof.PureSemantics.evalCStmt` interprets `C.CStmt`
assignments and nothing else — a `whileLoop` evaluates to `none` — so there is
no `result_preserved` for the rolled unit.  What *is* proved is the CCIR-level
statement `Verified.Reflect.rolledTrace_eq_augmented`: the rolled dynamic trace
equals the counter-augmented program's unrolled trace.  The missing link is
between the C `while` statement and that trace.

Consequences, stated plainly: on the rolled route a discharger's
`RunAdmission.denotes` field bundles one further unproved step — that the
rolled C's `while` loop realises the unrolled statement sequence — on top of
the empirical claim that a run happened.  That step is exactly the kind of
thing CompCert's own semantics would settle and this package has not yet
mechanised.  Use `provedStraightLine` wherever the unrolled unit is small
enough to emit, and record the rolled route honestly where it is not. -/
inductive EmissionRoute where
  /-- Emission of the `Computation`'s own lowered statements.  Fully covered by
  `Computation.result_preserved`. -/
  | provedStraightLine
  /-- `emitRolled`'s `while`-loop form for `program` under the C entry point
  `entry`.  Compact, and **not** covered by the proved C model. -/
  | rolledLoop (program : Reflect.Program) (entry : String)

/-- Whether the emitted text is inside the package's proved C model.

`false` for the rolled route.  A consumer that wants only the fully-proved
chain requires this to be `true`; `receiptBindsProved` does exactly that. -/
def EmissionRoute.coveredByProvedChain : EmissionRoute → Bool
  | .provedStraightLine => true
  | .rolledLoop _ _ => false

/-- The route's name, as it appears in the signed payload.  A receipt produced
under one route cannot be presented under the other. -/
def EmissionRoute.label : EmissionRoute → String
  | .provedStraightLine => "straight-line"
  | .rolledLoop _ _ => "rolled-loop"

/-! ## The artifact: a computation together with the exact bytes compiled -/

/-- The emitter, as a function of the computation and the route.

`mainC` is the self-checking `main` the certificates append after the
translation unit — the one whose exit status is `0` exactly when the computed
value equals the certified constant.  It is part of the hashed text because it
is part of the text handed to `ccomp`. -/
def emitFor (computation : Computation) (route : EmissionRoute)
    (mainC : String) : Except (Array String) String :=
  match route with
  | .provedStraightLine => do
      let (_, source) ←
        Lower.compileProgram .portable { functions := #[computation.fn] }
      pure (source ++ mainC)
  | .rolledLoop program entry => do
      let source ← Reflect.emitRolled program entry
      pure (source ++ mainC)

/-- The self-checking `main` a certificate appends: exit `0` exactly when the
emitted function returns `value`, `1` when it does not.

Build the `main` with this rather than spelling the constant out by hand.  If
the `main` tests one number and the receipt records another, the Lean-side
check *still passes* — the receipt and the proof site agree with each other
while the artifact tested something else.  Deriving both from one `value`
closes that by construction, and the `main` is inside the hashed text, so the
constant the binary tested is pinned by `programHash`. -/
def selfCheckMain (entry : String) (value : Nat) : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  s!"    return {entry}() == UINT64_C({value}) ? 0 : 1;\n" ++
  "}\n"

/-- **What was compiled: a computation, a route, and a `main`.**

Deliberately *pure data with no proof field*.  The C text is not a field the
author supplies and asserts is right — it is `Artifact.source?`, computed from
these three by this package's own emitter.  So there is nothing an author can
get wrong here, and no obligation that could be discharged carelessly: a
receipt binds to the emitter's output or to nothing.

This is the whole join.  `receiptBinds` compares the receipt's `programHash`
against the digest of `source?`, so a passing check says the signed record is
about the C text *this computation* compiles to. -/
structure Artifact where
  /-- The computation the proved chain is about. -/
  computation : Computation
  /-- Which emitter to use.  See `EmissionRoute`. -/
  route : EmissionRoute
  /-- The self-checking `main` appended to the emitted translation unit.
  Build it with `selfCheckMain` from the certified value. -/
  mainC : String

/-- **The exact bytes handed to `ccomp`**, as this package emits them.

`none` when emission fails, which makes `receiptBinds` refuse the receipt: an
artifact that cannot be emitted cannot be attested.

⚠ **This is the one thing the kernel cannot currently evaluate.**  The C
emitter and the C validator (`LeanCompCert/C/Emit.lean`,
`LeanCompCert/C/Validate.lean`) are written with `partial` definitions —
`CType.emit`, `CExpr.emit`, `emitStatements`, `emitStatement`, `validateType`,
`validateExpr`, `validateStatements` — which the kernel will not unfold, and
`CCIR.validateProgram` is stuck for the same reason.  Measured: `decide
+kernel` on `(Lower.compileProgram .portable ⟨#[computation.fn]⟩).toOption
.isSome = true` does not reduce, for a two-instruction program.

The consequence is stated plainly in
`docs/use-case-3-attested-run-receipts.md` and in `ROADMAP.md`: today a
consumer discharges `receiptBinds … = true` with **one named axiom per
artifact**, checked out of band by `lean-compcert verify-receipt`, which
re-emits the C and compares digests.  The fix is to make those seven
definitions structural or fuelled; nothing else in the chain is in the way,
and no part of the standard changes when they are. -/
def Artifact.source? (a : Artifact) : Option String :=
  (emitFor a.computation a.route a.mainC).toOption

/-! ## The receipt -/

/-- The artifact's exit-status classification, mirroring `NativeCheck.classify`.

Exactly one status — `1` — means "the computed value differs from the certified
constant".  Everything else nonzero is an **abnormal termination**, which says
nothing about the computed value and must never be reported as a
disagreement. -/
inductive RunVerdict where
  /-- Exit 0: the computed value equals the certified constant. -/
  | agrees
  /-- Exit 1: it does not. -/
  | disagrees
  /-- Anything else — killed by a signal, out of memory.  Evidence of
  nothing. -/
  | abnormal
  deriving DecidableEq, Repr, Inhabited

def RunVerdict.label : RunVerdict → String
  | .agrees => "agrees"
  | .disagrees => "disagrees"
  | .abnormal => "abnormal"

/-- What kind of assertion the receipt's signature is supposed to support.

This is a **structural** distinction, not a comment.  It appears in the signed
payload, `receiptBinds` refuses a receipt whose kind is not the one demanded,
and the two admission dischargers require different kinds — so a
locally-signed receipt cannot be fed to an enclave-grade discharger, or the
reverse, and `#print axioms` names which one was used. -/
inductive AttestationKind where
  /-- Signed at run time by a key generated on, and resident on, the machine
  that ran the binary.  Makes the record **tamper-evident**.  Does **not**
  establish that the machine was honest or that the run happened; see
  `LeanCompCert/Trusted/LocalReceipt.lean`. -/
  | localSignature
  /-- Signed inside a hardware-attested enclave whose measurement is checked
  against a pinned root of trust.  This package does not implement quote
  verification; `gpu_prover` does. -/
  | enclaveQuote
  deriving DecidableEq, Repr, Inhabited

def AttestationKind.label : AttestationKind → String
  | .localSignature => "local-signature"
  | .enclaveQuote => "enclave-quote"

/-- Identity of the compiler that produced the binary.

A version string alone does not identify a compiler: `ccomp -version` prints
only `The CompCert C verified compiler, version 3.17`, with **no architecture**,
so an install configured `aarch64-linux` and one configured `x86_64-linux` are
indistinguishable by it.  `binaryDigest` is a digest of the `ccomp` executable
itself, which also catches a CompCert rebuilt from patched sources at the same
release number.  This mirrors `NativeCheck.compcertIdentity`, which computes
exactly this. -/
structure ToolchainId where
  /-- `ccomp -version`, first line. -/
  ccompVersion : String
  /-- Digest of the `ccomp` binary and its `compcert.ini`, 64 lowercase hex. -/
  binaryDigest : String
  /-- How the object became an executable: `freestanding`/`hosted`, plus the
  startup stub, assembler and linker identities. -/
  linkDescription : String
  deriving DecidableEq, Repr

def ToolchainId.wellFormed (t : ToolchainId) : Bool :=
  isLabel t.ccompVersion && isDigest256 t.binaryDigest
    && isLabel t.linkDescription

/-- Format version of the receipt schema.  A receipt carrying any other value
is refused rather than interpreted. -/
def schemaVersion : String := "leancompcert-receipt/1"

/-- **A signed record that a binary ran and reported a value.**

Every field is data on the wire.  Nothing here is trusted until `receiptBinds`
has checked it, and `receiptBinds` passing still asserts nothing about whether
a run happened — see `RunAdmission`. -/
structure RunReceipt where
  /-- Must equal `schemaVersion`. -/
  schema : String
  /-- Which assertion the signature is supposed to support. -/
  attestation : AttestationKind
  /-- The emission route the hashed text came from, by label. -/
  routeLabel : String
  /-- Opaque campaign/shard identifier, for the operator's own bookkeeping.
  Bounded and non-empty; never interpreted here. -/
  campaign : String
  /-- Which digest was used, e.g. `"sha256"`.  Checked against the supplied
  `ReceiptCrypto`, so a receipt cannot be re-presented under another hash. -/
  digestName : String
  /-- Digest of the exact C text handed to `ccomp` — `Artifact.source`.
  **This is the join.** -/
  programHash : String
  /-- Digest of the canonical inputs the run was given.  For a closed
  certificate the canonical input string is empty and this is the digest of the
  empty string; for a sharded campaign it is the digest of the shard's
  parameter block. -/
  paramsHash : String
  /-- Identity of the compiler that produced the binary. -/
  toolchain : ToolchainId
  /-- The value the binary reported. -/
  value : Int
  /-- Exit-status classification. -/
  verdict : RunVerdict
  /-- Identity of the machine, in the sense of `NativeCheck.machineIdentity`. -/
  machine : String
  /-- A 256-bit nonce, fixed before the run.  It is what makes a *fresh* record
  distinguishable from a replayed one: the operator chooses it, and a receipt
  quoting a different nonce does not answer the challenge. -/
  nonce : String
  /-- When the record was produced.  Not interpreted; it is what makes a stale
  receipt visible to a reader. -/
  recordedAt : String
  /-- The signing key, SEC1 uncompressed, 130 lowercase hex characters. -/
  publicKey : String
  /-- The signature over `payload`, `r || s`, 128 lowercase hex characters. -/
  signature : String
  deriving DecidableEq, Repr

/-- **The exact bytes the signature covers.**

Newline-separated, one field per line, in this fixed order, with a trailing
newline.  Every field that goes in is constrained by `receiptBinds` to be a
digest, a bounded label, a decimal integer or a fixed enumeration label — none
of which can contain a newline — so the encoding is unambiguous without
escaping.

`publicKey` is inside the payload: a signature therefore commits to the key it
was made with, and a receipt cannot be re-presented under a substituted key
while keeping its signature.  `signature` is of course not inside it. -/
def RunReceipt.payload (r : RunReceipt) : String :=
  String.intercalate "\n" [
    r.schema,
    r.attestation.label,
    r.routeLabel,
    r.campaign,
    r.digestName,
    r.programHash,
    r.paramsHash,
    r.toolchain.ccompVersion,
    r.toolchain.binaryDigest,
    r.toolchain.linkDescription,
    toString r.value,
    r.verdict.label,
    r.machine,
    r.nonce,
    r.recordedAt,
    r.publicKey
  ] ++ "\n"

/-! ## The check -/

/-- **Does this receipt bind to this artifact, this input, and this value?**

Total and fail-closed: it is a `Bool`, and every clause is a comparison the
kernel reduces.  In order, it requires

1. the schema version is exactly `schemaVersion`;
2. the receipt's attestation kind is the one demanded (`kind`) — so a
   locally-signed receipt cannot be used where an enclave receipt was asked
   for, or the reverse;
3. the route label matches the artifact's route, so a rolled-loop receipt
   cannot be presented for a straight-line artifact;
4. the digest name matches the supplied `ReceiptCrypto`'s;
5. **`programHash = crypto.digest.hashHex source`**, where `source` is
   `artifact.source?` — the join, and the only clause whose cost depends on the
   artifact.  An artifact that fails to emit has no `source?` and the whole
   check is `false`;
6. `paramsHash = crypto.digest.hashHex params`;
7. the reported value is the value claimed;
8. the verdict is `agrees` — a disagreement and an abnormal termination both
   fail, and they are distinct;
9. the nonce is the one demanded, and is a 256-bit hex value;
10. every identity field is well formed and non-empty — a truncated receipt
    fails here;
11. **the signature verifies over `payload` under `publicKey`.**

What a passing `receiptBinds` does **not** establish: that a run happened, that
the machine was honest, or that `publicKey` belongs to anyone in particular.
Those are `RunAdmission`'s business, and `RunAdmission` is not proved here. -/
def receiptBinds (crypto : ReceiptCrypto) (artifact : Artifact)
    (kind : AttestationKind) (params : String) (nonce : String) (value : Int)
    (r : RunReceipt) : Bool :=
  match artifact.source? with
  | none => false
  | some source =>
  decide (r.schema = schemaVersion)
    && decide (r.attestation = kind)
    && decide (r.routeLabel = artifact.route.label)
    && decide (r.digestName = crypto.digest.name)
    && decide (r.programHash = crypto.digest.hashHex source)
    && decide (r.paramsHash = crypto.digest.hashHex params)
    && decide (r.value = value)
    && decide (r.verdict = RunVerdict.agrees)
    && decide (r.nonce = nonce)
    && isDigest256 r.nonce
    && isDigest256 r.programHash
    && isDigest256 r.paramsHash
    && r.toolchain.wellFormed
    && isLabel r.campaign
    && isLabel r.machine
    && isLabel r.recordedAt
    && isP256PublicKey r.publicKey
    && isP256Signature r.signature
    && crypto.signature.verify r.publicKey r.payload r.signature

/-- `receiptBinds`, additionally demanding the emission route the proved C
model covers.  Use this when you want the chain with no unmechanised step in
it; see `EmissionRoute`. -/
def receiptBindsProved (crypto : ReceiptCrypto) (artifact : Artifact)
    (kind : AttestationKind) (params : String) (nonce : String) (value : Int)
    (r : RunReceipt) : Bool :=
  artifact.route.coveredByProvedChain
    && receiptBinds crypto artifact kind params nonce value r

/-! ## What a passing check forces -/

/-- **The binding theorem.**  Everything `receiptBinds` establishes, as an
ordinary conjunction, so a caller does not have to re-derive it from the
definition. -/
theorem receiptBinds_sound {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {r : RunReceipt} (h : receiptBinds crypto artifact kind params nonce value r
      = true) :
    (∃ source, artifact.source? = some source
        ∧ r.programHash = crypto.digest.hashHex source)
      ∧ r.schema = schemaVersion
      ∧ r.attestation = kind
      ∧ r.routeLabel = artifact.route.label
      ∧ r.digestName = crypto.digest.name
      ∧ r.paramsHash = crypto.digest.hashHex params
      ∧ r.value = value
      ∧ r.verdict = RunVerdict.agrees
      ∧ r.nonce = nonce
      ∧ r.toolchain.wellFormed = true
      ∧ crypto.signature.verify r.publicKey r.payload r.signature = true := by
  unfold receiptBinds at h
  cases hs : artifact.source? with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some source =>
      rw [hs] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSchema, hKind⟩, hRoute⟩, hDigestName⟩, hProgram⟩,
        hParams⟩, hValue⟩, hVerdict⟩, hNonce⟩, _⟩, _⟩, _⟩, hToolchain⟩, _⟩, _⟩,
        _⟩, _⟩, _⟩, hSig⟩ := h
      exact ⟨⟨source, rfl, hProgram⟩, hSchema, hKind, hRoute, hDigestName,
        hParams, hValue, hVerdict, hNonce, hToolchain, hSig⟩

/-- **The join, isolated.**  A passing receipt's `programHash` is the digest of
the exact C text this package emits for this computation on this route — not of
some other text that happens to be lying around. -/
theorem receiptBinds_programHash {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {r : RunReceipt}
    (h : receiptBinds crypto artifact kind params nonce value r = true) :
    ∃ source, emitFor artifact.computation artifact.route artifact.mainC
        = .ok source
      ∧ r.programHash = crypto.digest.hashHex source := by
  obtain ⟨⟨source, hs, hd⟩, _⟩ := receiptBinds_sound h
  refine ⟨source, ?_, hd⟩
  unfold Artifact.source? at hs
  cases he : emitFor artifact.computation artifact.route artifact.mainC with
  | error e => rw [he] at hs; exact absurd hs (by simp [Except.toOption])
  | ok text =>
      rw [he] at hs
      simp only [Except.toOption, Option.some.injEq] at hs
      rw [hs]

/-- **An artifact that does not emit cannot be attested.**  Fail-closed at the
outermost level: no receipt binds to a computation whose C this package refuses
to produce. -/
theorem receiptBinds_false_of_noEmission {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : artifact.source? = none) :
    receiptBinds crypto artifact kind params nonce value r = false := by
  unfold receiptBinds
  rw [h]

/-! ### The failures, stated as failures

A checker that can only pass is worthless.  Each of these names a way a receipt
can fail to bind, and each is proved for *every* receipt rather than exhibited
on one hand-built instance. -/

private theorem not_true_of {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp_all

/-- **Wrong program.**  A receipt whose `programHash` is not the digest of this
artifact's emitted C does not bind.  This is the clause that stops a receipt
for one computation being presented for another. -/
theorem receiptBinds_false_of_programHash_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} {source : String}
    (hs : artifact.source? = some source)
    (h : r.programHash ≠ crypto.digest.hashHex source) :
    receiptBinds crypto artifact kind params nonce value r = false := by
  refine not_true_of fun hb => h ?_
  obtain ⟨⟨src, hsrc, hd⟩, _⟩ := receiptBinds_sound hb
  rw [hs] at hsrc
  obtain rfl := Option.some.inj hsrc
  exact hd

/-- **Wrong inputs.**  A receipt for a different parameter block does not
bind. -/
theorem receiptBinds_false_of_paramsHash_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt}
    (h : r.paramsHash ≠ crypto.digest.hashHex params) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.2.1

/-- **Wrong value.**  A receipt reporting a different output does not answer
this claim. -/
theorem receiptBinds_false_of_value_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.value ≠ value) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.2.2.1

/-- **A killed artifact is not a disagreement, and neither binds.**  Only
`agrees` passes. -/
theorem receiptBinds_false_of_verdict_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.verdict ≠ RunVerdict.agrees) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.2.2.2.1

/-- **Replay.**  A receipt echoing a different nonce does not answer a challenge
quoting this one. -/
theorem receiptBinds_false_of_nonce_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.nonce ≠ nonce) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.2.2.2.2.1

/-- **Tampering.**  A receipt whose signature does not verify over its own
payload does not bind — so no field of a bound receipt can have been edited
after signing. -/
theorem receiptBinds_false_of_badSignature {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt}
    (h : crypto.signature.verify r.publicKey r.payload r.signature ≠ true) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.2.2.2.2.2.2

/-- **Regime confusion.**  A receipt of the wrong attestation kind does not
bind, so a local signature cannot stand in for an enclave quote. -/
theorem receiptBinds_false_of_kind_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.attestation ≠ kind) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.1

/-- **Route confusion.**  A receipt filed under the other emission route does
not bind. -/
theorem receiptBinds_false_of_route_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.routeLabel ≠ artifact.route.label) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.1

/-- **Wrong digest.**  A receipt naming a digest other than the supplied one
does not bind, so a receipt cannot silently change hash function. -/
theorem receiptBinds_false_of_digestName_ne {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {value : Int} {r : RunReceipt} (h : r.digestName ≠ crypto.digest.name) :
    receiptBinds crypto artifact kind params nonce value r = false :=
  not_true_of fun hb => h (receiptBinds_sound hb).2.2.2.2.1

/-- The strict form implies the plain one, and additionally pins the route. -/
theorem receiptBindsProved_sound {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {r : RunReceipt}
    (h : receiptBindsProved crypto artifact kind params nonce value r = true) :
    artifact.route = EmissionRoute.provedStraightLine
      ∧ receiptBinds crypto artifact kind params nonce value r = true := by
  simp only [receiptBindsProved, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  cases hr : artifact.route with
  | provedStraightLine => rfl
  | rolledLoop p e =>
      rw [hr] at h
      simp [EmissionRoute.coveredByProvedChain] at h

end LeanCompCert.Attest
