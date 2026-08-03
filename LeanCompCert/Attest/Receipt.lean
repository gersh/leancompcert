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

## The two emission routes, and what covers them

Read `ArtifactBody` before using this.  **Both** routes are now inside the
proved C model — the rolled `while` loop as of
`Reflect.rolledResult_eq_denote` — and coverage is recorded in the data rather
than left to prose: `ArtifactBody.coveredByProvedChain` is a decidable,
program-sized side condition, and `ArtifactBody.modelResult_eq_sourceResult`
is what it buys.
-/

namespace LeanCompCert.Attest

open LeanCompCert.Verified

/-! ## Emission routes -/

/-- The route's name, as it appears in the signed payload.  A receipt produced
under one route cannot be presented under the other.

The tag carries no payload: what the route was *applied to* lives in
`ArtifactBody`, where it cannot be stated inconsistently with the computation.
See that type for why. -/
inductive EmissionRoute where
  /-- Emission of a `Computation`'s own lowered statements. -/
  | provedStraightLine
  /-- `emitRolled`'s `while`-loop form for a `Reflect.Program`. -/
  | rolledLoop
  deriving DecidableEq, Repr, Inhabited

def EmissionRoute.label : EmissionRoute → String
  | .provedStraightLine => "straight-line"
  | .rolledLoop => "rolled-loop"

/-! ## The artifact: what was compiled, and the exact bytes compiled

### Why this is an inductive and not a record with a route field

Coverage by the proved chain is a **relation between the route and the
computation**, not a property of the route alone.  On the rolled route the C
text is `emitRolled`'s output for a `Reflect.Program`, and what the proved
chain says about it is a statement about *that program's* counter-augmented
unrolling — so a `⟨computation, route⟩` pair could name one program in the
route and carry a `Computation` for a different one, and every check in this
file would still pass.

It cannot be repaired by comparing the two: comparing `Computation`s means
comparing their `statements`, and for a 10⁷-iteration artifact that list is
astronomically large — exactly what rolled emission exists to avoid.

So the rolled form carries **only the program**, and everything derived from it
— the emitted C, the CCIR trace, the source meaning — is computed here.  There
is no second thing to agree with, and therefore nothing to get wrong. -/

/-- **What was compiled.**  One constructor per emission route, each carrying
exactly the data its emitter consumes.

`straightLine` carries a `Computation`: the emitter's input *is* the
computation, so the pair cannot disagree.

`rolled` carries a `Reflect.Program` and the C entry point.  Its computation is
not supplied — `sourceResult` below is the counter-augmented program's
denotation, which `Reflect.counterAugment_sourceResult` shows is the source
result of the (never materialised) unrolled `Computation` for
`program.counterAugment`. -/
inductive ArtifactBody where
  /-- Emission of the `Computation`'s own lowered statements. -/
  | straightLine (computation : Computation)
  /-- `emitRolled`'s `while`-loop form for `program` under C entry point
  `entry`. -/
  | rolled (program : Reflect.Program) (entry : String)

def ArtifactBody.route : ArtifactBody → EmissionRoute
  | .straightLine _ => .provedStraightLine
  | .rolled _ _ => .rolledLoop

/-- **The emitter.**

`mainC` is the self-checking `main` the certificates append after the
translation unit — the one whose exit status is `0` exactly when the computed
value equals the certified constant.  It is part of the hashed text because it
is part of the text handed to `ccomp`. -/
def emitFor : ArtifactBody → String → Except (Array String) String
  | .straightLine computation, mainC => do
      let (_, source) ←
        Lower.compileProgram .portable { functions := #[computation.fn] }
      pure (source ++ mainC)
  | .rolled program entry, mainC => do
      let source ← Reflect.emitRolled program entry
      pure (source ++ mainC)

/-- The rolled emitter, unfolded once, so that a consumer can identify an
artifact's C with a certificate's without asking the elaborator to evaluate
either. -/
theorem emitFor_rolled (program : Reflect.Program) (entry mainC : String) :
    emitFor (.rolled program entry) mainC =
      (Reflect.emitRolled program entry).bind
        (fun source => pure (source ++ mainC)) := rfl

/-- **The meaning of the emitted text in the proved restricted-C model.**

For the straight-line route this is `Computation.targetResult`, the model of
the lowered statements.  For the rolled route it is `Reflect.rolledResult`, the
model of the emitted `while`-loop function — declarations, prologue, the
counted loop, epilogue — under `Proof.evalCSequenceFuel`. -/
def ArtifactBody.modelResult : ArtifactBody → Option Int
  | .straightLine computation => computation.targetResult
  | .rolled program entry => Reflect.rolledResult program entry

/-- **The source-level meaning the proved chain delivers.**

For the straight-line route, the `Computation`'s own CCIR result.  For the
rolled route, the counter-augmented program's denotation — ordinary Lean `Nat`
arithmetic, which is what a consumer's equivalence lemma is stated against. -/
def ArtifactBody.sourceResult : ArtifactBody → Option Int
  | .straightLine computation => computation.sourceResult
  | .rolled program _ =>
      (program.counterAugment).denote.map (fun n => (n : Int))

/-- The artifact computes this value. -/
def ArtifactBody.Returns (body : ArtifactBody) (value : Int) : Prop :=
  body.sourceResult = some value

/-- **Whether the emitted text is inside the package's proved C model.**

Not a property of the route: on the rolled route it is the decidable side
condition under which `Reflect.rolledResult_eq_denote` holds — the program is
well formed, and its trip count fits a `u64`.  Both are *program*-sized checks,
independent of how long the artifact runs.

A consumer that wants only the fully-proved chain requires this to be `true`;
`receiptBindsProved` does exactly that. -/
def ArtifactBody.coveredByProvedChain : ArtifactBody → Bool
  | .straightLine _ => true
  | .rolled program _ =>
      decide program.WF && decide (program.loopCount < Reflect.M)

/-- **The proved C model of the emitted text returns the source meaning.**

One statement for both routes.  For `straightLine` it is
`Computation.result_preserved`; for `rolled` it is
`Reflect.rolledResult_eq_denote`, which relates the emitted `while` loop to the
counter-augmented unrolling.  This is the theorem that makes the rolled route
carry no unmechanised step. -/
theorem ArtifactBody.modelResult_eq_sourceResult (body : ArtifactBody)
    (covered : body.coveredByProvedChain = true) :
    body.modelResult = body.sourceResult := by
  cases body with
  | straightLine computation => exact computation.result_preserved
  | rolled program entry =>
      simp only [coveredByProvedChain, Bool.and_eq_true, decide_eq_true_eq]
        at covered
      exact Reflect.rolledResult_eq_denote program entry covered.1 covered.2

/-- On the rolled route, "this artifact returns `n`" is exactly "the
counter-augmented program denotes `n`" — ordinary Lean `Nat` arithmetic, which
is what a consumer's equivalence lemma is stated against. -/
theorem ArtifactBody.rolled_Returns_iff_denote (program : Reflect.Program)
    (entry : String) (n : Nat) :
    (ArtifactBody.rolled program entry).Returns ((n : Nat) : Int) ↔
      (program.counterAugment).denote = some n := by
  constructor
  · intro h
    have hMap : (program.counterAugment).denote.map (fun n => (n : Int)) =
        some ((n : Nat) : Int) := h
    cases hDenote : (program.counterAugment).denote with
    | none =>
        rw [hDenote] at hMap
        exact absurd hMap (by simp)
    | some value =>
        rw [hDenote] at hMap
        have hValue : ((value : Nat) : Int) = ((n : Nat) : Int) :=
          Option.some.inj hMap
        exact congrArg some (by exact_mod_cast hValue)
  · intro h
    show (program.counterAugment).denote.map (fun n => (n : Int)) = _
    rw [h]
    rfl

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

/-- **What was compiled: a body and a `main`.**

Deliberately *pure data with no proof field*.  The C text is not a field the
author supplies and asserts is right — it is `Artifact.source?`, computed from
these two by this package's own emitter.  So there is nothing an author can get
wrong here, and no obligation that could be discharged carelessly: a receipt
binds to the emitter's output or to nothing.

This is the whole join.  `receiptBinds` compares the receipt's `programHash`
against the digest of `source?`, so a passing check says the signed record is
about the C text *this body* compiles to. -/
structure Artifact where
  /-- What the proved chain is about, and which emitter it selects.
  See `ArtifactBody`. -/
  body : ArtifactBody
  /-- The self-checking `main` appended to the emitted translation unit.
  Build it with `selfCheckMain` from the certified value. -/
  mainC : String

/-- The emission route, read off the body. -/
def Artifact.route (a : Artifact) : EmissionRoute := a.body.route

/-- Whether this artifact's emitted text is inside the proved C model. -/
def Artifact.coveredByProvedChain (a : Artifact) : Bool :=
  a.body.coveredByProvedChain

/-- **The exact bytes handed to `ccomp`**, as this package emits them.

`none` when emission fails, which makes `receiptBinds` refuse the receipt: an
artifact that cannot be emitted cannot be attested.

**The kernel evaluates this.**  That is what makes `receiptBinds … = true` a
`decide +kernel` rather than an axiom, so a consumer never has to assert the
digest of the emitted C out of band.  Getting there meant removing five kinds
of obstruction, all of which are the same mistake in different clothes — a
definition the kernel refuses to unfold:

* `partial` in the C emitter and the two validators (`CType.emit`,
  `CExpr.emit`, `emitStatements`, `emitStatement`, `validateType`,
  `validateExpr`, `validateStatements`, `collectLabels`), plus
  `CCIR.CCType.toString`, `C.CType.supportedBy` and `Lower.lowerCompoundType`.
  All are now structural, recursing through a `List` companion on `.toList` of
  the nested `Array`;
* the **derived `BEq`** on `CCIR.CCType` and `C.CType` — `deriving BEq` on an
  inductive that nests through `Array` compiles to well-founded recursion, and
  both validators compare types constantly.  Written out structurally;
* **`Subarray`'s `ForIn`**, reached by the `blocks[:index]` and
  `functions[:index]` duplicate scans in `CCIR/Validate.lean`.  `Array`'s
  `ForIn` reduces; `Subarray`'s does not;
* **`String.replace`** (`WellFounded.opaqueFix`), used to split `*/` inside an
  emitted comment.  Replaced by a structural character walk.

None of it changed a byte of the emitted C, and none of it changed this
standard.  See `docs/use-case-3-attested-run-receipts.md` for the measurements
and for where the remaining kernel cost actually sits (the `ReceiptCrypto`
instance over `RunReceipt.payload`, not the emitter). -/
def Artifact.source? (a : Artifact) : Option String :=
  (emitFor a.body a.mainC).toOption

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

/-- `receiptBinds`, additionally demanding that the emitted text be covered by
the proved C model.  Use this when you want the chain with no unmechanised step
in it; both routes can satisfy it, and on the rolled route the extra clause is
a decidable, program-sized side condition.  See
`ArtifactBody.coveredByProvedChain`. -/
def receiptBindsProved (crypto : ReceiptCrypto) (artifact : Artifact)
    (kind : AttestationKind) (params : String) (nonce : String) (value : Int)
    (r : RunReceipt) : Bool :=
  artifact.coveredByProvedChain
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
    ∃ source, emitFor artifact.body artifact.mainC = .ok source
      ∧ r.programHash = crypto.digest.hashHex source := by
  obtain ⟨⟨source, hs, hd⟩, _⟩ := receiptBinds_sound h
  refine ⟨source, ?_, hd⟩
  unfold Artifact.source? at hs
  cases he : emitFor artifact.body artifact.mainC with
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

/-- The strict form implies the plain one, and additionally gives coverage by
the proved C model — which, unlike before, both routes can have. -/
theorem receiptBindsProved_sound {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {value : Int}
    {r : RunReceipt}
    (h : receiptBindsProved crypto artifact kind params nonce value r = true) :
    artifact.coveredByProvedChain = true
      ∧ receiptBinds crypto artifact kind params nonce value r = true := by
  simp only [receiptBindsProved, Bool.and_eq_true] at h
  exact h

end LeanCompCert.Attest
