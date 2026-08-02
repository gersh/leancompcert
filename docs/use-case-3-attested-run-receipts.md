# Use case 3 — Attested run receipts

> **Vocabulary.** A *receipt* is a signed record that a binary ran and reported
> a value. *Binding* a receipt means checking, in Lean's kernel, that it is
> about the C text this package emits for your computation. *Admitting* a run
> means asserting that the execution the receipt describes really happened —
> the one thing no proof establishes.

**You are here because:** your computation is too large for the kernel even
after chunking, you want more than `native_decide`'s "trust Lean's compiler and
runtime", and you want the thing you trust to be *named, narrow, and visible in
`#print axioms`*.

Read [use case 1](use-case-1-verified-native-decide.md) first. If your
computation fits the kernel, do that instead: it needs no receipt and admits
nothing.

## The gap this closes

The package proves a forward chain, all of it machine-checked:

```text
reference Lean function
  ↕ your equivalence lemma
Program.denote
  ↕ Program.evalCC_compile
CCIR trace
  ↕ lowerSequence_correct  →  Computation.result_preserved
restricted-C model of the emitted statements
  ↕ CompCert (Coq)
assembly
```

Separately, an attestation service can sign "a binary with hash `H` ran and
printed `v`". Neither half holds the join: nothing said that the binary whose
run was attested is the compilation of the C whose semantics were proved. A
signed receipt over a real computation therefore discharged *nothing*.

The join is a decidable fact:

> `receipt.programHash = digest (the C this package emits for this computation)`

`Attest.receiptBinds` is that check, together with the well-formedness,
freshness, regime and signature clauses around it. Composing it with the
forward chain is `Attest.returns_of_receipt`, and it introduces **no axiom in
this package**.

It is affordable because of `emitRolled`: a 10⁷-iteration loop is a ~2 KB
artifact, so the digest is a few dozen compression blocks. The check's cost is
the *source* size and is independent of how long the artifact ran.

## The five pieces

| piece | where | what it is |
| --- | --- | --- |
| `RunReceipt` | `LeanCompCert/Attest/Receipt.lean` | the signed record |
| `Artifact` | same | a computation, an emission route, a `main` |
| `receiptBinds` | same | the decidable check, total and fail-closed |
| `RunAdmission` | `LeanCompCert/Attest/Admission.lean` | the empirical premise, **assumed** here |
| a discharger | `Trusted/LocalReceipt.lean`, or `gpu_prover` | one named axiom, opted into |

## Step by step

### 1. Register the certificate with a certified value

Exactly the `check-native` registration from use case 1, plus the constant:

```lean
def nativeCerts : List NativeCheck.Cert := [
  { name := "demo"
    emitted := MyProject.emittedC
    certifiedValue := some (MyProject.expectedValue : Nat) }
]
```

Build the `main` from that same value:

```lean
def mainC : String := Attest.selfCheckMain "l_MyProject_demo" expectedValue
```

⚠ Do not spell the constant out twice. If the `main` tests one number and the
receipt records another, the Lean-side check still passes — the receipt and the
proof site agree with each other while the artifact tested something else.
Deriving both from one value closes that by construction, and the `main` is
inside the hashed text, so `programHash` pins the constant the binary tested.

### 2. Generate a key and attest

```console
$ lake exe myproject attest-keygen
wrote .lake/build/attest/key.pem
public key (SEC1 uncompressed): 04e39bf78…

$ lake exe myproject attest
[run] demo: … native check passed; receipt .lake/build/native-check/receipts/demo.receipt
```

Caching is unchanged: a certificate whose generated C has not changed and whose
receipt still matches is neither recompiled nor re-signed.

Options: `--key PATH`, `--campaign NAME`, `--nonce HEX64` (pin the challenge; a
receipt quoting a different one is discarded and the artifact re-runs),
`--params FILE` (the canonical inputs; absent means the empty input, which is
right for a closed certificate), `--receipts DIR`.

### 3. Verify it out of band

```console
$ lake exe myproject verify-receipt .lake/build/native-check/receipts/demo.receipt --cert demo
  ok   schema leancompcert-receipt/1
  ok   verdict agrees
  ok   field shapes
  ok   programHash matches freshly emitted C (209d0523fbbb…)
  ok   signature verifies under 04e39bf78498…
  ok   route straight-line
  ok   value 28707
```

This re-emits the C and re-derives the digest, so it checks the same join
`receiptBinds` checks. It is a *convenience*, not the proof.

`--lean IDENT` additionally prints the `RunReceipt` term to paste into your
certificate file. A receipt belongs in your source, like the certified
constant: a reviewer reads it in the diff and the kernel re-checks every clause
against it.

### 4. Supply a `ReceiptCrypto`

The package parameterises over SHA-256 and ECDSA P-256 rather than shipping
copies of them. Supply the ones from `gpu_prover`, which are axiom-free,
`native_decide`-free, executable Lean:

```lean
import SparkInterval.Certificate.P256
open LeanCompCert.Attest SparkInterval.Certificate

def sparkCrypto : ReceiptCrypto := {
  digest := { name := "sha256", hashHex := SHA256.digestString }
  signature := { name := "ecdsa-p256-sha256", verify := P256.verifySha256 }
}

theorem sparkCrypto_selfTested : ReceiptCrypto.SelfTested sparkCrypto := by
  constructor <;> decide +kernel
```

`SelfTested` is nine known-answer tests: three FIPS 180-4 SHA-256 vectors, one
accepting ECDSA vector, and three rejecting ones (wrong message, wrong key,
altered signature). **Measured: 9.7 s for the whole set under `decide +kernel`,
axioms `[propext, Classical.choice, Quot.sound]`.**

The dischargers require it, so a garbage instance — `⟨fun _ => "0…0",
fun _ _ _ => true⟩`, under which `receiptBinds` accepts everything — cannot be
used to admit a run. `SelfTested` is a sanity gate, not a correctness proof: it
rules out the constant functions and the obvious mistakes, and no finite set of
vectors could do more.

### 5. Bind the receipt, in Lean

```lean
open LeanCompCert.Attest

def artifact : Artifact := {
  computation := MyProject.computation
  route := EmissionRoute.provedStraightLine
  mainC := MyProject.mainC
}
```

`Artifact` is **pure data with no proof field**. The C text is not something
you assert — it is `Artifact.source?`, computed by the package's own emitter —
so there is nothing here you can get wrong.

Then:

```lean
theorem demo_binds :
    receiptBinds sparkCrypto artifact AttestationKind.localSignature ""
      nonce ((expectedValue : Nat) : Int) demoReceipt = true := by
  decide +kernel
```

`receiptBinds` is a `Bool` every clause of which the kernel reduces, including
`Artifact.source?` — the C emitter and the CCIR and C validators are structural
and unfold.  There is no axiom here, and no out-of-band step: the kernel
re-emits the C text and compares its digest itself.

### 6. Discharge `RunAdmission`

Local key:

```lean
import LeanCompCert.Trusted.LocalReceipt   -- ← adds ONE named axiom

theorem demo_certificate : MyProject.referenceSum = MyProject.expectedValue :=
  LeanCompCert.Trusted.decide_of_localReceipt MyProject.decision rfl
    sparkCrypto_selfTested demo_binds
```

```console
#print axioms demo_certificate
-- [propext, Classical.choice, Quot.sound,
--  LeanCompCert.Trusted.localSignedRun_admits]
```

Enclave: `gpu_prover` supplies its own axiom with its own name, and its
receipts carry `AttestationKind.enclaveQuote`. `receiptBinds` refuses a
`localSignature` receipt wherever an `enclaveQuote` was demanded and the
reverse, so the two regimes cannot be confused by accident, and a downstream
`#print axioms` names which one a theorem rests on.

## What you are trusting

`RunAdmission`'s docstring is the authority; in short, a discharger asserts, of
the world and not of Lean:

1. that a machine really executed a binary produced by compiling the C text
   whose digest is `programHash`, with the CompCert install named by
   `toolchain`, on the inputs whose digest is `paramsHash`;
2. that the execution terminated normally and reported `value`;
3. that `publicKey` is a key you are willing to treat as speaking for that
   execution;
4. that the value the binary reported is the value the proved C model returns.

Nothing in that list is provable in Lean, and no cryptography makes it so. A
signature establishes who is speaking, never that what they said is true.

### Locally signed receipts, honestly

**What a local receipt buys.** Tamper-evidence. A receipt binds, in one signed
blob, the program digest, the input digest, the CompCert identity, the machine
identity, a nonce, a timestamp and the value. So: it cannot be edited after the
fact; it cannot be presented for a different program; a stale receipt cannot be
passed off as fresh; a receipt made under one CompCert install cannot be reused
under another; and a disagreeing or abnormally terminated run produces no
admissible receipt at all. That turns "a file in `.lake/build` says the check
passed" into an auditable record that an accidental copy, a stale cache, a
rebuilt toolchain or a post-hoc edit will visibly break.

**What it does not buy.** It does not establish that the computation was
performed or that the machine was honest. The key sits on the machine that ran
the binary; anyone who can read it can sign any value. A local receipt is
auditable bookkeeping *for a machine you already trust*. It is **not**
equivalent to enclave attestation and must never be described as such.

The distinction is structural: different `AttestationKind`, different axiom,
different name, different module. Grep an axiom listing for
`localSignedRun_admits` and you have found every theorem whose evidence is a
signature the running machine made about itself.

### Compared with `native_decide`

`native_decide` admits Lean's *unverified* compiler and runtime, opaquely, with
one axiom that says "whatever the compiled evaluator printed is true". This
admits CompCert's machine-checked semantic-preservation proof plus the
assembler and linker, through a named axiom whose premise is an inspectable
record the kernel re-checks — and, on the `provedStraightLine` route, the C
whose semantics this package proved. Strictly smaller and far better
understood.

It is not free: the computation has to be expressible in the proved fragment.
Do not present the replacement as mechanical.

## The two emission routes

`EmissionRoute.provedStraightLine` emits the `Computation`'s own lowered
statements. `Computation.result_preserved` is about exactly those statements,
so the chain from "the C model returns `v`" back to the CCIR computation is
proved end to end.

`EmissionRoute.rolledLoop` emits `emitRolled`'s `while`-loop form. This is what
makes a 10⁷-iteration computation a 2 KB artifact. ⚠ **It is not covered by the
proved C model**: `Proof.PureSemantics.evalCStmt` interprets assignments only,
so a `whileLoop` evaluates to `none` and there is no `result_preserved` for the
rolled unit. What *is* proved is `Verified.Reflect.rolledTrace_eq_augmented`,
at the CCIR level. On the rolled route a discharger's `RunAdmission.denotes`
therefore bundles one further unmechanised step.

Use `receiptBindsProved` when you want the route with no such step;
`receiptBinds` accepts both and records which in the signed payload.

## The receipt format

A receipt file is the signed payload followed by the signature — sixteen
newline-separated fields, then one more line:

```text
leancompcert-receipt/1
local-signature
rolled-loop
leancompcert-native-check
sha256
1d9a2280d979362d9f94361df8147de9d4c29212517c50db6335b5313ccf9622   ← programHash
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855   ← paramsHash
The CompCert C verified compiler, version 3.17
fd72dd77064ec8cb072b75748d95c11143605f146f272429a032888d0a540a87   ← ccomp identity
freestanding aarch64 6591516745511624930 GNU assembler … GNU ld …
177635701698593418
agrees
machine id 7af66f30966a49b6886e00e2fce4b42f
a99fa4b4499a52c4c16843289722d0977a188387745ba5c869605e624558aa23   ← nonce
2026-08-01T22:25:00Z
041333e51b8fd744…                                                  ← public key
356c9a9e18130cd7…                                                  ← signature
```

Line-oriented rather than JSON: every field is a digest, a bounded label, a
decimal integer or an enumeration label, none of which can contain a newline,
so the encoding needs no escaping and the bytes under signature are exactly the
file's first sixteen lines. `RunReceipt.payload` is the same function the
kernel check uses, so there is no second serialisation to drift out of step.

The toolchain digest is a SHA-256 of `NativeCheck.compcertIdentity`'s output —
a digest of the `ccomp` binary *and* the full text of its `compcert.ini`. A
version string alone does not identify a compiler: `ccomp -version` prints no
architecture, so an `aarch64` install and an `x86_64` one are indistinguishable
by it.

## The kernel-evaluability link, closed

**`receiptBinds … = true` is now a `decide +kernel`, with no axiom.**

It used to be one named axiom per artifact, because evaluating `Artifact.source?`
reached `partial` definitions in the emitter and the validators.  Those are
structural now, and so are three other things the kernel could not unfold and
which the original diagnosis missed:

* the derived `BEq` instances on `CCIR.CCType` and `C.CType` — `deriving BEq`
  on an inductive that nests through `Array` compiles to well-founded
  recursion, and both validators compare types constantly;
* `Subarray`'s `ForIn` instance, reached by the `fn.blocks[:index]` and
  `program.functions[:index]` duplicate scans in `CCIR/Validate.lean`;
* `String.replace`, used to split `*/` inside an emitted comment, which is
  compiled to `WellFounded.opaqueFix`.

Nothing about the standard changed: same `receiptBinds`, same theorems, same
receipts, same emitted C — byte for byte, checked against the recorded digests
of all fourteen certificates.

Measured on `LeanCompCertTests/Attest.lean`'s artifact (a `Computation`
emitting 1121 bytes of C), Lean 4.32.1, `decide +kernel`:

| goal | wall | peak RSS |
| --- | --- | --- |
| `(Lower.compileProgram .portable ⟨#[computation.fn]⟩).toOption.isSome = true` | 5 s | 0.7 GB |
| `artifact.source?.isSome = true` | 4 s | 0.7 GB |
| `programHash = digest source` — **the join** | 10 s | 2.6 GB |
| `receiptBinds … = true`, whole check | 54 s | 12.3 GB |

The gap between the third row and the fourth is **not** the emitter.  It is the
`ReceiptCrypto` instance applied to `RunReceipt.payload`: reducing
`payload.length` alone costs 28 s and 4.9 GB, because `payload` is built by
`String.intercalate` and Lean 4.32's `String` is UTF-8 bytes, so every
character read walks an append chain.  That cost is the receipt format's and
the instance's, not the artifact's — it does not grow with the size of the
computation, and the shipped kernel tests therefore stop at the join.

## Where the pieces live

* `LeanCompCert/Attest/Crypto.lean` — the interface and its known-answer tests
* `LeanCompCert/Attest/Receipt.lean` — `Artifact`, `RunReceipt`,
  `receiptBinds`, and what a passing check forces
* `LeanCompCert/Attest/Admission.lean` — `RunAdmission` and the composition
* `LeanCompCert/Attest/Tool.lean` — keys, signing, the on-disk format
* `LeanCompCert/Trusted/LocalReceipt.lean` — the local-key axiom
* `LeanCompCertTests/Attest.lean` — the refusals, in the kernel
* `examples/consumer/` — the whole loop from an external project

## Relationship to `Trusted/Evidence.lean`

The older `RunEvidence` record is an *unsigned* well-formedness and binding
check, resolved out of band by `LeanCompCert/Trusted/Resolve.lean` and closed
by the `evidenced_decide` tactic. It binds a record to a program by the
program's identity in Lean rather than by a digest of the emitted C, and it has
no cryptography.

`Attest` is the signed standard: it binds by digest, it carries a signature,
and it distinguishes regimes. The two coexist — `evidenced_decide` is the
convenient local workflow, receipts are what you hand to someone else.
