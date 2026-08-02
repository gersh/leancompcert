import LeanCompCert.Verified.Package
import LeanCompCert.Verified.EarlyExit
import LeanCompCert.Attest

/-!
# External consumer demo: a masked cube sum with a proved comparison

This project depends on `leancompcert` as an ordinary Lake dependency and
states its own bounded computation using only the public API
(`Verified.Reflect`, `Verified.Decide`, `Verified.EarlyExit`, and the
`Lower.compileProgram` emission entry point).

The certified quantity is

```
Σ_{k < 64} (m(k) + [m(k) < 512]),   m(k) = ((k+1)³ mod 2⁶⁴) &&& 1023
```

i.e. for each `k` the low ten bits of the cube plus an extra `1` whenever
that masked value is below `512` — exercising multiplication, bitwise
masking, and a proved unsigned comparison in one loop body. The expected
value `28707` was computed independently (bignum arithmetic, outside the
register machine).

Packaging follows the upstream `Testing.FixedPointCertificate` pattern:
`Program.toComputation` provides structural well-formedness and lowering
evidence, so the kernel evaluates only the program's denotation and the
reference fold.
-/

namespace Consumer

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

set_option maxRecDepth 800000

def count : Nat := 64
def mask : Nat := 1023
def threshold : Nat := 512
def expectedValue : Nat := 28707

/--
Per-iteration body (`n = idx + 1`): cube, mask to the low ten bits,
compare against the threshold (a proved comparison producing `0`/`1`),
accumulate both.
-/
def body : List Instr := [
  .binop 1 .add .idx (.lit 1),
  .binop 2 .mul (.reg 1) (.reg 1),
  .binop 3 .mul (.reg 2) (.reg 1),
  .binop 4 .band (.reg 3) (.lit mask),
  .binop 5 .lt (.reg 4) (.lit threshold),
  .binop 0 .add (.reg 0) (.reg 4),
  .binop 0 .add (.reg 0) (.reg 5)
]

def program : Program := {
  regCount := 6
  loopCount := count
  init := []
  body := body
  epilogue := []
  output := 0
}

theorem program_wf : program.WF := by decide

/-- Structural packaging from the public API — no trace-sized obligations. -/
def computation : Computation :=
  program.toComputation "Consumer.demo" program_wf

/-- The reference fold: direct bignum arithmetic, independent of the
register machine. -/
def referenceSum : Nat :=
  (List.range count).foldl
    (fun acc k =>
      let masked := (((k + 1) ^ 3) % (2 ^ 64)) &&& mask
      acc + masked + (if masked < threshold then 1 else 0))
    0

theorem returns_iff :
    computation.Returns ((expectedValue : Nat) : Int) ↔
      program.denote = some expectedValue :=
  toComputation_returns program "Consumer.demo" program_wf expectedValue

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := ((expectedValue : Nat) : Int)
  specification := returns_iff.trans (by decide +kernel)
}

/--
The consumer's certificate: the masked cube sum equals `28707`, discharged
through the proved fragment; the kernel evaluates only `program.denote`
and the reference fold.
-/
theorem demo_certificate : referenceSum = expectedValue :=
  Decision.prove decision (returns_iff.mpr (by decide +kernel))

/-- The generated-C model agrees, via the structural chain alone. -/
theorem generated_c_model_returns :
    computation.targetResult = some ((expectedValue : Nat) : Int) := by
  rw [computation.result_preserved]
  exact returns_iff.mpr (by decide +kernel)

/-! ## Equivalence-library surface

A type-checked use of `Verified.EarlyExit`: a step function that never
fails makes the predicated fold accept, via the public
`foldP_accepts_iff` characterization. -/

theorem addStep_total (acc : Nat) (indices : List Nat) :
    ∃ result,
      EarlyExit.foldE (fun a k => some (a + k)) acc indices = some result := by
  induction indices generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons index rest ih => exact ih (acc + index)

theorem foldP_accepts_total_step (indices : List Nat) :
    (EarlyExit.foldP (fun a k => some (a + k)) (0, true) indices).2 = true :=
  (EarlyExit.foldP_accepts_iff _ indices 0).mpr (addStep_total 0 indices)

/-! ## Emission -/

/-- The self-checking `main`, built from `expectedValue` rather than from a
literal spelled out a second time.  `Attest.selfCheckMain` exists so that the
constant the binary tests and the constant a receipt records cannot drift
apart; the `main` is inside the hashed text, so `programHash` pins it. -/
def mainC : String :=
  Attest.selfCheckMain "l_Consumer_demo" expectedValue

/-- The complete C translation unit for the computation plus a `main`
that exits `0` exactly when the native run reproduces the certified
value. -/
def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[computation.fn] }
  pure (source ++ mainC)

/-! ## Attested runs, from the public API alone

`Attest.Artifact` is pure data: the computation, the emission route, and the
`main`.  The C text is not something this file asserts — it is
`Artifact.source?`, computed by the package's own emitter — so there is nothing
here that can be got wrong, and a receipt binds to that text or to nothing.

Producing a receipt is `consumer attest`; checking one is
`consumer verify-receipt FILE --cert demo`.  Both go through
`LeanCompCert.NativeCheck`, which is the same five-line registration this
project already used for `check-native`.

The Lean-side check is `Attest.receiptBinds`, and closing it needs two things
this example deliberately does not fabricate:

* a `ReceiptCrypto` — SHA-256 and ECDSA P-256 as executable Lean.  The package
  parameterises over them rather than shipping a second copy; `gpu_prover`'s
  `SparkInterval.Certificate.{SHA256,P256}` are the intended implementations
  and satisfy `ReceiptCrypto.SelfTested` (measured: 9.7 s under
  `decide +kernel`, axiom-free).
* `RunAdmission` — the empirical premise, discharged by
  `LeanCompCert.Trusted.localSignedRun_admits` for a local key or by
  `gpu_prover`'s enclave axiom.  Both show up by name in `#print axioms`.

With those two supplied, the certified statement below follows from a receipt
by `Attest.decide_of_receipt` — the theorem is stated here against arbitrary
hypotheses, so this file stays axiom-free while showing exactly the shape a
campaign site has.

Note that only the *second* of those is an axiom.  With a concrete
`ReceiptCrypto` in hand, `bound` is `by decide +kernel`: the kernel re-emits
the C for this artifact and checks the receipt's `programHash` against its
digest itself.  There is no per-artifact axiom and no out-of-band step. -/

open LeanCompCert.Attest in
/-- The artifact this project attests: the demo computation, the straight-line
route, and the self-checking `main` above. -/
def artifact : Artifact := {
  computation
  route := EmissionRoute.provedStraightLine
  mainC
}

open LeanCompCert.Attest in
/-- **The consumer-side shape of an attested campaign.**

Read it as: given a crypto bundle that passes its known-answer tests, a receipt
that binds to *this* artifact and *this* value, and an admitted run, the
consumer's own theorem follows.  Nothing here is admitted; the hypotheses are
where a deployment plugs in its two axioms. -/
theorem demo_certificate_of_receipt
    (crypto : ReceiptCrypto) (receipt : RunReceipt) (nonce : String)
    (bound : receiptBinds crypto artifact AttestationKind.localSignature ""
      nonce ((expectedValue : Nat) : Int) receipt = true)
    (admitted : RunAdmission crypto artifact receipt) :
    referenceSum = expectedValue :=
  decide_of_receipt decision rfl bound admitted

end Consumer
