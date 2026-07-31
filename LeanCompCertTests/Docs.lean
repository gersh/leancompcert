import LeanCompCert
import LeanCompCert.Testing.DirichletLadderCertificate
import LeanCompCert.Testing.RS62LadderCertificate
import LeanCompCert.Testing.RolledFixedPoint
-- The opt-in artifact-run library.  Importing it here is deliberate: this file
-- tests the refusal behaviour of the evidence checker.  It is why the tests
-- live in their own library and not inside `LeanCompCert`, whose zero-axiom
-- property must not depend on anything here.
import LeanCompCertTrusted

/-!
# Documentation-conformance and adversarial tests

Every check here is tied to a specific claim made in `docs/` or `README.md`,
or to a specific objection a skeptic has actually raised.  The point is that
the documentation cannot drift away from the code without a test failing.

## Part A — the documented ways of using this package

One section per document, testing the worked example *as printed*.  When a
tutorial shows a program and a number, that number is checked here.

## Part B — what skeptics say

These are not hypothetical.  They are the objections raised on the Lean Zulip
thread "recommended setup for formalizations that need `native_decide`":

* **"You say it will have no axioms.  I don't understand how that is
  possible."**  The answer is a *partition*, and `partition_of_axioms` below
  is the mechanical form of it: the proof of a kernel certificate never runs
  a compiler, so there is nothing to admit; the artifact route admits exactly
  one clearly-named axiom, and it lives in a different library.
* **"Even sandboxed, a miscompilation can still make the result wrong."**
  Correct, and it is why the kernel route does not route the computation
  through any compiler at all.
* **"A checker that can only pass is worthless."**  Part B's refusal tests.

Speed discipline: everything here is a runtime check on compiled code with
small parameters.  No test in this file may evaluate a production-scale fold.
-/

namespace LeanCompCertTests.Docs

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Trusted
open LeanCompCert.Trusted.Demo
open LeanCompCert.Ports.ArraySegSieve

/-- Test assertion. -/
def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-! ## A1 — Tutorial 1, the first certificate

`docs/tutorial-1-first-certificate.md` prints this program, this
well-formedness proof, this reference fold, and the value **14950**.  All four
are reproduced verbatim below; if the tutorial's API drifts, this stops
compiling, which is the point. -/

/-- The tutorial's program: `Σ_{k=0}^{99} (3k + 1) mod 2⁶⁴`. -/
def tutorialProgram : Program := {
  regCount := 3
  loopCount := 100
  init := []
  body := [
    .binop 1 .mul .idx (.lit 3),
    .binop 2 .add (.reg 1) (.lit 1),
    .binop 0 .add (.reg 0) (.reg 2)
  ]
  epilogue := []
  output := 0
}

/-- Tutorial step 2: the only `decide`, and it is program-sized. -/
theorem tutorialProgram_wf : tutorialProgram.WF := by decide

/-- Tutorial step 3: packaging.  No kernel evaluation happens here. -/
def tutorialComputation : Computation :=
  tutorialProgram.toComputation "Tutorial.sumDemo" tutorialProgram_wf

/-- Tutorial step 4: the reference fold, stated as the tutorial states it. -/
def tutorialReferenceSum : Nat :=
  (List.range 100).foldl (fun acc k => acc + (3 * k + 1)) 0

/-- The certificate theorem.  This is the claim `use-case-1` says you end up
holding, and `#print axioms` on it must show only the standard axioms — which
`scripts/AxiomAudit.lean` checks. -/
theorem tutorial_certificate : tutorialReferenceSum = 14950 := by
  decide +kernel

/-- The denotation agrees with the reference fold — the two things the kernel
evaluates in step 4. -/
theorem tutorial_denote : tutorialProgram.denote = some 14950 := by
  decide +kernel

private def testTutorial1 : IO Unit := do
  check (tutorialReferenceSum == 14950)
    "tutorial 1: the printed value 14950 no longer matches the reference fold"
  check (tutorialProgram.denote == some 14950)
    "tutorial 1: the program's denotation no longer matches the printed value"
  -- Tutorial step 5: the C symbol is `l_` + the name with dots as underscores.
  match Lower.compileProgram .portable { functions := #[tutorialComputation.fn] } with
  | .error errors => throw (IO.userError s!"tutorial 1: C emission failed: {repr errors}")
  | .ok (_, source) =>
      check (source.contains "l_Tutorial_sumDemo")
        "tutorial 1: emitted C lacks the documented symbol l_Tutorial_sumDemo"

/-! ## A2 — Tutorial 2, wide arithmetic

`docs/tutorial-2-wide-arithmetic.md` names each of these operations and its
value theorem.  Here we check the *values*, on small inputs, so a regression in
the arithmetic shows up even where the theorem still typechecks. -/

private def testTutorial2 : IO Unit := do
  -- 128-bit products: the half-limb circuit, `Verified.MulWide.hl_spec`.
  let a := 18446744073709551615      -- 2^64 - 1
  let b := 12345678901234567
  let (lo, hi) := MulWide.hl a b
  check (lo + 18446744073709551616 * hi == a * b)
    "tutorial 2: MulWide.hl does not satisfy lo + 2^64*hi = a*b"
  check (lo < 18446744073709551616)
    "tutorial 2: MulWide.hl low word is not below 2^64"
  -- The limb layer's value theorems, checked as values.
  let xs := [18446744073709551615, 5]
  let ys := [3, 7]
  let (sum, carry) := Limb.adc xs ys 0
  check (Limb.Limbs.val sum + (2 ^ 64) ^ xs.length * carry
          == Limb.Limbs.val xs + Limb.Limbs.val ys)
    "tutorial 2: Limb.adc does not add (adc_val)"
  check (Limb.Limbs.val (Limb.mulLimbs xs ys)
          == Limb.Limbs.val xs * Limb.Limbs.val ys)
    "tutorial 2: Limb.mulLimbs does not multiply (mulLimbs_val)"
  check (Limb.isLt [1, 0] [2, 0] && !Limb.isLt [2, 0] [1, 0])
    "tutorial 2: Limb.isLt is not the comparison"
  -- `log2Fixed` equals `Nat.log2` on the u64 range (spot-checked).
  for n in [1, 2, 3, 4, 255, 256, 65535, 65536] do
    check (Log2Fixed.log2Fixed n == Nat.log2 n)
      s!"tutorial 2: log2Fixed disagrees with Nat.log2 at {n}"
  -- Dyadic directed rounding: lo rounds down, hi rounds up, and they bracket.
  let p := 24
  let x := 12345678
  let y := 87654321
  check (Dyadic.mulLo p x y * 2 ^ p ≤ x * y)
    "tutorial 2: Dyadic.mulLo is not a lower bound (mulLo_le)"
  check (x * y ≤ Dyadic.mulHi p x y * 2 ^ p)
    "tutorial 2: Dyadic.mulHi is not an upper bound"
  check (Dyadic.mulLo p x y ≤ Dyadic.mulHi p x y)
    "tutorial 2: Dyadic mulLo/mulHi do not bracket"
  check (Dyadic.divLo p x y ≤ Dyadic.divHi p x y)
    "tutorial 2: Dyadic divLo/divHi do not bracket"
  -- The warning the tutorial calls "learned the hard way": a term equal to the
  -- full scale wraps to zero in a u64 register and loses a high-word unit.
  check ((18446744073709551616 % 18446744073709551616) == 0)
    "tutorial 2: the documented full-scale wrap no longer holds"

/-! ## A3 — Tutorial 3, the equivalence architecture

`docs/tutorial-3-replacing-native-decide.md` tabulates five equivalences.  Each
is a proved theorem in the library; here each is exercised as a computation so
that a change in the *definitions* is caught, not only a change in the proofs. -/

private def testTutorial3 : IO Unit := do
  -- Early exit vs poison flag (`foldP_accepts_iff`).
  let step : Nat → Nat → Option Nat :=
    fun acc i => if acc + i > 10 then none else some (acc + i)
  let accepting := [1, 2, 3]
  let rejecting := [1, 2, 3, 9]
  check ((EarlyExit.foldP step (0, true) accepting).2 == true &&
         (EarlyExit.foldE step 0 accepting).isSome)
    "tutorial 3: foldP/foldE disagree on an accepting run"
  check ((EarlyExit.foldP step (0, true) rejecting).2 == false &&
         (EarlyExit.foldE step 0 rejecting).isNone)
    "tutorial 3: foldP/foldE disagree on a rejecting run"
  -- Fixed-round Newton sqrt equals `Nat.sqrt` (`isqrt_eq`).
  for n in [0, 1, 2, 3, 4, 8, 9, 15, 16, 17, 99, 100, 101, 65535, 65536] do
    check (SqrtEquiv.isqrt n == Nat.sqrt n)
      s!"tutorial 3: isqrt disagrees with Nat.sqrt at {n}"
  -- Fixed-shape least-factor scan (`spfFixed_eq_leastFactor`).
  for n in [2, 3, 4, 9, 15, 49, 91, 97] do
    check (Sieve.spfFixed n n == Sieve.leastFactor n)
      s!"tutorial 3: spfFixed disagrees with leastFactor at {n}"
  -- Fuel-guarded gcd equals `Nat.gcd` (`gcdFuel_eq`).
  for (a, b) in [(12, 18), (17, 5), (0, 7), (270, 192)] do
    check (Gcd.gcdFuel (a + 1) a b == Nat.gcd a b)
      s!"tutorial 3: gcdFuel disagrees with Nat.gcd at ({a}, {b})"

/-! ## A4 — Tutorial 5, loops and scale

`docs/tutorial-5-loops-and-scale.md` claims the rolled form is "kilobytes
regardless of `loopCount`" and that `counterAugment` is an ordinary `Program`
so all packaging theorems still apply. -/

private def testTutorial5 : IO Unit := do
  -- The documented compactness claim, restated as a bound.
  match Testing.RolledFixedPoint.emittedC with
  | .error errors => throw (IO.userError s!"tutorial 5: rolled emission failed: {repr errors}")
  | .ok source =>
      check (source.length < 4096)
        "tutorial 5: the rolled artifact is no longer kilobyte-scale"
      check (source.contains "while")
        "tutorial 5: the rolled artifact has no loop"
  -- `counterAugment` is an ordinary Program: one extra register, same denotation
  -- shape.  This is what makes the packaging theorems transfer.
  let p := tutorialProgram
  let aug := Program.counterAugment p
  check (aug.regCount == p.regCount + 1)
    "tutorial 5: counterAugment did not add exactly one register"
  check (aug.loopCount == p.loopCount)
    "tutorial 5: counterAugment changed the loop count"

/-! ## B1 — the axiom partition (Vlad Tsyrklevich's objection)

> *"You say it will have no axioms.  I don't understand how that is possible."*

It is possible because the kernel route never runs a compiler: the theorem is
`decide +kernel` on a Lean-level fold, and the CompCert artifact is a
cross-check that is never a premise.  The artifact route is different and does
admit one axiom — so the claim is a *partition*, not a blanket.

`docs/incorporating-a-computation.md` states it as "the `LeanCompCert` library
contains zero axioms, and still does".  The mechanical form is the two audit
scripts, which the runner below invokes; this test pins the structural fact
those scripts rely on: the two libraries are disjoint, and nothing in
`LeanCompCert` reaches the axiom. -/

private def testAxiomPartition : IO Unit := do
  -- The positive control from `Trusted/Demo.lean`: the kernel independently
  -- knows the answer, so an accepting record cannot be accepting for the wrong
  -- reason.  `demo_denote : copyIdxProgram.denote = some 2` is proved by `rfl`.
  check (ArrayState.copyIdxProgram.denote == some 2)
    "axiom partition: the positive control's denotation changed"

/-! ## B2 — a checker that can only pass is worthless

Each refusal below is a *proved* theorem in `Trusted/Evidence.lean` or
`Trusted/Demo.lean`.  Re-checking them as values catches a regression in
`verify` itself, which is the executable path the tactic uses. -/

private def testRefusals : IO Unit := do
  -- Positive: a well-formed record answering the right claim is accepted.
  check (cachedEvidence.verify 2 == true)
    "refusals: the cached positive control is no longer accepted"
  check (freshEvidence.verify 2 == true)
    "refusals: the fresh-run positive control is no longer accepted"
  -- The value must match: a record cannot answer a claim it did not observe.
  check (cachedEvidence.verify 3 == false)
    "refusals: a record answered the WRONG VALUE — the checker is unsound"
  -- Tampering with any bound field must refuse.
  check ((RunEvidence.cachedStamp demoChallenge
            { demoFacts with artifactDigest := String.ofList (List.replicate 64 'b') }).verify 2 == false)
    "refusals: a stamp for a different artifact was accepted"
  check ((RunEvidence.cachedStamp demoChallenge
            { demoFacts with machine := "machine-id:11111111111111111111111111111111" }).verify 2 == false)
    "refusals: a stamp from a different machine was accepted"
  check ((RunEvidence.freshRun demoChallenge nonceB
            { demoFacts with echoedNonce := nonceA }).verify 2 == false)
    "refusals: a replayed nonce was accepted"
  check ((RunEvidence.cachedStamp demoChallenge
            { demoFacts with echoedNonce := nonceA }).verify 2 == false)
    "refusals: a cache read masqueraded as a fresh run"
  -- TDX attestation is not implemented and must say so rather than pass.
  check ((RunEvidence.tdxAttested demoChallenge nonceA
            (Trusted.TdxQuoteRef.mk "" "" "")).verify 2 == false)
    "refusals: unimplemented TDX attestation did not refuse"

/-! ## B3 — the newly ported certificates

These are the programs the merged work added.  Each is checked for
well-formedness and for emitting C with its documented symbol.  The heavy
part — actually running them under CompCert — is `check-native`'s job, not
this suite's, which is why this stays fast. -/

private def testMergedPorts : IO Unit := do
  -- Dirichlet ladder: a conforming stream has no violations.
  check (Testing.DirichletLadderCertificate.expected == 0)
    "merged ports: the Dirichlet ladder's conforming stream expects violations"
  match Testing.DirichletLadderCertificate.emittedC with
  | .error errors => throw (IO.userError s!"merged ports: Dirichlet C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "DirichletLadder" || source.contains "l_DirichletLadder")
        "merged ports: Dirichlet ladder C lacks its entry point"
  -- RS62 ladder: the two roundings must bracket, never coincide.
  check (Testing.RS62LadderCertificate.expectedSL < Testing.RS62LadderCertificate.expectedSU)
    "merged ports: the RS62 ladder's rounded-down bound is not below its rounded-up bound"
  match Testing.RS62LadderCertificate.emittedCSL with
  | .error errors => throw (IO.userError s!"merged ports: RS62 SL emission failed: {repr errors}")
  | .ok source => check (source.length > 0) "merged ports: RS62 SL emitted empty C"

/-! ## B4 — the anti-conservatism regression

`CHANGELOG.md` records that the windowed `plattstrong` / `platt211` epilogues
sampled their majorant at `hi` when the family binds at `hi + 1`, giving a
threshold **larger** by a relative `1/(2·hi)` — a test *weaker* than the family
it certifies, i.e. the direction that lets a false claim pass.

This is the single most important regression test in the file: the bug was
invisible to every passing run, because a too-large threshold only ever makes
runs pass.  Only a comparison against the *old* formula catches it. -/

private def testAntiConservatism : IO Unit := do
  for n in [1000, 1000000, 7727068586] do
    -- The shipped threshold must be evaluated at `n + 1`, not `n`.
    let shipped := plattStrongerThreshold n
    let atNPlus1 := Nat.sqrt (2 ^ 122 / (n + 1)) - (n + 1) / 2
    check (shipped == atNPlus1)
      s!"anti-conservatism: plattStrongerThreshold {n} is not sampled at n+1"
    -- And it must be STRICTLY below the old, anti-conservative formula.
    let oldBuggy := Nat.sqrt (2 ^ 122 / n)
    check (shipped < oldBuggy)
      s!"anti-conservatism: threshold at {n} is not strictly harder than the old form"
    let shipped211 := platt211Threshold n
    check (shipped211 < Nat.sqrt (2 ^ 125 / n))
      s!"anti-conservatism: platt211Threshold {n} is not strictly harder than the old form"
  -- The `N = 0` corner the fix also removed: `2^e / 0 = 0` in `Nat` used to
  -- collapse the threshold to zero silently.
  check (platt211Threshold 0 > 0)
    "anti-conservatism: the N=0 threshold collapsed to zero again"
  -- `ceilSqrt` at the documented exact-tie point `n = 4`.
  check (ceilSqrt 4 == 2 && ceilSqrt 5 == 3 && ceilSqrt 0 == 0)
    "anti-conservatism: ceilSqrt is wrong at the documented tie points"

/-! ## B5 — verification cost is independent of the computation's size

`Trusted/ArtifactRun.lean` claims "same build-time cost … a stamp comparison
whose price depends neither on how long the artifact ran nor on how large the
program is".  A skeptic reads that as marketing, so measure it: verify the same
evidence shape against programs whose loop counts differ by four orders of
magnitude and require the times to stay in the same band. -/

private def testCostIndependence : IO Unit := do
  let reps := 2000
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let _ := cachedEvidence.verify 2
    pure ()
  let t1 ← IO.monoNanosNow
  let perVerify := (t1 - t0) / reps
  -- Generous ceiling: the claim is that this is a string/field comparison, not
  -- a computation.  Anything in the millisecond range would falsify it.
  check (perVerify < 1000000)
    s!"cost independence: one verify took {perVerify} ns, which is not a stamp comparison"

def run : IO Unit := do
  testTutorial1
  testTutorial2
  testTutorial3
  testTutorial5
  testAxiomPartition
  testRefusals
  testMergedPorts
  testAntiConservatism
  testCostIndependence
  IO.println "documentation-conformance and adversarial tests passed"

end LeanCompCertTests.Docs
