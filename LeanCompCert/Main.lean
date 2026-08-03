import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Testing.RolledFixedPoint
import LeanCompCert.Verified.ClightEmit
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ProthCertificate
import LeanCompCert.Testing.ArrayMobiusCertificate
import LeanCompCert.Testing.DirichletLadderCertificate
import LeanCompCert.Testing.ArraySegCertificate
import LeanCompCert.Testing.AbelScanCertificate
import LeanCompCert.Testing.RS62LadderCertificate
import LeanCompCert.Testing.AlgorithmProof
import LeanCompCert.NativeCheck
import LeanCompCert.Attest.LedgerReport

open LeanCompCert

private def usage : String :=
  "lean-compcert 0.2.0\n\n" ++
  "Commands:\n" ++
  "  demo                 print CCIR, interpreter result, and generated C\n" ++
  "  emit-demo-c FILE     write the pure-subset integration program\n" ++
  "  emit-verified-decide-c FILE\n" ++
  "                       write the verified-decision integration program\n" ++
  "  emit-mertens-cert-c FILE\n" ++
  "                       write the Goldbach-style fold-certificate program\n" ++
  "  emit-wide-mertens-cert-c FILE\n" ++
  "                       write the 2^64-scale 128-bit-accumulator certificate\n" ++
  "  emit-squarefree-mertens-cert-c FILE\n" ++
  "                       write the odd-squarefree Mertens (sec. 14.1 shape) certificate\n" ++
  "  emit-reflected-cert-c FILE\n" ++
  "                       write the reflection-bridge certificate program\n" ++
  "  emit-fixedpoint-cert-c FILE\n" ++
  "                       write the 128-bit-product fixed-point certificate\n" ++
  "  emit-rolled-10m-c FILE\n" ++
  "                       write the rolled 10^7-iteration fixed-point checker\n" ++
  "  check-native [--force] [--dir DIR] [--hosted] [--start-dir DIR]\n" ++
  "                       compile every certificate with CompCert and run the\n" ++
  "                       native cross-check; cached by generated-C content hash.\n" ++
  "                       Links freestanding (no libc) via runtime/start/<arch>.S;\n" ++
  "                       --hosted restores the old ccomp/glibc link.\n" ++
  "                       Exit 0 = agrees, 1 = disagrees, other = abnormal\n" ++
  "                       termination (never reported as a disagreement)\n" ++
  "  attest-keygen [--key PATH]\n" ++
  "                       generate a local P-256 signing key.  A receipt it\n" ++
  "                       signs is TAMPER-EVIDENT, not attested: the key sits\n" ++
  "                       on the machine that runs the binaries\n" ++
  "  attest [--key PATH] [--campaign NAME] [--nonce HEX64] [--params FILE]\n" ++
  "         [--receipts DIR] [check-native options]\n" ++
  "                       run the native check and write a signed run receipt\n" ++
  "                       for every certificate that agrees.  Same caching:\n" ++
  "                       a certificate whose C is unchanged and whose receipt\n" ++
  "                       still matches is neither recompiled nor re-signed\n" ++
  "  verify-receipt FILE --cert NAME [--lean IDENT]\n" ++
  "                       re-check a receipt against freshly emitted C: schema,\n" ++
  "                       field shapes, verdict, program digest, signature,\n" ++
  "                       route and value.  --lean prints the RunReceipt term\n" ++
  "                       to paste into a certificate file\n" ++
  "  ledger [--json] [check-native options]\n" ++
  "                       one row per registered program: whether its C has\n" ++
  "                       been COMPILED, whether the binary has been RUN, and\n" ++
  "                       whether a proved Lean chain runs from it to a\n" ++
  "                       mathematical proposition.  These are three\n" ++
  "                       independent facts and the table never merges them.\n" ++
  "                       A program whose C changed since its last run reads\n" ++
  "                       STALE, not RUN.  Exit 1 on a structural defect.\n" ++
  "  describe NAME [--full] [--source]\n" ++
  "                       what is IN a compiled program: shape, parameters,\n" ++
  "                       denotation theorem, the digest and size of the exact\n" ++
  "                       bytes ccomp was handed, the toolchain that last\n" ++
  "                       compiled them, and the instruction listing\n" ++
  "  mangle NAME...       print stable C symbols\n" ++
  "  abi-manifest         print the active ABI manifest\n" ++
  "  version              print backend and compiler versions\n\n" ++
  "For compatibility reconnaissance on an ordinary Lean source file, use\n" ++
  "`lean-compcert-probe`.\n"

private def printErrors (errors : Array String) : IO UInt32 := do
  for error in errors do
    IO.eprintln s!"error: {error}"
  pure 1

private def runDemo : IO UInt32 := do
  let program := Testing.pureProgram
  IO.println "== CCIR =="
  IO.println program.pretty
  IO.println "\n== Interpreter =="
  match CCIR.evalPure program ⟨"Example.sumTo"⟩
      #[.scalar .u64 100, .scalar .u64 0] with
  | .error error =>
      IO.eprintln error.pretty
      pure 1
  | .ok result =>
      IO.println s!"result: {result.value.pretty}; steps: {result.steps}"
      IO.println "\n== CompCert-compatible C =="
      match Testing.emittedDemo with
      | .error errors => printErrors errors
      | .ok source =>
          IO.print source
          pure 0

private def emitDemo (file : String) : IO UInt32 :=
  match Testing.emittedDemo with
  | .error errors => printErrors errors
  | .ok source => do
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      IO.println s!"wrote {file}"
      pure 0

private def emitCertificate
    (file : String)
    (emitted : Except (Array String) String) : IO UInt32 :=
  match emitted with
  | .error errors => printErrors errors
  | .ok source => do
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      IO.println s!"wrote {file}"
      pure 0

private def emitVerifiedDecide (file : String) : IO UInt32 :=
  emitCertificate file Testing.VerifiedDecide.emittedC

private def emitMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.MertensCertificate.emittedC

private def emitWideMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.WideMertensCertificate.emittedC

private def emitSquarefreeMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.SquarefreeMertensCertificate.emittedC

private def emitReflectedCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.ReflectedCertificate.emittedC

private def emitFixedPointCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.FixedPointCertificate.emittedC

private def emitRolled10M (file : String) : IO UInt32 :=
  emitCertificate file Testing.RolledFixedPoint.emittedC

/-! ## The program registry

**One list.**  `check-native`, `attest`, `verify-receipt`, `ledger` and
`describe` all read it, so a program is registered once and cannot be described
by one verb and compiled by another.

Each entry says what the program is, what it was instantiated at, what Lean
proves about it, and — through `leanSide` — which of the three states it is in.
The generic machinery is `LeanCompCert/Attest/Ledger.lean`; a consumer writes a
list like this one in its own repository and gets the same two verbs.

`certifiedValue` is the constant the generated `main` compares against, taken
from the certificate's own definition wherever the certificate has one rather
than spelled out again here.  Four of these (`wide-mertens`,
`squarefree-mertens`, `reflected`, `algorithm-sumrange`) compare against `1`
because their emitted function returns a flag: the certified value is checked
*inside* the program and the entry point reports whether it matched. -/

/-! ### Artifacts

An `Artifact` is what makes a receipt checkable in the kernel: `receiptBinds`
re-emits `Artifact.source?` and compares its digest.  Only the straight-line
certificates have one, and the reason is structural rather than an oversight —
see the `.unbindable` entries below. -/

private def verifiedDecideArtifact : Attest.Artifact := {
  computation := Testing.VerifiedDecide.computation
  route := .provedStraightLine
  mainC := Testing.VerifiedDecide.mainC }

private def mertensArtifact : Attest.Artifact := {
  computation := Testing.MertensCertificate.computation
  route := .provedStraightLine
  mainC := Testing.MertensCertificate.mainC }

private def wideMertensArtifact : Attest.Artifact := {
  computation := Testing.WideMertensCertificate.computation
  route := .provedStraightLine
  mainC := Testing.WideMertensCertificate.mainC }

private def squarefreeMertensArtifact : Attest.Artifact := {
  computation := Testing.SquarefreeMertensCertificate.computation
  route := .provedStraightLine
  mainC := Testing.SquarefreeMertensCertificate.mainC }

private def reflectedArtifact : Attest.Artifact := {
  computation := Testing.ReflectedCertificate.computation
  route := .provedStraightLine
  mainC := Testing.ReflectedCertificate.mainC }

private def fixedPointArtifact : Attest.Artifact := {
  computation := Testing.FixedPointCertificate.computation
  route := .provedStraightLine
  mainC := Testing.FixedPointCertificate.mainC }

/-- The end-to-end algorithm example, wired into the cross-check.

This is the only registered program whose chain is `Algorithm.Ensures` **and**
`ProgramRefinement`: `Testing.AlgorithmProof.reference_sound` turns success of
the checker into the mathematical fold equality, and
`Testing.AlgorithmProof.compilation` relates the register program's denotation
back to the checker — *structurally, for every input*, never by evaluating the
loop.  `CertifiedAlgorithm.claim` composes them at one input.

It is here so the `chain proved` column has a `true` in it that a reader can go
and check.  A column that is `false` everywhere teaches nobody what `true`
would require. -/
private def algorithmComputation : Verified.Computation :=
  Testing.AlgorithmProof.exampleClaim.computation "AlgorithmProof.sumRange"

/-- Built with `Attest.selfCheckMain` from the accepting value rather than with
the constant spelled out by hand — the discipline the other fourteen `mainC`
definitions predate.  The constant the binary tests is then pinned by
`programHash`, because the `main` is inside the hashed text. -/
private def algorithmMainC : String :=
  Attest.selfCheckMain "l_AlgorithmProof_sumRange" 1

private def algorithmArtifact : Attest.Artifact := {
  computation := algorithmComputation
  route := .provedStraightLine
  mainC := algorithmMainC }

private def algorithmEmitted : Except (Array String) String :=
  Attest.emitFor algorithmArtifact.computation algorithmArtifact.route
    algorithmArtifact.mainC

/-! ### The entries -/

private def registry : List Attest.ProgramEntry := [
  { name := "verified-decide"
    summary := "40 + 2, as a hand-built straight line: the smallest end-to-end \
      unit in the package"
    emitted := Testing.VerifiedDecide.emittedC
    certifiedValue := some 42
    entryPoint := "l_VerifiedDecide_addFortyTwo"
    shape := Attest.ProgramShape.ofComputation Testing.VerifiedDecide.computation
    parameters := [("addends", "40 and 2")]
    listing := Thunk.mk fun _ =>
      Attest.listingOfComputation Testing.VerifiedDecide.computation
    leanSide := .artifactOnly verifiedDecideArtifact
      "the only Decision here is `Decision.forResult computation 42`, which \
       decides that the computation returns 42.  That is a statement about the \
       program's own output, not about mathematics: there is no reference \
       function above it, so a run corroborates the number and nothing else." },

  { name := "mertens"
    summary := "Σ_{q ≤ 99, q odd} ⌊65536/q⌋, as a 64-bit straight-line fold"
    emitted := Testing.MertensCertificate.emittedC
    certifiedValue := some (Testing.MertensCertificate.expectedValue : Nat)
    entryPoint := "l_MertensCert_oddFloorSum"
    shape := Attest.ProgramShape.ofComputation Testing.MertensCertificate.computation
    parameters := [
      ("certHeight", toString Testing.MertensCertificate.certHeight),
      ("certScale", toString Testing.MertensCertificate.certScale),
      ("expectedValue", toString Testing.MertensCertificate.expectedValue)]
    listing := Thunk.mk fun _ =>
      Attest.listingOfComputation Testing.MertensCertificate.computation
    leanSide := .chained mertensArtifact
      (Attest.ChainProof.ofDecision mertensArtifact
        Testing.MertensCertificate.decision rfl
        "Σ_{q ≤ 99, q odd} ⌊65536/q⌋ = 192509 \
         (Testing.MertensCertificate.referenceSum = expectedValue)"
        "Testing.MertensCertificate.decision") },

  { name := "wide-mertens"
    summary := "Σ_{q ≤ 99, q odd} ⌊2⁶⁴/q⌋ on a two-limb accumulator; the entry \
      point returns a flag"
    emitted := Testing.WideMertensCertificate.emittedC
    certifiedValue := some 1
    entryPoint := "l_MertensCert_wideOddFloorSum"
    shape :=
      Attest.ProgramShape.ofComputation Testing.WideMertensCertificate.computation
    parameters := [
      ("certHeight", toString Testing.WideMertensCertificate.certHeight),
      ("certScale", "2^64"),
      ("expectedHi", toString Testing.WideMertensCertificate.expectedHi),
      ("expectedLo", toString Testing.WideMertensCertificate.expectedLo)]
    listing := Thunk.mk fun _ =>
      Attest.listingOfComputation Testing.WideMertensCertificate.computation
    leanSide := .chained wideMertensArtifact
      (Attest.ChainProof.ofDecision wideMertensArtifact
        Testing.WideMertensCertificate.decision rfl
        "Σ_{q ≤ 99, q odd} ⌊2⁶⁴/q⌋ = 2·2⁶⁴ + 17298892628578376934 \
         (Testing.WideMertensCertificate.referenceSum = expectedValue)"
        "Testing.WideMertensCertificate.decision") },

  { name := "squarefree-mertens"
    summary := "the §14.1 odd-squarefree Mertens sum Σ 2⁶⁴/φ(q) over odd \
      squarefree q ≤ 30; the entry point returns a flag"
    emitted := Testing.SquarefreeMertensCertificate.emittedC
    certifiedValue := some 1
    entryPoint := "l_MertensCert_oddSquarefreeMertens"
    shape := Attest.ProgramShape.ofComputation
      Testing.SquarefreeMertensCertificate.computation
    parameters := [
      ("certHeight", toString Testing.SquarefreeMertensCertificate.certHeight),
      ("certScale", "2^64"),
      ("expectedHi", toString Testing.SquarefreeMertensCertificate.expectedHi),
      ("expectedLo", toString Testing.SquarefreeMertensCertificate.expectedLo)]
    listing := Thunk.mk fun _ =>
      Attest.listingOfComputation Testing.SquarefreeMertensCertificate.computation
    leanSide := .chained squarefreeMertensArtifact
      (Attest.ChainProof.ofDecision squarefreeMertensArtifact
        Testing.SquarefreeMertensCertificate.decision rfl
        "the odd-squarefree Mertens sum to 30 equals \
         2·2⁶⁴ + 9362787364540279089 \
         (Testing.SquarefreeMertensCertificate.referenceSum = expectedValue)"
        "Testing.SquarefreeMertensCertificate.decision") },

  { name := "reflected"
    summary := "the same §14.1 sum, authored as a Verified.Reflect.Program and \
      discharged through the structural bridge"
    emitted := Testing.ReflectedCertificate.emittedC
    certifiedValue := some 1
    entryPoint := "l_MertensCert_reflectedOddSquarefreeMertens"
    shape := (Attest.ProgramShape.ofProgram Testing.ReflectedCertificate.program
      ).withComputation Testing.ReflectedCertificate.computation
    parameters := [
      ("certHeight", toString Testing.SquarefreeMertensCertificate.certHeight),
      ("certScale", "2^64"),
      ("expectedValue",
        toString Testing.SquarefreeMertensCertificate.expectedValue)]
    denotation := some {
      theoremName := "Testing.ReflectedCertificate.returns_iff"
      statement :=
        "computation.Returns 1 ↔ program.denote = some 1 — the bridge from the \
         CCIR model to the Lean-level fold, via Reflect.returns_iff_denote"
      atTheseParameters := true }
    listing := Thunk.mk fun _ =>
      Attest.listingOfProgram Testing.ReflectedCertificate.program
    leanSide := .chained reflectedArtifact
      (Attest.ChainProof.ofDecision reflectedArtifact
        Testing.ReflectedCertificate.decision rfl
        "the odd-squarefree Mertens sum to 30 equals \
         2·2⁶⁴ + 9362787364540279089 \
         (Testing.SquarefreeMertensCertificate.referenceSum = expectedValue)"
        "Testing.ReflectedCertificate.decision") },

  { name := "fixedpoint"
    summary := "Σ_{n = 1..150} ⌊n·10¹⁸ / 2⁴⁸⌋ by half-limb 128-bit products \
      and a cross-limb dyadic shift"
    emitted := Testing.FixedPointCertificate.emittedC
    certifiedValue := some (Testing.FixedPointCertificate.expectedValue : Nat)
    entryPoint := "l_FixedPoint_mulShiftSum"
    shape := (Attest.ProgramShape.ofProgram Testing.FixedPointCertificate.program
      ).withComputation Testing.FixedPointCertificate.computation
    parameters := [
      ("count", toString Testing.FixedPointCertificate.count),
      ("bigC", toString Testing.FixedPointCertificate.bigC),
      ("shift", toString Testing.FixedPointCertificate.shift),
      ("expectedValue", toString Testing.FixedPointCertificate.expectedValue)]
    denotation := some {
      theoremName := "Testing.FixedPointCertificate.returns_iff"
      statement :=
        "computation.Returns 40234404 ↔ program.denote = some 40234404, from \
         Reflect.toComputation_returns"
      atTheseParameters := true }
    listing := Thunk.mk fun _ =>
      Attest.listingOfProgram Testing.FixedPointCertificate.program
    leanSide := .chained fixedPointArtifact
      (Attest.ChainProof.ofDecision fixedPointArtifact
        Testing.FixedPointCertificate.decision rfl
        "Σ_{n = 1..150} ⌊n·10¹⁸ / 2⁴⁸⌋ = 40234404 \
         (Testing.FixedPointCertificate.referenceSum = expectedValue)"
        "Testing.FixedPointCertificate.decision") },

  { name := "rolled-10m"
    summary := "the fixed-point fold at 10⁷ iterations, emitted as a while \
      loop: a 2 KB artifact for a computation the unrolled form cannot express"
    emitted := Testing.RolledFixedPoint.emittedC
    routeLabel := Attest.EmissionRoute.rolledLoop
      Testing.RolledFixedPoint.program "FixedPoint.rolled10M" |>.label
    certifiedValue := some (Testing.RolledFixedPoint.expectedBig : Nat)
    entryPoint := "l_FixedPoint_rolled10M"
    shape := Attest.ProgramShape.ofProgram Testing.RolledFixedPoint.program
    parameters := [
      ("bigCount", toString Testing.RolledFixedPoint.bigCount),
      ("bigC", toString Testing.FixedPointCertificate.bigC),
      ("shift", toString Testing.FixedPointCertificate.shift),
      ("expectedBig", toString Testing.RolledFixedPoint.expectedBig)]
    listing := Thunk.mk fun _ =>
      Attest.listingOfProgram Testing.RolledFixedPoint.program
    leanSide := .unbindable
      "an Artifact needs a Computation, and Program.toComputation at 10⁷ trips \
       would unroll 10⁷ × 21 statements — which is exactly the size the rolled \
       route exists to avoid.  Nothing in Lean therefore reproduces this C, so \
       receiptBinds can never be applied to a receipt for it.  There is also \
       no theorem relating this program's denotation to any reference \
       function." },

  { name := "proth"
    summary := "3^((N−1)/2) mod N for the 91-bit Proth prime \
      N = 274877906947·2⁵² + 1, by Montgomery multiplication in 64-bit \
      registers with no division"
    emitted := Testing.ProthCertificate.emittedC
    routeLabel := Attest.EmissionRoute.rolledLoop
      Testing.ProthCertificate.program "ProthCertificate" |>.label
    certifiedValue := some 0
    entryPoint := "l_ProthCertificate"
    shape := Attest.ProgramShape.ofProgram Testing.ProthCertificate.program
    parameters := [
      ("n", toString Testing.ProthCertificate.n),
      ("kbits", toString Testing.ProthCertificate.kbits),
      ("k", toString Testing.ProthCertificate.k),
      ("a", toString Testing.ProthCertificate.a),
      ("N = k·2ⁿ + 1", toString Testing.ProthCertificate.N)]
    denotation := some {
      theoremName := "Ports.TGProth.prothProgram_denote"
      statement :=
        "(prothProgram n kbits k a).denote = some (if a^((N−1)/2) % N = N − 1 \
         then 0 else 1), under 32 ≤ n, kbits ≤ 64, 0 < k < 2^kbits, \
         2⁶⁴ < N < 2¹²⁷ and 0 < a"
      atTheseParameters := false
      gap :=
        "this certificate never instantiates it.  The hypotheses hold at these \
         parameters and discharging them is arithmetic, but until it is done \
         the theorem is about a family and the ledger will not report it as \
         being about this binary." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfProgram Testing.ProthCertificate.program
    leanSide := .unbindable
      "rolled emission with no Computation: Program.toComputation would unroll \
       the Montgomery ladder.  The denotation theorem above exists but is not \
       instantiated here, so nothing connects this binary's 0 to N's \
       primality." },

  { name := "mobius-array"
    summary := "L + Σ_{n < L} μ(n) at L = 100000, by a segmented array \
      sieve — the Mertens function offset to stay non-negative in u64, not the \
      squarefree count"
    emitted := Testing.ArrayMobiusCertificate.emittedC
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.ArrayMobiusCertificate.expected : Nat)
    entryPoint := "l_ArrayMobius_rolled100k"
    shape := Attest.ProgramShape.ofAProgram Testing.ArrayMobiusCertificate.program
    parameters := [
      ("segment", toString Testing.ArrayMobiusCertificate.segment),
      ("expected", toString Testing.ArrayMobiusCertificate.expected)]
    denotation := some {
      theoremName := "Ports.ArrayMobius (namespace Check, `example`s)"
      statement :=
        "(mobiusProgram L).denote = some (reference L) is checked by the kernel \
         at L = 8, 16 and 24"
      atTheseParameters := false
      gap :=
        "the spot-checks are at L = 8, 16, 24; this artifact runs at \
         L = 100000.  There is no theorem for general L." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.ArrayMobiusCertificate.program
    leanSide := .unbindable
      "emitted by AProgram.emitRolled, and Attest.emitFor has no array route: \
       EmissionRoute knows Lower.compileProgram and Reflect.emitRolled and \
       nothing else.  No Artifact reproduces this C, so no receipt for it can \
       be checked in the kernel." },

  { name := "mobius-seg"
    summary := "the windowed Mertens/Σμ(m)/m residue over [1, 32768], eight \
      windows of 4096 cells, on a two-limb accumulator; the entry point returns \
      a count of FAILED threshold tests, so 0 is the certified answer and 4 is \
      what this configuration produces"
    emitted := Testing.ArraySegCertificate.emittedC
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.ArraySegCertificate.expected : Nat)
    entryPoint := "l_ArraySeg_mertens32k"
    shape := Attest.ProgramShape.ofAProgram Testing.ArraySegCertificate.program
    parameters := [
      ("window length", "4096"),
      ("windows", "8"),
      ("range", "[1, 32768]"),
      ("bound numerator", "755"),
      ("bound denominator", "10000"),
      ("expected", toString Testing.ArraySegCertificate.expected)]
    denotation := some {
      theoremName := "Ports.ArraySegSieve (namespace Check, `example`s)"
      statement :=
        "(mertensProbe r).denote = some (refM 1 24) and companions, checked by \
         the kernel on a 24-cell probe"
      atTheseParameters := false
      gap :=
        "the probes run over 24 cells; this artifact runs over 32768.  There is \
         no theorem for the general configuration." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.ArraySegCertificate.program
    leanSide := .unbindable
      "emitted by AProgram.emitRolled; see `mobius-array`.  No Artifact \
       reproduces this C." },

  { name := "cdem-abel"
    summary := "the CDEM Abel increment scan over [1, 40]: five segments of \
      eight, weight scale 10⁶, K = 30; the entry point returns a count of \
      FAILED guards, so the certified answer is 0"
    emitted := Testing.AbelScanCertificate.emittedC
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.AbelScanCertificate.expected : Nat)
    entryPoint := "l_CDEMAbel_scan40"
    shape := Attest.ProgramShape.ofAProgram Testing.AbelScanCertificate.program
    parameters := [
      ("weight scale", "1000000"),
      ("K bound", "30"),
      ("segment length", "8"),
      ("segments", "5"),
      ("range", "[1, 40]"),
      ("expected", toString Testing.AbelScanCertificate.expected)]
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.AbelScanCertificate.program
    leanSide := .unbindable
      "emitted by AProgram.emitRolled, and — unlike the two sieves — there is \
       not even a kernel spot-check: Ports.CDEMAbelScan carries a reference \
       fold in `namespace Ref` and no theorem or `example` tying denote to it. \
       The corroboration is an emit-time reference and bench/ref_abel.c, \
       neither of which is Lean." },

  { name := "dirichlet-ladder"
    summary := "the Platt Theorem 7.1 finite content: a violation count over \
      156 zero records for a conjugate character pair mod 400000"
    emitted := Testing.DirichletLadderCertificate.emittedC
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.DirichletLadderCertificate.expected : Nat)
    entryPoint := "l_DirichletLadder_rolled156"
    shape :=
      Attest.ProgramShape.ofAProgram Testing.DirichletLadderCertificate.program
    parameters := [
      ("modulus q", "400000"),
      ("zero records", "156"),
      ("blocks per record", "78"),
      ("words per record", "13"),
      ("expected violations", toString Testing.DirichletLadderCertificate.expected)]
    denotation := some {
      theoremName := "Ports.DirichletLadder (namespace Check, `example`s)"
      statement :=
        "(seededTest goodStream).denote = some (refViolations (testCfg 6 …) \
         goodStream), plus ten mutated-stream cases"
      atTheseParameters := false
      gap :=
        "every `example` is at `testCfg`; this artifact runs at `sourceCfg`. \
         The mutation cases show the checker is not vacuous at the test \
         configuration and say nothing about this one." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.DirichletLadderCertificate.program
    leanSide := .unbindable
      "emitted by AProgram.emitRolled; see `mobius-array`.  No Artifact \
       reproduces this C." },

  { name := "rs62-ladder-sl"
    summary := "the RS62 ladder increment over 65536 candidates from 101, 256 \
      trial-division rounds each, rounding DOWN at every prime"
    emitted := Testing.RS62LadderCertificate.emittedCSL
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.RS62LadderCertificate.expectedSL : Nat)
    entryPoint := "l_RS62_ladderSL65k"
    shape := Attest.ProgramShape.ofAProgram Testing.RS62LadderCertificate.programSL
    parameters := [
      ("n0", toString Testing.RS62LadderCertificate.n0),
      ("f (candidates)", toString Testing.RS62LadderCertificate.f),
      ("B (rounds each)", toString Testing.RS62LadderCertificate.B),
      ("rounding", "down"),
      ("expectedSL", toString Testing.RS62LadderCertificate.expectedSL)]
    denotation := some {
      theoremName := "Ports.RS62LadderProgram.ladderProgram_denote"
      statement :=
        "(ladderProgram …).denote = (ladderScalarProgram …).denote — the array \
         lift agrees with the scalar program"
      atTheseParameters := true
      gap :=
        "it relates two programs to each other and neither to a reference \
         function.  The obligation that would do that, \
         Ports.RS62LadderProgram.LadderEncoding, is STATED AND NOT \
         DISCHARGED." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.RS62LadderCertificate.programSL
    leanSide := .unbindable
      "emitted by AProgram.emitRolled; see `mobius-array`.  No Artifact \
       reproduces this C." },

  { name := "rs62-ladder-su"
    summary := "the same RS62 ladder increment, rounding UP at every prime"
    emitted := Testing.RS62LadderCertificate.emittedCSU
    routeLabel := Attest.arrayRolledLabel
    certifiedValue := some (Testing.RS62LadderCertificate.expectedSU : Nat)
    entryPoint := "l_RS62_ladderSU65k"
    shape := Attest.ProgramShape.ofAProgram Testing.RS62LadderCertificate.programSU
    parameters := [
      ("n0", toString Testing.RS62LadderCertificate.n0),
      ("f (candidates)", toString Testing.RS62LadderCertificate.f),
      ("B (rounds each)", toString Testing.RS62LadderCertificate.B),
      ("rounding", "up"),
      ("expectedSU", toString Testing.RS62LadderCertificate.expectedSU)]
    denotation := some {
      theoremName := "Ports.RS62LadderProgram.ladderProgram_denote"
      statement :=
        "(ladderProgram …).denote = (ladderScalarProgram …).denote — the array \
         lift agrees with the scalar program"
      atTheseParameters := true
      gap :=
        "it relates two programs to each other and neither to a reference \
         function.  The obligation that would do that, \
         Ports.RS62LadderProgram.LadderEncoding, is STATED AND NOT \
         DISCHARGED." }
    listing := Thunk.mk fun _ =>
      Attest.listingOfAProgram Testing.RS62LadderCertificate.programSU
    leanSide := .unbindable
      "emitted by AProgram.emitRolled; see `mobius-array`.  No Artifact \
       reproduces this C." },

  { name := "algorithm-sumrange"
    summary := "Σ_{i < 10} (i mod M) mod M compared against 45: the one \
      registered program with Algorithm.Ensures AND ProgramRefinement above it"
    emitted := algorithmEmitted
    certifiedValue := some 1
    entryPoint := "l_AlgorithmProof_sumRange"
    shape := (Attest.ProgramShape.ofProgram
      (Testing.AlgorithmProof.program Testing.AlgorithmProof.exampleInput)
      ).withComputation algorithmComputation
    parameters := [
      ("count", toString Testing.AlgorithmProof.exampleInput.count),
      ("expected", toString Testing.AlgorithmProof.exampleInput.expected),
      ("M", "2^64")]
    denotation := some {
      theoremName := "Testing.AlgorithmProof.program_denote"
      statement :=
        "(program input).denote = some (if sumRangeMod input.count = \
         input.expected % M then 1 else 0), for EVERY input — proved \
         structurally through the fold bridge, never by evaluating the loop"
      atTheseParameters := true }
    listing := Thunk.mk fun _ =>
      Attest.listingOfProgram
        (Testing.AlgorithmProof.program Testing.AlgorithmProof.exampleInput)
    leanSide := .chained algorithmArtifact
      (Attest.ChainProof.ofClaim algorithmArtifact "AlgorithmProof.sumRange"
        Testing.AlgorithmProof.exampleClaim rfl
        "(List.range 10).foldl (fun acc i => (acc + i % M) % M) 0 = 45 % M \
         (Testing.AlgorithmProof.proposition exampleInput)"
        "Testing.AlgorithmProof.certified — Ensures (reference_sound) composed \
         with ProgramRefinement (compilation) by CertifiedAlgorithm.claim") }
]

/-- The cross-check units, derived from the registry so the two cannot drift. -/
private def nativeCerts : List NativeCheck.Cert :=
  registry.map NativeCheck.Cert.ofEntry

/-! ## Receipt verbs -/

private def attestKeygen (args : List String) : IO UInt32 := do
  let path : System.FilePath :=
    match args with
    | ["--key", path] => path
    | _ => Attest.Tool.defaultKeyPath
  match ← Attest.Tool.generateKey path with
  | .error message =>
      IO.eprintln s!"error: {message}"
      pure 1
  | .ok message =>
      IO.println message
      let scratch := path.parent.getD "." / "scratch"
      match ← Attest.Tool.publicKeyHex path scratch with
      | .error detail =>
          IO.eprintln s!"error: {detail}"
          pure 1
      | .ok hex =>
          IO.println s!"public key (SEC1 uncompressed): {hex}"
          IO.println ""
          IO.println
            "This is a LOCAL key.  A receipt it signs is tamper-evident, not attested:"
          IO.println
            "anyone who can read the key file can sign any value.  It is auditable"
          IO.println
            "bookkeeping for a machine you already trust, and nothing stronger."
          pure 0

private structure VerifyArgs where
  file : Option String := none
  cert : Option String := none
  leanName : Option String := none

private def parseVerifyArgs : List String → Except String VerifyArgs
  | [] => .ok {}
  | "--cert" :: name :: rest => do
      let a ← parseVerifyArgs rest
      .ok { a with cert := some name }
  | "--lean" :: name :: rest => do
      let a ← parseVerifyArgs rest
      .ok { a with leanName := some name }
  | arg :: rest =>
      if arg.startsWith "--" then .error s!"unknown verify-receipt argument '{arg}'"
      else do
        let a ← parseVerifyArgs rest
        .ok { a with file := some arg }

private def verifyReceipt (args : List String) : IO UInt32 := do
  let parsed ←
    match parseVerifyArgs args with
    | .error message => IO.eprintln s!"error: {message}"; return 2
    | .ok parsed => pure parsed
  let some file := parsed.file
    | IO.eprintln "error: verify-receipt needs a receipt file"; return 2
  let some certName := parsed.cert
    | IO.eprintln
        ("error: verify-receipt needs --cert NAME, so the receipt is checked " ++
         "against a program rather than against itself")
      return 2
  let some cert := nativeCerts.find? (·.name == certName)
    | IO.eprintln s!"error: no registered certificate named '{certName}'"
      IO.eprintln s!"       known: {String.intercalate ", " (nativeCerts.map (·.name))}"
      return 2
  let text ← IO.FS.readFile file
  let receipt ←
    match Attest.Tool.parseReceipt text with
    | .error message => IO.eprintln s!"error: {message}"; return 1
    | .ok receipt => pure receipt
  let scratch : System.FilePath := ".lake" / "build" / "attest" / "verify"
  let outcome ← Attest.Tool.verifyReceiptAgainst scratch receipt cert.emitted
  for line in outcome.lines do
    IO.println line
  if receipt.routeLabel != cert.routeLabel then
    IO.println
      s!"  FAIL route is '{receipt.routeLabel}', certificate '{certName}' emits '{cert.routeLabel}'"
    return 1
  IO.println s!"  ok   route {receipt.routeLabel}"
  match cert.certifiedValue with
  | some value =>
      if receipt.value != value then
        IO.println
          s!"  FAIL value {receipt.value} ≠ the certificate's constant {value}"
        return 1
      IO.println s!"  ok   value {receipt.value}"
  | none =>
      IO.println
        s!"  FAIL certificate '{certName}' declares no certifiedValue to compare"
      return 1
  if !outcome.ok then
    IO.eprintln
      "verify-receipt: FAILED.  Note this tool is a convenience: the authoritative"
    IO.eprintln
      "check is `Attest.receiptBinds` in the Lean kernel with your own verifier."
    return 1
  if let some name := parsed.leanName then
    IO.println ""
    IO.print (Attest.Tool.renderLean name receipt)
  IO.println ""
  IO.println
    "verify-receipt: every field this tool can check is consistent.  This is NOT"
  IO.println
    "the proof: `Attest.receiptBinds` re-does all of it in the kernel, and even"
  IO.println
    "then a locally signed receipt attests nothing about whether the run happened."
  pure 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["demo"] => runDemo
  | ["emit-demo-c", file] => emitDemo file
  | ["emit-verified-decide-c", file] => emitVerifiedDecide file
  | ["emit-mertens-cert-c", file] => emitMertensCertificate file
  | ["emit-wide-mertens-cert-c", file] => emitWideMertensCertificate file
  | ["emit-squarefree-mertens-cert-c", file] => emitSquarefreeMertensCertificate file
  | ["emit-reflected-cert-c", file] => emitReflectedCertificate file
  | ["emit-fixedpoint-cert-c", file] => emitFixedPointCertificate file
  | ["emit-rolled-10m-c", file] => emitRolled10M file
  | "check-native" :: rest => NativeCheck.run nativeCerts rest
  | "attest" :: rest => NativeCheck.run nativeCerts ("--attest" :: rest)
  | "ledger" :: rest => Attest.Ledger.ledgerVerb registry rest
  | "describe" :: rest => Attest.Ledger.describeVerb registry rest
  | "attest-keygen" :: rest => attestKeygen rest
  | "verify-receipt" :: rest => verifyReceipt rest
  | ["emit-clight-fixedpoint-v", file] =>
      match Verified.ClightEmit.emitClight "direct_FixedPoint_mulShiftSum"
          Testing.FixedPointCertificate.computation.statements
          "v_1" with
      | none => do
          IO.eprintln "error: direct Clight emission failed"
          pure 1
      | some source => do
          let path : System.FilePath := file
          if let some parent := path.parent then
            IO.FS.createDirAll parent
          IO.FS.writeFile path source
          IO.println s!"wrote {file}"
          pure 0
  | "mangle" :: names => do
      if names.isEmpty then
        IO.eprintln "error: mangle requires at least one Lean name"
        pure 2
      else
        for name in names do
          IO.println s!"{name}\t{ABI.mangle name}"
        pure 0
  | ["abi-manifest"] => do
      let manifest := ABI.Manifest.current "development-runtime"
      IO.println manifest.toJson.pretty
      pure 0
  | ["version"] => do
      IO.println s!"lean-compcert {backendVersion}"
      IO.println s!"Lean {Lean.versionString} ({Lean.githash})"
      pure 0
  | _ => do
      IO.print usage
      pure (if args.isEmpty then 0 else 2)
