import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Testing.RolledFixedPoint
import LeanCompCert.Testing.PackedCoverageCertificate
import LeanCompCert.Testing.AlgorithmProof
import LeanCompCert.Testing.ArrayMobiusCertificate
import LeanCompCert.Attest.LedgerReport
import LeanCompCertTests.Docs
import LeanCompCertTests.Attest
import LeanCompCertTests.ClightContractTest
import LeanCompCertTests.ProgramClightEmitTest

open LeanCompCert

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

private def testSymbols : IO Unit := do
  check (ABI.mangle "Data.Tree.map" == "l_Data_Tree_map")
    "readable symbol mangling changed"
  check (ABI.mangle "A_b" != ABI.mangle "A.b")
    "underscore and module separator collided"
  check (ABI.isCollisionFreeOn #["A.b", "A_b", "A-b", "λ"])
    "symbol mangling collision"

private def testInterpreter : IO Unit := do
  let errors := CCIR.validateProgram Testing.pureProgram
  check errors.isEmpty s!"pure program failed validation: {repr errors}"
  match CCIR.evalPure Testing.pureProgram ⟨"Example.add"⟩
      #[.scalar .u64 40, .scalar .u64 2] with
  | .error error => throw (IO.userError error.pretty)
  | .ok result =>
      check (result.value == .scalar .u64 42) "CCIR addition produced the wrong result"
  match CCIR.evalPure Testing.pureProgram ⟨"Example.sumTo"⟩
      #[.scalar .u64 100, .scalar .u64 0] with
  | .error error => throw (IO.userError error.pretty)
  | .ok result =>
      check (result.value == .scalar .u64 5050) "CCIR loop produced the wrong result"
      check (result.steps < 1000) "CCIR loop used an unexpected number of steps"
  for n in [0:128] do
    match CCIR.evalPure Testing.pureProgram ⟨"Example.add"⟩
        #[.scalar .u64 n, .scalar .u64 (127 - n)] with
    | .error error => throw (IO.userError error.pretty)
    | .ok result =>
        check (result.value == .scalar .u64 127)
          s!"CCIR generated arithmetic case {n} produced the wrong result"
  match CCIR.evalPure Testing.pureProgram ⟨"Example.add"⟩
      #[.scalar .u64 18446744073709551615, .scalar .u64 1] with
  | .error error => throw (IO.userError error.pretty)
  | .ok result =>
      check (result.value == .scalar .u64 0)
        "CCIR UInt64 addition did not wrap modulo 2^64"

private def testCEmission : IO Unit := do
  match Testing.emittedDemo with
  | .error errors => throw (IO.userError s!"C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "uint64_t l_Example_add")
        "generated C lacks add function"
      check (source.contains "goto block_0;")
        "generated C lacks explicit control flow"
      check (!source.contains "f(g()")
        "generated C contains nested effectful example"

private def testCValidator : IO Unit := do
  let signed : C.CFunction := {
    name := "bad_signed"
    params := #[{ name := "x", type := .i32 }]
    result := .i32
    body := #[
      .return (some (.binary .i32 .add
        (.var "x" .i32) (.intLit .i32 1)))
    ]
  }
  let errors := C.validateFunction .portable signed
  check (errors.any (fun error => error.rule == .signedOverflow))
    "C validator accepted potentially overflowing signed arithmetic"

private def indexedFunction (baseType : CCIR.CCType) : CCIR.Function := {
  name := ⟨"Indexed.test"⟩
  params := #[{ id := ⟨0⟩, type := baseType }, { id := ⟨1⟩, type := .u64 }]
  result := .u64
  entry := ⟨0⟩
  blocks := #[{
    id := ⟨0⟩
    instructions := #[
      .loadIndex { id := ⟨2⟩, type := .u64 } (.local ⟨0⟩) (.local ⟨1⟩),
      .storeIndex (.local ⟨0⟩) (.local ⟨1⟩) (.local ⟨2⟩)
    ]
    terminator := .return (some (.local ⟨2⟩))
  }]
}

private def testIndexedMemory : IO Unit := do
  let good : CCIR.Program := { functions := #[indexedFunction (.ptr .u64)] }
  check (CCIR.validateProgram good).isEmpty
    "CCIR validator rejected typed indexed load/store"
  let bad : CCIR.Program := { functions := #[indexedFunction .u64] }
  check ((CCIR.validateProgram bad).any
      (fun error => error.rule == .instructionType))
    "CCIR validator accepted an integer as an indexed-memory base"
  match Testing.ArrayMobiusCertificate.emittedC with
  | .error errors =>
      throw (IO.userError s!"pointer-native array emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "uint64_t *")
        "array function lacks a pointer-typed base"
      check (source.contains "[v_")
        "array function lacks indexed pointer accesses"
      check (!source.contains "uintptr_t")
        "array function still integerizes its base pointer"

private def testPolicies : IO Unit := do
  let active := ABI.Manifest.current "hash-a"
  let expected := { active with runtimeAbiHash := "hash-b" }
  check (!(expected.validateAgainst active).isEmpty)
    "ABI hash mismatch was accepted"
  let runtimeErrors :=
    Runtime.defaultInventory.validateSymbols #["lean_spawn_task"] false
  check (!runtimeErrors.isEmpty) "unsupported runtime symbol was accepted"
  let strictConfig : Config := { runtime := .strict, profile := .portable }
  check (!strictConfig.validate.isEmpty)
    "inconsistent strict configuration was accepted"

private def testVerifiedDecide : IO Unit := do
  check
    (Testing.VerifiedDecide.computation.sourceResult == some 42)
    "verified source computation produced the wrong result"
  check
    (Testing.VerifiedDecide.computation.targetResult == some 42)
    "verified generated-C model produced the wrong result"
  match Testing.VerifiedDecide.emittedC with
  | .error errors =>
      throw (IO.userError s!"verified-decision C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_VerifiedDecide_addFortyTwo")
        "verified-decision C lacks the compiled entry point"

private def testMertensCertificate : IO Unit := do
  check
    (Testing.MertensCertificate.computation.sourceResult == some 192509)
    "fold-certificate source computation produced the wrong result"
  check
    (Testing.MertensCertificate.computation.targetResult == some 192509)
    "fold-certificate generated-C model produced the wrong result"
  check
    (Testing.MertensCertificate.referenceSum ==
      Testing.MertensCertificate.expectedValue)
    "fold-certificate reference fold disagrees with the certified value"
  match Testing.MertensCertificate.emittedC with
  | .error errors =>
      throw (IO.userError s!"fold-certificate C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_MertensCert_oddFloorSum")
        "fold-certificate C lacks the compiled entry point"

private def testWideMertensCertificate : IO Unit := do
  check
    (Testing.WideMertensCertificate.computation.sourceResult == some 1)
    "wide fold-certificate source computation did not accept"
  check
    (Testing.WideMertensCertificate.computation.targetResult == some 1)
    "wide fold-certificate generated-C model did not accept"
  check
    (Testing.WideMertensCertificate.referenceSum ==
      Testing.WideMertensCertificate.expectedValue)
    "wide fold-certificate reference fold disagrees with the certified value"
  check
    (Testing.WideMertensCertificate.expectedValue >
      Testing.WideMertensCertificate.certScale)
    "wide fold-certificate value does not exceed 64 bits"
  match Testing.WideMertensCertificate.emittedC with
  | .error errors =>
      throw (IO.userError s!"wide fold-certificate C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_MertensCert_wideOddFloorSum")
        "wide fold-certificate C lacks the compiled entry point"

private def testSquarefreeMertensCertificate : IO Unit := do
  check
    (Testing.SquarefreeMertensCertificate.computation.sourceResult == some 1)
    "squarefree Mertens certificate source computation did not accept"
  check
    (Testing.SquarefreeMertensCertificate.computation.targetResult == some 1)
    "squarefree Mertens certificate generated-C model did not accept"
  check
    (Testing.SquarefreeMertensCertificate.referenceSum ==
      Testing.SquarefreeMertensCertificate.expectedValue)
    "squarefree Mertens reference fold disagrees with the certified value"
  match Testing.SquarefreeMertensCertificate.emittedC with
  | .error errors =>
      throw (IO.userError
        s!"squarefree Mertens certificate C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_MertensCert_oddSquarefreeMertens")
        "squarefree Mertens certificate C lacks the compiled entry point"

private def testReflectedCertificate : IO Unit := do
  check
    (Testing.ReflectedCertificate.program.denote == some 1)
    "reflected certificate denotation did not accept"
  check
    (Testing.ReflectedCertificate.computation.sourceResult == some 1)
    "reflected certificate CCIR model did not accept"
  check
    (Testing.ReflectedCertificate.computation.targetResult == some 1)
    "reflected certificate generated-C model did not accept"
  match Testing.ReflectedCertificate.emittedC with
  | .error errors =>
      throw (IO.userError s!"reflected certificate C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_MertensCert_reflectedOddSquarefreeMertens")
        "reflected certificate C lacks the compiled entry point"

private def testAlgorithmProof : IO Unit := do
  check
    (Testing.AlgorithmProof.exampleClaim.program.denote == some 1)
    "certified algorithm example did not accept"
  check
    ((Testing.AlgorithmProof.exampleClaim.computation
      "AlgorithmProof.sumRange").targetResult == some 1)
    "certified algorithm generated-C model did not accept"

private def testArrayAlgorithmProof : IO Unit := do
  -- the array analogue: an `AProgramClaim` whose `sound` field is a theorem,
  -- and whose decoder rejects both a wrong value and an inadmissible input
  check
    (Ports.ArraySieveCount.exampleClaim.program.denote == some 9)
    "array certified algorithm example did not accept"
  check
    (Ports.ArraySieveCount.decode Ports.ArraySieveCount.exampleInput 9 == some ())
    "array decoder rejected the accepting value"
  check
    (Ports.ArraySieveCount.decode Ports.ArraySieveCount.exampleInput 8 == none)
    "array decoder accepted a wrong value"
  check
    (Ports.ArraySieveCount.decode ⟨0, 24, 9⟩ 9 == none)
    "array decoder accepted an inadmissible configuration"
  -- the Möbius port's layout bounds, evaluated: the crude estimates
  -- `layoutOk` relies on are true of the layout the port actually builds
  check
    (Ports.ArrayMobius.Layout.tableLen (Ports.ArrayMobius.Layout.ofSegment 1000)
      <= 1000)
    "mobius prime table longer than its segment"
  check
    (Ports.ArrayMobius.Layout.markSteps (Ports.ArrayMobius.Layout.ofSegment 1000)
      <= 1000 * 1000 + 1000 + 16)
    "mobius mark budget above its bound"

private def scaleProgram : Verified.Reflect.Program := {
  regCount := 6
  loopCount := 150000
  init := []
  body := [
    .binop 2 .add .idx (.lit 1),
    .binop 3 .band (.reg 2) (.lit 1),
    .binop 4 .eq (.reg 3) (.lit 1),
    .binop 5 .add (.reg 5) (.reg 4)
  ]
  epilogue := []
  output := 5
}

private theorem scaleProgram_wf : scaleProgram.WF := by decide

/-- M1 acceptance: a 750k-instruction certificate packaged with purely
structural evidence — the only proof obligation was the program-sized
`scaleProgram.WF` decide above. -/
private def scaleComputation : Verified.Computation :=
  scaleProgram.toComputation "Scale.sweep" scaleProgram_wf

private def testPackagingScale : IO Unit := do
  check (scaleComputation.instructions.length == 750007)
    "M1 scale packaging produced the wrong trace length"
  check (scaleComputation.statements.length == 750007)
    "M1 scale packaging produced the wrong statement count"

private def testFixedPointCertificate : IO Unit := do
  check
    (Testing.FixedPointCertificate.program.denote ==
      some Testing.FixedPointCertificate.expectedValue)
    "fixed-point certificate denotation disagrees"
  check
    (Testing.FixedPointCertificate.computation.sourceResult ==
      some (Testing.FixedPointCertificate.expectedValue : Int))
    "fixed-point certificate CCIR model disagrees"
  check
    (Testing.FixedPointCertificate.referenceSum ==
      Testing.FixedPointCertificate.expectedValue)
    "fixed-point reference fold disagrees"
  match Testing.FixedPointCertificate.emittedC with
  | .error errors =>
      throw (IO.userError s!"fixed-point certificate C emission failed: {repr errors}")
  | .ok source =>
      check (source.contains "l_FixedPoint_mulShiftSum")
        "fixed-point certificate C lacks the compiled entry point"

private def testRolledEmission : IO Unit := do
  match Testing.RolledFixedPoint.emittedC with
  | .error errors =>
      throw (IO.userError s!"rolled emission failed: {repr errors}")
  | .ok source =>
      check (source.length < 4096)
        "rolled 10M artifact is not compact"
      check (source.contains "while")
        "rolled artifact lacks a loop"

private def testDirectClight : IO Unit := do
  let source := Verified.ProgramClightEmit.emitProgram
    "direct_FixedPoint_mulShiftSum"
    Testing.FixedPointCertificate.program
    Testing.FixedPointCertificate.expectedValue
    Testing.FixedPointCertificate.program_compCertWF
    Testing.FixedPointCertificate.program_denote
  check (source.contains
      "Definition f_direct_FixedPoint_mulShiftSum : function := compile_program")
    "proved Clight emission does not use the verified compiler"
  check (source.contains "source_direct_FixedPoint_mulShiftSum_denote")
    "proved Clight emission lacks its closed denotation check"
  check (source.contains "compile_program_correct")
    "proved Clight emission lacks the CompCert semantics theorem"

/-- The receipt tool's byte surgery and on-disk format, at run time.

The kernel-checked half is `LeanCompCertTests/Attest.lean`; this exercises the
same functions compiled, so a divergence between the two evaluators would show
up here. -/
private def testAttestTool : IO Unit := do
  let sig := Attest.p256KatSignature
  check ((Attest.Tool.signatureDerOfHex sig).bind Attest.Tool.signatureHexOfDer
      == some sig)
    "ECDSA signature DER round trip changed"
  check ((Attest.Tool.publicKeyDerOfHex Attest.p256KatPublicKey).bind
      Attest.Tool.publicKeyHexOfDer == some Attest.p256KatPublicKey)
    "SEC1 public key DER round trip changed"
  check (Attest.Tool.signatureDerOfHex "beef" == none)
    "a short signature must not encode to DER"
  check (Attest.Tool.publicKeyDerOfHex (String.ofList (List.replicate 130 '0')) == none)
    "a public key without the 04 tag must be refused"
  let text := Attest.Tool.renderReceipt LeanCompCertTests.Attest.receipt
  check (match Attest.Tool.parseReceipt text with
      | .ok parsed => parsed == LeanCompCertTests.Attest.receipt
      | .error _ => false)
    "receipt file round trip changed"
  check ((Attest.Tool.parseReceipt (text ++ "extra\n")).toOption.isNone)
    "a receipt with an extra line must be refused"
  check (Attest.Tool.renderReceipt LeanCompCertTests.Attest.receipt
      |>.startsWith Attest.schemaVersion)
    "the signed payload must be a prefix of the receipt file"

/-! ## The program ledger

The ledger's value is entirely in its refusals, so what is tested is that each
refusal fires.  A ledger that only ever prints `RUN` and `PROVED` would pass a
happy-path test and be worthless.

`defectsOf` is checked against a registration that is right and against four
that are wrong in one way each — and the four are the ways two internally
consistent halves come to be about different things. -/
private def ledgerArtifact : Attest.Artifact := LeanCompCertTests.Attest.artifact

private def ledgerEmitted : Except (Array String) String :=
  Attest.emitFor ledgerArtifact.body ledgerArtifact.mainC

/-- A `ChainProof` for the test artifact, accepting `204`. -/
private def ledgerChain : Attest.ChainProof ledgerArtifact :=
  Attest.ChainProof.ofDecision ledgerArtifact
    (Verified.Decision.forResult LeanCompCertTests.Attest.computation 204) rfl
    "the computation returns 204" "LeanCompCertTests.ledgerChain"

private def ledgerEntry : Attest.ProgramEntry := {
  name := "ledger-test"
  summary := "Σ_{k < 8} (k+1)² = 204"
  emitted := ledgerEmitted
  certifiedValue := some 204
  entryPoint := "l_Attest_squareSum"
  shape := Attest.ProgramShape.ofComputation LeanCompCertTests.Attest.computation
  leanSide := .chained ledgerArtifact ledgerChain }

private def testProgramLedger : IO Unit := do
  -- A correct registration has no defects.
  check (Attest.Ledger.defectsOf ledgerEntry).isEmpty
    "a consistent ledger entry reported a defect"
  check (Attest.Ledger.defectsOf
      { ledgerEntry with leanSide := .artifactOnly ledgerArtifact "none" }).isEmpty
    "an artifact-only entry reported a defect"
  -- 1. The binary self-checks one number and the proved arrow consumes another.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with certifiedValue := some 205 }).isEmpty)
    "a chain consuming a different value than the binary tests was accepted"
  -- 2. A chain with nothing for the binary to have tested.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with certifiedValue := none }).isEmpty)
    "a chain with no certifiedValue was accepted"
  -- 3. A route label the artifact's route contradicts.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with routeLabel := "rolled-loop" }).isEmpty)
    "a route label contradicting the artifact was accepted"
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with routeLabel := Attest.arrayRolledLabel }).isEmpty)
    "the array-rolled label on a straight-line artifact was accepted"
  -- 4. The artifact does not re-emit the C that is compiled.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with emitted := .ok "int main(void) { return 0; }" }).isEmpty)
    "an artifact that does not reproduce the compiled C was accepted"
  -- The three states are read off independently.
  check (ledgerEntry.chainProved && ledgerEntry.bindable)
    "a chained entry must be both chain proved and bindable"
  check (!(Attest.ProgramEntry.chainProved
      { ledgerEntry with leanSide := .artifactOnly ledgerArtifact "none" })
    && Attest.ProgramEntry.bindable
      { ledgerEntry with leanSide := .artifactOnly ledgerArtifact "none" })
    "an artifact-only entry must be bindable and NOT chain proved"
  check (!(Attest.ProgramEntry.chainProved
      { ledgerEntry with leanSide := .unbindable "none" })
    && !(Attest.ProgramEntry.bindable
      { ledgerEntry with leanSide := .unbindable "none" }))
    "an unbindable entry must be neither bindable nor chain proved"
  -- The run record round-trips, and is refused rather than patched up.
  let record : Attest.RunRecord := {
    schema := Attest.runRecordSchema
    name := "ledger-test"
    recordedAt := "2026-08-02T00:00:00Z"
    sourceDigest := String.ofList (List.replicate 64 'a')
    sourceBytes := 448
    ccompVersion := "The CompCert C verified compiler, version 3.17"
    ccompDigest := String.ofList (List.replicate 64 'b')
    linkDescription := "freestanding test"
    machine := "machine test-harness"
    exitCode := 0
    outcome := .agrees
    certifiedValue := "204"
    receiptPath := "-" }
  let text := record.render
  check (Attest.RunRecord.parse text == some record)
    "run record round trip changed"
  check ((Attest.RunRecord.parse (text ++ "extra\n")).isNone)
    "a run record with an extra line must be refused"
  -- The format is thirteen NON-EMPTY lines and `parse` enforces that, so
  -- `render` must never produce an empty field: a record its own reader
  -- refuses is indistinguishable from a missing one.
  check (Attest.RunRecord.parse
      ({ record with ccompVersion := "", machine := "  " } : Attest.RunRecord).render
    |>.isSome)
    "a record with an empty field must still round trip"
  check ((Attest.RunRecord.parse
      (text.replace "leancompcert-run/1" "leancompcert-run/2")).isNone)
    "a run record with an unknown schema must be refused"
  check ((Attest.RunRecord.parse (text.replace "agrees" "victory")).isNone)
    "a run record with an unknown outcome must be refused"
  -- `compiled` and `executed` are different facts about the same attempt, and
  -- neither is "the run passed" — that is `outcome = .agrees` and nothing else.
  check (Attest.RunOutcome.compiled .linkFailed
      && !(Attest.RunOutcome.executed .linkFailed))
    "a link failure means ccomp accepted the C and nothing ran"
  check (!(Attest.RunOutcome.compiled .compileFailed))
    "a compile failure must not read as compiled"
  check (Attest.RunOutcome.executed .abnormal
      && Attest.RunOutcome.executed .disagrees)
    "a killed artifact and a disagreement both executed"
  check (Attest.RunOutcome.executed .abnormal
      && Attest.RunOutcome.abnormal != Attest.RunOutcome.agrees)
    "executing is not agreeing"
  -- 5. An entry with no Artifact must not be filed under the straight-line
  -- route, which is the one whose proved chain covers an emission it is not.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with
        leanSide := .unbindable "no Computation at this scale" }).isEmpty)
    "an unbindable entry defaulting to the straight-line route was accepted"
  check (Attest.Ledger.defectsOf
      { ledgerEntry with
        leanSide := .unbindable "no Computation at this scale"
        routeLabel := Attest.arrayRolledLabel }).isEmpty
    "an unbindable entry with a route no Artifact claims reported a defect"
  -- 6. A gap with no explanation is an omission, not a refusal.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with
        leanSide := .unbindable ""
        routeLabel := Attest.arrayRolledLabel }).isEmpty)
    "an unexplained gap was accepted"
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with leanSide := .artifactOnly ledgerArtifact "  " }).isEmpty)
    "a whitespace-only gap was accepted"
  -- 7. A declared entry point that does not occur in the compiled text.
  check (!(Attest.Ledger.defectsOf
      { ledgerEntry with entryPoint := "l_NoSuchSymbol" }).isEmpty)
    "an entry point absent from the emitted C was accepted"

def main : IO Unit := do
  testSymbols
  testInterpreter
  testCEmission
  testCValidator
  testIndexedMemory
  testPolicies
  testVerifiedDecide
  testMertensCertificate
  testWideMertensCertificate
  testSquarefreeMertensCertificate
  testReflectedCertificate
  testAlgorithmProof
  testArrayAlgorithmProof
  testPackagingScale
  testFixedPointCertificate
  testRolledEmission
  testDirectClight
  testProgramLedger
  LeanCompCertTests.Docs.run
  testAttestTool
  IO.println "LeanCompCert tests passed"
