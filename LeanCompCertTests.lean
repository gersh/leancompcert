import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Testing.RolledFixedPoint
import LeanCompCert.Verified.ClightEmit

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
  match Verified.ClightEmit.emitClight "direct_FixedPoint_mulShiftSum"
      Testing.FixedPointCertificate.computation.statements "v_1" with
  | none => throw (IO.userError "direct Clight emission failed")
  | some source => do
      check (source.contains "Definition f_direct_FixedPoint_mulShiftSum")
        "direct Clight emission lacks the function definition"
      check (source.contains "Sreturn (Some (Etempvar _v_1 tulong))")
        "direct Clight emission lacks the return"
      check (!source.contains "goto" && !source.contains "Sgoto")
        "direct Clight emission must be goto-free"

def main : IO Unit := do
  testSymbols
  testInterpreter
  testCEmission
  testCValidator
  testPolicies
  testVerifiedDecide
  testMertensCertificate
  testWideMertensCertificate
  testSquarefreeMertensCertificate
  testReflectedCertificate
  testPackagingScale
  testFixedPointCertificate
  testRolledEmission
  testDirectClight
  IO.println "LeanCompCert tests passed"
