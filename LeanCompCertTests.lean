import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide

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

def main : IO Unit := do
  testSymbols
  testInterpreter
  testCEmission
  testCValidator
  testPolicies
  testVerifiedDecide
  IO.println "LeanCompCert tests passed"
