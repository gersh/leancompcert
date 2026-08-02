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
import LeanCompCert.NativeCheck

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

/-- Registered certificates.

`certifiedValue` is the constant the generated `main` compares against, taken
from the certificate's own definition wherever the certificate has one rather
than spelled out again here.  It is required by `--attest` and ignored
otherwise.  Three of these (`wide-mertens`, `squarefree-mertens`, `reflected`)
compare against `1` because their emitted function returns a flag: the wide
value is checked *inside* the program and the entry point reports whether it
matched. -/
private def nativeCerts : List NativeCheck.Cert := [
  { name := "verified-decide", emitted := Testing.VerifiedDecide.emittedC,
    certifiedValue := some 42 },
  { name := "mertens", emitted := Testing.MertensCertificate.emittedC,
    certifiedValue := some (Testing.MertensCertificate.expectedValue : Nat) },
  { name := "wide-mertens", emitted := Testing.WideMertensCertificate.emittedC,
    certifiedValue := some 1 },
  { name := "squarefree-mertens",
    emitted := Testing.SquarefreeMertensCertificate.emittedC,
    certifiedValue := some 1 },
  { name := "reflected", emitted := Testing.ReflectedCertificate.emittedC,
    certifiedValue := some 1 },
  { name := "fixedpoint", emitted := Testing.FixedPointCertificate.emittedC,
    certifiedValue := some (Testing.FixedPointCertificate.expectedValue : Nat) },
  { name := "rolled-10m", emitted := Testing.RolledFixedPoint.emittedC,
    routeLabel := Attest.EmissionRoute.rolledLoop.label,
    certifiedValue := some (Testing.RolledFixedPoint.expectedBig : Nat) },
  { name := "proth", emitted := Testing.ProthCertificate.emittedC,
    certifiedValue := some 0 },
  { name := "mobius-array", emitted := Testing.ArrayMobiusCertificate.emittedC,
    certifiedValue := some (Testing.ArrayMobiusCertificate.expected : Nat) },
  { name := "mobius-seg", emitted := Testing.ArraySegCertificate.emittedC,
    certifiedValue := some (Testing.ArraySegCertificate.expected : Nat) },
  { name := "cdem-abel", emitted := Testing.AbelScanCertificate.emittedC,
    certifiedValue := some (Testing.AbelScanCertificate.expected : Nat) },
  { name := "dirichlet-ladder",
    emitted := Testing.DirichletLadderCertificate.emittedC,
    certifiedValue := some (Testing.DirichletLadderCertificate.expected : Nat) },
  { name := "rs62-ladder-sl", emitted := Testing.RS62LadderCertificate.emittedCSL,
    certifiedValue := some (Testing.RS62LadderCertificate.expectedSL : Nat) },
  { name := "rs62-ladder-su", emitted := Testing.RS62LadderCertificate.emittedCSU,
    certifiedValue := some (Testing.RS62LadderCertificate.expectedSU : Nat) }
]

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
