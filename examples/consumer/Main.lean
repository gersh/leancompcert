import Consumer
import LeanCompCert.NativeCheck

open LeanCompCert

/-- The consumer's registered certificates for the cached native
cross-check. -/
def nativeCerts : List NativeCheck.Cert := [
  { name := "demo"
    emitted := Consumer.emittedC
    certifiedValue := some (Consumer.expectedValue : Nat) }
]

/--
`consumer [output.c]` — write the emitted C for the certified computation
(default `demo.c`).

`consumer check-native [--force] [--dir DIR] [--include DIR] [--hosted]`
— compile the certificate with CompCert and run the native cross-check,
cached by content hash of the generated C: nothing re-runs unless the
generated C actually changed.

`consumer attest-keygen` then `consumer attest` — the same run, plus a
signed run receipt per passing certificate.  `consumer verify-receipt FILE`
re-emits the C and re-checks the digest and the signature.  A locally
signed receipt is **tamper-evident, not attested**; see
`docs/use-case-3-attested-run-receipts.md`.

The link is freestanding (no libc) by default, so the startup stub in
`runtime/start/` has to be locatable from this sub-project; `--start-dir`
is passed explicitly below.  `--hosted` falls back to the old
`ccomp -o exe exe.c` link.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | "check-native" :: rest =>
      NativeCheck.run nativeCerts
        (rest ++ ["--start-dir", "../../runtime/start"])
  | "attest" :: rest =>
      NativeCheck.run nativeCerts
        ("--attest" :: rest ++ ["--start-dir", "../../runtime/start"])
  | "attest-keygen" :: rest =>
      let path : System.FilePath :=
        match rest with
        | ["--key", path] => path
        | _ => Attest.Tool.defaultKeyPath
      match ← Attest.Tool.generateKey path with
      | .error message => IO.eprintln s!"error: {message}"; pure 1
      | .ok message =>
          IO.println message
          IO.println
            "This is a LOCAL key: a receipt it signs is tamper-evident, not attested."
          pure 0
  | ["verify-receipt", file] =>
      let text ← IO.FS.readFile file
      match Attest.Tool.parseReceipt text with
      | .error message => IO.eprintln s!"error: {message}"; pure 1
      | .ok receipt =>
          let outcome ← Attest.Tool.verifyReceiptAgainst
            (".lake" / "build" / "attest" / "verify") receipt Consumer.emittedC
          for line in outcome.lines do IO.println line
          pure (if outcome.ok then 0 else 1)
  | _ =>
    let file := args.headD "demo.c"
    match Consumer.emittedC with
    | .error errors =>
        for error in errors do
          IO.eprintln error
        pure 1
    | .ok source =>
        IO.FS.writeFile file source
        IO.println s!"wrote {file}"
        pure 0
