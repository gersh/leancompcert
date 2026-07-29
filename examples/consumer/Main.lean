import Consumer
import LeanCompCert.NativeCheck

open LeanCompCert

/-- The consumer's registered certificates for the cached native
cross-check. -/
def nativeCerts : List NativeCheck.Cert := [
  ⟨"demo", Consumer.emittedC⟩
]

/--
`consumer [output.c]` — write the emitted C for the certified computation
(default `demo.c`).

`consumer check-native [--force] [--dir DIR] [--include DIR]` — compile
the certificate with CompCert and run the native cross-check, cached by
content hash of the generated C: nothing re-runs unless the generated C
actually changed.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | "check-native" :: rest =>
      NativeCheck.run nativeCerts
        (rest ++ ["--include", "../../runtime/include"])
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
