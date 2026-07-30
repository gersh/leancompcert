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

`consumer check-native [--force] [--dir DIR] [--include DIR] [--hosted]`
— compile the certificate with CompCert and run the native cross-check,
cached by content hash of the generated C: nothing re-runs unless the
generated C actually changed.

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
