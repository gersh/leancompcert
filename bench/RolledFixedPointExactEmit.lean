import LeanCompCert.Testing.RolledFixedPoint

/-!
Emit the two inputs to `scripts/clight-exact-rolled.py` for the 10^7 rolled
fixed-point regression.  This imports only the focused artifact module, so it
does not require the repository's aggregate executable to be rebuilt.

Run with:

```console
lake env lean --run bench/RolledFixedPointExactEmit.lean OUT.c SOURCE.v
```
-/

open LeanCompCert.Testing.RolledFixedPoint

private def writeOutput (name contents : String) : IO Unit := do
  let path : System.FilePath := name
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path contents

def main (args : List String) : IO UInt32 := do
  match args with
  | [cPath, sourcePath] =>
      match emittedC with
      | .error errors =>
          for error in errors do
            IO.eprintln s!"error: {error}"
          pure 1
      | .ok cSource =>
          writeOutput cPath cSource
          writeOutput sourcePath emittedCoqContract
          IO.println s!"wrote {cPath}"
          IO.println s!"wrote {sourcePath}"
          pure 0
  | _ =>
      IO.eprintln
        "usage: RolledFixedPointExactEmit OUT.c SOURCE.v"
      pure 2
