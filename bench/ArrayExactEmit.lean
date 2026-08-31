import LeanCompCert.Verified.ArrayProgramClightEmit

/-!
Emit a compact, genuinely stateful `AProgram` and its symbolic Coq contract
for the exact Clight array bridge.  The example has a trillion loop iterations
and indexes sixteen cells cyclically, so it exercises pointer stores, pointer
loads, and symbolic large-count handling without running the computation.

```console
lake env lean --run bench/ArrayExactEmit.lean OUT.c SOURCE.v
```
-/

namespace LeanCompCert.Bench.ArrayExact

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayProgramClightEmit

def program : AProgram := {
  regCount := 3
  arrayLen := 16
  loopCount := 1000000000000
  init := [.scalar (.mov 0 (.lit 1))]
  body := [
    .scalar (.mov 1 .idx),
    .scalar (.binop 1 .urem (.reg 1) (.lit 16)),
    .load 2 1,
    .scalar (.binop 2 .add (.reg 2) (.reg 0)),
    .store 1 2]
  epilogue := [
    .scalar (.mov 1 (.lit 1)),
    .load 2 1]
  output := 2
}

theorem program_wf : program.WF := by decide

theorem program_loop_fits : program.loopCount < M := by decide

theorem program_array_fits : 8 * program.arrayLen ≤ M := by decide

def emittedC : Except (Array String) String :=
  program.emitRolled "ArrayExact.selftest"

def emittedCoqContract : String :=
  emitRolledAProgramContract "array_selftest" program program_wf
    program_loop_fits program_array_fits

private def writeOutput (name contents : String) : IO Unit := do
  let path : System.FilePath := name
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path contents

end LeanCompCert.Bench.ArrayExact

open LeanCompCert.Bench.ArrayExact

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
      IO.eprintln "usage: ArrayExactEmit OUT.c SOURCE.v"
      pure 2
