import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Verified.ArrayProgramClightEmit

/-!
Emit one retained R2 dense-head production `AProgram` together with the
count-free symbolic Coq contract consumed by `scripts/clight-exact-array.py`.
This does not run the shard: all three prerequisites are structural proofs.

```console
lake env lean --run bench/R2DenseHeadExactEmit.lean \
  first OUT.c SOURCE.v
```
-/

namespace LeanCompCert.Bench.R2DenseHeadExact

open LeanCompCert
open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayProgramClightEmit

def firstProgram : AProgram :=
  r2DenseHeadProgram denseHeadFirstCfg denseHeadFirstSeed

def secondProgram : AProgram :=
  r2DenseHeadProgram denseHeadSecondCfg denseHeadSecondSeed

theorem firstProgram_wf : firstProgram.WF :=
  r2DenseHeadProgram_wf denseHeadFirstCfg denseHeadFirstSeed

theorem secondProgram_wf : secondProgram.WF :=
  r2DenseHeadProgram_wf denseHeadSecondCfg denseHeadSecondSeed

theorem firstProgram_loop_fits : firstProgram.loopCount < M := by decide

theorem secondProgram_loop_fits : secondProgram.loopCount < M := by decide

theorem firstProgram_array_fits : 8 * firstProgram.arrayLen ≤ M := by decide

theorem secondProgram_array_fits : 8 * secondProgram.arrayLen ≤ M := by decide

def firstC : Except (Array String) String :=
  firstProgram.emitRolled "r2densefirst"

def secondC : Except (Array String) String :=
  secondProgram.emitRolled "r2densesecond"

def firstContract : String :=
  emitRolledAProgramContract "r2densefirst" firstProgram firstProgram_wf
    firstProgram_loop_fits firstProgram_array_fits

def secondContract : String :=
  emitRolledAProgramContract "r2densesecond" secondProgram secondProgram_wf
    secondProgram_loop_fits secondProgram_array_fits

private def writeOutput (name contents : String) : IO Unit := do
  let path : System.FilePath := name
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def emitPair (emittedC : Except (Array String) String)
    (contract cPath sourcePath : String) : IO UInt32 := do
  match emittedC with
  | .error errors =>
      for error in errors do
        IO.eprintln s!"error: {error}"
      pure 1
  | .ok cSource =>
      writeOutput cPath cSource
      writeOutput sourcePath contract
      IO.println s!"wrote {cPath}"
      IO.println s!"wrote {sourcePath}"
      pure 0

end LeanCompCert.Bench.R2DenseHeadExact

open LeanCompCert.Bench.R2DenseHeadExact

def main (args : List String) : IO UInt32 := do
  match args with
  | ["first", cPath, sourcePath] =>
      emitPair firstC firstContract cPath sourcePath
  | ["second", cPath, sourcePath] =>
      emitPair secondC secondContract cPath sourcePath
  | _ =>
      IO.eprintln
        "usage: R2DenseHeadExactEmit first|second OUT.c SOURCE.v"
      pure 2
