import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Verified.ArrayAuditFromArray

/-! Emit the retained positive and fail-safe dense-head CompCert programs. -/

open LeanCompCert
open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Verified.ArrayState

def driver (name : String) (p : AProgram) (expected : R2Seed)
    (audit : Bool) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString p.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t out = l_" ++ name ++ "((uint64_t *)(uintptr_t)cells);\n" ++
  "  printf(\"out %llu\\n\", (unsigned long long)out);\n" ++
  (if audit then
    "  return out == UINT64_C(0) ? 0 : 2;\n"
  else
    String.join ((List.range 11).map fun i =>
      "  printf(\"slot" ++ toString i ++ " %llu\\n\", " ++
        "(unsigned long long)cells[" ++ toString (p.arrayLen - 21 + i) ++ "]);\n") ++
    String.join ((List.range 11).map fun i =>
      "  if (cells[" ++ toString (p.arrayLen - 21 + i) ++
        "] != UINT64_C(" ++ toString (expected.words[i]!) ++
        ")) return " ++ toString (10 + i) ++ ";\n") ++
    "  return out == UINT64_C(0) ? 0 : 2;\n") ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  let (shard, mode, outPath) := match args with
    | [shard, mode, outPath] => (shard, mode, outPath)
    | _ => ("", "", "")
  if (shard != "first" && shard != "second") ||
      (mode != "positive" && mode != "audit") then
    IO.eprintln "usage: first|second positive|audit OUT.c"
    return 1
  let p := if shard = "first" then
      r2DenseHeadProgram denseHeadFirstCfg denseHeadFirstSeed
    else r2DenseHeadProgram denseHeadSecondCfg denseHeadSecondSeed
  let expected := if shard = "first" then denseHeadFirstCarry
    else denseHeadFinalCarry
  let audit := mode = "audit"
  let name := "r2dense" ++ shard ++ if audit then "audit" else ""
  let emitted := if audit then
      (LeanCompCert.Verified.ArrayAudit.auditProgram p).emitRolled
        name
    else p.emitRolled name
  match emitted with
  | .error errs =>
      for e in errs do IO.eprintln e
      return 1
  | .ok src =>
      IO.FS.writeFile outPath (src ++ driver name p expected audit)
      IO.println s!"shard={shard} mode={mode} arrayLen={p.arrayLen} loopCount={p.loopCount}"
      return 0
