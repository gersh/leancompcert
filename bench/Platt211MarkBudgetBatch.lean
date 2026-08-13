import LeanCompCert.Ports.ArraySegMobiusPlatt211MarkBudgetCertificate
import LeanCompCert.Verified.Rolled

/-!
Batch emitter for the post-prefix Platt (2.11) full-table marking-budget
verdicts.  Each job is `IDX OUT.c`; the hosted driver exits successfully only
when the proved weighted-prime sieve returns zero.
-/

namespace Bench.Platt211MarkBudgetBatch

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySieveWeightedSum
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData

def driver (symbol : String) (cells : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n    return " ++ LeanCompCert.ABI.mangle symbol ++
    "(cells) == UINT64_C(0) ? 0 : 1;\n}\n"

def emitOne (idx : Nat) (out : String) : IO Bool := do
  let some row := rows[idx]? | do
    IO.eprintln s!"row index out of range: {idx}"
    return false
  if row.idx != idx then
    IO.eprintln s!"manifest index mismatch at {idx}: {row.idx}"
    return false
  if row.idx < 75 then
    IO.eprintln s!"row {idx} belongs to the independently certified prefix"
    return false
  let p := sieveWeightedBudgetProgram row.bootBound (row.rootCap + 1)
    row.segLen 2 row.markSteps
  let symbol := s!"platt211_mark_budget_{row.idx}"
  match p.emitRolled symbol with
  | .error errors =>
      for error in errors do IO.eprintln error
      return false
  | .ok source =>
      IO.FS.writeFile out (source ++ driver symbol p.arrayLen)
      IO.println s!"job {idx} rootCap={row.rootCap} segLen={row.segLen} loops={p.loopCount} expected=0 out={out}"
      return true

def emitAll (outDir : String) : IO Bool := do
  IO.FS.createDirAll outDir
  let mut ok := true
  for idx in List.range rows.length do
    if 75 ≤ idx then
      unless ← emitOne idx s!"{outDir}/row_{idx}.c" do ok := false
  return ok

end Bench.Platt211MarkBudgetBatch

open Bench.Platt211MarkBudgetBatch in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["all", outDir] =>
      return if ← emitAll outDir then 0 else 1
  | [jobs] =>
      let input ← IO.FS.readFile jobs
      let mut ok := true
      for line in input.splitOn "\n" do
        let fields := (line.splitOn " ").filter (· ≠ "")
        match fields with
        | [] => pure ()
        | [idxS, out] =>
            let some idx := idxS.toNat? | do
              IO.eprintln s!"bad index: {idxS}"
              ok := false
              continue
            unless ← emitOne idx out do ok := false
        | _ =>
            IO.eprintln s!"bad job line: {line}"
            ok := false
      return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: Platt211MarkBudgetBatch JOBS | all OUTDIR"
      return 2
