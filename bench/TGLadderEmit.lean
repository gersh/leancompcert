import LeanCompCert.Ports.TGLadder

/-!
Benchmark support: emit the **unrolled** C artifact for stage (c) of the
Helfgott–Platt prime ladder — the ladder-gap checker of
`tg_goldbach_ladder_native.cpp` (arXiv:1305.3062v2, sections 2--4).

The input is the delta stream the reference producer writes on the wire
(`writeVarint(rung.k - previousK)`), minus its first record, which is the
first rung's `k` and is checked against the anchor instead.  The program
returns `0` exactly when every delta lies in `[1, BOUND]` and the deltas
total `EXPECTED`; `LeanCompCert.Ports.TGLadder.ladderProgram_denote` proves
that equivalence, and `covers_of_accepts` turns it into the coverage of
`(anchor, target]`.

The loop runs over data, so the emission is unrolled and the C file grows
with the record count.

Run with `lake env lean --run bench/TGLadderEmit.lean DELTAS BOUND EXPECTED OUT`.
`DELTAS` is a text file with one delta per line.  Emission only.
-/

open LeanCompCert
open LeanCompCert.Ports.TGLadder

namespace Bench.TGLadderEmit

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(0) ? 0 : 1;\n}\n"

end Bench.TGLadderEmit

open Bench.TGLadderEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [deltaFile, boundStr, expectedStr, out] =>
      let some bound := boundStr.toNat? | do IO.eprintln "bad bound"; return 1
      let some expected := expectedStr.toNat? |
        do IO.eprintln "bad expected"; return 1
      let text ← IO.FS.readFile deltaFile
      let ds : List Nat := (text.splitOn "\n").filterMap (fun line =>
        (line.trimAscii).toString.toNat?)
      let p := ladderProgram bound expected ds
      let name := s!"TGLadder{ds.length}"
      match emitUnrolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"{ds.length} records ok"
          return 0
  | _ => do IO.eprintln "usage: DELTAS BOUND EXPECTED OUT"; return 1
