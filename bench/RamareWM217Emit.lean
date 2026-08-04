import LeanCompCert.Ports.RamareWM217
import LeanCompCert.Verified.ArrayBridge

/-!
Rolled emitter for the Helfgott (2.17) weighted-moment sweep
(`Ports/RamareWM217.lean`).

Usage:

```
lake env lean --run bench/RamareWM217Emit.lean \
  N0 LEN B LOWER SEEDL ACC0 CAPA TABLELEN SEEDSFILE OUT
```

`SEEDSFILE` holds one `cell value` pair per line — the ladder seeds
`(p, directLogUBfp p)` for the prime bases, produced (and later certified) in
the goldbach tree.  Emission refuses a configuration that fails `wmOK`.
Emission only; no proof obligation is discharged here.
-/

open LeanCompCert.Ports.RamareWM217

namespace Bench.RamareWM217Emit

def arrayDriver (name : String) (cells : Nat) (expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 2;\n}\n"

def parseSeeds (text : String) : Option (List (Nat × Nat)) := do
  let mut out : List (Nat × Nat) := []
  for line in text.splitOn "\n" do
    let t := line.trim
    if t.isEmpty then continue
    match t.splitOn " " with
    | [a, b] =>
        let some cell := a.toNat? | none
        let some value := b.toNat? | none
        out := (cell, value) :: out
    | _ => none
  return out.reverse

end Bench.RamareWM217Emit

open Bench.RamareWM217Emit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [n0S, lenS, bS, lowS, seedLS, acc0S, capS, tblS, seedsFile, out] =>
      let some n0 := n0S.toNat? | do IO.eprintln "bad N0"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad LEN"; return 1
      let some B := bS.toNat? | do IO.eprintln "bad B"; return 1
      let some lower := lowS.toNat? | do IO.eprintln "bad LOWER"; return 1
      let some seedL := seedLS.toNat? | do IO.eprintln "bad SEEDL"; return 1
      let some acc0 := acc0S.toNat? | do IO.eprintln "bad ACC0"; return 1
      let some capA := capS.toNat? | do IO.eprintln "bad CAPA"; return 1
      let some tableLen := tblS.toNat? | do IO.eprintln "bad TABLELEN"; return 1
      let text ← IO.FS.readFile seedsFile
      let some seeds := parseSeeds text | do IO.eprintln "bad seeds"; return 1
      let c : Cfg :=
        { n0, len, B, lower, seedL, acc0, capA, tableLen, seeds }
      if !wmOK c then do IO.eprintln "wmOK failed"; return 1
      let p := wmProgram c
      let name := s!"RamareWM217x{n0}x{len}x{B}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ arrayDriver name p.arrayLen 0)
          IO.println s!"wm217 n0={n0} len={len} B={B} loopCount={p.loopCount} \
            body={p.body.length} init={p.init.length} arrayLen={p.arrayLen}"
          return 0
  | _ => do
      IO.eprintln "usage: N0 LEN B LOWER SEEDL ACC0 CAPA TABLELEN SEEDSFILE OUT"
      return 1
