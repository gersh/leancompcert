import LeanCompCert.Ports.RamareMStar140M
import LeanCompCert.Verified.ArrayBridge

/-!
Rolled emitter for the Ramaré `m★` sweep (`Ports/RamareMStar140M.lean`).

```
lake env lean --run bench/RamareMStar140MEmit.lean \
  N0 LEN B LIMIT TAB HANDOFF SEED CELL1 CAPL CAPS CAPLOG LOGSFILE OUT
```

`LOGSFILE` holds one `slot value` pair per line — the direct LeanCert
enclosures `directLogUpper m` in the order the checks consume them, certified
in the goldbach tree by `decide +kernel`.  Emission refuses a configuration
that fails `msOK`.  Emission only; no proof obligation is discharged here.
-/

open LeanCompCert.Ports.RamareMStar140M

namespace Bench.RamareMStar140MEmit

def arrayDriver (name : String) (cells : Nat) (expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 2;\n}\n"

def parseLogs (text : String) : Option (List (Nat × Nat)) := do
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

end Bench.RamareMStar140MEmit

open Bench.RamareMStar140MEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [n0S, lenS, bS, limS, tabS, hoS, seedS, cell1S, capLS, capSS, capLogS,
     logsFile, out] =>
      let some n0 := n0S.toNat? | do IO.eprintln "bad N0"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad LEN"; return 1
      let some B := bS.toNat? | do IO.eprintln "bad B"; return 1
      let some limit := limS.toNat? | do IO.eprintln "bad LIMIT"; return 1
      let some tab := tabS.toNat? | do IO.eprintln "bad TAB"; return 1
      let some handoff := hoS.toNat? | do IO.eprintln "bad HANDOFF"; return 1
      let some seed := seedS.toNat? | do IO.eprintln "bad SEED"; return 1
      let some cell1 := cell1S.toNat? | do IO.eprintln "bad CELL1"; return 1
      let some capL := capLS.toNat? | do IO.eprintln "bad CAPL"; return 1
      let some capS := capSS.toNat? | do IO.eprintln "bad CAPS"; return 1
      let some capLog := capLogS.toNat? | do IO.eprintln "bad CAPLOG"; return 1
      let text ← IO.FS.readFile logsFile
      let some logs := parseLogs text | do IO.eprintln "bad logs"; return 1
      let c : Cfg :=
        { n0, len, B, limit, tab, handoff, seed, cell1, capL, capS, capLog,
          logs }
      if !msOK c then do IO.eprintln "msOK failed"; return 1
      let p := msProgram c
      let name := s!"RamareMStar140Mx{limit}x{B}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ arrayDriver name p.arrayLen 0)
          IO.println s!"mstar limit={limit} len={len} B={B} \
            loopCount={p.loopCount} body={p.body.length} init={p.init.length} \
            arrayLen={p.arrayLen}"
          return 0
  | _ => do
      IO.eprintln "usage: N0 LEN B LIMIT TAB HANDOFF SEED CELL1 CAPL CAPS \
        CAPLOG LOGSFILE OUT"
      return 1
