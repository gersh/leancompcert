import LeanCompCert.Ports.LiouvilleEllSweep

/-!
Benchmark support: emit the **rolled** C artifact for the Liouville
little-sum sweep (Ramaré 2014 Lemma 2.4(3), finite head `[8918, 4·10⁶)`).

`LeanCompCert.Ports.LiouvilleEllSweep.lProgram_denote` proves the emitted
program denotes `value c`, the violation flag of a fold written in ordinary
`Nat` arithmetic.  A run of the artifact is evidence for that value; it
discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/LiouvilleEllSweepEmit.lean \
    LO LEN EX DSM DBG NLO NHI E0 LB0 OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.LiouvilleEllSweep

namespace Bench.LiouvilleEllSweepEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.LiouvilleEllSweepEmit

open Bench.LiouvilleEllSweepEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loS, lenS, exS, dsmS, dbgS, nloS, nhiS, e0S, lb0S, out] =>
      go loS lenS exS dsmS dbgS nloS nhiS e0S lb0S out 0
  | [loS, lenS, exS, dsmS, dbgS, nloS, nhiS, e0S, lb0S, out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v => go loS lenS exS dsmS dbgS nloS nhiS e0S lb0S out v
  | _ => do
      IO.eprintln "usage: LO LEN EX DSM DBG NLO NHI E0 LB0 OUT [VALUE]"
      return 1
where
  go (loS lenS exS dsmS dbgS nloS nhiS e0S lb0S out : String)
      (value : Nat) : IO UInt32 := do
    let nums := [loS, lenS, exS, dsmS, dbgS, nloS, nhiS, e0S, lb0S]
    match nums.mapM String.toNat? with
    | some [lo, len, ex, dsm, dbg, nlo, nhi, e0, lb0] => do
      let c : Cfg :=
        { lo := lo, len := len, ex := ex, dsm := dsm, dbg := dbg
        , rounds := ex * dsm + (dbg - dsm)
        , nlo := nlo, nhi := nhi, e0 := e0, lb0 := lb0 }
      if lOK c = false then
        IO.eprintln "configuration fails lOK"
        return 1
      let p := lProgram c
      let name := s!"LiouvilleEllSweep{lo}x{len}x{c.rounds}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{lo} {len} {c.rounds} ok loopCount={len * c.rounds}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
