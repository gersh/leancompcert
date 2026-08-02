import LeanCompCert.Ports.MertensCDEM

/-!
Benchmark support: emit the **rolled** C artifact for the Cohen--Dress--El
Marraki per-row Mertens sweep.

`LeanCompCert.Ports.MertensCDEM.cdemProgram_denote` proves the emitted
program denotes `value c`, the violation flag of a fold written in ordinary
`Nat` arithmetic.  A run of the artifact is evidence for that value; it
discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/MertensCDEMEmit.lean \
    LO LEN ROUNDS BIAS M0 LOWER DEN SLACK CAP ANCHORX ANCHORM OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MertensCDEM

namespace Bench.MertensCDEMEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.MertensCDEMEmit

open Bench.MertensCDEMEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loS, lenS, rndS, biasS, m0S, lowS, denS, slkS, capS, axS, amS, out] =>
      go loS lenS rndS biasS m0S lowS denS slkS capS axS amS out 0
  | [loS, lenS, rndS, biasS, m0S, lowS, denS, slkS, capS, axS, amS, out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v => go loS lenS rndS biasS m0S lowS denS slkS capS axS amS out v
  | _ => do
      IO.eprintln "usage: LO LEN ROUNDS BIAS M0 LOWER DEN SLACK CAP ANCHORX ANCHORM OUT [VALUE]"
      return 1
where
  go (loS lenS rndS biasS m0S lowS denS slkS capS axS amS out : String)
      (value : Nat) : IO UInt32 := do
    let nums := [loS, lenS, rndS, biasS, m0S, lowS, denS, slkS, capS, axS, amS]
    match nums.mapM String.toNat? with
    | none => do IO.eprintln "bad numeric argument"; return 1
    | some [lo, len, rnd, bias, m0, low, den, slk, cap, ax, am] => do
      let c : Cfg :=
        { lo := lo, len := len, rounds := rnd, bias := bias, m0 := m0
        , lower := low, den := den, slack := slk, cap := cap
        , anchorX := ax, anchorM := am }
      let p := cdemProgram c
      let name := s!"MertensCDEM{lo}x{len}x{rnd}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{lo} {len} {rnd} ok loopCount={len * rnd}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
