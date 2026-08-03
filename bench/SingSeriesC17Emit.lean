import LeanCompCert.Ports.SingSeriesC17

/-!
Benchmark support: emit the **rolled** C artifact for the Helfgott `(C.17)`
running totient-mirror sweep.

`LeanCompCert.Ports.SingSeriesC17.c17Program_denote` proves the emitted
program denotes `value c`, the violation flag of a fold written in ordinary
`Nat` arithmetic.  A run of the artifact is evidence for that value; it
discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/SingSeriesC17Emit.lean \
    LO LEN ROUNDS SCALE M0 ACCMUL LOWER ACCCAP OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.SingSeriesC17

namespace Bench.SingSeriesC17Emit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.SingSeriesC17Emit

open Bench.SingSeriesC17Emit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loS, lenS, rndS, scS, m0S, mulS, lowS, capS, out] =>
      go loS lenS rndS scS m0S mulS lowS capS out 0
  | [loS, lenS, rndS, scS, m0S, mulS, lowS, capS, out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v => go loS lenS rndS scS m0S mulS lowS capS out v
  | _ => do
      IO.eprintln "usage: LO LEN ROUNDS SCALE M0 ACCMUL LOWER ACCCAP OUT [VALUE]"
      return 1
where
  go (loS lenS rndS scS m0S mulS lowS capS out : String)
      (value : Nat) : IO UInt32 := do
    let nums := [loS, lenS, rndS, scS, m0S, mulS, lowS, capS]
    match nums.mapM String.toNat? with
    | none => do IO.eprintln "bad numeric argument"; return 1
    | some [lo, len, rnd, sc, m0, mul, low, cap] => do
      let c : Cfg :=
        { lo := lo, len := len, rounds := rnd, scale := sc, m0 := m0
        , accMul := mul, lower := low, accCap := cap }
      let p := c17Program c
      let name := s!"SingSeriesC17{lo}x{len}x{rnd}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{lo} {len} {rnd} ok loopCount={len * rnd}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
