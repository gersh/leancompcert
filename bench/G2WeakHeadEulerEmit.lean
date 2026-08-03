import LeanCompCert.Ports.G2WeakHeadEuler

/-!
Benchmark support: emit the **rolled** C artifact for the Helfgott §4.1.3
G₂-weak Euler-product head sweep.

`LeanCompCert.Ports.G2WeakHeadEuler.g2wProgram_denote` proves the emitted
program denotes `value c`, the violation flag of a fold written in ordinary
`Nat` arithmetic.  A run of the artifact is evidence for that value; it
discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/G2WeakHeadEulerEmit.lean \
    LO LEN ROUNDS AMAX SDK STK SDM STM SDS STS OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.G2WeakHeadEuler

namespace Bench.G2WeakHeadEulerEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.G2WeakHeadEulerEmit

open Bench.G2WeakHeadEulerEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loS, lenS, rndS, amaxS, sdKS, stKS, sdMS, stMS, sdSS, stSS, out] =>
      go loS lenS rndS amaxS sdKS stKS sdMS stMS sdSS stSS out 0
  | [loS, lenS, rndS, amaxS, sdKS, stKS, sdMS, stMS, sdSS, stSS, out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v => go loS lenS rndS amaxS sdKS stKS sdMS stMS sdSS stSS out v
  | _ => do
      IO.eprintln
        "usage: LO LEN ROUNDS AMAX SDK STK SDM STM SDS STS OUT [VALUE]"
      return 1
where
  go (loS lenS rndS amaxS sdKS stKS sdMS stMS sdSS stSS out : String)
      (value : Nat) : IO UInt32 := do
    let nums := [loS, lenS, rndS, amaxS, sdKS, stKS, sdMS, stMS, sdSS, stSS]
    match nums.mapM String.toNat? with
    | none => do IO.eprintln "bad numeric argument"; return 1
    | some [lo, len, rnd, amax, sdK, stK, sdM, stM, sdS, stS] => do
      let c : Cfg :=
        { lo := lo, len := len, rounds := rnd, amax := amax
        , sdK := sdK, stK := stK, sdM := sdM, stM := stM
        , sdS := sdS, stS := stS }
      let p := g2wProgram c
      let name := s!"G2WeakHeadEuler{lo}x{len}x{rnd}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{lo} {len} {rnd} ok loopCount={len * rnd}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
