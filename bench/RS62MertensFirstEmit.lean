import LeanCompCert.Ports.RS62MertensFirst

/-!
Benchmark support: emit the **rolled** C artifact for the RS62 first-Mertens
`Λ(n)/n` ladder fold.

`LeanCompCert.Ports.RS62MertensFirst.mfProgram_denote` proves the emitted
program denotes `value c`, the violation flag of a fold written in ordinary
`Nat` arithmetic.  A run of the artifact is evidence for that value; it
discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/RS62MertensFirstEmit.lean \
    N0 LEN ROUNDS ANCHOR LOGL0 LOGU0 SUML0 SUMU0 C752 C060 C055 CAP OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RS62MertensFirst

namespace Bench.RS62MertensFirstEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.RS62MertensFirstEmit

open Bench.RS62MertensFirstEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [n0S, lenS, rndS, ancS, lLS, lUS, sLS, sUS, c752S, c060S, c055S, capS,
      out] =>
      go n0S lenS rndS ancS lLS lUS sLS sUS c752S c060S c055S capS out 0
  | [n0S, lenS, rndS, ancS, lLS, lUS, sLS, sUS, c752S, c060S, c055S, capS,
      out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v =>
          go n0S lenS rndS ancS lLS lUS sLS sUS c752S c060S c055S capS out v
  | _ => do
      IO.eprintln
        "usage: N0 LEN ROUNDS ANCHOR LOGL0 LOGU0 SUML0 SUMU0 C752 C060 C055 CAP OUT [VALUE]"
      return 1
where
  go (n0S lenS rndS ancS lLS lUS sLS sUS c752S c060S c055S capS out : String)
      (value : Nat) : IO UInt32 := do
    let nums := [n0S, lenS, rndS, ancS, lLS, lUS, sLS, sUS, c752S, c060S,
      c055S, capS]
    match nums.mapM String.toNat? with
    | none => do IO.eprintln "bad numeric argument"; return 1
    | some [n0, len, rnd, anc, lL, lU, sL, sU, c752, c060, c055, cap] => do
      let c : Cfg :=
        { n0 := n0, len := len, rounds := rnd, anchor := anc
        , logL0 := lL, logU0 := lU, sumL0 := sL, sumU0 := sU
        , c752 := c752, c060 := c060, c055 := c055, cap := cap }
      let p := mfProgram c
      let name := s!"RS62MertensFirst{n0}x{len}x{rnd}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{n0} {len} {rnd} ok loopCount={len * rnd}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
