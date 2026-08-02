import LeanCompCert.Ports.DeficitProduct

/-!
Benchmark support: emit the **rolled** C artifact for the singular-series
deficit Euler product.

`LeanCompCert.Ports.DeficitProduct.deficitProgram_denote` proves the emitted
program denotes `value c`, the epilogue's verdict on a fold written in
ordinary `Nat` arithmetic.  A run of the artifact is evidence for that value;
it discharges no Lean obligation on its own.

Run with
  lake env lean --run bench/DeficitProductEmit.lean \
    LO LEN ROUNDS ACCINIT THRESHOLD OUT [VALUE]
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.DeficitProduct

namespace Bench.DeficitProductEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.DeficitProductEmit

open Bench.DeficitProductEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [loS, lenS, rndS, accS, thrS, out] => go loS lenS rndS accS thrS out 0
  | [loS, lenS, rndS, accS, thrS, out, vS] =>
      match vS.toNat? with
      | none => do IO.eprintln "bad value"; return 1
      | some v => go loS lenS rndS accS thrS out v
  | _ => do
      IO.eprintln "usage: LO LEN ROUNDS ACCINIT THRESHOLD OUT [VALUE]"
      return 1
where
  go (loS lenS rndS accS thrS out : String) (value : Nat) : IO UInt32 := do
    match [loS, lenS, rndS, accS, thrS].mapM String.toNat? with
    | some [lo, len, rnd, acc, thr] => do
      let c : Cfg :=
        { lo := lo, len := len, rounds := rnd, accInit := acc, threshold := thr }
      let p := deficitProgram c
      let name := s!"DeficitProduct{lo}x{len}x{rnd}"
      match emitRolled p name with
      | .error errs => do
          for e in errs do IO.eprintln e
          return 1
      | .ok src => do
          IO.FS.writeFile out (src ++ mainC name value)
          IO.println s!"{lo} {len} {rnd} ok loopCount={len * rnd}"
          return 0
    | _ => do IO.eprintln "bad numeric argument"; return 1
