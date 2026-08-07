import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.MobiusResidueTrial

/-!
Emit the rolled scalar fallback for the live Möbius residue.  The producer is
`MertensCDEM` trial division, so it is much slower than the segmented sieve,
but `MobiusResidueTrial.fullProgram_denote` proves the entire program denotes
the transparent joint fold whenever the executable `safeCheck` succeeds.

Usage:

```
lake env lean --run bench/MobiusResidueTrialEmit.lean \
  K LO LEN ROUNDS BIAS M0 LOWER DEN SLACK CAP ANCHORX ANCHORM OUT [VALUE]
```
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Ports.MobiusResidueTrial

namespace Bench.MobiusResidueTrialEmit

def mainC (name : String) (value : Nat) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++ "() == UINT64_C(" ++
    toString value ++ ") ? 0 : 1;\n}\n"

end Bench.MobiusResidueTrialEmit

open Bench.MobiusResidueTrialEmit in
def main (args : List String) : IO UInt32 := do
  let (raw, value) := match args with
    | [k, lo, len, rnd, bias, m0, low, den, slk, cap, ax, am, out] =>
        ([k, lo, len, rnd, bias, m0, low, den, slk, cap, ax, am, out], 0)
    | [k, lo, len, rnd, bias, m0, low, den, slk, cap, ax, am, out, v] =>
        match v.toNat? with
        | some n => ([k, lo, len, rnd, bias, m0, low, den, slk, cap, ax, am, out], n)
        | none => ([], 0)
    | _ => ([], 0)
  match raw with
  | [kS, loS, lenS, rndS, biasS, m0S, lowS, denS, slkS, capS, axS, amS, out] =>
      match [kS, loS, lenS, rndS, biasS, m0S, lowS, denS, slkS, capS,
          axS, amS].mapM String.toNat? with
      | some [k, lo, len, rnd, bias, m0, low, den, slk, cap, ax, am] => do
          let c : Cfg :=
            { lo := lo, len := len, rounds := rnd, bias := bias, m0 := m0
            , lower := low, den := den, slack := slk, cap := cap
            , anchorX := ax, anchorM := am }
          let p := fullProgram c k (standardResidue k)
          let name := s!"MobiusResidueTrial{k}x{lo}x{len}x{rnd}"
          match emitRolled p name with
          | .error errs => do
              for e in errs do IO.eprintln e
              return 1
          | .ok src => do
              IO.FS.writeFile out (src ++ mainC name value)
              IO.println s!"{k} {lo} {len} {rnd} ok loopCount={len * rnd}"
              return 0
      | _ => do IO.eprintln "bad numeric argument"; return 1
  | _ => do
      IO.eprintln "usage: K LO LEN ROUNDS BIAS M0 LOWER DEN SLACK CAP ANCHORX ANCHORM OUT [VALUE]"
      return 1
