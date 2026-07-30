import LeanCompCert.Ports.TGProth

/-!
Benchmark support: emit the C artifact for stage (b) of the Helfgott–Platt
prime ladder — the Proth test of `tg_goldbach_ladder_native.cpp`
(arXiv:1305.3062v2, sections 2–4).

The program returns `0` exactly when `a^((N−1)/2) ≡ N − 1 (mod N)` for
`N = k·2ⁿ + 1`, which is Proth's criterion for the witness `a`.
`LeanCompCert.Ports.TGProth.prothProgram_denote` proves that equivalence.

Emission is rolled, so the C size is independent of the exponent length.

    lake env lean --run bench/TGProthEmit.lean N K A KBITS REPS OUT

`REPS` multiplies the loop count.  `REPS = 1` is the certificate: the loop
runs exactly `KBITS + N − 1` times and the output is the Proth verdict.
`REPS > 1` keeps the *same body* running longer and is a cost measurement
only — its output carries no theorem.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.TGProth

namespace Bench.TGProthEmit

def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++
    "() == UINT64_C(0) ? 0 : 1;\n}\n"

end Bench.TGProthEmit

open Bench.TGProthEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [nStr, kStr, aStr, kbitsStr, repsStr, out] =>
      let some n := nStr.toNat? | do IO.eprintln "bad N"; return 1
      let some k := kStr.toNat? | do IO.eprintln "bad K"; return 1
      let some a := aStr.toNat? | do IO.eprintln "bad A"; return 1
      let some kbits := kbitsStr.toNat? | do IO.eprintln "bad KBITS"; return 1
      let some reps := repsStr.toNat? | do IO.eprintln "bad REPS"; return 1
      let base := prothProgram n kbits k a
      let p := { base with loopCount := base.loopCount * reps }
      let name := s!"TGProth{n}x{kbits}"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name)
          IO.println s!"N = {prothN n k}"
          IO.println s!"loop = {p.loopCount}, body = {p.body.length} instructions"
          return 0
  | _ => do
      IO.eprintln "usage: N K A KBITS REPS OUT"
      return 1
