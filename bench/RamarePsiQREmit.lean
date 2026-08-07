import LeanCompCert.Ports.RamarePsiQRBlock
import LeanCompCert.Verified.Rolled

/-!
Emit the proved one-step Ramaré quotient/remainder block with a small hosted
timing harness.  The harness repeats calls only to make the 22-instruction
function measurable; the emitted function itself is exactly
`PsiQRBlock.program`, covered by `PsiQRBlock.program_compiled`.

```
lake env lean --run bench/RamarePsiQREmit.lean REPS OUT
```
-/

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.PsiQRBlock

namespace Bench.RamarePsiQREmit

def sampleN : Nat := 10001
def sampleLam : Nat := 123456789
def sample : PsiQR := ⟨281474976710650, 5000⟩
def expected : Nat := (sample.advance sampleN sampleLam).q

def mainC (name : String) (reps : Nat) : String :=
  "\nint main(void)\n{\n" ++
  "    volatile uint64_t x = UINT64_C(0);\n" ++
  "    for (uint64_t i = UINT64_C(0); i < UINT64_C(" ++ toString reps ++
  "); ++i) x ^= l_" ++ name ++ "();\n" ++
  "    return x == UINT64_C(" ++ toString (if reps % 2 = 0 then 0 else expected) ++
  ") ? 0 : 2;\n}\n"

end Bench.RamarePsiQREmit

open Bench.RamarePsiQREmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [repsS, out] =>
      let some reps := repsS.toNat? | do IO.eprintln "bad REPS"; return 1
      let p := program sample.q sample.r sampleLam sampleN rq
      let name := "RamarePsiQRStep"
      match emitRolled p name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ mainC name reps)
          IO.println s!"reps={reps} body={p.body.length} expected={expected}"
          return 0
  | _ =>
      IO.eprintln "usage: REPS OUT"
      return 1
