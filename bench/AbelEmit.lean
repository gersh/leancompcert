import LeanCompCert.Ports.CDEMAbelScan

/-!
Emission driver for the CDEM Abel increment scan of `Ports.CDEMAbelScan`.

```
lake env lean --run bench/AbelEmit.lean W K SEGLEN SEGCOUNT OUT [EXPECTED] [ref]
```

The scan covers `[1, SEGLEN·SEGCOUNT]` with weight scale `W` and Möbius
prefix bound `K`.  Without `EXPECTED` the driver is *hosted*: it prints the
violation count and the twelve result slots, which is what the comparison
against `bench/ref_abel.c` reads.  With `EXPECTED` it is *freestanding* and
returns `0` exactly when the violation count matches, which is the shape
`check-native` and the timing runs use.

A third argument `ref` additionally prints the Lean-side reference fold, so
the emitter, the Lean reference and the C oracle can be compared without
leaving the shell.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan

namespace Bench.AbelEmit

def hostedDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < 12; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 12 + i]);\n" ++
  "    return 0;\n}\n"

def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.AbelEmit

open Bench.AbelEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | w :: k :: segLen :: segCount :: out :: rest => do
      let W := w.toNat!
      let K := k.toNat!
      let L := segLen.toNat!
      let C := segCount.toNat!
      if W == 0 || K == 0 || L == 0 || C == 0 then
        IO.eprintln "require W, K, SEGLEN, SEGCOUNT >= 1"
        return 2
      let cfg := Cfg.ofRange W K L C
      let p := abelProgram cfg
      let name := "CDEMAbel.scan"
      let sym := "CDEMAbel_scan"
      IO.println s!"W={W}"
      IO.println s!"K={K}"
      IO.println s!"HI={cfg.hi}"
      IO.println s!"PRIMES={cfg.pn}"
      IO.println s!"BS_STEPS={cfg.bsSteps}"
      IO.println s!"MARK_STEPS={cfg.markSteps}"
      IO.println s!"SIEVE_LEN={cfg.sieveLen}"
      IO.println s!"PERIOD={cfg.period}"
      IO.println s!"LOOP={p.loopCount}"
      IO.println s!"CELLS={cfg.arrayLen}"
      IO.println s!"BODY={cfg.body.length}"
      if rest.length ≥ 2 && rest[1]! ≠ "" then
        let r := Ref.fold W K cfg.hi
        IO.println s!"REF_UPOS={r.uPos}"
        IO.println s!"REF_UNEG={r.uNeg}"
        IO.println s!"REF_V={r.v}"
        IO.println s!"REF_TV={r.tv}"
      let driver :=
        match rest.head? with
        | some e =>
            match e.toNat? with
            | some n => exitDriver sym cfg.arrayLen n
            | none => hostedDriver sym cfg.arrayLen
        | none => hostedDriver sym cfg.arrayLen
      match p.emitRolled name with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"wrote {out}"
          return 0
  | _ =>
      IO.eprintln
        "usage: AbelEmit W K SEGLEN SEGCOUNT OUT [EXPECTED] [ref]"
      return 2
