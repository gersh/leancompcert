import LeanCompCert.Ports.ExpFixPort

/-!
Emission driver for the fixed-point exponential of `Ports.ExpFixPort`.

```
lake env lean --run bench/ExpFixEmit.lean P S R ROUNDS OUT
```

Emits the rolled C for `expProgram ⟨P, S, R, ROUNDS, rViol⟩`, i.e. the mantissa
of `2 ^ (R / 2^S)` at precision `P`, computed in `ROUNDS` rounds of the
restoring square root with every root certified in flight.  The driver prints

```
viol V   mant M   rem Q
```

where `V` is the number of failed root certifications (`0` means every root
passed `ExpFixed.expOK`'s two comparisons, so by `expOK_sound` the run *is*
`expIter` and `expFix_bracket` applies), `M` is the mantissa and `Q` the
unconsumed exponent bits.  Two further lines split `V` into the roots that came
out **too large** and the roots that came out **too small**, and the exit
status is `0` only when both are zero — see `hostedDriver`.

Setting `ROUNDS` above `S` is the benchmark mode: the exponent register empties
and every later round recomputes `2^P`, but the body is branch-free and its
instruction count is data-independent, so the cost per round is unchanged.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Ports.ExpFixPort

namespace Bench.ExpFixEmit

/-- The driver prints the mantissa, the unconsumed exponent bits and both
failure classes, and then **decides**: it exits `0` exactly when every root
passed both of `ExpFixed.expOK`'s comparisons, which is the condition under
which `expOK_sound` makes the run `expIter` and `expFix_bracket` applies.

| exit | meaning |
| ---: | --- |
| `0` | every root certified |
| `1` | the two classes do not sum to the aggregate |
| `2` | `root_over` — some `v·v > Z`: the root came out too large |
| `3` | `root_under` — some `Z ≥ (v+1)·(v+1)`: too small |
-/
def hostedDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"viol %llu mant %llu rem %llu\\n\",\n" ++
  "           (unsigned long long)r,\n" ++
  "           (unsigned long long)cells[0],\n" ++
  "           (unsigned long long)cells[1]);\n" ++
  "    printf(\"class root_over %llu\\n\", (unsigned long long)cells[3]);\n" ++
  "    printf(\"class root_under %llu\\n\", (unsigned long long)cells[4]);\n" ++
  "    if (cells[3] + cells[4] != r) {\n" ++
  "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
  "               (unsigned long long)(cells[3] + cells[4]),\n" ++
  "               (unsigned long long)r);\n" ++
  "        return 1;\n    }\n" ++
  "    if (cells[3] != UINT64_C(0)) {\n" ++
  "        printf(\"verdict FAIL root_over\\n\");\n        return 2;\n    }\n" ++
  "    if (cells[4] != UINT64_C(0)) {\n" ++
  "        printf(\"verdict FAIL root_under\\n\");\n        return 3;\n    }\n" ++
  "    printf(\"verdict PASS\\n\");\n" ++
  "    return 0;\n}\n"

end Bench.ExpFixEmit

open Bench.ExpFixEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | pS :: sS :: rS :: roundS :: out :: _ => do
      let some P := pS.toNat? | do IO.eprintln "bad P"; return 1
      let some S := sS.toNat? | do IO.eprintln "bad S"; return 1
      let some r := rS.toNat? | do IO.eprintln "bad R"; return 1
      let some rounds := roundS.toNat? | do IO.eprintln "bad ROUNDS"; return 1
      if P > 30 then
        IO.eprintln s!"P={P} exceeds the proved word-size bound P ≤ 30"
        return 1
      if r ≥ 2 ^ S then
        IO.eprintln s!"R={r} must be below 2^S = {2 ^ S}"
        return 1
      let c : ExpCfg := ⟨P, S, r, rounds, rViol⟩
      let p := expProgram c
      let name := s!"ExpP{P}S{S}R{r}N{rounds}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ hostedDriver name p.arrayLen)
          IO.println s!"P={P} S={S} R={r} rounds={rounds} name={name}"
          IO.println s!"  bodyLen={p.body.length} initLen={p.init.length} arrayLen={p.arrayLen}"
          IO.println s!"  instructions={p.body.length * rounds}"
          return 0
  | _ => do
      IO.eprintln "usage: P S R ROUNDS OUT"
      return 1
