import LeanCompCert.Ports.Prop1224Row

/-!
Emission driver for the per-`q` row of `Ports.Prop1224Row`.

```
lake env lean --run bench/Prop1224RowEmit.lean LO SEGLEN SEGCOUNT TABLEHI UNROLL ROWS OUT
```

`TABLEHI` is the **global** `hi` the mark table is built for — `3300000000` in
production — so that a slice can be emitted with the primes of the whole sweep,
which is the only way to measure the cost at `q ≈ 3·10⁹` without sweeping
`3·10⁹` rows.  `UNROLL` is the squaring rounds per iteration in both engines;
it must divide `24`, and it is the module's main cost knob.  `ROWS` is how many
per-row lines the hosted driver prints, in `bench/ref_p1224.c`'s `row` format,
followed by that file's `SUM` line.  Only the **last** window's rows survive in
the planes, so a per-row comparison wants `SEGCOUNT = 1`.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Prop1224Row

namespace Bench.Prop1224RowEmit

def hostedDriver (name : String) (cells rowBase segLen resultBase lo rows : Nat) :
    String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    const uint64_t RB = " ++ toString rowBase ++ ", L = " ++ toString segLen ++
  ", RES = " ++ toString resultBase ++ ", LO = " ++ toString lo ++ ";\n" ++
  "    for (uint64_t i = 0; i < " ++ toString rows ++ "; i++) {\n" ++
  "        printf(\"%llu\", (unsigned long long)(LO + i));\n" ++
  "        for (int j = 0; j < 10; j++)\n" ++
  "            printf(\" %llu\", (unsigned long long)cells[RB + (uint64_t)j*L + i]);\n" ++
  "        printf(\"\\n\");\n" ++
  "    }\n" ++
  "    printf(\"SUM %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu\\n\",\n" ++
  "           (unsigned long long)cells[RES+0], (unsigned long long)cells[RES+2],\n" ++
  "           (unsigned long long)cells[RES+4], (unsigned long long)cells[RES+5],\n" ++
  "           (unsigned long long)cells[RES+6], (unsigned long long)cells[RES+7],\n" ++
  "           (unsigned long long)cells[RES+8], (unsigned long long)cells[RES+9],\n" ++
  "           (unsigned long long)cells[RES+10], (unsigned long long)cells[RES+11]);\n" ++
  "    printf(\"ROWS %llu CELLS0 %llu RET %llu\\n\",\n" ++
  "           (unsigned long long)cells[RES+1], (unsigned long long)cells[RES+3],\n" ++
  "           (unsigned long long)r);\n" ++
  "    return 0;\n}\n"

end Bench.Prop1224RowEmit

open Bench.Prop1224RowEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | loS :: lenS :: cntS :: thiS :: unrS :: rowsS :: out :: _ => do
      let nat (s : String) (nm : String) : IO Nat := do
        match s.toNat? with
        | some v => pure v
        | none => do IO.eprintln s!"bad {nm}"; pure 0
      let lo ← nat loS "LO"
      let len ← nat lenS "SEGLEN"
      let cnt ← nat cntS "SEGCOUNT"
      let thi ← nat thiS "TABLEHI"
      let unr ← nat unrS "UNROLL"
      let rows ← nat rowsS "ROWS"
      if lo < 1 then IO.eprintln "LO must be at least 1"; return 1
      if unr = 0 || 24 % unr ≠ 0 then
        IO.eprintln s!"UNROLL={unr} must divide 24"; return 1
      let c := RowCfg.ofChain lo len cnt thi unr
      if c.hi > thi then
        IO.eprintln s!"hi={c.hi} exceeds TABLEHI={thi}"; return 1
      if !tableOK thi then
        IO.eprintln "a packed mark-table field does not round-trip"; return 1
      let p := rowProgram c
      let name := s!"P1224RowLo{lo}L{len}N{cnt}U{unr}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out
            (src ++ hostedDriver name p.arrayLen c.rowBase c.segLen c.resultBase
              lo (min rows len))
          IO.println s!"lo={lo} hi={c.hi} tableHi={thi} root={Nat.sqrt thi} name={name}"
          IO.println s!"  primes={c.entries} markSteps={c.markSteps} slots={c.slots} \
smallQ={c.smallQ} roundsPerSlot={c.roundsPerSlot}"
          IO.println s!"  period={c.period} bodyLen={p.body.length} \
arrayLen={p.arrayLen} loopCount={p.loopCount}"
          IO.println s!"  itersPerRow(x100)={c.period * 100 / c.segLen} \
instructions={p.body.length * p.loopCount}"
          IO.println s!"  instrPerRow={(p.body.length * p.loopCount) / (c.segLen * c.segCount)}"
          return 0
  | _ => do
      IO.eprintln "usage: LO SEGLEN SEGCOUNT TABLEHI UNROLL ROWS OUT"
      return 1
