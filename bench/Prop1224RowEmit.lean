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

## The emitted `main` carries a verdict

It exits `0` **exactly when** the artifact's own acceptance condition held: the
violation register `RET` is `0`.  One `class` line is printed per failure mode,
and the exit status names the first nonzero one in this order:

| exit | class | meaning |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the classes and the aggregate disagree about being zero |
| `2` | `budget_marktable` | the mark cursor had not finished: the sieve was truncated |
| `3` | `root_over` | an emitted square root failed `v² ≤ Z` |
| `4` | `root_under` | …or failed `Z < (v+1)²` |
| `5` | `enclosure_Lq_inverted` | `L(q)`'s lower bound came out above its upper |
| `6` | `enclosure_phiq_inverted` | …the same for `φ(q)/q` |
| `7` | `enclosure_logq_inverted` | …the same for `log q` |
| `8` | `kappa_lower_zero` | `κ*`'s lower bound collapsed to `0` |
| `9` | `lambda_zero` | `λ(q)` collapsed to `0` |

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Prop1224Row

namespace Bench.Prop1224RowEmit

/-- One failure class: label, offset inside the class block, exit status. -/
abbrev Class := String × Nat × Nat

/-- The eight classes, in scan order.  Slot offsets follow
`Ports.Prop1224Row.violRegs`.

⚠ The last five count **conditions** while the aggregate counts *rows* with at
least one of them, so the classes bound the aggregate from above rather than
equalling it.  The driver checks what does always hold: they vanish exactly
when the aggregate does, and never undercount it. -/
def classes : List Class :=
  [ ("budget_marktable", 0, 2)
  , ("root_over", 1, 3)
  , ("root_under", 2, 4)
  , ("enclosure_Lq_inverted", 3, 5)
  , ("enclosure_phiq_inverted", 4, 6)
  , ("enclosure_logq_inverted", 5, 7)
  , ("kappa_lower_zero", 6, 8)
  , ("lambda_zero", 7, 9) ]

def hostedDriver (name : String) (cells rowBase segLen resultBase lo rows : Nat) :
    String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    uint64_t sum = 0;\n" ++
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
  String.join (classes.map (fun x =>
    "    printf(\"class " ++ x.1 ++ " %llu\\n\",\n" ++
    "           (unsigned long long)cells[RES+" ++ toString (12 + x.2.1) ++ "]);\n" ++
    "    sum += cells[RES+" ++ toString (12 + x.2.1) ++ "];\n")) ++
  "    if ((sum == UINT64_C(0)) != (r == UINT64_C(0)) || sum < r) {\n" ++
  "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
  "               (unsigned long long)sum, (unsigned long long)r);\n" ++
  "        return 1;\n    }\n" ++
  String.join (classes.map (fun x =>
    "    if (cells[RES+" ++ toString (12 + x.2.1) ++ "] != UINT64_C(0)) {\n" ++
    "        printf(\"verdict FAIL " ++ x.1 ++ "\\n\");\n" ++
    "        return " ++ toString x.2.2 ++ ";\n    }\n")) ++
  "    printf(\"verdict PASS\\n\");\n" ++
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
