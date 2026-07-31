import LeanCompCert.Ports.Prop1224Cell

/-!
Emission driver for the per-cell margin of `Ports.Prop1224Cell`.

```
lake env lean --run bench/Prop1224CellEmit.lean Q PHILO CONSTLO AF KLO KHI LO SEGLEN SEGCOUNT G EX TH T PRIMES OUT
```

`PRIMES` is a comma-separated list of the distinct primes of `Q` (empty for
`Q = 1`).  `G`, `EX`, `TH`, `T` are the carry-in at `LO − 1`: the running `G_q`
at scale `2^C`, `⌊log₂(LO−1)⌋`, `2^(⌊log₂(LO−1)⌋+1)`, and
`⌊2^5·(20000(LO−1))^{1/3}⌋`.  `LO` must exceed `⌊√hi⌋`, so that a cell whose
radical differs from `r` hides exactly one prime above the root.

The driver prints the six result cells:

```
slot0 G   slot1 cells   slot2 minMargin+2^(C+6)   slot3 cubeRoot
slot4 ⌊log₂⌋            slot5 violations
```

A nonzero `slot5` is a failed margin **or** a failed guard — the mark budget,
the `⌊log₂ r⌋` step, or the cube-root increment budget.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Prop1224Cell

namespace Bench.Prop1224CellEmit

def hostedDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < 6; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 12 + i]);\n" ++
  "    return 0;\n}\n"

def parsePrimes (s : String) : List Nat :=
  (s.splitOn ",").filterMap (fun t => t.trim.toNat?)

end Bench.Prop1224CellEmit

open Bench.Prop1224CellEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | qS :: plS :: clS :: afS :: kloS :: khiS :: loS :: lenS :: cntS ::
    gS :: exS :: thS :: tS :: psS :: out :: _ => do
      let nat (s : String) (nm : String) : IO Nat := do
        match s.toNat? with
        | some v => pure v
        | none => do IO.eprintln s!"bad {nm}"; pure 0
      let q ← nat qS "Q"
      let pl ← nat plS "PHILO"
      let cl ← nat clS "CONSTLO"
      let af ← nat afS "AF"
      let klo ← nat kloS "KLO"
      let khi ← nat khiS "KHI"
      let lo ← nat loS "LO"
      let len ← nat lenS "SEGLEN"
      let cnt ← nat cntS "SEGCOUNT"
      let g ← nat gS "G"
      let ex ← nat exS "EX"
      let th ← nat thS "TH"
      let t ← nat tS "T"
      let c := CellCfg.ofRow q pl cl af klo khi (parsePrimes psS) lo len cnt
      if lo ≤ c.root then
        IO.eprintln s!"LO={lo} must exceed floor(sqrt(hi))={c.root}"
        return 1
      let s : CellSeed := { g := g, ex := ex, th := th, t := t, cells := 0 }
      let p := cellProgram c s
      let name := s!"P1224CellQ{q}L{len}N{cnt}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ hostedDriver name p.arrayLen)
          IO.println s!"q={q} lo={lo} hi={c.hi} root={c.root} name={name}"
          IO.println s!"  tableLen={c.tableLen} markSteps={c.markSteps} period={c.period}"
          IO.println s!"  bodyLen={p.body.length} arrayLen={p.arrayLen} loopCount={p.loopCount}"
          IO.println s!"  instructions={p.body.length * p.loopCount}"
          return 0
  | _ => do
      IO.eprintln "usage: Q PHILO CONSTLO AF KLO KHI LO SEGLEN SEGCOUNT G EX TH T PRIMES OUT"
      return 1
