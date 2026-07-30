import LeanCompCert.Ports.R2SegSieve

/-!
Emission driver for the `R₂*` residue of `Ports.R2SegSieve`.

```
lake env lean --run bench/R2SegEmit.lean LO SEGLEN SEGCOUNT OUT [S] [EXPECTED] [ref]
```

`LO` must exceed `⌊√hi⌋`, so that an unmarked cell of a window is a prime; the
head `[1, LO−1]` is folded at **emit time** with the same fixed-point
arithmetic and becomes the artifact's carry-in, with both clauses tested there
at every integer.  `S` defaults to `24`.

The driver prints the ten result cells:

```
slot0 D        slot1 err     slot2 prev   slot3 terms   slot4 ⌊√prev⌋
slot5 ⌊log₂⌋   slot6 2^…     slot7 lnLo   slot8 thr     slot9 violations
```

with `R₂*(hi) = (D − 2^(S+24))/2^S` up to the enclosure `err/2^S`.  A nonzero
`slot9` is a failed clause **or** a failed guard — the stream budget, the
drain, the gap bound, the `⌊√n⌋` step or the `⌊log₂ n⌋` step.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Ports.PsiSegSieve (lnFix)

namespace Bench.R2SegEmit

def hostedDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < 10; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 12 + i]);\n" ++
  "    return 0;\n}\n"

def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.R2SegEmit

open Bench.R2SegEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | loS :: lenS :: cntS :: out :: rest => do
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some cnt := cntS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let scale := (rest[0]?.bind String.toNat?).getD defaultS
      -- A fourth optional argument makes this a *chained* artifact: the mark
      -- table and the budgets are those of the global sweep to TABLEHI, the
      -- swept range is only `[lo, lo+L·N−1]`, and the carry-in is synthetic —
      -- the previous link's carry-out is what a production chain would pass.
      -- Such a run measures cost at `n ≈ TABLEHI`; its slots are not a
      -- verification of anything.
      -- An empty positional argument is "absent": the reference fold below
      -- builds a smallest-prime-factor table of size `hi`, which at `hi = 2.1
      -- ⋅ 10¹⁰` is not a thing one asks for by accident.
      let chain := rest[3]?.bind String.toNat?
      let c := match chain with
        | some th => R2Cfg.ofChain scale lo len cnt th
        | none => R2Cfg.ofScale scale lo len cnt
      let root := match chain with
        | some th => Nat.sqrt th
        | none => c.root
      if lo ≤ root then
        IO.eprintln s!"LO={lo} must exceed floor(sqrt(hi))={root}"
        return 1
      if c.hi ≥ 2 ^ valBits then
        IO.eprintln s!"hi={c.hi} exceeds the entry value field, 2^{valBits}"
        return 1
      let s0 := Nat.sqrt (lo - 1)
      let seed := match chain with
        | some _ =>
            { d := biasOf scale, err := 0, prev := lo - 1, terms := 0
              sq := s0, sq2 := (s0 + 1) * (s0 + 1)
              ex := Nat.log2 (lo - 1), th := 2 ^ (Nat.log2 (lo - 1) + 1)
              ln := lnFix scale (lo - 1)
              thr := a193 * s0 * lnFix scale (lo - 1) / 2 ^ 16
              viol := 0 : R2Seed }
        | none => headFold scale (lo - 1) root
      let p := r2Program c seed
      let name := s!"R2s{scale}L{lo}S{len}N{cnt}"
      let driver :=
        match rest[1]?.bind String.toNat? with
        | some n => exitDriver name p.arrayLen n
        | none => hostedDriver name p.arrayLen
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"S={scale} lo={lo} L={len} N={cnt} hi={c.hi} root={c.root}"
          IO.println s!"  table={c.tableLen} markSteps={c.markSteps} logSteps={c.logSteps} streamCap={c.streamCap} period={c.period}"
          IO.println s!"  arrayLen={c.arrayLen} memoryBytes={8 * c.arrayLen}"
          IO.println s!"  loopCount={p.loopCount} bodyLen={p.body.length} initLen={p.init.length}"
          IO.println s!"  iterPerInteger={(1000 * p.loopCount) / (len * cnt)}e-3"
          IO.println s!"  head d={seed.d} err={seed.err} prev={seed.prev} terms={seed.terms} sq={seed.sq} ex={seed.ex} ln={seed.ln} thr={seed.thr} viol={seed.viol}"
          IO.println s!"  bias={biasOf scale} gammaStep={gammaStep scale} ln2Up={ln2Up scale} a193={a193}"
          if rest[2]?.getD "" ≠ "" then
            let r := refR2 scale lo c.hi root seed
            IO.println s!"  refD={r.1} refErr={r.2.1} refTerms={r.2.2.1} refPrev={r.2.2.2}"
          return 0
  | _ => do
      IO.eprintln "usage: LO SEGLEN SEGCOUNT OUT [S] [EXPECTED] [ref] [TABLEHI]"
      return 1
