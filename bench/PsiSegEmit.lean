import LeanCompCert.Ports.PsiSegSieve

/-!
Emission driver for the `ψ` residue of `Ports.PsiSegSieve`.

```
lake env lean --run bench/PsiSegEmit.lean LO SEGLEN SEGCOUNT OUT [S] [CAP]
```

`LO` must exceed `⌊√hi⌋`, so that an unmarked cell of a main window is a prime;
the head `[1, LO−1]` is folded at **emit time** with the same `logFix`
arithmetic, and becomes the artifact's carry-in.  `S` defaults to `48` and
`CAP` — the test points budgeted per window, which sets `logSteps = S·CAP` —
to `L/(ln LO − 1)` with an `8%` margin.

The driver prints the eight result cells:

```
slot0 D.lo     slot1 D.hi     slot2 prev   slot3 terms
slot4 ⌊√prev⌋  slot5 ⌊log₂⌋   slot6 2^…    slot7 violations
```

with `ψ(hi) = prev + (D − 2^(S+23))/2^S`, since `ψ` is constant between the
last test point and `hi`.  A nonzero `slot7` is a failed clause **or** a failed
guard — the stream budget, the drain, the gap bound, the `⌊√n⌋` step, the
`⌊log₂ n⌋` step, or the accumulator's range.  All six are checked in the loop.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.PsiSegSieve

namespace Bench.PsiSegEmit

def hostedDriver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < 8; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 8 + i]);\n" ++
  "    return 0;\n}\n"

def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.PsiSegEmit

open Bench.PsiSegEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | loS :: lenS :: cntS :: out :: rest => do
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some cnt := cntS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let scale := (rest[0]?.bind String.toNat?).getD defaultS
      let c0 := PsiCfg.ofScale scale lo len cnt
      let c := match rest[1]?.bind String.toNat? with
        | some cap => { c0 with streamCap := cap }
        | none => c0
      if lo ≤ c.rootCap then
        IO.eprintln s!"LO={lo} must exceed floor(sqrt(hi))={c.rootCap}"
        return 1
      let seed := psiHead scale lo
      let p := psiProgram c seed
      let name := s!"Psi{scale}L{lo}S{len}N{cnt}"
      let driver :=
        match rest[2]?.bind String.toNat? with
        | some n => exitDriver name p.arrayLen n
        | none => hostedDriver name p.arrayLen
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"S={scale} lo={lo} L={len} N={cnt} hi={c.hi}"
          IO.println s!"  primes={c.tableLen} markSteps={c.markSteps} rootCount={c.rootCount} rootLen={c.rootLen} rootCap={c.rootCap} boot={c.bootCount}"
          IO.println s!"  streamCap={c.streamCap} logSteps={c.logSteps} period={c.period}"
          IO.println s!"  primePowers={c.ppLen} arrayLen={c.arrayLen} memoryBytes={8 * c.arrayLen}"
          IO.println s!"  loopCount={p.loopCount} bodyLen={p.body.length} initLen={p.init.length}"
          IO.println s!"  iterPerInteger={(1000 * p.loopCount) / (len * cnt)}e-3"
          IO.println s!"  seed dlo={seed.dlo} dhi={seed.dhi} prev={seed.prev} terms={seed.terms} sq={seed.sq} ex={seed.ex}"
          IO.println s!"  bias={biasOf scale} cUp={cUp scale} cDown={cDown scale} cUp16={cUp16 scale} cDown16={cDown16 scale}"
          if (rest[3]?).isSome then
            IO.println s!"  refD={(refPsiLimbs scale lo c.hi)} refPrev={(refPsi scale lo c.hi).2}"
          return 0
  | _ => do
      IO.eprintln "usage: LO SEGLEN SEGCOUNT OUT [S] [CAP] [EXPECTED] [ref]"
      return 1
