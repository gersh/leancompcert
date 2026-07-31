import LeanCompCert.Ports.ArraySegSieve

/-!
Emission driver for the offset segmented sieve of `Ports.ArraySegSieve`.

```
lake env lean --run bench/ArraySegEmit.lean MODE LO SEGLEN SEGCOUNT OUT [EXPECTED]
```

`MODE` is one of

* `mertens`  — the Mertens / squarefree residue, thresholds from Hurst
               (`|M| ≤ 0.571√n`) and CDEM (`b = 755/10⁴`), compared **once**
               in the epilogue against the majorant at the window's worst
               endpoint;
* `mertens2` — the same with the second CDEM threshold `b = 285/10⁴`;
* `mertenslive`, `mertenslive2` — the same two, with all four clauses tested
               **at every integer** against `⌊α·⌊√n⌋⌋`, so no window schedule
               and no `√(hi/lo) − 1` weakening.  Result slots are
               `M, Q, G, ⌊√hi⌋`;
* `platt211` — the `Σ μ(m)/m` residue against `√(2/(n+1))`;
* `plattstrong` — the same against `1/(2√(n+1))`;
* `plattstronglive` — the same against `1/(2√(n+1))` tested **at every
               integer**, on a two-limb accumulator at scale
               `2^(63+mobWideBits)`.  No window schedule, and a rounding budget
               `2^(mobWideBits+1)` times smaller.  Result slots are the two
               accumulator limbs, `⌈√(hi+1)⌉` and its square; the seeds are the
               two limbs.

Two drivers are emitted.  Without `EXPECTED` the driver is *hosted*: it
prints the result cells, which is what a chained run needs and what the
reference cross-check compares against.  With `EXPECTED` the driver is
*freestanding*: it returns `0` exactly when the artifact's output — the number
of failed threshold tests — equals `EXPECTED`, which is the shape
`check-native` and the timing runs use.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

namespace Bench.ArraySegEmit

def hostedDriver (name : String) (cells slots : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < " ++ toString slots ++ "; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString cells ++ " - 8 + i]);\n" ++
  "    return 0;\n}\n"

def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.ArraySegEmit

open Bench.ArraySegEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: loS :: lenS :: cntS :: out :: rest => do
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some cnt := cntS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let c := Cfg.ofRange lo len cnt
      let name := s!"Seg{mode}L{lo}S{len}N{cnt}"
      -- rest = [EXPECTED] ++ [seed...]; EXPECTED = "-" means the hosted driver
      let expected := rest.head?
      let seeds := (rest.drop 1).filterMap String.toNat?
      let seedA := seeds[0]?.getD mertensBias
      let seedB := seeds[1]?.getD 0
      let seedC := seeds[2]?.getD gBias
      let seedT := seeds[0]?.getD tBias
      let p ←
        match mode with
        | "mertens" =>
            pure (mertensProgram c ⟨seedA, seedB, seedC⟩ 755 10000)
        | "mertens2" =>
            pure (mertensProgram c ⟨seedA, seedB, seedC⟩ 285 10000)
        | "mertenslive" =>
            pure (mertensLiveProgram c (Nat.sqrt (lo - 1))
              ⟨seedA, seedB, seedC⟩ 755 10000)
        | "mertenslive2" =>
            pure (mertensLiveProgram c (Nat.sqrt (lo - 1))
              ⟨seedA, seedB, seedC⟩ 285 10000)
        | "platt211" =>
            pure (mobiusProgram c seedT (platt211Threshold c.hi))
        | "plattstrong" =>
            pure (mobiusProgram c seedT (plattStrongerThreshold c.hi))
        | "plattstronglive" =>
            -- carry-in: the two accumulator limbs.  Absent, the walk is
            -- assumed to open at n = 1 and the accumulator is the bare bias.
            let k := mobWideBits
            let dflt := mobLiveSeedStart k
            let s : MobLiveSeed :=
              (mobLiveSeed lo (seeds[0]?.getD dflt.tLo) (seeds[1]?.getD dflt.tHi))
            pure (mobiusLiveProgram c k s)
        | _ => do IO.eprintln "bad MODE"; return 1
      let driver :=
        match expected.bind String.toNat? with
        | some n => exitDriver name p.arrayLen n
        | none => hostedDriver name p.arrayLen 7
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver)
          IO.println s!"mode={mode} lo={lo} L={len} S={cnt} hi={c.hi}"
          IO.println s!"  primes={c.tableLen} markSteps={c.markSteps} period={c.period}"
          IO.println s!"  rootCount={c.rootCount} rootLen={c.rootLen} rootCap={c.rootCap} boot={c.bootCount} initLen={c.coreInit.length}"
          IO.println s!"  loopCount={p.loopCount} arrayLen={p.arrayLen} bodyLen={p.body.length}"
          IO.println s!"  memoryBytes={8 * p.arrayLen}"
          IO.println s!"  cdemC={cdemC} hurstThr={hurstThreshold c.lo}"
          IO.println s!"  cdemThr755={cdemThreshold 755 10000 c.lo} cdemThr285={cdemThreshold 285 10000 c.lo}"
          IO.println s!"  platt211Thr={platt211Threshold c.hi} plattStrongThr={plattStrongerThreshold c.hi}"
          return 0
  | _ => do
      IO.eprintln "usage: MODE LO SEGLEN SEGCOUNT OUT [EXPECTED|-] [SEED...]"
      return 1
