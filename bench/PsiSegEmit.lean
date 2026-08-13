import LeanCompCert.Ports.PsiSegSieve

/-!
Legacy small-range differential emitter for the `ψ` residue of
`Ports.PsiSegSieve`.

```
lake env lean --run bench/PsiSegEmit.lean LO SEGLEN SEGCOUNT OUT [S] [CAP] [EXPECTED] [ref]
```

This driver is intentionally capped at `hi <= 10^8`: it constructs tables and
the head in Lean and therefore must never be used for a production proof run.
Production uses `PsiRuntimePrimeTable` and `PsiRuntimePrimePowers`, where the
finite work happens in CompCert-compiled code.

`LO` must exceed `⌊√hi⌋`, so that an unmarked cell of a main window is a prime;
the small control head `[1, LO−1]` is folded at emit time with the same
`logFix` arithmetic, and becomes the artifact's carry-in.  `S` defaults to `48` and
`CAP` — the test points budgeted per window, which sets `logSteps = S·CAP` —
to `L/(ln LO − 1)` with an `8%` margin.

## The emitted `main` carries a verdict

It exits `0` **exactly when** the artifact's own acceptance condition held:
every guard clear and both clauses satisfied, i.e. the aggregate violation
count is `0`.  Any other outcome is a distinct nonzero status, and stdout names
the class:

| exit | class | meaning |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the eight class counters do not sum to the aggregate |
| `2` | `budget_streamcap` | a test point was pushed past `streamCap` |
| `3` | `budget_drain` | the window turned over with the stream undrained |
| `4` | `guard_gap` | a test-point gap did not fit `16` bits |
| `5` | `guard_sqrt` | one `⌊√n⌋` increment did not suffice |
| `6` | `guard_log2` | one `⌊log₂ n⌋` increment did not suffice |
| `7` | `guard_accrange` | the accumulator left `[0, 2^(S+24))` |
| `8` | `clause1_upper` | `ψ(n) − n ≤ 0.79059276·√n` failed |
| `9` | `clause2_lower` | `ψ(n) − n ≥ −√2·√n` failed |

The six budget/guard statuses come **first** on purpose.  They do not say the
family failed; they say the run was not a test of the family at all, because
terms are missing or the arithmetic left the range in which it is exact.  A
budget overrun in particular drops positive terms, which pushes the residual
*down* — it makes clause 1 easier and clause 2 harder, so in an aggregate it is
indistinguishable from, and means the opposite of, a genuine lower-bound
failure.

With `EXPECTED` the driver is *freestanding*: no `printf`, and the acceptance
condition is unchanged — it exits `0` only when the aggregate is `0`.  A
supplied `EXPECTED` is an **additional** demand (exit `1` if the artifact did
not reproduce it), never a substitute for acceptance: a run that reproduces a
nonzero count exits `2`, because reproducing a failure is not passing.

## The result cells

```
slot0 D.lo     slot1 D.hi     slot2 prev   slot3 terms
slot4 ⌊√prev⌋  slot5 ⌊log₂⌋   slot6 2^…    slot7 violations (the aggregate)
slot8..15      the eight classes above, in that order; they sum to slot7
slot16         floorform_only — NOT a failure, see below
```

with `ψ(hi) = prev + (D − 2^(S+23))/2^S`, since `ψ` is constant between the
last test point and `hi`.

`slot16` counts the integers at which the **discarded** `⌊√n⌋` form of clause 1
would have fired while clause 1 itself held.  It is the substitution loss and
nothing else, and it is deliberately outside the aggregate.  A run over
`n = 110 102 617` — where `(ψ(x) − x)/√x` attains its maximum `0.7905927544` —
reports `slot16 = 1` and `violations 0`.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.PsiSegSieve

namespace Bench.PsiSegEmit

def legacyMaxHi : Nat := 100000000

/-- The failure classes in result-slot order: label, and the exit status the
driver returns when that class is the first nonzero one in *scan* order.  The
scan order is the `code` order, so the run-invalidating budgets and guards
outrank the two clauses. -/
def classes : List (String × Nat) :=
  [ ("clause1_upper", 8)
  , ("clause2_lower", 9)
  , ("budget_streamcap", 2)
  , ("budget_drain", 3)
  , ("guard_gap", 4)
  , ("guard_sqrt", 5)
  , ("guard_log2", 6)
  , ("guard_accrange", 7) ]

/-- `classes` sorted by exit status: the order the driver tests them in. -/
def scanOrder : List (Nat × String × Nat) :=
  let idx := classes.zipIdx.map (fun x => (x.2, x.1.1, x.1.2))
  (idx.toArray.qsort (fun a b => a.2.2 < b.2.2)).toList

def hostedDriver (name : String) (cells : Nat) : String :=
  let base := cells - 17
  let cell (i : Nat) : String := "cells[" ++ toString (base + i) ++ "]"
  let classLine (slot : Nat) (label : String) : String :=
    "    printf(\"class " ++ label ++ " %llu\\n\", (unsigned long long)" ++
      cell (8 + slot) ++ ");\n" ++
    "    sum += " ++ cell (8 + slot) ++ ";\n"
  let verdictLine (slot : Nat) (label : String) (code : Nat) : String :=
    "    if (" ++ cell (8 + slot) ++ " != UINT64_C(0)) {\n" ++
    "        printf(\"verdict FAIL " ++ label ++ "\\n\");\n" ++
    "        return " ++ toString code ++ ";\n    }\n"
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    uint64_t sum = 0;\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < 8; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString base ++ " + i]);\n" ++
  String.join (classes.zipIdx.map (fun x => classLine x.2 x.1.1)) ++
  "    printf(\"diag floorform_only %llu\\n\", (unsigned long long)" ++
    cell 16 ++ ");\n" ++
  "    if (sum != r) {\n" ++
  "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
  "               (unsigned long long)sum, (unsigned long long)r);\n" ++
  "        return 1;\n    }\n" ++
  String.join (scanOrder.map (fun x => verdictLine x.1 x.2.1 x.2.2)) ++
  "    printf(\"verdict PASS\\n\");\n" ++
  "    return 0;\n}\n"

/-- The freestanding driver.  Acceptance is still `r == 0`; `EXPECTED` is an
extra demand on top of it, never a replacement for it. -/
def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    if (r != UINT64_C(" ++ toString expected ++ ")) return 1;\n" ++
  "    return r == UINT64_C(0) ? 0 : 2;\n}\n"

end Bench.PsiSegEmit

open Bench.PsiSegEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | loS :: lenS :: cntS :: out :: rest => do
      let some lo := loS.toNat? | do IO.eprintln "bad LO"; return 1
      let some len := lenS.toNat? | do IO.eprintln "bad SEGLEN"; return 1
      let some cnt := cntS.toNat? | do IO.eprintln "bad SEGCOUNT"; return 1
      let hi := lo + len * cnt - 1
      if legacyMaxHi < hi then
        IO.eprintln s!"refusing hi={hi}: PsiSegEmit is limited to small \
differential controls through {legacyMaxHi}; use the compiled runtime setup"
        return 1
      let scale := (rest[0]?.bind String.toNat?).getD defaultS
      if !cUp16Fits scale then
        IO.eprintln s!"S={scale} exceeds the squared clause's range: cUp16 S = \
{cUp16 scale} needs to be below 2^32, which holds exactly for S ≤ 48"
        return 1
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
          IO.println s!"  cUp16Sq={cUp16Sq scale} (lo={cUp16SqLo scale} hi={cUp16SqHi scale})"
          if (rest[3]?).isSome then
            IO.println s!"  refD={(refPsiLimbs scale lo c.hi)} refPrev={(refPsi scale lo c.hi).2}"
          return 0
  | _ => do
      IO.eprintln "usage: LO SEGLEN SEGCOUNT OUT [S] [CAP] [EXPECTED] [ref]"
      return 1
