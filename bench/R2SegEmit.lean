import LeanCompCert.Ports.R2DenseHead

/-!
Emission driver for the `R₂*` residue of `Ports.R2SegSieve`.

```
lake env lean --run bench/R2SegEmit.lean LO SEGLEN SEGCOUNT OUT [S] [EXPECTED]
```

For the sparse production program, `LO` must exceed `⌊√hi⌋` and an exact
eleven-word receipt from a compiled predecessor is mandatory.  The dense-head
mode begins at `3` from the closed two-integer seed and computes its finite
range in compiled code.  There is no Lean-evaluated head fold. `S` defaults to
`24`.

The driver prints the eleven-word carry receipt:

```
slot0 D       slot1 err   slot2 prev  slot3 terms  slot4 ⌊√prev⌋  slot5 nextSquare
slot6 ⌊log₂⌋  slot7 2^…    slot8 lnLo  slot9 thr    slot10 violations
```

with `R₂*(hi) = (D − 2^(S+24))/2^S` up to the enclosure `err/2^S`, and

```
slot11..20  the ten failure classes; they sum to slot10
```

## The emitted `main` carries a verdict

It exits `0` **exactly when** the aggregate is `0`, and otherwise names the
class:

| exit | class | meaning |
| ---: | --- | --- |
| `0` | — | accepted |
| `1` | `INCONSISTENT` | the ten classes do not sum to the aggregate |
| `2` | `budget_marktable` | the mark cursor had not finished |
| `3` | `budget_streamcap` | a test point was pushed past `streamCap` |
| `4` | `budget_drain` | the window turned over with the stream undrained |
| `5` | `guard_gap` | a test-point gap did not fit `16` bits |
| `6` | `guard_sqrt` | one `⌊√n⌋` increment did not suffice |
| `7` | `guard_log2` | one `⌊log₂ n⌋` increment did not suffice |
| `8` | `guard_negative_sub` | a finished negative jump exceeded the post-linear accumulator |
| `9` | `clause1_upper` | `R₂* ≤ 1.93·√n·log n` failed at a test point |
| `10` | `clause2_lower` | `R₂* ≥ −1.93·√n·log n` failed at a test point |
| `11` | `clause1_tail_at_hi` | clause 1 failed in the epilogue, at `hi` |

The seven budget/guard statuses come first: they do not say the family failed,
they say the run was not a test of it, because terms are missing or the
arithmetic left the range in which it is exact.

This is the strengthened future causal layout.  Historical artifacts with
only nine individual failure cells do not certify `guard_negative_sub` and
must not be accepted as runs of this emitted program.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Ports.PsiSegSieve (lnFix)

namespace Bench.R2SegEmit

/-- One failure class: its label, its offset inside the class block, and the
exit status the driver returns when it is the first nonzero one.  The list is
given in **scan order**, so the classes that invalidate a run come before the
classes that are a result. -/
abbrev Class := String × Nat × Nat

/-- A hosted driver that prints the result cells and then **decides**.

`base` is the first result cell, `slots` how many of them the chain reads, and
`classBase` the slot at which the class counters start.  The emitted `main` returns `0` only when every
class counter is zero, `1` when the classes do not sum to the aggregate (a
split that has come adrift is a reason to trust neither number), and otherwise
the status of the first nonzero class in scan order. -/
def verdictDriver (name : String) (cells base slots classBase : Nat)
    (classes : List Class) (diags : List (String × Nat)) (sumIsExact : Bool) :
    String :=
  let cell (i : Nat) : String := "cells[" ++ toString (base + i) ++ "]"
  let classLine (x : Class) : String :=
    "    printf(\"class " ++ x.1 ++ " %llu\\n\", (unsigned long long)" ++
      cell (classBase + x.2.1) ++ ");\n" ++
    "    sum += " ++ cell (classBase + x.2.1) ++ ";\n"
  let diagLine (x : String × Nat) : String :=
    "    printf(\"diag " ++ x.1 ++ " %llu\\n\", (unsigned long long)" ++
      cell x.2 ++ ");\n"
  let verdictLine (x : Class) : String :=
    "    if (" ++ cell (classBase + x.2.1) ++ " != UINT64_C(0)) {\n" ++
    "        printf(\"verdict FAIL " ++ x.1 ++ "\\n\");\n" ++
    "        return " ++ toString x.2.2 ++ ";\n    }\n"
  let consistency :=
    if sumIsExact then
      "    if (sum != r) {\n" ++
      "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
      "               (unsigned long long)sum, (unsigned long long)r);\n" ++
      "        return 1;\n    }\n"
    else
      -- the aggregate collapses several conditions per row, so the classes
      -- bound it from above rather than equalling it; what must hold is that
      -- they vanish together
      "    if ((sum == UINT64_C(0)) != (r == UINT64_C(0)) || sum < r) {\n" ++
      "        printf(\"verdict INCONSISTENT classes %llu aggregate %llu\\n\",\n" ++
      "               (unsigned long long)sum, (unsigned long long)r);\n" ++
      "        return 1;\n    }\n"
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    uint64_t sum = 0;\n" ++
  "    printf(\"violations %llu\\n\", (unsigned long long)r);\n" ++
  "    for (int i = 0; i < " ++ toString slots ++ "; i++)\n" ++
  "        printf(\"slot%d %llu\\n\", i,\n" ++
  "               (unsigned long long)cells[" ++ toString base ++ " + i]);\n" ++
  String.join (classes.map classLine) ++
  String.join (diags.map diagLine) ++
  consistency ++
  String.join (classes.map verdictLine) ++
  "    printf(\"verdict PASS\\n\");\n" ++
  "    return 0;\n}\n"

/-- The freestanding driver.  Acceptance is `r == 0`; a supplied `EXPECTED` is
an **additional** demand (exit `1` if the artifact did not reproduce it), never
a substitute for it — reproducing a nonzero count exits `2`. -/
def exitDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    if (r != UINT64_C(" ++ toString expected ++ ")) return 1;\n" ++
  "    return r == UINT64_C(0) ? 0 : 2;\n}\n"


/-- The ten classes, in scan order: the seven that retract the run first, then
the three that are a result.  Slot offsets are `Ports.R2SegSieve.violRegs`'
order, which is `[Up, Lo, Tail, Mark, Cap, Drain, Gap, Sqrt, Log2, Sub]`. -/
def classes : List Class :=
  [ ("budget_marktable", 3, 2)
  , ("budget_streamcap", 4, 3)
  , ("budget_drain", 5, 4)
  , ("guard_gap", 6, 5)
  , ("guard_sqrt", 7, 6)
  , ("guard_log2", 8, 7)
  , ("guard_negative_sub", 9, 8)
  , ("clause1_upper", 0, 9)
  , ("clause2_lower", 1, 10)
  , ("clause1_tail_at_hi", 2, 11) ]

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
      let rawC := match chain with
        | some th => R2Cfg.ofChain scale lo len cnt th
        | none => R2Cfg.ofScale scale lo len cnt
      let headMode := rest[4]?.getD ""
      let compiledHead := headMode == "compiled-head" ||
        headMode == "compiled-head-full"
      let headC := if headMode == "compiled-head-full" then
          rawC.withFullFactorTable
        else rawC
      let c := if compiledHead then headC.withDenseHeadBudgets else rawC
      let root := match chain with
        | some th => Nat.sqrt th
        | none => c.root
      if !compiledHead && lo ≤ root then
        IO.eprintln s!"LO={lo} must exceed floor(sqrt(hi))={root}"
        return 1
      if c.hi ≥ 2 ^ valBits then
        IO.eprintln s!"hi={c.hi} exceeds the entry value field, 2^{valBits}"
        return 1
      let s0 := Nat.sqrt (lo - 1)
      let receipt := (rest.drop 5).filterMap String.toNat?
      let receiptSeed? : Option R2Seed :=
        if receipt.length = 11 then
          some
            { d := receipt[0]!, err := receipt[1]!, prev := receipt[2]!
              terms := receipt[3]!, sq := receipt[4]!, sq2 := receipt[5]!
              ex := receipt[6]!, th := receipt[7]!, ln := receipt[8]!
              thr := receipt[9]!, viol := receipt[10]! }
        else none
      if !compiledHead && chain.isNone && receiptSeed?.isNone then
        IO.eprintln
          "a production high-range artifact requires the 11-word receipt from a compiled predecessor"
        return 1
      let defaultSeed := if compiledHead then
          R2Seed.afterTwo scale
        else
          -- Cost-only chained benchmarks use a synthetic carry.  A real
          -- verification artifact always overrides this with `receiptSeed?`.
          { d := biasOf scale, err := 0, prev := lo - 1, terms := 0
            sq := s0, sq2 := (s0 + 1) * (s0 + 1)
            ex := Nat.log2 (lo - 1), th := 2 ^ (Nat.log2 (lo - 1) + 1)
            ln := lnFix scale (lo - 1)
            thr := a193 * s0 * lnFix scale (lo - 1) / 2 ^ 16
            viol := 0 : R2Seed }
      let seed := receiptSeed?.getD defaultSeed
      let p := if compiledHead then r2DenseHeadProgram c seed else r2Program c seed
      let name := s!"R2s{scale}L{lo}S{len}N{cnt}"
      let driver :=
        match rest[1]?.bind String.toNat? with
        | some n => exitDriver name p.arrayLen n
        | none =>
            verdictDriver name p.arrayLen (p.arrayLen - 21) 21 11 classes [] true
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
          return 0
  | _ => do
      IO.eprintln "usage: LO SEGLEN SEGCOUNT OUT [S] [EXPECTED] [ref] [TABLEHI] [compiled-head|compiled-head-full] [d err prev terms sq sq2 ex th ln thr viol]"
      return 1
