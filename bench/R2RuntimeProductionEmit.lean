import LeanCompCert.Ports.R2RuntimeTableReceipt

/-!
Emission driver for the production `R₂*` pipeline.

Unlike `R2SegEmit`, this driver performs no prime enumeration, logarithm
table construction, budget scan, or head fold in Lean.  It emits four small
rolled CompCert programs over one shared array:

1. composite marking for the root table;
2. fixed-log packing of the prime entries;
3. the compiled table receipt checker;
4. the sparse production sweep, seeded by the compiled dense-head receipt.

The expensive finite computations occur only after `ccomp` has compiled the
emitted C.  Lean constructs syntax and proves the generic compiler/refinement
theorems; it does not run the production loops.
-/

open LeanCompCert
open LeanCompCert.Ports.R2SegSieve

def productionSeed : R2Seed :=
  { d := 281482090502886
    err := 10983953
    prev := 144999
    terms := 61171
    sq := 380
    sq2 := 145161
    ex := 17
    th := 262144
    ln := 199388523
    thr := 146230987829
    viol := 0 }

def productionDriver (c : R2Cfg) : String :=
  let base := c.resultBase
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t mark = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t count = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t violations = l_r2__production((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t classes = UINT64_C(0);\n" ++
  "    printf(\"mark %llu\\ncount %llu\\nreceipt %llu\\nviolations %llu\\n\",\n" ++
  "      (unsigned long long)mark, (unsigned long long)count,\n" ++
  "      (unsigned long long)receipt, (unsigned long long)violations);\n" ++
  "    for (int i = 0; i < 20; ++i)\n" ++
  "      printf(\"slot%d %llu\\n\", i,\n" ++
  "        (unsigned long long)cells[" ++ toString base ++ " + i]);\n" ++
  "    for (int i = 11; i < 20; ++i) classes += cells[" ++
    toString base ++ " + i];\n" ++
  "    if (mark != UINT64_C(0)) return 1;\n" ++
  "    if (count != UINT64_C(" ++ toString runtimePrimeCount ++ ")) return 2;\n" ++
  "    if (receipt != UINT64_C(0)) return 3;\n" ++
  "    if (classes != violations) return 4;\n" ++
  "    return violations == UINT64_C(0) ? 0 : 5;\n" ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  let out := args.headD "/tmp/r2_runtime_production.c"
  let c := runtimeProductionCfg
  let sweep := r2RuntimeProgram c productionSeed
  match (r2RootMarkProgram c).emitRolled "r2_root_mark",
      (r2RootPackProgram c).emitRolled "r2_root_pack",
      (rootReceiptProgram c).emitRolled "r2_root_receipt",
      sweep.emitRolled "r2_production" with
  | .ok mark, .ok pack, .ok receipt, .ok mainSweep =>
      IO.FS.writeFile out
        (mark ++ pack ++ receipt ++ mainSweep ++ productionDriver c)
      IO.println s!"lo={c.lo} hi={c.hi} root={runtimeRoot} scale={runtimeScale}"
      IO.println s!"arrayLen={c.arrayLen} memoryBytes={8 * c.arrayLen}"
      IO.println s!"tableCount={runtimePrimeCount} tableBase={c.tableBase}"
      IO.println s!"markLoop={(r2RootMarkProgram c).loopCount} packLoop={(r2RootPackProgram c).loopCount}"
      IO.println s!"sweepLoop={sweep.loopCount} sweepBody={sweep.body.length}"
      IO.println s!"seedPrev={productionSeed.prev} seedTerms={productionSeed.terms}"
      return 0
  | .error errs, _, _, _ | _, .error errs, _, _ |
      _, _, .error errs, _ | _, _, _, .error errs =>
      for e in errs do IO.eprintln e
      return 1
