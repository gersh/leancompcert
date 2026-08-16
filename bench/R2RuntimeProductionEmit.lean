import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Ports.R2RuntimeTableReceipt
import LeanCompCert.Ports.R2ProductAudit
import LeanCompCert.Ports.R2ClauseAudit
import LeanCompCert.Verified.ArrayAuditFromArray

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

def productionDriver (c : R2Cfg) (control : Bool) : String :=
  let base := c.resultBase
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t mark = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t count = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  (if control then
    "    cells[" ++ toString (c.tableBase + 100) ++ "] ^= UINT64_C(1);\n"
   else "") ++
  "    uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  (if control then
    "    printf(\"mark %llu\\ncount %llu\\nreceipt %llu\\n\",\n" ++
    "      (unsigned long long)mark, (unsigned long long)count,\n" ++
    "      (unsigned long long)receipt);\n" ++
    "    return mark == UINT64_C(0) && count == UINT64_C(" ++
      toString runtimePrimeCount ++ ") && receipt != UINT64_C(0) ? 0 : 6;\n"
   else
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
  "    return violations == UINT64_C(0) ? 0 : 5;\n") ++
  "}\n"

/-- Self-checking driver for the fail-safe consumer.  The compiled producer
stages build and validate the caller-owned table before the audited sparse
sweep reads it. -/
def auditDriver (c : R2Cfg) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t mark = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t count = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t audit = l_r2__production__audit((uint64_t *)(uintptr_t)cells);\n" ++
  "    printf(\"mark %llu\\ncount %llu\\nreceipt %llu\\naudit %llu\\n\",\n" ++
  "      (unsigned long long)mark, (unsigned long long)count,\n" ++
  "      (unsigned long long)receipt, (unsigned long long)audit);\n" ++
  "    if (mark != UINT64_C(0)) return 1;\n" ++
  "    if (count != UINT64_C(" ++ toString runtimePrimeCount ++ ")) return 2;\n" ++
  "    if (receipt != UINT64_C(0)) return 3;\n" ++
  "    return audit == UINT64_C(0) ? 0 : 4;\n" ++
  "}\n"

/-- Self-checking driver for the combined partial-operation and exact-product
audit. -/
def productAuditDriver (c : R2Cfg) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t mark = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t count = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t audit = l_r2__production__product__audit((uint64_t *)(uintptr_t)cells);\n" ++
  "    printf(\"mark %llu\\ncount %llu\\nreceipt %llu\\nproduct_audit %llu\\n\",\n" ++
  "      (unsigned long long)mark, (unsigned long long)count,\n" ++
  "      (unsigned long long)receipt, (unsigned long long)audit);\n" ++
  "    if (mark != UINT64_C(0)) return 1;\n" ++
  "    if (count != UINT64_C(" ++ toString runtimePrimeCount ++ ")) return 2;\n" ++
  "    if (receipt != UINT64_C(0)) return 3;\n" ++
  "    return audit == UINT64_C(0) ? 0 : 4;\n" ++
  "}\n"

def clauseAuditDriver (c : R2Cfg) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t mark = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t count = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  "    uint64_t audit = l_r2__production__clause__audit((uint64_t *)(uintptr_t)cells);\n" ++
  "    printf(\"mark %llu\\ncount %llu\\nreceipt %llu\\nclause_audit %llu\\n\",\n" ++
  "      (unsigned long long)mark, (unsigned long long)count,\n" ++
  "      (unsigned long long)receipt, (unsigned long long)audit);\n" ++
  "    if (mark != UINT64_C(0)) return 1;\n" ++
  "    if (count != UINT64_C(" ++ toString runtimePrimeCount ++ ")) return 2;\n" ++
  "    if (receipt != UINT64_C(0)) return 3;\n" ++
  "    return audit == UINT64_C(0) ? 0 : 4;\n" ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  let (mode, out) := match args with
    | [mode, out] => (mode, out)
    | [out] => ("positive", out)
    | _ => ("", "")
  if mode != "positive" && mode != "control" && mode != "audit" &&
      mode != "product-audit" && mode != "clause-audit" then
    IO.eprintln "usage: positive|control|audit|product-audit|clause-audit OUT.c"
    return 1
  let c := runtimeProductionCfg
  let sweep := r2RuntimeProgram c runtimeProductionSeed
  match (r2RootMarkProgram c).emitRolled "r2_root_mark",
      (r2RootPackProgram c).emitRolled "r2_root_pack",
      (rootReceiptProgram c).emitRolled "r2_root_receipt" with
  | .ok mark, .ok pack, .ok receipt =>
      let emitted := if mode = "audit" then
          (LeanCompCert.Verified.ArrayAudit.auditProgram sweep).emitRolled
            "r2_production_audit"
        else if mode = "product-audit" then
          R2ProductAudit.runtimeProductAuditProgram.emitRolled
            "r2_production_product_audit"
        else if mode = "clause-audit" then
          R2ClauseAudit.runtimeClauseAuditProgram.emitRolled
            "r2_production_clause_audit"
        else sweep.emitRolled "r2_production"
      match emitted with
      | .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok mainSweep =>
        IO.FS.writeFile out
          (mark ++ pack ++ receipt ++ mainSweep ++
            if mode = "audit" then auditDriver c
            else if mode = "product-audit" then productAuditDriver c
            else if mode = "clause-audit" then clauseAuditDriver c
            else productionDriver c (mode = "control"))
      IO.println s!"mode={mode}"
      IO.println s!"lo={c.lo} hi={c.hi} root={runtimeRoot} scale={runtimeScale}"
      IO.println s!"arrayLen={c.arrayLen} memoryBytes={8 * c.arrayLen}"
      IO.println s!"tableCount={runtimePrimeCount} tableBase={c.tableBase}"
      IO.println s!"markLoop={(r2RootMarkProgram c).loopCount} packLoop={(r2RootPackProgram c).loopCount}"
      IO.println s!"sweepLoop={sweep.loopCount} sweepBody={sweep.body.length}"
      if mode = "product-audit" then
        IO.println s!"productAuditBody={R2ProductAudit.runtimeProductAuditProgram.body.length}"
      if mode = "clause-audit" then
        IO.println s!"clauseAuditBody={R2ClauseAudit.runtimeClauseAuditProgram.body.length}"
      IO.println s!"seedPrev={runtimeProductionSeed.prev} seedTerms={runtimeProductionSeed.terms}"
      return 0
  | .error errs, _, _ | _, .error errs, _ | _, _, .error errs =>
      for e in errs do IO.eprintln e
      return 1
