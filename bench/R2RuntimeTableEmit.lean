import LeanCompCert.Ports.R2RuntimeTableReceipt

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.R2SegSieve

def driver (c : R2Cfg) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t a = l_r2__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t n = l_r2__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "#ifdef R2_RECEIPT_CORRUPT\n" ++
  "  cells[" ++ toString (c.tableBase + 100) ++ "] ^= UINT64_C(1);\n" ++
  "#endif\n" ++
  "  uint64_t h = l_r2__root__checksum((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t receipt = l_r2__root__receipt((uint64_t *)(uintptr_t)cells);\n" ++
  "  printf(\"mark %llu\\ncount %llu\\nfirst %llu\\nlast %llu\\nsentinel %llu\\nchecksum %llu\\nreceipt %llu\\n\",\n" ++
  "    (unsigned long long)a, (unsigned long long)n,\n" ++
  "    (unsigned long long)cells[" ++ toString c.tableBase ++ "],\n" ++
  "    (unsigned long long)cells[" ++ toString c.tableBase ++ " + n - 1],\n" ++
  "    (unsigned long long)cells[" ++ toString c.tableBase ++ " + n],\n" ++
  "    (unsigned long long)h, (unsigned long long)receipt);\n" ++
  "  return (a == 0 && n == " ++ toString runtimePrimeCount ++
  " && receipt == 0) ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  let out := args.headD "/tmp/r2_runtime_table.c"
  let c := runtimeProductionCfg
  match (r2RootMarkProgram c).emitRolled "r2_root_mark",
      (r2RootPackProgram c).emitRolled "r2_root_pack",
      (rootChecksumProgram c).emitRolled "r2_root_checksum",
      (rootReceiptProgram c).emitRolled "r2_root_receipt" with
  | .ok mark, .ok pack, .ok checksum, .ok receipt =>
      IO.FS.writeFile out (mark ++ pack ++ checksum ++ receipt ++ driver c)
      IO.println s!"root={runtimeRoot} divisors={runtimeDivCap} expectedPrimes={runtimePrimeCount}"
      IO.println s!"markLoop={(r2RootMarkProgram c).loopCount} packLoop={(r2RootPackProgram c).loopCount}"
      IO.println s!"markBody={(r2RootMarkProgram c).body.length} packBody={(r2RootPackProgram c).body.length}"
      IO.println s!"arrayLen={c.arrayLen} tableBase={c.tableBase}"
      return 0
  | .error errs, _, _, _ | _, .error errs, _, _ |
      _, _, .error errs, _ | _, _, _, .error errs =>
      for e in errs do IO.eprintln e
      return 1
