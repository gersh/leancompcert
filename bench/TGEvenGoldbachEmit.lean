import LeanCompCert.Ports.TGEvenGoldbach

/-! Emit a small timing harness for the proved even-Goldbach witness consumer.
This benchmarks only receipt checking; it does not run the source-scale
Goldbach computation or claim that the synthetic primality bits are true. -/

open LeanCompCert.Ports.TGEvenGoldbach

namespace Bench.TGEvenGoldbachEmit

def driver (c : Cfg) (reps : Nat) : String :=
  "\n#include <stdio.h>\n#include <stdlib.h>\n#include <time.h>\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t *cells = calloc(" ++ toString c.arrayLen ++
    ", sizeof(uint64_t));\n" ++
  "  if (cells == NULL) return 2;\n" ++
  "  for (uint64_t k = 0; k < UINT64_C(" ++ toString c.count ++ "); ++k) {\n" ++
  "    uint64_t n = UINT64_C(" ++ toString c.evenLo ++ ") + UINT64_C(2) * k;\n" ++
  "    cells[k] = UINT64_C(3);\n" ++
  "    cells[UINT64_C(" ++ toString c.count ++ ") + k] = n - UINT64_C(3);\n" ++
  "    cells[UINT64_C(" ++ toString (2 * c.count) ++ ") + k] = UINT64_C(1);\n" ++
  "    cells[UINT64_C(" ++ toString (3 * c.count) ++ ") + k] = UINT64_C(1);\n" ++
  "  }\n" ++
  "  uint64_t verdict = 0, audit = 0;\n" ++
  "  clock_t start = clock();\n" ++
  "  for (uint64_t r = 0; r < UINT64_C(" ++ toString reps ++ "); ++r)\n" ++
  "    verdict |= l_tg__even__goldbach((uint64_t *)(uintptr_t)cells);\n" ++
  "  clock_t stop = clock();\n" ++
  "  clock_t audit_start = clock();\n" ++
  "  for (uint64_t r = 0; r < UINT64_C(" ++ toString reps ++ "); ++r)\n" ++
  "    audit |= l_tg__even__goldbach__audit((uint64_t *)(uintptr_t)cells);\n" ++
  "  clock_t audit_stop = clock();\n" ++
  "  printf(\"rows %llu reps %llu verdict %llu cpu_seconds %.9f audit %llu audit_cpu_seconds %.9f\\n\",\n" ++
  "    (unsigned long long)UINT64_C(" ++ toString c.count ++ "),\n" ++
  "    (unsigned long long)UINT64_C(" ++ toString reps ++ "),\n" ++
  "    (unsigned long long)verdict,\n" ++
  "    (double)(stop-start)/(double)CLOCKS_PER_SEC,\n" ++
  "    (unsigned long long)audit,\n" ++
  "    (double)(audit_stop-audit_start)/(double)CLOCKS_PER_SEC);\n" ++
  "  free(cells);\n" ++
  "  return verdict == UINT64_C(0) && audit == UINT64_C(0) ? 0 : 1;\n}\n"

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [countS, repsS, out] =>
      let some count := countS.toNat? | throw <| IO.userError "bad count"
      let some reps := repsS.toNat? | throw <| IO.userError "bad reps"
      let c : Cfg := { evenLo := 4, count := count }
      match (program c).emitRolled "tg_even_goldbach",
          (LeanCompCert.Verified.ArrayAudit.auditProgram (program c)).emitRolled
            "tg_even_goldbach_audit" with
      | .error errs, _ | _, .error errs =>
          for e in errs do IO.eprintln e
          return 1
      | .ok source, .ok auditSource =>
          IO.FS.writeFile out (source ++ auditSource ++ driver c reps)
          IO.println s!"rows={count} array_cells={c.arrayLen} bytes={8*c.arrayLen}"
          return 0
  | _ =>
      IO.eprintln "usage: COUNT REPS OUT.c"
      return 1

end Bench.TGEvenGoldbachEmit

def main (args : List String) : IO UInt32 :=
  Bench.TGEvenGoldbachEmit.runMain args
