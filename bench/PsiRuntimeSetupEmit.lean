import LeanCompCert.Ports.PsiRuntimeHead

/-!
Small compiled-only differential driver for the psi runtime setup stages.
Lean emits syntax and scalar bounds only; the executable constructs and sorts
the prime and prime-power tables.
-/

open LeanCompCert
open LeanCompCert.Ports.PsiSegSieve

def smokeMeta : PsiRuntimeMeta :=
  PsiRuntimeMeta.ofScalars 101 100 1 48 100 16 100 10 25 16

def driver (m : PsiRuntimeMeta) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString m.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t mark = l_psi__root__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t primes = l_psi__root__pack((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t overflow = l_psi__pp__generate((uint64_t *)(uintptr_t)cells);\n" ++
  "  (void)l_psi__pp__sort((uint64_t *)(uintptr_t)cells);\n" ++
  "  (void)l_psi__pp__exponent((uint64_t *)(uintptr_t)cells);\n" ++
  "  (void)l_psi__pp__log((uint64_t *)(uintptr_t)cells);\n" ++
  "  (void)l_psi__prime__exponent((uint64_t *)(uintptr_t)cells);\n" ++
  "  (void)l_psi__prime__log((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t terms = l_psi__head((uint64_t *)(uintptr_t)cells);\n" ++
  "  printf(\"mark %llu\\nprimes %llu\\noverflow %llu\\n\",\n" ++
  "    (unsigned long long)mark, (unsigned long long)primes,\n" ++
  "    (unsigned long long)overflow);\n" ++
  "  for (int i = 0; i < " ++ toString m.ppCount ++ "; ++i) {\n" ++
  "    uint64_t q = cells[" ++ toString m.cfg.ppBase ++ " + 2*i];\n" ++
  "    uint64_t w = cells[" ++ toString m.cfg.ppBase ++ " + 2*i + 1];\n" ++
  "    if (q != 0) printf(\"pp %llu %llu\\n\",\n" ++
  "      (unsigned long long)q, (unsigned long long)w);\n" ++
  "  }\n" ++
  "  for (int i = 0; i < 7; ++i)\n" ++
  "    printf(\"head%d %llu\\n\", i, (unsigned long long)cells[" ++
    toString m.cfg.resultBase ++ " + i]);\n" ++
  "  if (mark != 0 || primes != 25 || overflow != 0 || terms != 35) return 1;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ "] != UINT64_C(18445067977826515759)) return 2;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ " + 1] != UINT64_C(127)) return 3;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ " + 2] != UINT64_C(100)) return 4;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ " + 4] != UINT64_C(10)) return 5;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ " + 5] != UINT64_C(6)) return 6;\n" ++
  "  if (cells[" ++ toString m.cfg.resultBase ++ " + 6] != UINT64_C(128)) return 7;\n" ++
  "  return 0;\n" ++
  "}\n"

def main (args : List String) : IO UInt32 := do
  let out := args.headD "/tmp/psi_runtime_setup.c"
  let m := smokeMeta
  match (psiRootMarkProgram m).emitRolled "psi_root_mark",
      (psiRootPackProgram m).emitRolled "psi_root_pack",
      (psiPPGenerateProgram m).emitRolled "psi_pp_generate",
      (psiPPSortProgram m).emitRolled "psi_pp_sort",
      (psiPPExponentProgram m).emitRolled "psi_pp_exponent",
      (psiPPLogProgram m).emitRolled "psi_pp_log",
      (psiPrimeExponentProgram m).emitRolled "psi_prime_exponent",
      (psiPrimeLogProgram m).emitRolled "psi_prime_log",
      (psiHeadFoldProgram m).emitRolled "psi_head" with
  | .ok mark, .ok pack, .ok gen, .ok sort, .ok exponent, .ok log,
      .ok primeExponent, .ok primeLog, .ok head =>
      IO.FS.writeFile out
        (mark ++ pack ++ gen ++ sort ++ exponent ++ log ++ primeExponent ++
          primeLog ++ head ++ driver m)
      IO.println s!"root={m.root} divCap={m.divCap} primeCount={m.primeCount}"
      IO.println s!"ppCapacity={m.ppCount} arrayLen={m.arrayLen}"
      return 0
  | .error errs, _, _, _, _, _, _, _, _
  | _, .error errs, _, _, _, _, _, _, _
  | _, _, .error errs, _, _, _, _, _, _
  | _, _, _, .error errs, _, _, _, _, _
  | _, _, _, _, .error errs, _, _, _, _
  | _, _, _, _, _, .error errs, _, _, _
  | _, _, _, _, _, _, .error errs, _, _
  | _, _, _, _, _, _, _, .error errs, _
  | _, _, _, _, _, _, _, _, .error errs =>
      for e in errs do IO.eprintln e
      return 1
