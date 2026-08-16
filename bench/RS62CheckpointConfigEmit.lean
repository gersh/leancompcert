import LeanCompCert.Ports.ArraySieveCount
import LeanCompCert.Ports.ArraySieveWeightedSum
import LeanCompCert.Verified.Rolled

/-!
Emit the two proved configuration computations for one RS62 checkpoint row.
The generated CompCert C counts the primes through `rootCap` and independently
checks the weighted marking allowance.  The hosted driver accepts only the
manifest's exact count and a zero budget-overflow verdict.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum

namespace Bench.RS62CheckpointConfigEmit

def sieveBound : Nat := 134

def driver (countName budgetName : String) (cells expectedCount : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t count_cells[" ++ toString cells ++ "];\n" ++
  "static uint64_t budget_cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t count = " ++ LeanCompCert.ABI.mangle countName ++
    "((uint64_t *)(uintptr_t)count_cells);\n" ++
  "  uint64_t budget = " ++ LeanCompCert.ABI.mangle budgetName ++
    "((uint64_t *)(uintptr_t)budget_cells);\n" ++
  "  printf(\"count %llu\\nbudget %llu\\n\",\n" ++
  "    (unsigned long long)count, (unsigned long long)budget);\n" ++
  "  if (count != UINT64_C(" ++ toString expectedCount ++ ")) return 1;\n" ++
  "  if (budget != UINT64_C(0)) return 2;\n" ++
  "  return 0;\n}\n"

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? | throw <| IO.userError s!"bad {label}: {value}"
  return n

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [idxS, rootCapS, mainCountS, segLenS, markStepsS, out] =>
      try
        let idx ← parseNat "idx" idxS
        let rootCap ← parseNat "rootCap" rootCapS
        let mainCount ← parseNat "mainCount" mainCountS
        let segLen ← parseNat "segLen" segLenS
        let markSteps ← parseNat "markSteps" markStepsS
        let len := rootCap + 1
        let count := sieveCountProgram sieveBound len
        let budget := sieveWeightedBudgetProgram sieveBound len segLen 2 markSteps
        let countName := s!"rs62_config_count_{idx}"
        let budgetName := s!"rs62_config_budget_{idx}"
        match count.emitRolled countName, budget.emitRolled budgetName with
        | .ok countC, .ok budgetC =>
            IO.FS.writeFile out
              (countC ++ budgetC ++ driver countName budgetName len mainCount)
            IO.println s!"row={idx} rootCap={rootCap} segLen={segLen}"
            IO.println s!"countLoops={count.loopCount} budgetLoops={budget.loopCount} cells={len}"
            return 0
        | .error errors, _ | _, .error errors =>
            for error in errors do IO.eprintln error
            return 1
      catch e =>
        IO.eprintln e.toString
        return 1
  | _ =>
      IO.eprintln "usage: IDX ROOTCAP MAINCOUNT SEGLEN MARKSTEPS OUT.c"
      return 1

end Bench.RS62CheckpointConfigEmit

def main (args : List String) : IO UInt32 :=
  Bench.RS62CheckpointConfigEmit.runMain args
