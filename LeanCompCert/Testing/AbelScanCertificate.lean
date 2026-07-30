import LeanCompCert.Ports.CDEMAbelScan

/-!
# `check-native` certificate for the CDEM Abel increment scan

A deliberately small configuration of `Ports/CDEMAbelScan.lean`: weight scale
`10⁶`, Möbius prefix bound `K = 30`, five windows of eight cells, so the scan
covers `[1, 40]`.  The range has to exceed `K` for the residue to be
non-trivial at all — `F(k) = Σ_{n ≤ k} Σ_{d ∣ n} μ(d) = 1` identically for
`k ≤ K`, so `G` is `0` there and every accumulator would stay empty.

`expected = 0`: the artifact's output register is the number of failed guards,
and a correct run fails none.  A budget that was too small, a bisection that
did not close, an incremental `⌊√k⌋` that needed two bumps, or an `a·a` that
would have wrapped all raise it.

Exit status is not a theorem.  What is proved is `abelProgram_wf` and, through
`AProgram.evalCC_compile`, `abelProgram_compiled`: the emitted C computes
`denote`.  That `denote` is the residue is corroborated by the emit-time
reference in `Ports.CDEMAbelScan.Ref` and by `bench/ref_abel.c`.
-/

namespace LeanCompCert.Testing.AbelScanCertificate

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan

def cfg : Cfg := Cfg.ofRange 1000000 30 8 5

/-- Failed guards on a correct run. -/
def expected : Nat := 0

def program : AProgram := abelProgram cfg

theorem program_wf : program.WF := abelProgram_wf cfg

def symbolName : String := "CDEMAbel.scan40"

def mainC : String :=
  "\nstatic uint64_t cells[" ++ toString program.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    return l_CDEMAbel_scan40((uint64_t)(uintptr_t)cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emittedC : Except (Array String) String := do
  let source ← program.emitRolled symbolName
  pure (source ++ mainC)

end LeanCompCert.Testing.AbelScanCertificate
