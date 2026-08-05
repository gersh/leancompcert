import LeanCompCert.Ports.ArrayMobius

/-!
# M6 demonstration: the array path, end to end

The segmented Möbius sieve of `Ports.ArrayMobius` at `L = 100000`, emitted as
a rolled loop with a static `uint64_t` array supplied by the driver.  This is
the first certificate in the suite whose artifact performs **memory** loads
and stores; the whole point is that CompCert compiles it and the binary
agrees.

What is proved in Lean and what the binary corroborates are, as always,
different things:

* proved — `Ports.ArrayMobius.mobiusProgram_compiled`: for a well-formed base
  address, the compiled CCIR trace leaves `mobiusProgram L |>.denote` in the
  output register.  `mobiusProgram_wf` discharges its only side condition, at
  every `L`;
* proved — that the denotation *is* `L + Σ_{n<L} μ(n)` at `L = 8, 16, 24`, by
  kernel evaluation against a trial-division reference (see `ArrayMobius`);
* corroborated only — the numeric value below at `L = 100000`.  Its exit
  status is not a theorem, exactly as for `rolled-10m`.
-/

namespace LeanCompCert.Testing.ArrayMobiusCertificate

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArrayMobius

def segment : Nat := 100000

/-- `L + Σ_{n<L} μ(n)` at `L = 100000`; `Σ = -48`. -/
def expected : Nat := 99952

def program : AProgram := mobiusProgram segment

theorem program_wf : program.WF := mobiusProgram_wf segment

def symbolName : String := "ArrayMobius.rolled100k"

def mainC : String :=
  "\nstatic uint64_t cells[" ++ toString program.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    return l_ArrayMobius_rolled100k(cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emittedC : Except (Array String) String := do
  let source ← program.emitRolled symbolName
  pure (source ++ mainC)

end LeanCompCert.Testing.ArrayMobiusCertificate
