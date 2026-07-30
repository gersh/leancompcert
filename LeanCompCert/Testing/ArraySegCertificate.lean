import LeanCompCert.Ports.ArraySegSieve

/-!
# The offset segmented sieve, end to end

`Testing/ArrayMobiusCertificate.lean` runs the one-shot `[0, L)` sieve through
CompCert.  This is its offset, multi-window successor: eight windows of 4096
cells covering `[1, 32768]`, carrying the Mertens sum, the squarefree count and
the CDEM fixed-point discrepancy across window boundaries in registers, and
re-using the same 3·4096-cell array for every window.

What is proved in Lean and what the binary corroborates are, as always,
different things:

* proved — `ArraySegSieve.mertensProgram_compiled`: for a well-formed base
  address the compiled CCIR trace leaves `denote` in the output register, with
  `mertensProgram_wf` discharging its only side condition at every
  configuration;
* proved — that `denote` accumulates the reference `M`, `Q` and `T` at
  `[1, 24]`, by kernel evaluation against trial division (`ArraySegSieve.Check`);
* corroborated only — the numeric value below, and the `M(10⁸) = 1928`,
  `Q(10⁸) = 60 792 694` agreement with `bench/ref_seg.c`.  Exit status is not a
  theorem.

The certified constant is the artifact's **output**: the number of failed
epilogue threshold tests.  It is `4` here and not `0` because the window opens
at `lo = 1`, where the Hurst majorant `0.571√n` is `0` and the CDEM majorant is
likewise below the discrepancy — the reduced families start at `n = 33` and
`n = 9243`.  What the certificate exercises is the machinery, not the number
theory; the number theory needs the window schedule described in
`bench/results/array_seg_folds.md`.
-/

namespace LeanCompCert.Testing.ArraySegCertificate

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

def cfg : Cfg := Cfg.ofRange 1 4096 8

def seed : MertensSeed := ⟨mertensBias, 0, gBias⟩

/-- Failed threshold tests at `lo = 1`: both Hurst clauses and both CDEM
clauses, since every majorant vanishes at the left end of this window. -/
def expected : Nat := 4

def program : AProgram := mertensProgram cfg seed 755 10000

theorem program_wf : program.WF := mertensProgram_wf cfg seed 755 10000

def symbolName : String := "ArraySeg.mertens32k"

def mainC : String :=
  "\nstatic uint64_t cells[" ++ toString program.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    return l_ArraySeg_mertens32k((uint64_t)(uintptr_t)cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emittedC : Except (Array String) String := do
  let source ← program.emitRolled symbolName
  pure (source ++ mainC)

end LeanCompCert.Testing.ArraySegCertificate
