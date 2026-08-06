import LeanCompCert.Verified.Package

/-!
# Closed Boolean carrier

This small verified carrier is for finite checks whose transparent Lean model
is cheap in compiled evaluation but too large for repeated kernel reduction.
The generated program returns zero exactly when the closed Boolean is true.
`Program.evalCC_compile` then proves that the lowered CCIR and generated C
preserve that result.  A consuming project still exposes the physical run as
a named run axiom; no native-code proof primitive is used.
-/

namespace LeanCompCert.Ports.ClosedBoolCarrier

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Proof

def result (b : Bool) : Nat := if b then 0 else 1

def program (b : Bool) : Program := {
  regCount := 1
  loopCount := 0
  init := [.mov 0 (.lit (result b))]
  body := []
  epilogue := []
  output := 0
}

theorem program_wf (b : Bool) : (program b).WF := by
  simp [program, Program.WF, Instr.WF, Operand.WF]

theorem denote_eq (b : Bool) : (program b).denote = some (result b) := by
  cases b <;> decide +kernel

theorem denote_zero_iff (b : Bool) :
    (program b).denote = some 0 ↔ b = true := by
  rw [denote_eq]
  cases b <;> simp [result]

theorem compiled_result (b : Bool) :
    ((evalCCSequence LeanCompCert.Verified.emptyCCEnv (program b).compile).bind
      (fun env => env ⟨1⟩)) =
      (program b).denote.map (fun n => (n : Int)) := by
  simpa [program] using Program.evalCC_compile (program b) (program_wf b)

/-- Package the carrier through the production LeanCompCert lowering path. -/
def computation (b : Bool) : LeanCompCert.Verified.Computation :=
  (program b).toComputation "ClosedBoolCarrier" (program_wf b)

/-- A run admission for the packaged compiled program is equivalent to the
source Boolean.  The forward direction is the one used by certificates. -/
theorem computation_returns_zero_iff (b : Bool) :
    (computation b).Returns ((0 : Nat) : Int) ↔ b = true := by
  unfold computation
  rw [LeanCompCert.Verified.Reflect.toComputation_returns]
  exact denote_zero_iff b

end LeanCompCert.Ports.ClosedBoolCarrier
