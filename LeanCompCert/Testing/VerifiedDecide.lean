import LeanCompCert.Verified.Decide
import LeanCompCert.Lower.Pure

namespace LeanCompCert.Testing.VerifiedDecide

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified

private def mkLocal (id : Nat) : CCIR.LocalDecl := {
  id := ⟨id⟩
  type := .u64
}

def instructions : List StraightInstruction := [
  .assign (mkLocal 0) (.uintLit .u64 40),
  .assign (mkLocal 1) (.uintLit .u64 2),
  .binary (mkLocal 2) .add (.local ⟨0⟩) (.local ⟨1⟩)
]

def block : CCIR.Block := {
  id := ⟨0⟩
  instructions := (instructions.map StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨2⟩))
}

def fn : CCIR.Function := {
  name := ⟨"VerifiedDecide.addFortyTwo"⟩
  params := #[]
  result := .u64
  entry := block.id
  blocks := #[block]
  sourceDecl := some "verified_decide example"
}

def statements : List C.CStmt := [
  .assign (.var "v_0" .u64) (.uintLit .u64 40),
  .assign (.var "v_1" .u64) (.uintLit .u64 2),
  .assign (.var "v_2" .u64)
    (.binary .u64 .add (.var "v_0" .u64) (.var "v_1" .u64))
]

def computation : Computation := {
  fn
  block
  instructions
  statements
  output := ⟨2⟩
  wellFormed := by
    intro instruction hInstruction
    simp [instructions] at hInstruction
    rcases hInstruction with rfl | rfl | rfl
    all_goals
      simp [StraightInstruction.WellFormed, mkLocal, CCIR.CCType.isUnsigned]
  lowered := by rfl
}

def decision :
    Decision (computation.Returns 42) :=
  Decision.forResult computation 42

theorem source_computation_returns_42 :
    computation.sourceResult = some 42 := by
  verified_decide using decision

theorem generated_c_model_returns_42 :
    computation.targetResult = some 42 := by
  rw [computation.result_preserved]
  exact source_computation_returns_42

/--
The no-argument form is a sound drop-in replacement when the proposition is a
closed total computation.  This is the first real Lean/Lake corpus case:
ordinary `decide` exceeds its default recursion depth at this size.
-/
theorem kernel_list_range :
    (List.range 1000).length = 1000 := by
  verified_decide

def program : CCIR.Program := {
  functions := #[fn]
}

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_VerifiedDecide_addFortyTwo() == UINT64_C(42) ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable program
  pure (source ++ mainC)

end LeanCompCert.Testing.VerifiedDecide
