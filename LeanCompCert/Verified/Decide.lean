import LeanCompCert.Proof.PureSemantics

namespace LeanCompCert.Verified

open LeanCompCert
open LeanCompCert.Proof

/-- Initial state for a closed computation: no source locals are defined. -/
def emptyCCEnv : CCEnv := fun _ => none

/-- Initial state for the corresponding closed generated-C computation. -/
def emptyCEnv : CEnv := fun _ => none

theorem emptyEnvRel : EnvRel emptyCCEnv emptyCEnv := by
  intro id
  rfl

/--
A closed, compiled computation in the proved straight-line fragment.

`lowered` is a proof that `statements` were produced by the verified lowering
function. It is data checked by Lean's kernel, not a claim supplied by an
external executable.
-/
structure Computation where
  fn : CCIR.Function
  block : CCIR.Block
  instructions : List StraightInstruction
  statements : List C.CStmt
  output : CCIR.LocalId
  wellFormed : ∀ instruction ∈ instructions, instruction.WellFormed fn
  lowered : lowerSequence fn instructions = .ok statements

namespace Computation

/-- Execute the source CCIR model and read the designated result local. -/
def sourceResult (computation : Computation) : Option Int := do
  let env ← evalCCSequence emptyCCEnv computation.instructions
  env computation.output

/-- Execute the corresponding restricted generated-C model. -/
def targetResult (computation : Computation) : Option Int := do
  let env ← evalCSequence emptyCEnv computation.statements
  env (ABI.localName computation.output.value)

/--
Each stored target statement is exactly the output of the production
`Lower.lowerInstruction` function.
-/
theorem producedByLowerInstruction (computation : Computation) :
    InstructionLoweringRel computation.fn computation.block 0
      computation.instructions computation.statements :=
  lowerSequence_is_lowerInstructions
    computation.fn computation.block 0 computation.instructions
      computation.statements computation.lowered

/--
The generated-C computation returns exactly the source CCIR result.

This is the reusable semantic-preservation theorem consumed by
`verified_decide`.
-/
theorem result_preserved (computation : Computation) :
    computation.targetResult = computation.sourceResult := by
  have hTrace := lowerSequence_correct
    computation.fn computation.instructions computation.statements
      emptyCCEnv emptyCEnv emptyEnvRel computation.wellFormed
      computation.lowered
  unfold sourceResult targetResult
  generalize hSource :
    evalCCSequence emptyCCEnv computation.instructions = source at hTrace ⊢
  generalize hTarget :
    evalCSequence emptyCEnv computation.statements = target at hTrace ⊢
  cases source with
  | none =>
      cases target with
      | none => rfl
      | some targetEnv => contradiction
  | some sourceEnv =>
      cases target with
      | none => contradiction
      | some targetEnv =>
          exact hTrace computation.output

def Returns (computation : Computation) (value : Int) : Prop :=
  computation.sourceResult = some value

instance (computation : Computation) (value : Int) :
    Decidable (computation.Returns value) :=
  inferInstanceAs (Decidable (computation.sourceResult = some value))

theorem targetReturns_iff (computation : Computation) (value : Int) :
    computation.targetResult = some value ↔ computation.Returns value := by
  simp [Returns, computation.result_preserved]

end Computation

/--
A proposition decided by a compiled computation.

The specification is proved once. Individual uses only evaluate the closed
CCIR computation and let the kernel check the resulting equality certificate.
-/
structure Decision (proposition : Prop) where
  computation : Computation
  acceptingValue : Int := 1
  specification : computation.Returns acceptingValue ↔ proposition

namespace Decision

def forResult (computation : Computation) (value : Int) :
    Decision (computation.Returns value) := {
  computation
  acceptingValue := value
  specification := Iff.rfl
}

theorem prove
    {proposition : Prop}
    (decision : Decision proposition)
    (accepted : decision.computation.Returns decision.acceptingValue) :
    proposition :=
  decision.specification.mp accepted

theorem target_accepts_iff
    {proposition : Prop}
    (decision : Decision proposition) :
    decision.computation.targetResult = some decision.acceptingValue ↔
      proposition := by
  rw [decision.computation.targetReturns_iff]
  exact decision.specification

end Decision

/--
Kernel-checked analogue of `native_decide`.

With an explicit `Decision`, the tactic checks a computation in the proved
CCIR-to-C fragment and applies its specification.  With no argument, it runs
Lean's kernel evaluator directly.  The latter is useful for closed, total
computations that merely exceed `decide`'s conservative default recursion
limit.

Neither form invokes `native_decide` or admits a native-code result as a proof.
-/
syntax (name := verifiedDecideKernel) "verified_decide" : tactic
syntax (name := verifiedDecideCertified)
  "verified_decide" ppSpace "using" ppSpace term : tactic

macro_rules
  | `(tactic| verified_decide) =>
      `(tactic|
        set_option maxRecDepth 100000 in (decide +kernel))
  | `(tactic| verified_decide using $decision) =>
      `(tactic|
        exact LeanCompCert.Verified.Decision.prove $decision (by decide +kernel))

end LeanCompCert.Verified
