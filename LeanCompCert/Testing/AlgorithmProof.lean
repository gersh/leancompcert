import LeanCompCert.Verified.Algorithm.Mvcgen
import LeanCompCert.Verified.FoldBridge

/-!
# End-to-end algorithm-to-mathematics example

This example exercises the new public path rather than proving a toy theorem
about the wrapper structures:

* `sumRangeMod` is ordinary mutable `do` notation;
* `sumRangeMod_eq_foldl` is proved with `mvcgen` and a loop invariant;
* `reference_sound` turns success of a checker into a mathematical equality;
* `program_denote` uses the existing structural fold bridge;
* `compilation` relates accepted program output to the reference checker;
* `example_claim` packages the result for compilation or external run
  evidence.

There is no run axiom and no attestation import in this module.
-/

namespace LeanCompCert.Testing.AlgorithmProof

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.FoldBridge
open LeanCompCert.Verified.Algorithm
open Std.Do

set_option mvcgen.warning false

structure Input where
  count : Nat
  expected : Nat
  deriving Repr, DecidableEq

/-- A reference algorithm written as a conventional mutable loop. -/
def sumRangeMod (count : Nat) : Nat := Id.run do
  let mut acc := 0
  for index in List.range count do
    acc := (acc + index % M) % M
  return acc

/-- `mvcgen` turns the loop into the single inductive invariant saying that
the mutable accumulator is the fold over the consumed prefix. -/
theorem sumRangeMod_eq_foldl (count : Nat) :
    sumRangeMod count =
      (List.range count).foldl (fun acc index => (acc + index % M) % M) 0 := by
  generalize h : sumRangeMod count = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨cursor, acc⟩ =>
      ⌜acc = cursor.prefix.foldl (fun total index => (total + index % M) % M) 0⌝
  all_goals simp_all [List.foldl_append]

def check (input : Input) : Bool :=
  sumRangeMod input.count == input.expected % M

def reference : Algorithm Input Unit :=
  Algorithm.ofChecker check

def proposition (input : Input) : Prop :=
  (List.range input.count).foldl
    (fun acc index => (acc + index % M) % M) 0 = input.expected % M

/-- Successful execution of the reference checker implies the mathematical
fold equality.  The only algorithmic fact it needs is the `mvcgen` theorem. -/
theorem reference_sound : reference.Ensures proposition := by
  apply Algorithm.ofChecker_ensures
  intro input accepted
  simp only [check, beq_iff_eq] at accepted
  rw [sumRangeMod_eq_foldl] at accepted
  exact accepted

/-- The fixed-shape register program: accumulate in `r0`, then compare the
result with the expected value into `r1`. -/
def program (input : Input) : Program := {
  regCount := 2
  loopCount := input.count
  init := []
  body := [.binop 0 .add (.reg 0) .idx]
  epilogue := [.binop 1 .eq (.reg 0) (.lit input.expected)]
  output := 1
}

theorem program_wf (input : Input) : (program input).WF := by
  simp [program, Program.WF, Instr.WF, Operand.WF]

private def step (index : Nat) (state : RegState) : RegState :=
  state.set 0 ((state 0 + index % M) % M)

private def finish (expected : Nat) (state : RegState) : RegState :=
  state.set 1 (if state 0 = expected % M then 1 else 0)

/-- The register program computes exactly the comparison performed by the
reference checker.  This proof is structural in `input.count`; it never
evaluates the loop. -/
theorem program_denote (input : Input) :
    (program input).denote =
      some (if sumRangeMod input.count = input.expected % M then 1 else 0) := by
  have hfold := Program.denote_eq_foldl (program input)
    (fun _ => True) step (finish input.expected) initialState
    rfl trivial
    (by intro index state _; rfl)
    (by intro _ _ _; trivial)
    (by intro state _; rfl)
  have hobs := foldl_obs (fun _ => True) step
    (fun state => state 0)
    (fun index acc => (acc + index % M) % M)
    (by intro _ _ _; trivial)
    (by intro _ _ _; rfl)
    (List.range input.count) initialState trivial
  have hfold' : (program input).denote =
      some (finish input.expected
        ((List.range input.count).foldl (fun state index => step index state)
          initialState) 1) := by
    simpa only [program] using hfold
  rw [hfold']
  simp [finish, RegState.set]
  rw [hobs]
  simp only [initialState]
  rw [sumRangeMod_eq_foldl]
  rfl

/-- Machine result `1` decodes to the unit success witness; every other
machine result is rejection. -/
def decode (_input : Input) (value : Nat) : Option Unit :=
  if value = 1 then some () else none

/-- The verified program-to-reference refinement. -/
def compilation : ProgramRefinement reference := {
  program
  wellFormed := program_wf
  decode
  refines := by
    intro input value output returned decoded
    have hvalue : value = 1 := by
      simpa [decode] using decoded
    subst value
    cases output
    rw [program_denote] at returned
    by_cases accepted : sumRangeMod input.count = input.expected % M
    · simp [reference, Algorithm.ofChecker, check, accepted]
    · simp [accepted] at returned
}

def certified : CertifiedAlgorithm Input Unit proposition := {
  algorithm := reference
  sound := reference_sound
  compilation
}

def exampleInput : Input := ⟨10, 45⟩

def exampleClaim : ProgramClaim (proposition exampleInput) :=
  certified.claim exampleInput 1 () (by decide)

theorem example_program_accepts : exampleClaim.program.denote = some 1 := by
  rw [show exampleClaim.program = program exampleInput from rfl, program_denote]
  decide

/-- Kernel-checked end-to-end theorem from the packaged computation result. -/
theorem example_result : proposition exampleInput :=
  exampleClaim.prove "AlgorithmProof.sumRange" <|
    (exampleClaim.returns_iff "AlgorithmProof.sumRange").mpr
      example_program_accepts

end LeanCompCert.Testing.AlgorithmProof
