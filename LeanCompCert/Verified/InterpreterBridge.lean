import LeanCompCert.CCIR.Interpreter
import LeanCompCert.Verified.Package

/-!
# A total evaluator for the emitted scalar CCIR fragment

`CCIR.evalPure` is a useful executable diagnostic interpreter, but its support
for calls and cyclic control flow makes its core mutually `partial`.  Proofs
about the certificate fragment do not need that generality: a packaged
`Reflect.Program` is a closed, one-block CCIR function whose body contains
only assignments, unsigned scalar operations, comparisons, and casts.

This file gives that actual CCIR instruction list a small, kernel-reducible
semantics.  The central theorem, `evalSequence_map_toCCIR`, proves once and for
all that it is exactly `Proof.evalCCSequence` on every trace produced from
`Proof.StraightInstruction`.  Consequently `evalClosedScalar_toFn`
connects the total evaluator of the packaged CCIR function directly to
`Program.denote`; the existing lowering theorem then connects the same
`Proof.evalCCSequence` result to emitted restricted C.

Unsupported instructions return `none`.  This is deliberate: the evaluator
does not assign semantics to memory, calls, Lean objects, signed arithmetic,
or control flow.
-/

namespace LeanCompCert.Verified.InterpreterBridge

open LeanCompCert
open LeanCompCert.Proof

/-- Execute one actual CCIR instruction in the proved scalar subset.

The environment and scalar operators are the ones used by
`Proof.PureSemantics`, so this definition is both total and kernel-reducible.
Every constructor outside the emitted scalar subset is rejected. -/
def evalInstruction (env : CCEnv) : CCIR.Instruction → Option CCEnv
  | .assign dest value => evalCCAssignStep env dest value
  | .unary dest (.cast target) value => do
      let operandValue ← evalOperand env value
      let result ← normalizeCC target operandValue
      pure (env.set dest.id result)
  | .unary _ _ _ => none
  | .binary dest op lhs rhs =>
      match op with
      | .add => evalCCBinaryStep env dest .add lhs rhs
      | .sub => evalCCBinaryStep env dest .sub lhs rhs
      | .mul => evalCCBinaryStep env dest .mul lhs rhs
      | .udiv => evalCCBinaryStep env dest .udiv lhs rhs
      | .urem => evalCCBinaryStep env dest .urem lhs rhs
      | .bitAnd => evalCCBinaryStep env dest .bitAnd lhs rhs
      | .bitOr => evalCCBinaryStep env dest .bitOr lhs rhs
      | .bitXor => evalCCBinaryStep env dest .bitXor lhs rhs
      | .shl => evalCCBinaryStep env dest .shl lhs rhs
      | .lshr => evalCCBinaryStep env dest .lshr lhs rhs
      | .eq => evalCCComparisonStep env dest .eq lhs rhs
      | .ne => evalCCComparisonStep env dest .ne lhs rhs
      | .ult => evalCCComparisonStep env dest .ult lhs rhs
      | .ule => evalCCComparisonStep env dest .ule lhs rhs
      | .ugt => evalCCComparisonStep env dest .ugt lhs rhs
      | .uge => evalCCComparisonStep env dest .uge lhs rhs
      | .sdiv | .srem | .ashr | .slt | .sle | .sgt | .sge => none
  | .load _ _ | .store _ _ | .loadIndex _ _ _ | .storeIndex _ _ _
  | .call _ _ _ _ | .runtimeCall _ _ _ _ | .retain _ | .release _
  | .allocCtor _ _ _ | .setField _ _ _ | .getTag _ _ | .project _ _ _ => none

/-- Total execution of a finite actual-CCIR instruction list. -/
def evalSequence (env : CCEnv) : List CCIR.Instruction → Option CCEnv
  | [] => some env
  | instruction :: rest => do
      let env ← evalInstruction env instruction
      evalSequence env rest

/-- One instruction produced by the proved straight-line front end has
exactly the existing source semantics used by the C-lowering theorem. -/
theorem evalInstruction_toCCIR (env : CCEnv)
    (instruction : StraightInstruction) :
    evalInstruction env instruction.toCCIR =
      evalCCStraight env instruction := by
  cases instruction with
  | assign => rfl
  | binary dest op lhs rhs => cases op <;> rfl
  | compare dest op lhs rhs => cases op <;> rfl
  | cast => rfl

/-- Generic trace bridge.  It is structural in the trace and does not execute
the computation represented by that trace. -/
theorem evalSequence_map_toCCIR (env : CCEnv) :
    ∀ instructions : List StraightInstruction,
      evalSequence env (instructions.map StraightInstruction.toCCIR) =
        evalCCSequence env instructions := by
  intro instructions
  induction instructions generalizing env with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.map_cons, evalSequence, evalCCSequence]
      rw [evalInstruction_toCCIR]
      cases evalCCStraight env instruction with
      | none => rfl
      | some next => exact ih next

/-- Read the result of a closed, one-block scalar CCIR function.  This is the
kernel-visible counterpart of the corresponding `evalPure` use case; it
rejects parameters, non-local returns, and all control flow. -/
def evalClosedScalar (fn : CCIR.Function) : Option Int :=
  if fn.params.isEmpty then
    match fn.findBlock? fn.entry with
    | some block => do
        let env ← evalSequence Verified.emptyCCEnv block.instructions.toList
        match block.terminator with
        | .return (some (.local id)) => env id
        | _ => none
    | none => none
  else
    none

/-- The actual instruction array installed in a packaged reflected block has
the same total semantics as its proved straight-line trace. -/
theorem evalSequence_toBlock
    (p : Verified.Reflect.Program) (env : CCEnv) :
    evalSequence env p.toBlock.instructions.toList =
      evalCCSequence env p.compile := by
  rw [show p.toBlock.instructions.toList =
      p.compile.map StraightInstruction.toCCIR by
    simp [Verified.Reflect.Program.toBlock]]
  exact evalSequence_map_toCCIR env p.compile

/-- End-to-end Lean-side denotation bridge for the restricted scalar
functions actually handed to the C emitter.  This theorem is generic in the
program and function name; it does not evaluate a concrete certificate. -/
theorem evalClosedScalar_toFn
    (p : Verified.Reflect.Program) (name : String) (hWF : p.WF) :
    evalClosedScalar (p.toFn name) =
      p.denote.map (fun n => (n : Int)) := by
  unfold evalClosedScalar
  simp only [Verified.Reflect.Program.toFn, Array.isEmpty_empty,
    ↓reduceIte, CCIR.Function.findBlock?]
  change
    ((evalSequence Verified.emptyCCEnv p.toBlock.instructions.toList).bind
      (fun env => env ⟨p.output + 1⟩)) = _
  rw [evalSequence_toBlock]
  exact p.evalCC_compile hWF

/-- The same actual-CCIR result is also the result of the restricted-C AST
produced by the verified lowering.  This composes the new bridge with the
existing whole-trace lowering theorem; no C execution is a premise. -/
theorem evalClosedScalar_toFn_eq_targetResult
    (p : Verified.Reflect.Program) (name : String) (hWF : p.WF) :
    evalClosedScalar (p.toFn name) =
      (p.toComputation name hWF).targetResult := by
  calc
    evalClosedScalar (p.toFn name) =
        p.denote.map (fun n => (n : Int)) :=
      evalClosedScalar_toFn p name hWF
    _ = (p.toComputation name hWF).sourceResult := by
      symm
      exact p.evalCC_compile hWF
    _ = (p.toComputation name hWF).targetResult :=
      (p.toComputation name hWF).result_preserved.symm

/-! Small kernel regressions: one checks literal conversion in the total
actual-CCIR evaluator; the other exercises the generic reflected-program
theorem without `native_decide` or an external computation. -/

private def literalDest : CCIR.LocalDecl := { id := ⟨0⟩, type := .u8 }

theorem evalSequence_wide_u8_literal :
    ((evalSequence Verified.emptyCCEnv
      [.assign literalDest (.uintLit .u8 257)]).bind (fun env => env ⟨0⟩)) =
      some 1 := by
  decide

private def bridgeRegressionProgram : Verified.Reflect.Program := {
  regCount := 1
  loopCount := 0
  init := [.mov 0 (.lit (2 ^ 64 + 7))]
  body := []
  epilogue := []
  output := 0
}

private theorem bridgeRegressionProgram_wf : bridgeRegressionProgram.WF := by
  decide

theorem evalClosedScalar_bridge_regression :
    evalClosedScalar (bridgeRegressionProgram.toFn "Bridge.regression") =
      some 7 := by
  rw [evalClosedScalar_toFn bridgeRegressionProgram _
    bridgeRegressionProgram_wf]
  decide

end LeanCompCert.Verified.InterpreterBridge
