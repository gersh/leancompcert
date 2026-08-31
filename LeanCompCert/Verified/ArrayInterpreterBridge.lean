import LeanCompCert.Verified.InterpreterBridge
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ClightContract

/-!
# A total evaluator for the emitted array CCIR fragment

This is the memory analogue of `Verified.InterpreterBridge`.  It gives the
*actual* `CCIR.Instruction` array installed by `AProgram.toFn` a small total
semantics and proves that semantics equal to `MemFragment.evalMCCSequence`.
The proof is structural in the instruction trace: it does not run the
certificate computation.

The caller supplies the initial state because the sole pointer parameter is
represented in the proof model by its abstract integer base address.  Loads
and stores use precisely the same typed-indexed address operation as
`MemFragment`; unsupported CCIR instructions are rejected.
-/

namespace LeanCompCert.Verified.ArrayInterpreterBridge

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment

/-- Execute one actual CCIR instruction in the proved scalar-plus-array
fragment.  Scalar instructions delegate to the already proved total scalar
interpreter, while memory instructions use `MCCState`'s single-array model. -/
def evalInstruction (s : MCCState) : CCIR.Instruction → Option MCCState
  | .load dest address =>
      Option.bind (evalOperand s.env address) fun addr =>
      Option.bind (s.mem addr) fun value =>
        some { s with env := s.env.set dest.id value }
  | .store address value =>
      Option.bind (evalOperand s.env address) fun addr =>
      Option.bind (evalOperand s.env value) fun stored =>
        some { s with mem := Mem.set s.mem addr stored }
  | .loadIndex dest base index =>
      Option.bind (evalOperand s.env base) fun baseValue =>
      Option.bind (evalOperand s.env index) fun indexValue =>
      Option.bind (s.mem (indexedAddr baseValue indexValue)) fun value =>
        some { s with env := s.env.set dest.id value }
  | .storeIndex base index value =>
      Option.bind (evalOperand s.env base) fun baseValue =>
      Option.bind (evalOperand s.env index) fun indexValue =>
      Option.bind (evalOperand s.env value) fun stored =>
        some { s with
          mem := Mem.set s.mem (indexedAddr baseValue indexValue) stored }
  | instruction =>
      match InterpreterBridge.evalInstruction s.env instruction with
      | some env => some { s with env := env }
      | none => none

/-- Total execution of a finite actual-CCIR instruction list with memory. -/
def evalSequence (s : MCCState) : List CCIR.Instruction → Option MCCState
  | [] => some s
  | instruction :: rest => do
      let next ← evalInstruction s instruction
      evalSequence next rest

@[simp] private theorem envFrame_eq_bind (s : MCCState)
    (result : Option CCEnv) :
    (match result with
      | some env => some { s with env := env }
      | none => none) =
      result.bind (fun env => some { s with env := env }) := by
  cases result <;> rfl

/-- Every memory-fragment instruction has exactly the semantics assigned to
its actual CCIR encoding. -/
theorem evalInstruction_toCCIR (s : MCCState) (instruction : MInstr) :
    evalInstruction s instruction.toCCIR = evalMCC s instruction := by
  cases instruction with
  | straight scalar =>
      cases scalar with
      | assign => simp [MInstr.toCCIR, StraightInstruction.toCCIR,
          evalInstruction, evalMCC, evalCCStraight,
          InterpreterBridge.evalInstruction]
      | binary dest op lhs rhs => cases op <;>
          simp [MInstr.toCCIR, StraightInstruction.toCCIR, evalInstruction,
            evalMCC, evalCCStraight, UnsignedBinary.ccir,
            InterpreterBridge.evalInstruction]
      | compare dest op lhs rhs => cases op <;>
          simp [MInstr.toCCIR, StraightInstruction.toCCIR, evalInstruction,
            evalMCC, evalCCStraight, UnsignedComparison.ccir,
            InterpreterBridge.evalInstruction]
      | cast => simp [MInstr.toCCIR, StraightInstruction.toCCIR,
          evalInstruction, evalMCC, evalCCStraight,
          InterpreterBridge.evalInstruction, evalCCCastStep]
  | load => rfl
  | store => rfl
  | loadIndex => rfl
  | storeIndex => rfl

/-- Generic actual-instruction-array bridge.  The induction only traverses
the syntax; it never evaluates a concrete `AProgram`. -/
theorem evalSequence_map_toCCIR (s : MCCState) :
    ∀ instructions : List MInstr,
      evalSequence s (instructions.map MInstr.toCCIR) =
        evalMCCSequence s instructions := by
  intro instructions
  induction instructions generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.map_cons, evalSequence, evalMCCSequence]
      rw [evalInstruction_toCCIR]
      cases evalMCC s instruction with
      | none => rfl
      | some next => exact ih next

/-- Evaluate a one-block actual CCIR function from an explicitly supplied
state.  This lets the caller interpret the pointer parameter as the abstract
base address used by the proved memory model. -/
def evalClosedMemoryFunction (fn : CCIR.Function)
    (initial : MCCState) : Option Int :=
  match fn.findBlock? fn.entry with
  | some block => do
      let final ← evalSequence initial block.instructions.toList
      match block.terminator with
      | .return (some (.local id)) => final.env id
      | _ => none
  | none => none

/-- The instruction array installed in `AProgram.toBlock` is the program's
proved memory-fragment trace, not merely text accepted by the C emitter. -/
theorem evalSequence_toBlock (p : AProgram) (s : MCCState) :
    evalSequence s p.toBlock.instructions.toList =
      evalMCCSequence s p.compile := by
  rw [show p.toBlock.instructions.toList =
      p.compile.map MInstr.toCCIR by
    simp [AProgram.toBlock]]
  exact evalSequence_map_toCCIR s p.compile

/-- End-to-end Lean-side denotation theorem for the actual unrolled array
CCIR function.  Its only runtime premise is that the supplied allocation is
large enough and does not wrap. -/
theorem evalClosedMemoryFunction_toFn
    (p : AProgram) (name : String) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (n : Nat) (hDenote : p.denote = some n) :
    evalClosedMemoryFunction (p.toFn name) (p.initialMCC base) =
      some ((n : Nat) : Int) := by
  unfold evalClosedMemoryFunction
  simp only [AProgram.toFn, CCIR.Function.findBlock?]
  change
    ((evalSequence (p.initialMCC base) p.toBlock.instructions.toList).bind
      (fun final => final.env ⟨p.output + 1⟩)) = _
  rw [evalSequence_toBlock]
  exact p.evalCC_compile hWF base hBase n hDenote

/-- Under the full CompCert dynamic-definedness contract, the preceding
theorem is an equality with `AProgram.denote`.  This formulation makes clear
that the bridge proves denotation and does not perform the large run. -/
theorem evalClosedMemoryFunction_toFn_eq_denote
    (p : AProgram) (name : String) (hWF : p.CompCertWF)
    (base : Int) (hBase : BaseOk p.arrayLen base) :
    evalClosedMemoryFunction (p.toFn name) (p.initialMCC base) =
      p.denote.map (fun n => ((n : Nat) : Int)) := by
  rw [ClightContract.aProgram_denote_eq_totalRun p hWF.2]
  simp only [Option.map_some]
  exact evalClosedMemoryFunction_toFn p name hWF.1 base hBase _
    (ClightContract.aProgram_denote_eq_totalRun p hWF.2)

end LeanCompCert.Verified.ArrayInterpreterBridge
