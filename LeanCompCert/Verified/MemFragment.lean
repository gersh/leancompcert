import LeanCompCert.Proof.PureSemantics

/-!
# M5 — CCIR load/store in the proved fragment and the C model

This file extends the proved straight-line fragment of
`LeanCompCert.Proof.PureSemantics` with memory instructions, bringing the
production lowering of CCIR `.load`/`.store` (see `Lower.lowerInstruction`)
into the certified fragment.

## The disjoint-single-array discipline

Memory is modeled as one flat abstract array of integer cells indexed by
integer addresses (`Mem := Int → Option Int`). The CCIR-side state and the
generated-C-side state each carry a memory component, and the state relation
`MRel` demands the two memories be *equal* — both sides act on the same
single abstract array. This is the disjoint-single-array discipline:

* there is exactly one linear memory, shared by both semantics;
* the register file (`CCEnv`/`CEnv`) is disjoint from memory — register
  writes never touch `mem`, and memory writes never touch the environment
  (proved by the frame shape of every case of `lowerM_correct`);
* address arithmetic is left abstract — an unmapped address reads as `none`,
  the same failure discipline as division by zero in the scalar fragment.

## Normalization design

Values move between registers and memory **as-is, with no width
normalization on either side**: the CCIR `.load` writes the raw cell value
into the destination register, and the generated-C deref-load semantics
(`evalMC`) does the same for the emitted `*(T*)addr` read; symmetrically,
`.store` writes the raw operand value on both sides. Because both semantics
share the identical convention (and the identical memory), preservation
holds with no normalization lemma. Width discipline is the store producer's
obligation: values reaching memory through the proved fragment originate
from operands and instruction results that are already normalized at their
CCIR types.
-/

namespace LeanCompCert.Verified.MemFragment

open LeanCompCert

/-- Abstract memory: a single flat array of integer cells addressed by
integers. `none` means the address is unmapped and any access fails. -/
abbrev Mem := Int → Option Int

/-- Point update of one memory cell. -/
def Mem.set (mem : Mem) (addr value : Int) : Mem :=
  fun candidate => if candidate = addr then some value else mem candidate

/-- CCIR-side memory-extended state: the scalar register environment of the
proved fragment plus the single abstract memory. -/
structure MCCState where
  env : Proof.CCEnv
  mem : Mem

/-- Generated-C-side memory-extended state. -/
structure MCState where
  env : Proof.CEnv
  mem : Mem

/-- The memory-extended state relation: environments are related exactly as
in the scalar fragment, and the two memories are equal — the single shared
abstract array of the disjoint-single-array discipline. -/
def MRel (s : MCCState) (t : MCState) : Prop :=
  Proof.EnvRel s.env t.env ∧ s.mem = t.mem

/-- Result relation mirroring `Proof.ResultsRel`: both sides fail together
or succeed into related states. -/
def MResultsRel : Option MCCState → Option MCState → Prop
  | none, none => True
  | some s, some t => MRel s t
  | _, _ => False

/-- Memory-extended instructions: the proved straight-line fragment embedded
unchanged, plus CCIR `.load` and `.store`. -/
inductive MInstr where
  | straight (si : Proof.StraightInstruction)
  | load (dest : CCIR.LocalDecl) (address : CCIR.Operand)
  | store (address value : CCIR.Operand)
  deriving Repr

/-- The CCIR instruction denoted by a memory-extended instruction. -/
def MInstr.toCCIR : MInstr → CCIR.Instruction
  | .straight si => si.toCCIR
  | .load dest address => .load dest address
  | .store address value => .store address value

/-- Loads and stores need no side conditions beyond operand lowerability;
straight instructions carry the scalar fragment's well-formedness. -/
def MInstr.WellFormed (fn : CCIR.Function) : MInstr → Prop
  | .straight si => si.WellFormed fn
  | .load _ _ => True
  | .store _ _ => True

instance (fn : CCIR.Function) (mi : MInstr) : Decidable (mi.WellFormed fn) := by
  cases mi <;> simp only [MInstr.WellFormed] <;> infer_instance

/--
CCIR-side semantics. Straight instructions defer to `Proof.evalCCStraight`
and leave memory unchanged; `.load` reads the shared array (failing on an
unmapped address) and writes the cell value into the destination register
as-is; `.store` writes the raw operand value into the addressed cell.
-/
def evalMCC (s : MCCState) : MInstr → Option MCCState
  | .straight si =>
      Option.bind (Proof.evalCCStraight s.env si) fun env =>
        some { s with env := env }
  | .load dest address =>
      Option.bind (Proof.evalOperand s.env address) fun addr =>
        Option.bind (s.mem addr) fun value =>
          some { s with env := s.env.set dest.id value }
  | .store address value =>
      Option.bind (Proof.evalOperand s.env address) fun addr =>
        Option.bind (Proof.evalOperand s.env value) fun stored =>
          some { s with mem := Mem.set s.mem addr stored }

/--
Generated-C-side extended statement semantics. The three assignment shapes
are disjoint by construction of the match:

* a variable target with a `.deref` value is a memory load;
* a `.deref` target is a memory store;
* every other assignment defers to the scalar `Proof.evalCAssign` with
  memory unchanged (for a variable target this is exactly
  `Proof.evalCStmt`, definitionally, so the scalar preservation theorem
  applies verbatim — note `Proof.evalCExpr` returns `none` on `.deref`, so
  the deferred case never silently evaluates a memory access).

Like the CCIR side, loads and stores move values with no renormalization.
-/
def evalMC (t : MCState) : C.CStmt → Option MCState
  | .assign (.var name _) (.deref _ addressExpr) =>
      Option.bind (Proof.evalCExpr t.env addressExpr) fun addr =>
        Option.bind (t.mem addr) fun value =>
          some { t with env := t.env.set name value }
  | .assign (.deref _ addressExpr) valueExpr =>
      Option.bind (Proof.evalCExpr t.env addressExpr) fun addr =>
        Option.bind (Proof.evalCExpr t.env valueExpr) fun value =>
          some { t with mem := Mem.set t.mem addr value }
  | .assign target value =>
      Option.bind (Proof.evalCAssign t.env target value) fun env =>
        some { t with env := env }
  | _ => none

/--
Lowering of memory-extended instructions. Straight instructions defer to
the proved `Proof.lowerStraight`; `.load` and `.store` build exactly the
statement shapes emitted by the production `Lower.lowerInstruction`
(connected below by `lowerM_is_lowerInstruction`).
-/
def lowerM (fn : CCIR.Function) : MInstr → Except Lower.LowerError C.CStmt
  | .straight si => Proof.lowerStraight fn si
  | .load dest address => do
      let addressExpr ← Lower.lowerOperand fn address
      pure (.assign (Lower.localExpr dest)
        (.deref (Lower.lowerType dest.type) addressExpr))
  | .store address value => do
      let addressExpr ← Lower.lowerOperand fn address
      let valueExpr ← Lower.lowerOperand fn value
      pure (.assign (.deref valueExpr.type addressExpr) valueExpr)

private theorem obind_none {α β : Type} (f : α → Option β) :
    Option.bind (none : Option α) f = none := rfl

private theorem obind_some {α β : Type} (a : α) (f : α → Option β) :
    Option.bind (some a) f = f a := rfl

/-- The load case of `evalMC`, exposed as an unconditional equation. -/
private theorem evalMC_deref_load
    (t : MCState)
    (name : String)
    (varType derefType : C.CType)
    (addressExpr : C.CExpr) :
    evalMC t (.assign (.var name varType) (.deref derefType addressExpr)) =
      (Option.bind (Proof.evalCExpr t.env addressExpr) fun addr =>
        Option.bind (t.mem addr) fun value =>
          some { t with env := t.env.set name value }) := rfl

/-- The store case of `evalMC`, exposed as an unconditional equation. -/
private theorem evalMC_deref_store
    (t : MCState)
    (derefType : C.CType)
    (addressExpr valueExpr : C.CExpr) :
    evalMC t (.assign (.deref derefType addressExpr) valueExpr) =
      (Option.bind (Proof.evalCExpr t.env addressExpr) fun addr =>
        Option.bind (Proof.evalCExpr t.env valueExpr) fun value =>
          some { t with mem := Mem.set t.mem addr value }) := rfl

/--
Memory-frame argument for the embedded scalar fragment: every statement
produced by `Proof.lowerStraight` evaluates under `evalMC` exactly as under
the scalar `Proof.evalCStmt`, with memory carried through unchanged. This
holds because lowered straight-line statements are always assignments to a
local variable from a deref-free expression, so the deferred case of
`evalMC` applies.
-/
theorem evalMC_straight_frame
    (fn : CCIR.Function)
    (si : Proof.StraightInstruction)
    (stmt : C.CStmt)
    (t : MCState)
    (hWF : si.WellFormed fn)
    (hLower : Proof.lowerStraight fn si = .ok stmt) :
    evalMC t stmt =
      Option.bind (Proof.evalCStmt t.env stmt) fun env =>
        some { t with env := env } := by
  cases si with
  | assign dest value =>
      simp only [Proof.lowerStraight] at hLower
      generalize hExpr : Lower.lowerOperand fn value = operandResult at hLower
      cases operandResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          cases value with
          | «local» id =>
              simp only [Lower.lowerOperand] at hExpr
              split at hExpr
              next type hType =>
                  cases hExpr
                  rfl
              next => contradiction
          | global id => simp [Lower.lowerOperand] at hExpr
          | uintLit type litValue =>
              simp only [Lower.lowerOperand] at hExpr
              cases hExpr
              rfl
          | intLit type litValue =>
              simp only [Lower.lowerOperand] at hExpr
              cases hExpr
              rfl
          | null type =>
              simp only [Lower.lowerOperand] at hExpr
              cases hExpr
              rfl
  | binary dest op lhs rhs =>
      simp only [Proof.StraightInstruction.WellFormed] at hWF
      simp only [Proof.lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerBinary fn dest op.ccir lhs rhs = binaryResult at hLower
      cases binaryResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          rw [Proof.lowerBinary_unsigned fn dest op lhs rhs hWF] at hExpr
          generalize hLhs : Lower.lowerOperand fn lhs = lhsResult at hExpr
          cases lhsResult with
          | error error =>
              change Except.error error = Except.ok expr at hExpr
              contradiction
          | ok lhsExpr =>
              generalize hRhs : Lower.lowerOperand fn rhs = rhsResult at hExpr
              cases rhsResult with
              | error error =>
                  change Except.error error = Except.ok expr at hExpr
                  contradiction
              | ok rhsExpr =>
                  change
                    Except.ok
                        (C.CExpr.binary (Lower.lowerType dest.type) op.c
                          lhsExpr rhsExpr) =
                      Except.ok expr at hExpr
                  cases hExpr
                  rfl
  | compare dest op lhs rhs =>
      simp only [Proof.StraightInstruction.WellFormed] at hWF
      obtain ⟨hLhsU, hRhsU⟩ := hWF
      simp only [Proof.lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerBinary fn dest op.ccir lhs rhs = binaryResult at hLower
      cases binaryResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          obtain ⟨⟨lhsExpr, hLhs⟩, ⟨rhsExpr, hRhs⟩⟩ :=
            Proof.lowerBinary_comparison_error fn dest op lhs rhs expr hExpr
          unfold Proof.operandLowersUnsigned at hLhsU hRhsU
          rw [hLhs] at hLhsU
          rw [hRhs] at hRhsU
          simp only [Bool.not_eq_true'] at hLhsU hRhsU
          rw [Proof.lowerBinary_comparison fn dest op lhs rhs lhsExpr rhsExpr
            hLhs hRhs hLhsU hRhsU] at hExpr
          injection hExpr with hE
          subst expr
          rfl
  | cast dest value =>
      simp only [Proof.lowerStraight] at hLower
      generalize hExpr :
        Lower.lowerUnary fn dest (.cast dest.type) value = castResult at hLower
      cases castResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok expr =>
          change
            Except.ok (.assign (Lower.localExpr dest) expr) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          obtain ⟨operandExpr, hOperand, hCast⟩ :=
            Proof.lowerUnary_cast_inv fn dest value expr hExpr
          subst expr
          rfl

/--
Semantic preservation for one memory-extended instruction: from related
states, a successfully lowered instruction either fails on both sides or
produces related states again. The straight case is the scalar theorem
`Proof.lowerStraight_correct` plus the memory-frame argument; loads and
stores go through `Proof.lowerOperand_correct` on the shared memory.
-/
theorem lowerM_correct
    (fn : CCIR.Function)
    (mi : MInstr)
    (stmt : C.CStmt)
    (s : MCCState)
    (t : MCState)
    (hRel : MRel s t)
    (hWF : mi.WellFormed fn)
    (hLower : lowerM fn mi = .ok stmt) :
    MResultsRel (evalMCC s mi) (evalMC t stmt) := by
  obtain ⟨hEnv, hMem⟩ := hRel
  cases mi with
  | straight si =>
      simp only [lowerM] at hLower
      simp only [MInstr.WellFormed] at hWF
      have hFrame := evalMC_straight_frame fn si stmt t hWF hLower
      have hStep :=
        Proof.lowerStraight_correct fn si stmt s.env t.env hEnv hWF hLower
      rw [hFrame]
      simp only [evalMCC]
      generalize hCC : Proof.evalCCStraight s.env si = ccResult at hStep ⊢
      generalize hC : Proof.evalCStmt t.env stmt = cResult at hStep ⊢
      cases ccResult with
      | none =>
          cases cResult with
          | none => trivial
          | some tEnv => contradiction
      | some sEnv =>
          cases cResult with
          | none => contradiction
          | some tEnv =>
              simp only [obind_some, MResultsRel, MRel]
              exact ⟨hStep, by first | rfl | exact hMem⟩
  | load dest address =>
      simp only [lowerM] at hLower
      generalize hAddr : Lower.lowerOperand fn address = addressResult at hLower
      cases addressResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok addressExpr =>
          change
            Except.ok (.assign (Lower.localExpr dest)
              (.deref (Lower.lowerType dest.type) addressExpr)) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          have hAddrEq :=
            Proof.lowerOperand_correct fn address addressExpr s.env t.env
              hEnv hAddr
          simp only [evalMCC, Lower.localExpr, evalMC_deref_load]
          rw [hAddrEq, ← hMem]
          generalize hAddrValue : Proof.evalOperand s.env address = addrValue
          cases addrValue with
          | none => trivial
          | some addr =>
              simp only [obind_some]
              generalize hLoaded : s.mem addr = loaded
              cases loaded with
              | none => trivial
              | some value =>
                  simp only [obind_some, MResultsRel, MRel]
                  exact ⟨hEnv.set dest.id value, by first | trivial | exact hMem⟩
  | store address value =>
      simp only [lowerM] at hLower
      generalize hAddr : Lower.lowerOperand fn address = addressResult at hLower
      cases addressResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok addressExpr =>
          generalize hValue : Lower.lowerOperand fn value = valueResult at hLower
          cases valueResult with
          | error error =>
              change Except.error error = Except.ok stmt at hLower
              contradiction
          | ok valueExpr =>
              change
                Except.ok (.assign (.deref valueExpr.type addressExpr)
                  valueExpr) = Except.ok stmt at hLower
              injection hLower with hStmt
              subst stmt
              have hAddrEq :=
                Proof.lowerOperand_correct fn address addressExpr s.env t.env
                  hEnv hAddr
              have hValueEq :=
                Proof.lowerOperand_correct fn value valueExpr s.env t.env
                  hEnv hValue
              simp only [evalMCC, evalMC_deref_store]
              rw [hAddrEq, hValueEq, ← hMem]
              generalize hAddrValue : Proof.evalOperand s.env address = addrValue
              cases addrValue with
              | none => trivial
              | some addr =>
                  simp only [obind_some]
                  generalize hStored : Proof.evalOperand s.env value = storedValue
                  cases storedValue with
                  | none => trivial
                  | some stored =>
                      simp only [obind_some, MResultsRel, MRel]
                      exact ⟨hEnv, by first | trivial | exact hMem⟩

/--
Production connection for loads: whenever the address operand lowers, the
production instruction lowerer emits exactly the single deref-load
assignment modeled by `lowerM`/`evalMC`.
-/
theorem lowerInstruction_load
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (dest : CCIR.LocalDecl)
    (address : CCIR.Operand)
    (addressExpr : C.CExpr)
    (hAddr : Lower.lowerOperand fn address = .ok addressExpr) :
    Lower.lowerInstruction fn block index (.load dest address) =
      .ok {
        statements := #[.assign (Lower.localExpr dest)
          (.deref (Lower.lowerType dest.type) addressExpr)]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hAddr]
  rfl

/--
Production connection for stores: whenever both operands lower, the
production instruction lowerer emits exactly the single deref-store
assignment modeled by `lowerM`/`evalMC`.
-/
theorem lowerInstruction_store
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (address value : CCIR.Operand)
    (addressExpr valueExpr : C.CExpr)
    (hAddr : Lower.lowerOperand fn address = .ok addressExpr)
    (hValue : Lower.lowerOperand fn value = .ok valueExpr) :
    Lower.lowerInstruction fn block index (.store address value) =
      .ok {
        statements := #[.assign (.deref valueExpr.type addressExpr) valueExpr]
      } := by
  simp only [Lower.lowerInstruction]
  rw [hAddr, hValue]
  rfl

/--
Every successful `lowerM` result is exactly the singleton statement array
returned by the production `Lower.lowerInstruction` on the corresponding
CCIR instruction — including the memory instructions.
-/
theorem lowerM_is_lowerInstruction
    (fn : CCIR.Function)
    (block : CCIR.Block)
    (index : Nat)
    (mi : MInstr)
    (stmt : C.CStmt)
    (hLower : lowerM fn mi = .ok stmt) :
    Lower.lowerInstruction fn block index mi.toCCIR =
      .ok { statements := #[stmt] } := by
  cases mi with
  | straight si =>
      simp only [lowerM] at hLower
      simp only [MInstr.toCCIR]
      exact Proof.lowerStraight_is_lowerInstruction fn block index si stmt hLower
  | load dest address =>
      simp only [lowerM] at hLower
      simp only [MInstr.toCCIR]
      generalize hAddr : Lower.lowerOperand fn address = addressResult at hLower
      cases addressResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok addressExpr =>
          change
            Except.ok (.assign (Lower.localExpr dest)
              (.deref (Lower.lowerType dest.type) addressExpr)) =
              Except.ok stmt at hLower
          injection hLower with hStmt
          subst stmt
          exact lowerInstruction_load fn block index dest address addressExpr hAddr
  | store address value =>
      simp only [lowerM] at hLower
      simp only [MInstr.toCCIR]
      generalize hAddr : Lower.lowerOperand fn address = addressResult at hLower
      cases addressResult with
      | error error =>
          change Except.error error = Except.ok stmt at hLower
          contradiction
      | ok addressExpr =>
          generalize hValue : Lower.lowerOperand fn value = valueResult at hLower
          cases valueResult with
          | error error =>
              change Except.error error = Except.ok stmt at hLower
              contradiction
          | ok valueExpr =>
              change
                Except.ok (.assign (.deref valueExpr.type addressExpr)
                  valueExpr) = Except.ok stmt at hLower
              injection hLower with hStmt
              subst stmt
              exact lowerInstruction_store fn block index address value
                addressExpr valueExpr hAddr hValue

/-- Whole-trace CCIR semantics for memory-extended straight-line programs. -/
def evalMCCSequence (s : MCCState) : List MInstr → Option MCCState
  | [] => some s
  | mi :: rest =>
      Option.bind (evalMCC s mi) fun next => evalMCCSequence next rest

/-- Whole-trace generated-C semantics under the extended statement model. -/
def evalMCSequence (t : MCState) : List C.CStmt → Option MCState
  | [] => some t
  | stmt :: rest =>
      Option.bind (evalMC t stmt) fun next => evalMCSequence next rest

/-- Lower a memory-extended straight-line trace, one statement per
instruction, with the production helpers. -/
def lowerMSequence
    (fn : CCIR.Function) :
    List MInstr → Except Lower.LowerError (List C.CStmt)
  | [] => .ok []
  | mi :: rest => do
      let stmt ← lowerM fn mi
      let statements ← lowerMSequence fn rest
      pure (stmt :: statements)

/--
Semantic preservation for any successfully lowered memory-extended
straight-line trace: an induction over program length, mirroring
`Proof.lowerSequence_correct` with the shared memory carried through.
-/
theorem lowerMSequence_correct
    (fn : CCIR.Function)
    (instructions : List MInstr)
    (statements : List C.CStmt)
    (s : MCCState)
    (t : MCState)
    (hRel : MRel s t)
    (hWellFormed : ∀ mi ∈ instructions, mi.WellFormed fn)
    (hLower : lowerMSequence fn instructions = .ok statements) :
    MResultsRel
      (evalMCCSequence s instructions)
      (evalMCSequence t statements) := by
  induction instructions generalizing statements s t with
  | nil =>
      simp only [lowerMSequence] at hLower
      injection hLower with hStatements
      subst statements
      simpa [evalMCCSequence, evalMCSequence, MResultsRel] using hRel
  | cons mi rest ih =>
      simp only [lowerMSequence] at hLower
      generalize hHead : lowerM fn mi = headResult at hLower
      cases headResult with
      | error error =>
          change Except.error error = Except.ok statements at hLower
          contradiction
      | ok stmt =>
          generalize hTail : lowerMSequence fn rest = tailResult at hLower
          cases tailResult with
          | error error =>
              change Except.error error = Except.ok statements at hLower
              contradiction
          | ok tail =>
              change Except.ok (stmt :: tail) = Except.ok statements at hLower
              injection hLower with hStatements
              subst statements
              have hHeadWellFormed : mi.WellFormed fn :=
                hWellFormed mi (by simp)
              have hRestWellFormed : ∀ next ∈ rest, next.WellFormed fn := by
                intro next hNext
                exact hWellFormed next (by simp [hNext])
              have hStep :=
                lowerM_correct fn mi stmt s t hRel hHeadWellFormed hHead
              simp only [evalMCCSequence, evalMCSequence]
              generalize hCC : evalMCC s mi = ccResult at hStep ⊢
              generalize hC : evalMC t stmt = cResult at hStep ⊢
              cases ccResult with
              | none =>
                  cases cResult with
                  | none => trivial
                  | some tNext => contradiction
              | some sNext =>
                  cases cResult with
                  | none => contradiction
                  | some tNext =>
                      simp only [obind_some]
                      exact ih tail sNext tNext hStep hRestWellFormed hTail

end LeanCompCert.Verified.MemFragment
