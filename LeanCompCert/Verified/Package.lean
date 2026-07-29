import LeanCompCert.Verified.Reflect

/-!
# M1 — Scale-free certificate packaging

`Verified.Computation` demands `wellFormed` and `lowered` evidence, which
concrete certificates previously discharged by kernel evaluation at trace
size. This module removes that cost: for any well-formed `Reflect.Program`,
lowering success, the lowered statements, and fragment well-formedness are
established **structurally**, by classifying the finitely many instruction
shapes the compiler emits and resolving `Lower.localType?` through the
preamble's declarations.

The result is `Program.toComputation`: packaging whose proof obligations
are program-sized (`Program.WF`, decidable over the source program), never
trace-sized. Combined with `returns_iff_denote`, a certificate's total
kernel cost is evaluating its denotation once.
-/

namespace LeanCompCert.Verified.Reflect

open LeanCompCert
open LeanCompCert.Proof

/-- Operand shapes the compiler emits: bounded registers and `u64`
literals (the loop index compiles to a literal). -/
inductive SrcOp (regCount : Nat) : CCIR.Operand → Prop where
  | reg (i : Nat) (h : i < regCount) : SrcOp regCount (.local ⟨i + 1⟩)
  | lit (value : Nat) : SrcOp regCount (.uintLit .u64 value)

/-- The finitely many instruction shapes `Program.compile` emits. -/
inductive Shape (regCount : Nat) : StraightInstruction → Prop where
  | scratchInit :
      Shape regCount (.assign scratchLocal (.uintLit .u8 0))
  | assignReg (dest : Nat) (src : CCIR.Operand)
      (hSrc : SrcOp regCount src) :
      Shape regCount (.assign (regLocal dest) src)
  | binary (dest : Nat) (op : UnsignedBinary) (lhs rhs : CCIR.Operand)
      (hLhs : SrcOp regCount lhs) (hRhs : SrcOp regCount rhs) :
      Shape regCount (.binary (regLocal dest) op lhs rhs)
  | compare (cmp : UnsignedComparison) (lhs rhs : CCIR.Operand)
      (hLhs : SrcOp regCount lhs) (hRhs : SrcOp regCount rhs) :
      Shape regCount (.compare scratchLocal cmp lhs rhs)
  | cast (dest : Nat) :
      Shape regCount (.cast (regLocal dest) (.local ⟨0⟩))

theorem srcOp_compileOperand {regCount : Nat} (index : Nat)
    (operand : Operand) (hWF : operand.WF regCount) :
    SrcOp regCount (compileOperand index operand) := by
  cases operand with
  | reg i => exact .reg i hWF
  | lit value => exact .lit value
  | idx => exact .lit index

theorem shape_compileInstr {regCount : Nat} (index : Nat) (instr : Instr)
    (hWF : instr.WF regCount) :
    ∀ si ∈ compileInstr index instr, Shape regCount si := by
  cases instr with
  | mov dest src =>
      intro si hMem
      obtain ⟨hDest, hSrc⟩ := hWF
      simp only [compileInstr, List.mem_singleton] at hMem
      subst hMem
      exact .assignReg dest _ (srcOp_compileOperand index src hSrc)
  | binop dest op lhs rhs =>
      intro si hMem
      obtain ⟨hDest, hLhs, hRhs⟩ := hWF
      cases hArith : op.arithmetic? with
      | some arith =>
          rw [show compileInstr index (.binop dest op lhs rhs) =
            [.binary (regLocal dest) arith
              (compileOperand index lhs) (compileOperand index rhs)] from by
              show (match op.arithmetic?, op.comparison? with
                | some arith, _ =>
                    [StraightInstruction.binary (regLocal dest) arith
                      (compileOperand index lhs) (compileOperand index rhs)]
                | none, some comparison =>
                    [StraightInstruction.compare scratchLocal comparison
                      (compileOperand index lhs) (compileOperand index rhs),
                     StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                | none, none => []) = _
              rw [hArith]] at hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact .binary dest arith _ _
            (srcOp_compileOperand index lhs hLhs)
            (srcOp_compileOperand index rhs hRhs)
      | none =>
          cases hCmp : op.comparison? with
          | none =>
              exfalso
              cases op <;> simp [Op.arithmetic?] at hArith <;>
                simp [Op.comparison?] at hCmp
          | some cmp =>
              rw [show compileInstr index (.binop dest op lhs rhs) =
                [.compare scratchLocal cmp
                  (compileOperand index lhs) (compileOperand index rhs),
                 .cast (regLocal dest) (.local ⟨0⟩)] from by
                  show (match op.arithmetic?, op.comparison? with
                    | some arith, _ =>
                        [StraightInstruction.binary (regLocal dest) arith
                          (compileOperand index lhs)
                          (compileOperand index rhs)]
                    | none, some comparison =>
                        [StraightInstruction.compare scratchLocal comparison
                          (compileOperand index lhs)
                          (compileOperand index rhs),
                         StraightInstruction.cast (regLocal dest)
                          (.local ⟨0⟩)]
                    | none, none => []) = _
                  rw [hArith, hCmp]] at hMem
          -- membership in the two-element list
              simp only [List.mem_cons, List.not_mem_nil,
                or_false] at hMem
              cases hMem with
              | inl hCompare =>
                  subst hCompare
                  exact .compare cmp _ _
                    (srcOp_compileOperand index lhs hLhs)
                    (srcOp_compileOperand index rhs hRhs)
              | inr hCast =>
                  subst hCast
                  exact .cast dest

theorem shape_compileInstrs {regCount : Nat} (index : Nat)
    (instrs : List Instr) (hWF : ∀ instr ∈ instrs, instr.WF regCount) :
    ∀ si ∈ compileInstrs index instrs, Shape regCount si := by
  intro si hMem
  simp only [compileInstrs, List.mem_flatMap] at hMem
  obtain ⟨instr, hInstr, hSi⟩ := hMem
  exact shape_compileInstr index instr (hWF instr hInstr) si hSi

theorem shape_preamble (regCount : Nat) :
    ∀ si ∈ preamble regCount, Shape regCount si := by
  intro si hMem
  unfold preamble at hMem
  rcases List.mem_cons.mp hMem with hScratch | hTail
  · subst hScratch
    exact .scratchInit
  · simp only [List.mem_map, List.mem_range] at hTail
    obtain ⟨i, hi, hSi⟩ := hTail
    subst hSi
    exact .assignReg i _ (.lit 0)

/-- Every instruction a compiled program contains has a compiled shape. -/
theorem shape_compile (p : Program) (hWF : p.WF) :
    ∀ si ∈ p.compile, Shape p.regCount si := by
  obtain ⟨_, hInit, hBody, hEpilogue⟩ := hWF
  intro si hMem
  simp only [Program.compile, List.append_assoc, List.mem_append] at hMem
  rcases hMem with hPre | hInit' | hFold | hEpi
  · exact shape_preamble p.regCount si hPre
  · exact shape_compileInstrs 0 p.init hInit si hInit'
  · simp only [foldTrace, List.mem_flatMap, List.mem_range] at hFold
    obtain ⟨index, _, hSi⟩ := hFold
    exact shape_compileInstrs index p.body hBody si hSi
  · exact shape_compileInstrs 0 p.epilogue hEpilogue si hEpi

/-! ## Resolving `Lower.localType?` structurally -/

theorem findSome?_uniform {α β : Type _} (l : List α) (f : α → Option β)
    (v : β)
    (hUniform : ∀ x ∈ l, f x = none ∨ f x = some v)
    (hExists : ∃ x ∈ l, f x ≠ none) :
    List.findSome? f l = some v := by
  induction l with
  | nil =>
      obtain ⟨x, hx, _⟩ := hExists
      exact (List.not_mem_nil hx).elim
  | cons head tail ih =>
      show (match f head with
        | some b => some b
        | none => List.findSome? f tail) = some v
      cases hHead : f head with
      | some b =>
          rcases hUniform head (by simp) with hNone | hSome
          · rw [hHead] at hNone
            exact absurd hNone (by simp)
          · rw [hHead] at hSome
            injection hSome with hb
            rw [hb]
      | none =>
          obtain ⟨x, hx, hne⟩ := hExists
          rcases List.mem_cons.mp hx with rfl | hTail
          · exact absurd hHead hne
          · exact ih (fun y hy => hUniform y (by simp [hy]))
              ⟨x, hTail, hne⟩

def Program.toBlock (p : Program) : CCIR.Block := {
  id := ⟨0⟩
  instructions := (p.compile.map Proof.StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨p.output + 1⟩))
}

def Program.toFn (p : Program) (name : String) : CCIR.Function := {
  name := ⟨name⟩
  params := #[]
  result := .u64
  entry := ⟨0⟩
  blocks := #[p.toBlock]
  sourceDecl := some name
}

private theorem beq_ids_true (a : Nat) :
    (((⟨a⟩ : CCIR.LocalId) == ⟨a⟩)) = true := by
  show ((a == a : Bool)) = true
  simp

theorem localType?_reg (p : Program) (name : String) (hWF : p.WF)
    (i : Nat) (hi : i < p.regCount) :
    Lower.localType? (p.toFn name) ⟨i + 1⟩ = some CCIR.CCType.u64 := by
  unfold Lower.localType? Program.toFn
  simp only [List.findSome?_cons, List.findSome?_nil, List.find?_nil]
  rw [show (p.toBlock).instructions.toList =
    p.compile.map Proof.StraightInstruction.toCCIR from by
      simp [Program.toBlock]]
  rw [findSome?_uniform _ _ CCIR.CCType.u64 ?hUniform ?hExists]
  case hUniform =>
      intro instr hMem
      obtain ⟨si, hSi, rfl⟩ := List.mem_map.mp hMem
      cases shape_compile p hWF si hSi with
      | scratchInit =>
          left
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, scratchLocal]
          rw [if_neg]
          show ¬ ((0 == i + 1 : Bool) = true)
          simp
      | assignReg dest src hSrc =>
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          by_cases hEq : dest = i
          · subst hEq
            right
            rw [if_pos (beq_ids_true (dest + 1))]
          · left
            rw [if_neg]
            show ¬ ((dest + 1 == i + 1 : Bool) = true)
            simp
            omega
      | binary dest op lhs rhs hLhs hRhs =>
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          by_cases hEq : dest = i
          · subst hEq
            right
            rw [if_pos (beq_ids_true (dest + 1))]
          · left
            rw [if_neg]
            show ¬ ((dest + 1 == i + 1 : Bool) = true)
            simp
            omega
      | compare cmp lhs rhs hLhs hRhs =>
          left
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, scratchLocal]
          rw [if_neg]
          show ¬ ((0 == i + 1 : Bool) = true)
          simp
      | cast dest =>
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          by_cases hEq : dest = i
          · subst hEq
            right
            rw [if_pos (beq_ids_true (dest + 1))]
          · left
            rw [if_neg]
            show ¬ ((dest + 1 == i + 1 : Bool) = true)
            simp
            omega
  case hExists =>
      refine ⟨Proof.StraightInstruction.toCCIR
        (.assign (regLocal i) (.uintLit .u64 0)), ?_, ?_⟩
      · refine List.mem_map.mpr ⟨_, ?_, rfl⟩
        simp only [Program.compile, List.append_assoc, List.mem_append]
        refine Or.inl ?_
        unfold preamble
        exact List.mem_cons.mpr (Or.inr
          (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      · simp only [Proof.StraightInstruction.toCCIR,
          CCIR.Instruction.destination?, regLocal]
        rw [if_pos (beq_ids_true (i + 1))]
        simp

theorem localType?_scratch (p : Program) (name : String) (hWF : p.WF) :
    Lower.localType? (p.toFn name) ⟨0⟩ = some CCIR.CCType.u8 := by
  unfold Lower.localType? Program.toFn
  simp only [List.findSome?_cons, List.findSome?_nil, List.find?_nil]
  rw [show (p.toBlock).instructions.toList =
    p.compile.map Proof.StraightInstruction.toCCIR from by
      simp [Program.toBlock]]
  rw [findSome?_uniform _ _ CCIR.CCType.u8 ?hUniform ?hExists]
  case hUniform =>
      intro instr hMem
      obtain ⟨si, hSi, rfl⟩ := List.mem_map.mp hMem
      cases shape_compile p hWF si hSi with
      | scratchInit =>
          right
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, scratchLocal]
          rw [if_pos (beq_ids_true 0)]
      | assignReg dest src hSrc =>
          left
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          rw [if_neg]
          show ¬ ((dest + 1 == 0 : Bool) = true)
          simp
      | binary dest op lhs rhs hLhs hRhs =>
          left
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          rw [if_neg]
          show ¬ ((dest + 1 == 0 : Bool) = true)
          simp
      | compare cmp lhs rhs hLhs hRhs =>
          right
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, scratchLocal]
          rw [if_pos (beq_ids_true 0)]
      | cast dest =>
          left
          simp only [Proof.StraightInstruction.toCCIR,
            CCIR.Instruction.destination?, regLocal]
          rw [if_neg]
          show ¬ ((dest + 1 == 0 : Bool) = true)
          simp
  case hExists =>
      refine ⟨Proof.StraightInstruction.toCCIR
        (.assign scratchLocal (.uintLit .u8 0)), ?_, ?_⟩
      · refine List.mem_map.mpr ⟨_, ?_, rfl⟩
        simp only [Program.compile, List.append_assoc, List.mem_append]
        refine Or.inl ?_
        unfold preamble
        exact List.mem_cons.mpr (Or.inl rfl)
      · simp only [Proof.StraightInstruction.toCCIR,
          CCIR.Instruction.destination?, scratchLocal]
        rw [if_pos (beq_ids_true 0)]
        simp

/-! ## Structural lowering and well-formedness -/

/-- The C expression each compiled operand lowers to. -/
def srcExpr : CCIR.Operand → C.CExpr
  | .local id => .var (ABI.localName id.value) .u64
  | .uintLit t v => .uintLit (Lower.lowerType t) v
  | _ => .null .void

private theorem lowerOperand_srcOp (p : Program) (name : String)
    (hWF : p.WF) {operand : CCIR.Operand}
    (hSrc : SrcOp p.regCount operand) :
    Lower.lowerOperand (p.toFn name) operand = .ok (srcExpr operand) := by
  cases hSrc with
  | reg i hi =>
      simp only [Lower.lowerOperand]
      rw [localType?_reg p name hWF i hi]
      rfl
  | lit value => rfl

private theorem srcExpr_unsigned {regCount : Nat} {operand : CCIR.Operand}
    (hSrc : SrcOp regCount operand) :
    (srcExpr operand).type.isSigned = false := by
  cases hSrc <;> rfl

/-- The C statement each compiled instruction lowers to. -/
def compiledStmt : StraightInstruction → C.CStmt
  | .assign dest src => .assign (Lower.localExpr dest) (srcExpr src)
  | .binary dest op lhs rhs =>
      .assign (Lower.localExpr dest)
        (.binary (Lower.lowerType dest.type) op.c
          (srcExpr lhs) (srcExpr rhs))
  | .compare dest cmp lhs rhs =>
      .assign (Lower.localExpr dest)
        (.binary (Lower.lowerType dest.type) cmp.c
          (srcExpr lhs) (srcExpr rhs))
  | .cast dest _ =>
      .assign (Lower.localExpr dest)
        (.cast (Lower.lowerType dest.type) (.var (ABI.localName 0) .u8))

private theorem lowerStraight_shape (p : Program) (name : String)
    (hWF : p.WF) {si : StraightInstruction}
    (hShape : Shape p.regCount si) :
    lowerStraight (p.toFn name) si = .ok (compiledStmt si) := by
  cases hShape with
  | scratchInit => rfl
  | assignReg dest src hSrc =>
      simp only [lowerStraight]
      rw [lowerOperand_srcOp p name hWF hSrc]
      rfl
  | binary dest op lhs rhs hLhs hRhs =>
      simp only [lowerStraight]
      rw [lowerBinary_unsigned (p.toFn name) (regLocal dest) op lhs rhs rfl]
      rw [lowerOperand_srcOp p name hWF hLhs,
        lowerOperand_srcOp p name hWF hRhs]
      rfl
  | compare cmp lhs rhs hLhs hRhs =>
      simp only [lowerStraight]
      rw [lowerBinary_comparison (p.toFn name) scratchLocal cmp lhs rhs
        (srcExpr lhs) (srcExpr rhs)
        (lowerOperand_srcOp p name hWF hLhs)
        (lowerOperand_srcOp p name hWF hRhs)
        (srcExpr_unsigned hLhs) (srcExpr_unsigned hRhs)]
      rfl
  | cast dest =>
      simp only [lowerStraight]
      rw [lowerUnary_cast (p.toFn name) (regLocal dest) (.local ⟨0⟩)
        (.var (ABI.localName 0) .u8)
        (by
          simp only [Lower.lowerOperand]
          rw [localType?_scratch p name hWF]
          rfl)]
      rfl

private theorem lowerSequence_of_pointwise (fn : CCIR.Function) :
    ∀ (l : List StraightInstruction),
      (∀ si ∈ l, lowerStraight fn si = .ok (compiledStmt si)) →
      lowerSequence fn l = .ok (l.map compiledStmt) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons si rest ih =>
      intro h
      show (do
        let stmt ← lowerStraight fn si
        let statements ← lowerSequence fn rest
        pure (stmt :: statements)) = _
      rw [h si (by simp), ih (fun x hx => h x (by simp [hx]))]
      rfl

/-- **M1, lowering half**: a compiled program always lowers, to exactly
the mapped statements — structurally, with no evaluation. -/
theorem compile_lowered (p : Program) (name : String) (hWF : p.WF) :
    lowerSequence (p.toFn name) p.compile =
      .ok (p.compile.map compiledStmt) :=
  lowerSequence_of_pointwise (p.toFn name) p.compile
    (fun si hSi => lowerStraight_shape p name hWF (shape_compile p hWF si hSi))

/-- **M1, well-formedness half**: every compiled instruction is in the
proved fragment's well-formed subset — structurally. -/
theorem compile_wellFormed (p : Program) (name : String) (hWF : p.WF) :
    ∀ si ∈ p.compile, si.WellFormed (p.toFn name) := by
  intro si hSi
  cases shape_compile p hWF si hSi with
  | scratchInit => trivial
  | assignReg dest src hSrc => trivial
  | binary dest op lhs rhs hLhs hRhs => exact rfl
  | compare cmp lhs rhs hLhs hRhs =>
      refine ⟨?_, ?_⟩
      · unfold operandLowersUnsigned
        rw [lowerOperand_srcOp p name hWF hLhs]
        simp [srcExpr_unsigned hLhs]
      · unfold operandLowersUnsigned
        rw [lowerOperand_srcOp p name hWF hRhs]
        simp [srcExpr_unsigned hRhs]
  | cast dest => trivial

/--
**M1 — scale-free packaging**: a `Computation` from any well-formed
program, with every field structural. The only decidable obligation is
`Program.WF` — program-sized, never trace-sized.
-/
def Program.toComputation (p : Program) (name : String) (hWF : p.WF) :
    Verified.Computation := {
  fn := p.toFn name
  block := p.toBlock
  instructions := p.compile
  statements := p.compile.map compiledStmt
  output := ⟨p.output + 1⟩
  wellFormed := compile_wellFormed p name hWF
  lowered := compile_lowered p name hWF
}

/-- Acceptance reduces to the denotation, with packaging and bridge both
structural: the certificate's entire kernel cost is one fold evaluation. -/
theorem toComputation_returns (p : Program) (name : String) (hWF : p.WF)
    (n : Nat) :
    (p.toComputation name hWF).Returns ((n : Nat) : Int) ↔
      p.denote = some n :=
  returns_iff_denote p hWF (p.toComputation name hWF) rfl rfl n

end LeanCompCert.Verified.Reflect

