import LeanCompCert.Ports.A7BoundaryRow
import LeanCompCert.Ports.ArraySegSieve

/-!
# Complete emitted checker shape for the CH25 Lemma A.7 transcript

Each retained row is embedded as literal post-parser data.  The generated C
program executes the row predicates and the gap-free edge cursor at runtime;
no Boolean result is precomputed during Lean elaboration.  The body is
unrolled once so there is no large runtime input array or unverified parser.
-/

namespace LeanCompCert.Ports.A7BoundaryProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.A7BoundaryRow
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB forall_wf_of_all)

def gridDepth : Nat := 17
def gridScale : Nat := 2 ^ gridDepth
def rowCountLimit : Nat := 2000000

/-- Exact post-base64 representation used by the compiled checker.  Negative
dyadic exponents are stored as their positive denominator shifts. -/
structure EncodedRow where
  edge : Nat
  depth : Nat
  index : Nat
  norm0 : Nat
  norm1 : Nat
  norm2 : Nat
  normShift : Nat
  zeta0 : Nat
  zeta1 : Nat
  zeta2 : Nat
  zetaShift : Nat
  deriving Repr, DecidableEq

def EncodedRow.norm (r : EncodedRow) : Limbs4 :=
  { l0 := r.norm0, l1 := r.norm1, l2 := r.norm2, l3 := 0 }

def EncodedRow.zeta (r : EncodedRow) : Limbs4 :=
  { l0 := r.zeta0, l1 := r.zeta1, l2 := r.zeta2, l3 := 0 }

/-- Least natural threshold `t` with
`62500 * m < 121801 * 2^shift` iff `m < t`. -/
def targetLimit (shift : Nat) : Nat :=
  (121801 * 2 ^ shift - 1) / 62500 + 1

def limbs4 (n : Nat) : Limbs4 :=
  { l0 := n % M
    l1 := n / M % M
    l2 := n / M / M % M
    l3 := n / M / M / M % M }

def EncodedRow.limit (r : EncodedRow) : Limbs4 :=
  limbs4 (targetLimit r.normShift)

def EncodedRow.startGrid (r : EncodedRow) : Nat :=
  r.index * 2 ^ (gridDepth - r.depth)

def EncodedRow.finishGrid (r : EncodedRow) : Nat :=
  (r.index + 1) * 2 ^ (gridDepth - r.depth)

/-- Source-shaped finite predicate checked for one row after a prior edge and
dyadic cursor.  The narrow shift ranges are stronger than the parser's broad
`[-16384,16384]` guards and contain every retained production row. -/
def EncodedRow.ValidAfter (r : EncodedRow)
    (currentEdge cursor : Nat) : Prop :=
  r.edge < 4 ∧
    r.depth ≤ gridDepth ∧
    r.index < 2 ^ r.depth ∧
    0 < r.norm.val ∧
    r.norm.val < r.limit.val ∧
    178 ≤ r.normShift ∧ r.normShift ≤ 196 ∧
    0 < r.zeta.val ∧
    182 ≤ r.zetaShift ∧ r.zetaShift ≤ 198 ∧
    r.startGrid < r.finishGrid ∧ r.finishGrid ≤ gridScale ∧
    ((r.edge = currentEdge ∧ r.startGrid = cursor) ∨
      (r.edge = currentEdge + 1 ∧ cursor = gridScale ∧
        r.startGrid = 0))

instance (r : EncodedRow) (edge cursor : Nat) :
    Decidable (r.ValidAfter edge cursor) := by
  unfold EncodedRow.ValidAfter
  infer_instance

def rCurrentEdge : Nat := 12
def rCursor : Nat := 13
def rViol : Nat := 14
def rOK : Nat := 15
def rFlag : Nat := 16
def rA : Nat := 17
def rB : Nat := 18
def rC : Nat := 19
def rD : Nat := 20
def regCount : Nat := 32

def comparePrelude (r : EncodedRow) : List AInstr :=
  [ .scalar (.mov rX0 (.lit r.norm0))
  , .scalar (.mov rX1 (.lit r.norm1))
  , .scalar (.mov rX2 (.lit r.norm2))
  , .scalar (.mov 11 (.lit 0))
  , .scalar (.mov rY0 (.lit r.limit.l0))
  , .scalar (.mov rY1 (.lit r.limit.l1))
  , .scalar (.mov rY2 (.lit r.limit.l2))
  , .scalar (.mov rY3 (.lit r.limit.l3)) ]

def gate (op : Op) (lhs rhs : Operand) : List AInstr :=
  [ .scalar (.binop rFlag op lhs rhs)
  , .scalar (.binop rOK .mul (.reg rOK) (.reg rFlag)) ]

/-- All non-wide row predicates plus the consecutive-edge state update. -/
def guardBody (r : EncodedRow) : List AInstr :=
  [ .scalar (.mov rOK (.reg rBorrow)) ] ++
  gate .lt (.lit r.edge) (.lit 4) ++
  gate .le (.lit r.depth) (.lit gridDepth) ++
  gate .lt (.lit r.index) (.lit (2 ^ r.depth)) ++
  [ .scalar (.binop rA .ne (.lit r.norm0) (.lit 0))
  , .scalar (.binop rB .ne (.lit r.norm1) (.lit 0))
  , .scalar (.binop rC .ne (.lit r.norm2) (.lit 0))
  , .scalar (.binop rA .bor (.reg rA) (.reg rB))
  , .scalar (.binop rA .bor (.reg rA) (.reg rC)) ] ++
  gate .eq (.reg rA) (.lit 1) ++
  gate .le (.lit 178) (.lit r.normShift) ++
  gate .le (.lit r.normShift) (.lit 196) ++
  [ .scalar (.binop rA .ne (.lit r.zeta0) (.lit 0))
  , .scalar (.binop rB .ne (.lit r.zeta1) (.lit 0))
  , .scalar (.binop rC .ne (.lit r.zeta2) (.lit 0))
  , .scalar (.binop rA .bor (.reg rA) (.reg rB))
  , .scalar (.binop rA .bor (.reg rA) (.reg rC)) ] ++
  gate .eq (.reg rA) (.lit 1) ++
  gate .le (.lit 182) (.lit r.zetaShift) ++
  gate .le (.lit r.zetaShift) (.lit 198) ++
  gate .lt (.lit r.startGrid) (.lit r.finishGrid) ++
  gate .le (.lit r.finishGrid) (.lit gridScale) ++
  [ -- same-edge branch
    .scalar (.binop rA .eq (.lit r.edge) (.reg rCurrentEdge))
  , .scalar (.binop rB .eq (.lit r.startGrid) (.reg rCursor))
  , .scalar (.binop rA .mul (.reg rA) (.reg rB))
    -- exact next-edge branch
  , .scalar (.binop rB .add (.reg rCurrentEdge) (.lit 1))
  , .scalar (.binop rB .eq (.lit r.edge) (.reg rB))
  , .scalar (.binop rC .eq (.reg rCursor) (.lit gridScale))
  , .scalar (.binop rD .eq (.lit r.startGrid) (.lit 0))
  , .scalar (.binop rB .mul (.reg rB) (.reg rC))
  , .scalar (.binop rB .mul (.reg rB) (.reg rD))
  , .scalar (.binop rA .bor (.reg rA) (.reg rB))
  , .scalar (.binop rOK .mul (.reg rOK) (.reg rA))
    -- accumulate one failure bit and advance the literal cursor
  , .scalar (.binop rA .sub (.lit 1) (.reg rOK))
  , .scalar (.binop rViol .add (.reg rViol) (.reg rA))
  , .scalar (.mov rCurrentEdge (.lit r.edge))
  , .scalar (.mov rCursor (.lit r.finishGrid)) ]

def rowBody (r : EncodedRow) : List AInstr :=
  comparePrelude r ++ compareBody ++ guardBody r

def sweepBody (rows : List EncodedRow) : List AInstr :=
  rows.flatMap rowBody

def epilogueAt (finalEdge finalCursor : Nat) : List AInstr :=
  [ .scalar (.binop rA .ne (.reg rCurrentEdge) (.lit finalEdge))
  , .scalar (.binop rViol .add (.reg rViol) (.reg rA))
  , .scalar (.binop rA .ne (.reg rCursor) (.lit finalCursor))
  , .scalar (.binop rViol .add (.reg rViol) (.reg rA)) ]

/-- A transcript fragment with explicit source-state boundaries.  This is the
production form used for bounded-memory CompCert shards. -/
def programFrom (rows : List EncodedRow)
    (initialEdge initialCursor finalEdge finalCursor : Nat) : AProgram := {
  regCount := regCount
  arrayLen := 1
  loopCount := 1
  init :=
    [ .scalar (.mov rCurrentEdge (.lit initialEdge))
    , .scalar (.mov rCursor (.lit initialCursor))
    , .scalar (.mov rViol (.lit 0)) ]
  body := sweepBody rows
  epilogue := epilogueAt finalEdge finalCursor
  output := rViol
}

def program (rows : List EncodedRow) : AProgram :=
  programFrom rows 0 0 3 gridScale

theorem comparePrelude_all (r : EncodedRow) :
    (comparePrelude r).all (ainstrWFB regCount) = true := by rfl

theorem compareBody_all :
    compareBody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 100000 in
theorem guardBody_all (r : EncodedRow) :
    (guardBody r).all (ainstrWFB regCount) = true := by rfl

theorem rowBody_all (r : EncodedRow) :
    (rowBody r).all (ainstrWFB regCount) = true := by
  simp [rowBody, comparePrelude_all, compareBody_all, guardBody_all]

theorem sweepBody_all (rows : List EncodedRow) :
    (sweepBody rows).all (ainstrWFB regCount) = true := by
  simp [sweepBody, List.all_flatMap, rowBody_all]

theorem epilogueAt_all (finalEdge finalCursor : Nat) :
    (epilogueAt finalEdge finalCursor).all (ainstrWFB regCount) = true := by rfl

theorem programFrom_wf (rows : List EncodedRow)
    (initialEdge initialCursor finalEdge finalCursor : Nat) :
    (programFrom rows initialEdge initialCursor finalEdge finalCursor).WF :=
  ⟨show rViol < regCount by decide,
   forall_wf_of_all (by rfl),
   forall_wf_of_all (sweepBody_all rows),
   forall_wf_of_all (epilogueAt_all finalEdge finalCursor)⟩

theorem program_wf (rows : List EncodedRow) : (program rows).WF :=
  programFrom_wf rows 0 0 3 gridScale

theorem programFrom_compiled (rows : List EncodedRow)
    (initialEdge initialCursor finalEdge finalCursor : Nat) (base : Int)
    (hBase : BaseOk
      (programFrom rows initialEdge initialCursor finalEdge finalCursor).arrayLen base)
    (n : Nat)
    (hDenote :
      (programFrom rows initialEdge initialCursor finalEdge finalCursor).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((programFrom rows initialEdge initialCursor finalEdge finalCursor).initialMCC base)
          (programFrom rows initialEdge initialCursor finalEdge finalCursor).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(programFrom rows initialEdge initialCursor finalEdge finalCursor).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _
    (programFrom_wf rows initialEdge initialCursor finalEdge finalCursor)
    base hBase n hDenote

theorem program_compiled (rows : List EncodedRow) (base : Int)
    (hBase : BaseOk (program rows).arrayLen base)
    (n : Nat) (hDenote : (program rows).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program rows).initialMCC base) (program rows).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program rows).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf rows) base hBase n hDenote

#print axioms program_compiled

end LeanCompCert.Ports.A7BoundaryProgram
