import LeanCompCert.Ports.Prop1224Cell

/-!
# Compiled smallest-prime-factor table for Proposition 12.2.4

The production cell checker receives `q` at runtime.  Rather than asking Lean
to factor every retained `q`, or executing a long Euclidean loop for every
pair `(q,r)`, this program constructs the smallest prime factor of every
`1 ≤ r ≤ rowCount` once.  The later checker divides a squarefree `r` through
this table and performs one runtime `q % p` test per distinct factor.

The marking cursor visits the literal prime table in increasing order.  A
cell is written only while it is zero, so the retained value is the first
(hence smallest) prime divisor.  Unmarked cells are finalized to themselves;
the special cell `r = 1` is finalized to `1`.  Mark-budget exhaustion is a
reported violation and every inactive store is redirected to a sink.
-/

namespace LeanCompCert.Ports.Prop1224SPFTable

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
  (operandWFB instrWFB ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.Prop1224Cell (markTable)

structure Cfg where
  lo : Nat
  segLen : Nat
  segCount : Nat
  markSteps : Nat
  table : List Nat
  destBase : Nat
  arrayLen : Nat
  deriving Repr

def Cfg.hi (c : Cfg) : Nat := c.lo + c.segLen * c.segCount - 1
def Cfg.tableLen (c : Cfg) : Nat := c.table.length
def Cfg.sink (c : Cfg) : Nat := c.segLen
def Cfg.tableBase (c : Cfg) : Nat := 2 * c.segLen + 1
def Cfg.resultCell (c : Cfg) : Nat := c.destBase + c.hi + 1
def Cfg.period (c : Cfg) : Nat := c.markSteps + c.segLen
def Cfg.q0 (c : Cfg) : Nat := c.table.headD 2

def rPi : Nat := 0
def rP : Nat := 1
def rJ : Nat := 2
def rR : Nat := 3
def rW : Nat := 4
def rOne : Nat := 5
def rZero : Nat := 6
def rViol : Nat := 7
def regCount : Nat := 96

def Cfg.tableCells (c : Cfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [(c.tableBase + c.tableLen, 1)]

def Cfg.seedList (c : Cfg) : List (Nat × Nat) :=
  [(rW, c.lo), (rOne, 1), (rZero, 0), (rP, c.q0)]

def Cfg.init (c : Cfg) : List AInstr :=
  storeLits c.tableCells ++ seedRegs c.seedList

def Cfg.body (c : Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let SNK := c.sink
  let q0 := c.q0
  [ -- phases and window-start cursor reset
    .scalar (.binop 10 .lt (.reg rR) (.lit T))
  , .scalar (.binop 11 .lt (.reg rR) (.lit (T + L)))
  , .scalar (.binop 12 .sub (.reg 11) (.reg 10))
  , .scalar (.binop 13 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 14 .sub (.lit 1) (.reg 13))
  , .scalar (.binop rPi .mul (.reg 14) (.reg rPi))
  , .scalar (.binop 15 .mul (.reg 13) (.lit q0))
  , .scalar (.binop 16 .mul (.reg 14) (.reg rP))
  , .scalar (.binop rP .add (.reg 15) (.reg 16))
  , .scalar (.binop 17 .urem (.reg rW) (.lit q0))
  , .scalar (.binop 18 .sub (.lit q0) (.reg 17))
  , .scalar (.binop 19 .urem (.reg 18) (.lit q0))
  , .scalar (.binop 20 .mul (.reg 13) (.reg 19))
  , .scalar (.binop 21 .mul (.reg 14) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 20) (.reg 21))
    -- first-write-wins SPF mark, or the sink
  , .scalar (.binop 22 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 23 .mul (.reg 22) (.reg 10))
  , .scalar (.binop 24 .sub (.lit 1) (.reg 23))
  , .scalar (.binop 25 .mul (.reg 23) (.reg rJ))
  , .scalar (.binop 26 .mul (.reg 24) (.lit SNK))
  , .scalar (.binop 27 .add (.reg 25) (.reg 26))
  , .load 28 27
  , .scalar (.binop 29 .eq (.reg 28) (.lit 0))
  , .scalar (.binop 30 .mul (.reg 29) (.reg rP))
  , .scalar (.binop 31 .sub (.lit 1) (.reg 29))
  , .scalar (.binop 32 .mul (.reg 31) (.reg 28))
  , .scalar (.binop 33 .add (.reg 30) (.reg 32))
  , .store 27 33
    -- advance inside this prime or move to the next prime
  , .scalar (.binop 34 .mul (.reg 10) (.reg 24))
  , .scalar (.binop 35 .add (.reg rPi) (.reg 34))
  , .scalar (.binop 36 .gt (.reg 35) (.lit K))
  , .scalar (.binop 37 .sub (.lit 1) (.reg 36))
  , .scalar (.binop 38 .mul (.reg 37) (.reg 35))
  , .scalar (.binop 39 .mul (.reg 36) (.lit K))
  , .scalar (.binop rPi .add (.reg 38) (.reg 39))
  , .scalar (.binop 40 .add (.reg rPi) (.lit c.tableBase))
  , .load 41 40
  , .scalar (.binop 42 .sub (.lit 1) (.reg 34))
  , .scalar (.binop 43 .mul (.reg 34) (.reg 41))
  , .scalar (.binop 44 .mul (.reg 42) (.reg rP))
  , .scalar (.binop rP .add (.reg 43) (.reg 44))
  , .scalar (.binop 45 .urem (.reg rW) (.reg 41))
  , .scalar (.binop 46 .sub (.reg 41) (.reg 45))
  , .scalar (.binop 47 .urem (.reg 46) (.reg 41))
  , .scalar (.binop 48 .eq (.reg rPi) (.lit K))
  , .scalar (.binop 49 .sub (.lit 1) (.reg 48))
  , .scalar (.binop 50 .mul (.reg 48) (.lit (L + 1)))
  , .scalar (.binop 51 .mul (.reg 49) (.reg 47))
  , .scalar (.binop 52 .add (.reg 50) (.reg 51))
  , .scalar (.binop 53 .add (.reg rJ) (.reg rP))
  , .scalar (.binop 54 .mul (.reg 34) (.reg 52))
  , .scalar (.binop 55 .mul (.reg 42) (.reg 53))
  , .scalar (.binop rJ .add (.reg 54) (.reg 55))
    -- reject a truncated marking phase
  , .scalar (.binop 56 .eq (.reg rR) (.lit (T - 1)))
  , .scalar (.binop 57 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 58 .mul (.reg 56) (.reg 57))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 58))
    -- finalize and publish one SPF cell
  , .scalar (.binop 60 .sub (.reg rR) (.lit T))
  , .scalar (.binop 61 .mul (.reg 12) (.reg 60))
  , .scalar (.binop 62 .add (.reg rW) (.reg 61))
  , .scalar (.binop 63 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 64 .mul (.reg 63) (.lit SNK))
  , .scalar (.binop 65 .add (.reg 61) (.reg 64))
  , .load 66 65
  , .scalar (.binop 67 .eq (.reg 66) (.lit 0))
  , .scalar (.binop 68 .mul (.reg 67) (.reg 62))
  , .scalar (.binop 69 .sub (.lit 1) (.reg 67))
  , .scalar (.binop 70 .mul (.reg 69) (.reg 66))
  , .scalar (.binop 71 .add (.reg 68) (.reg 70))
  , .scalar (.binop 72 .eq (.reg 62) (.lit 1))
  , .scalar (.binop 73 .mul (.reg 72) (.lit 1))
  , .scalar (.binop 74 .sub (.lit 1) (.reg 72))
  , .scalar (.binop 75 .mul (.reg 74) (.reg 71))
  , .scalar (.binop 76 .add (.reg 73) (.reg 75))
  , .scalar (.binop 77 .add (.reg 62) (.lit c.destBase))
  , .scalar (.binop 78 .mul (.reg 12) (.reg 77))
  , .scalar (.binop 79 .mul (.reg 63) (.lit SNK))
  , .scalar (.binop 80 .add (.reg 78) (.reg 79))
  , .store 80 76
  , .store 65 rZero
    -- period/window cursor
  , .scalar (.binop 81 .add (.reg rR) (.lit 1))
  , .scalar (.binop 82 .eq (.reg 81) (.lit (T + L)))
  , .scalar (.binop 83 .sub (.lit 1) (.reg 82))
  , .scalar (.binop rR .mul (.reg 83) (.reg 81))
  , .scalar (.binop 84 .mul (.reg 82) (.lit L))
  , .scalar (.binop rW .add (.reg rW) (.reg 84)) ]

def Cfg.epilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov 90 (.lit c.resultCell)), .store 90 rViol ]

def prefixLoopCount (c : Cfg) (rows : Nat) : Nat :=
  let full := rows / c.segLen
  let tail := rows % c.segLen
  full * c.period + if tail = 0 then 0 else c.markSteps + tail

def program (c : Cfg) (rows : Nat) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := prefixLoopCount c rows
  init := c.init
  body := c.body
  epilogue := c.epilogue
  output := rViol
}

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem tableCells_all (c : Cfg) :
    (storeLits c.tableCells).all (ainstrWFB regCount) = true :=
  storeLits_all _

theorem seedList_ok (c : Cfg) :
    ∀ x ∈ c.seedList, x.1 < regCount := by
  intro x hx
  have hall : c.seedList.all (fun y => decide (y.1 < regCount)) = true := by
    rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem seedRegs_all (l : List (Nat × Nat))
    (h : ∀ x ∈ l, x.1 < regCount) :
    (seedRegs l).all (ainstrWFB regCount) = true := by
  simp only [seedRegs, List.all_map]
  refine List.all_eq_true.mpr (fun x hx => ?_)
  have hlt := h x hx
  simp only [Function.comp_apply, ainstrWFB, instrWFB, operandWFB,
    Bool.and_true, decide_eq_true_eq]
  exact hlt

theorem init_all (c : Cfg) : c.init.all (ainstrWFB regCount) = true :=
  all_append (tableCells_all c)
    (seedRegs_all _ (seedList_ok c))

set_option maxRecDepth 100000 in
theorem body_all (c : Cfg) : c.body.all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, markSteps, table, destBase, arrayLen⟩ := c
  rfl

theorem epilogue_all (c : Cfg) : c.epilogue.all (ainstrWFB regCount) = true := by
  rfl

theorem program_wf (c : Cfg) (rows : Nat) : (program c rows).WF :=
  ⟨show rViol < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : Cfg) (rows : Nat) (base : Int)
    (hBase : BaseOk (program c rows).arrayLen base)
    (n : Nat) (hDenote : (program c rows).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c rows).initialMCC base) (program c rows).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c rows).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c rows) base hBase n hDenote

/-- Sufficient marking budget for the emitted ascending prime table.  The
extra three iterations per prime cover the first offset and cursor advance. -/
def markBudget (root len : Nat) : Nat :=
  16 + (Prop1224Cell.markTable (root * root)).foldl
    (fun acc p => acc + len / p + 3) 0

def Cfg.production (rows segLen destBase arrayLen : Nat) : Cfg :=
  let hi := rows
  let table := markTable hi
  { lo := 1
    segLen := segLen
    segCount := (rows + segLen - 1) / segLen
    markSteps := 16 + table.foldl (fun acc p => acc + segLen / p + 3) 0
    table := table
    destBase := destBase
    arrayLen := arrayLen }

#print axioms program_compiled

end LeanCompCert.Ports.Prop1224SPFTable
