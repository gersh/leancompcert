import LeanCompCert.Ports.RamareCombined100MShapeSieve
import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.RegFrame

/-!
# Log-ladder carry on the segmented Ramaré sweep

This is the first candidate-arithmetic layer above the segmented shape sieve.
For every classified candidate `n` it evaluates the exact word-safe RS62
increments `incLWord n` and `incUWord n`, then advances the two carried
fixed-point logarithms.  The arithmetic is the same instruction sequence used
and proved in `RS62LadderProgram`; here it is scheduled once per segmented
candidate, without the obsolete trial-division rounds.

The phase gate affects only the commit.  The divisions also execute during
the mark phase, as required by the data-independent array fragment, but their
denominators are the positive window base there.  Production begins at
`10001`, so every division is defined.
-/

namespace LeanCompCert.Ports.RamareCombined100M.LogSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RS62 (fpD incLWord incUWord)

abbrev ShapeCfg := LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg
abbrev shapeOutputReg : Nat :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.outputReg
abbrev shapeSmokeCfg : ShapeCfg :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.smokeCfg

structure Seed where
  logL : Nat
  logU : Nat
  deriving Repr, DecidableEq

def rLogL : Nat := 180
def rLogU : Nat := 181
def rIL : Nat := 182
def rIU : Nat := 183
def rA : Nat := 184
def rB : Nat := 185
def rC : Nat := 186
def regCount : Nat := 200

/-- The nine physical instructions computing `incLWord n`. -/
def lowerScalarBody : List Instr :=
  [ .binop rA .mul (.reg 132) (.lit 2)
  , .binop rA .add (.reg rA) (.lit (3 * fpD))
  , .binop rB .udiv (.lit (fpD - 1)) (.reg 132)
  , .binop rA .add (.reg rA) (.reg rB)
  , .binop rB .mul (.reg 132) (.lit 2)
  , .binop rA .udiv (.reg rA) (.reg rB)
  , .binop rA .sub (.lit fpD) (.reg rA)
  , .binop rB .sub (.reg 132) (.lit 1)
  , .binop rIL .udiv (.reg rA) (.reg rB) ]

/-- The thirteen physical instructions computing `incUWord n`. -/
def upperScalarBody : List Instr :=
  [ .binop rA .mul (.reg 132) (.lit 2)
  , .binop rA .add (.reg rA) (.lit (3 * fpD))
  , .binop rB .add (.reg 132) (.lit (3 * fpD))
  , .binop rB .sub (.reg rB) (.lit 1)
  , .binop rB .udiv (.reg rB) (.reg 132)
  , .binop rA .sub (.reg rA) (.reg rB)
  , .binop rB .mul (.reg 132) (.lit 2)
  , .binop rA .udiv (.reg rA) (.reg rB)
  , .binop rB .add (.reg 132) (.lit fpD)
  , .binop rB .sub (.reg rB) (.lit 1)
  , .binop rA .sub (.reg rB) (.reg rA)
  , .binop rB .sub (.reg 132) (.lit 1)
  , .binop rIU .udiv (.reg rA) (.reg rB) ]

/-- The four-instruction phase-gated log commit. -/
def commitScalarBody : List Instr :=
  [ .binop rA .mul (.reg 11) (.reg rIL)
  , .binop rLogL .add (.reg rLogL) (.reg rA)
  , .binop rB .mul (.reg 11) (.reg rIU)
  , .binop rLogU .add (.reg rLogU) (.reg rB) ]

/-- `incLWord n` and `incUWord n`, followed by a phase-gated commit.  Register
`132` is the candidate retained by `Shape.classBody`; register `11` is its
classification-phase gate. -/
def candidateBody : List AInstr :=
  lift lowerScalarBody ++ lift upperScalarBody ++ lift commitScalarBody

private theorem wordSub_eq_sub {x y : Nat} (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hrew : x + (M - y) = M + (x - y) := by omega
  rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le x y) hx

private theorem lowerCorrection_le (n : Nat) (hn : 2 ≤ n) :
    (n * 2 + 3 * fpD + (fpD - 1) / n) / (n * 2) ≤ fpD := by
  have hraw :
      (n + n + 3 * fpD + (fpD - 1) / n) / (n + n) ≤ fpD := by
    refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
    have h1 : (fpD - 1) / n ≤ fpD - 1 := Nat.div_le_self _ _
    have hf4 : 4 * fpD ≤ (n + n) * fpD :=
      Nat.mul_le_mul_right fpD (by omega)
    have hmul : (n + n) * (fpD + 1) =
        (n + n) * fpD + (n + n) := by rw [Nat.mul_add, Nat.mul_one]
    have hmul' : (fpD + 1) * (n + n) =
        (n + n) * fpD + (n + n) := by
      rw [Nat.mul_comm (fpD + 1) (n + n)]
      exact hmul
    have hmul'' : (n + n) * Nat.succ fpD =
        (n + n) * fpD + (n + n) := Nat.mul_succ _ _
    have hpos : 0 < fpD := by decide
    omega
  simpa [Nat.mul_two] using hraw

private theorem lowerShape (n : Nat) :
    (fpD - (n * 2 + 3 * fpD + (fpD - 1) / n) / (n * 2)) /
        (n - 1) = incLWord n := by
  unfold incLWord
  rw [show n * 2 + 3 * fpD = 3 * fpD + 2 * n by omega,
    show n * 2 = 2 * n by omega]

def init (c : ShapeCfg) (s : Seed) : List AInstr :=
  c.init ++ seedRegs [(rLogL, s.logL), (rLogU, s.logU)]

def body (c : ShapeCfg) : List AInstr := c.body ++ candidateBody

def epilogue (c : ShapeCfg) : List AInstr :=
  c.epilogue ++
  [ .scalar (.mov 20 (.lit (c.resultBase + 4))), .store 20 rLogL
  , .scalar (.mov 20 (.lit (c.resultBase + 5))), .store 20 rLogU ]

def program (c : ShapeCfg) (s : Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen + 2
  loopCount := c.period * c.segCount
  init := init c s
  body := body c
  epilogue := epilogue c
  output := shapeOutputReg
}

/-! ## Verified compiler package -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

set_option maxRecDepth 40000 in
theorem init_all (c : ShapeCfg) (s : Seed) :
    (init c s).all (ainstrWFB regCount) = true := by
  unfold init LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg.init
  simp only [List.all_append, storeLits_all]
  rfl

set_option maxRecDepth 40000 in
theorem body_all (c : ShapeCfg) :
    (body c).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem epilogue_all (c : ShapeCfg) :
    (epilogue c).all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : ShapeCfg) (s : Seed) : (program c s).WF :=
  ⟨show shapeOutputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : ShapeCfg) (s : Seed) (base : Int)
    (hBase : BaseOk (program c s).arrayLen base)
    (n : Nat) (hDenote : (program c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c s).initialMCC base) (program c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c s) base hBase n hDenote

/-! ## Kernel controls -/

def smokeSeed : Seed := ⟨100, 200⟩
def smokeProbe (out : Nat) : AProgram :=
  { program shapeSmokeCfg smokeSeed with output := out }

def expectedL : Nat :=
  (List.range 20).foldl (fun a i => a + incLWord (11 + i)) smokeSeed.logL

def expectedU : Nat :=
  (List.range 20).foldl (fun a i => a + incUWord (11 + i)) smokeSeed.logU

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (program shapeSmokeCfg smokeSeed).denote = some 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (smokeProbe rLogL).denote = some expectedL := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (smokeProbe rLogU).denote = some expectedU := by decide

end LeanCompCert.Ports.RamareCombined100M.LogSweep
