import LeanCompCert.Ports.RamareCombined100MShapeSieve
import LeanCompCert.Ports.RS62Increments

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

/-- `incLWord n` and `incUWord n`, followed by a phase-gated commit.  Register
`132` is the candidate retained by `Shape.classBody`; register `11` is its
classification-phase gate. -/
def candidateBody : List AInstr :=
  [ -- lower increment
    .scalar (.binop rA .mul (.reg 132) (.lit 2))
  , .scalar (.binop rA .add (.reg rA) (.lit (3 * fpD)))
  , .scalar (.binop rB .udiv (.lit (fpD - 1)) (.reg 132))
  , .scalar (.binop rA .add (.reg rA) (.reg rB))
  , .scalar (.binop rB .mul (.reg 132) (.lit 2))
  , .scalar (.binop rA .udiv (.reg rA) (.reg rB))
  , .scalar (.binop rA .sub (.lit fpD) (.reg rA))
  , .scalar (.binop rB .sub (.reg 132) (.lit 1))
  , .scalar (.binop rIL .udiv (.reg rA) (.reg rB))
    -- upper increment
  , .scalar (.binop rA .mul (.reg 132) (.lit 2))
  , .scalar (.binop rA .add (.reg rA) (.lit (3 * fpD)))
  , .scalar (.binop rB .add (.reg 132) (.lit (3 * fpD)))
  , .scalar (.binop rB .sub (.reg rB) (.lit 1))
  , .scalar (.binop rB .udiv (.reg rB) (.reg 132))
  , .scalar (.binop rA .sub (.reg rA) (.reg rB))
  , .scalar (.binop rB .mul (.reg 132) (.lit 2))
  , .scalar (.binop rA .udiv (.reg rA) (.reg rB))
  , .scalar (.binop rB .add (.reg 132) (.lit fpD))
  , .scalar (.binop rB .sub (.reg rB) (.lit 1))
  , .scalar (.binop rA .sub (.reg rB) (.reg rA))
  , .scalar (.binop rB .sub (.reg 132) (.lit 1))
  , .scalar (.binop rIU .udiv (.reg rA) (.reg rB))
    -- candidate-only commit
  , .scalar (.binop rA .mul (.reg 11) (.reg rIL))
  , .scalar (.binop rLogL .add (.reg rLogL) (.reg rA))
  , .scalar (.binop rB .mul (.reg 11) (.reg rIU))
  , .scalar (.binop rLogU .add (.reg rLogU) (.reg rB)) ]

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
