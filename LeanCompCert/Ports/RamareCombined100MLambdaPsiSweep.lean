import LeanCompCert.Ports.RamareCombined100MLambdaPsiArithmetic

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M

/-- State at the verified seam between seven-plane classification and the
log/lambda/psi arithmetic. -/
def afterClassification (c : Cfg) (k : Nat) (s : AState) : AState :=
  arun k s c.shape.classBody

/-- Complete live-candidate path from seven-plane classification through all
proved log, lambda, sum, and psi arithmetic. -/
def classifiedArithmeticBody (c : Cfg) : List AInstr :=
  c.shape.classBody ++ arithmeticBody c

set_option maxRecDepth 20000 in
/-- The classifier supplies the exact candidate and live gate consumed by the
already-proved arithmetic suffix.  All arithmetic preconditions are stated on
that concrete post-classification state. -/
theorem classifiedArithmeticBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.shape.markSteps ≤ s.regs ShapeSieve.rR)
    (hR : s.regs ShapeSieve.rR < M)
    (hsum : s.regs ShapeSieve.rR - c.shape.markSteps +
      s.regs ShapeSieve.rW < M)
    (hpre : ArithmeticPre c k (afterClassification c k s)) :
    let classified := afterClassification c k s
    let out := arun k s (classifiedArithmeticBody c)
    classified.regs 132 =
        s.regs ShapeSieve.rR - c.shape.markSteps + s.regs ShapeSieve.rW ∧
      classified.regs 11 = 1 ∧
      out.regs lRLogL = classified.regs lRLogL +
        RS62.incLWord (classified.regs 132) ∧
      out.regs lRLogU = classified.regs lRLogU +
        RS62.incUWord (classified.regs 132) ∧
      observeCandidate out =
        candidateArithmetic c (afterLogCandidate k classified) ∧
      out.arr = classified.arr := by
  let classified := afterClassification c k s
  have hclass :=
    ShapeSieve.Cfg.classBody_candidate_run c.shape k s hphase hT hR hsum
  change classified.regs 132 =
      s.regs ShapeSieve.rR - c.shape.markSteps + s.regs ShapeSieve.rW ∧
    classified.regs 11 = 1 at hclass
  have harith := arithmeticBody_run_of_pre c k classified hpre
  dsimp only at harith
  have hlogL := harith.1
  have hlogU := harith.2.1
  rw [hclass.2, Nat.one_mul] at hlogL hlogU
  rw [classifiedArithmeticBody, arun_append]
  change classified.regs 132 = _ ∧ classified.regs 11 = 1 ∧ _
  exact ⟨hclass.1, hclass.2, hlogL, hlogU,
    harith.2.2.1, harith.2.2.2⟩

def init (c : Cfg) (s : Seed) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.init c.shape s.log ++
    storeLits c.logCells ++
    seedRegs [(rSumL, s.sumL), (rSumU, s.sumU),
      (rPsiLQ, s.psiL.q), (rPsiLR, s.psiL.r),
      (rPsiUQ, s.psiU.q), (rPsiUR, s.psiU.r)]

def body (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.body c.shape ++ candidateBody c

def storeResult (c : Cfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov rT0 (.lit (c.resultBase + slot))), .store rT0 reg ]

def epilogue (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.epilogue c.shape ++
    storeResult c 0 rSumL ++ storeResult c 1 rSumU ++
    storeResult c 2 rPsiLQ ++ storeResult c 3 rPsiLR ++
    storeResult c 4 rPsiUQ ++ storeResult c 5 rPsiUR

def program (c : Cfg) (s : Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.shape.period * c.shape.segCount
  init := init c s
  body := body c
  epilogue := epilogue c
  output := shapeOutputReg
}

theorem program_loopCount (c : Cfg) (s : Seed) :
    (program c s).loopCount = c.shape.period * c.shape.segCount := rfl

/-! ## Verified compiler package -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

set_option maxRecDepth 50000 in
theorem init_all (c : Cfg) (s : Seed) :
    (init c s).all (ainstrWFB regCount) = true := by
  unfold init LeanCompCert.Ports.RamareCombined100M.LogSweep.init
    LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg.init
  simp only [List.all_append, storeLits_all]
  rfl

set_option maxRecDepth 50000 in
theorem body_all (c : Cfg) : (body c).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 50000 in
theorem epilogue_all (c : Cfg) :
    (epilogue c).all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : Cfg) (s : Seed) : (program c s).WF :=
  ⟨show shapeOutputReg < regCount by decide,
   forall_wf_of_all (init_all c s), forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : Cfg) (s : Seed) (base : Int)
    (hBase : BaseOk (program c s).arrayLen base)
    (n : Nat) (hDenote : (program c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c s).initialMCC base) (program c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c s) base hBase n hDenote

/-! ## Kernel-sized control -/

def smokeLogs : List LogCell :=
  (List.range 15).map fun i =>
    { idx := i, active := decide (i = 2 ∨ i = 3 ∨ i = 5)
      lo48 := 1000 * i, hi48 := 1000 * i + 7, lo32 := 0, hi32 := 0 }

def smokeShapeCfg : ShapeCfg :=
  { lo := 11, segLen := 4, segCount := 1, tableHi := 14
    markSteps := 30, table := [2, 3] }

def smokeCfg : Cfg := ⟨smokeShapeCfg, smokeLogs⟩
def smokeSeed : Seed :=
  { log := logSmokeSeed, sumL := 3, sumU := 5
    psiL := PsiQR.ofValue 11 10000, psiU := PsiQR.ofValue 11 10020 }

end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep
