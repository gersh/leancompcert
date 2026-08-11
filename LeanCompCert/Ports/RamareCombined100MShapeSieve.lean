import LeanCompCert.Ports.RamareCombined100MShapeSieveClassSem


namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.R2SegSieve
  (markBudget markBudget_lt_word markBudget_add_len_lt_word)

/-- State obtained by clearing the seven live classifier cells. -/
def clearClassCells (s : AState) : AState :=
  let s := s.writeArr (s.regs 131) 0
  let s := s.writeArr (s.regs 133) 0
  let s := s.writeArr (s.regs 134) 0
  let s := s.writeArr (s.regs 135) 0
  let s := s.writeArr (s.regs 136) 0
  let s := s.writeArr (s.regs 137) 0
  s.writeArr (s.regs 138) 0

/-- The physical clear stage writes zero to exactly the seven plane cells. -/
theorem Cfg.classClearBody_run (k : Nat) (s : AState)
    (hzero : s.regs 0 = 0) :
    arun k s Cfg.classClearBody = clearClassCells s := by
  simp [Cfg.classClearBody, clearClassCells, arun, astep,
    AState.writeArr, hzero]

/-- Exactly the seven live plane addresses are the partiality obligations of
the classifier clear stage. -/
theorem Cfg.classClearBody_defined (len k : Nat) (s : AState)
    (h131 : s.regs 131 < len) (h133 : s.regs 133 < len)
    (h134 : s.regs 134 < len) (h135 : s.regs 135 < len)
    (h136 : s.regs 136 < len) (h137 : s.regs 137 < len)
    (h138 : s.regs 138 < len) :
    AllDefined len k s Cfg.classClearBody := by
  simp [Cfg.classClearBody, AllDefined, ADefined, astep, AState.writeArr,
    h131, h133, h134, h135, h136, h137, h138]

def Cfg.tailBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 20 .add (.reg rR) (.lit 1))
  , .scalar (.binop 21 .eq (.reg 20) (.lit c.period))
  , .scalar (.binop 22 .sub (.lit 1) (.reg 21))
  , .scalar (.binop rR .mul (.reg 22) (.reg 20))
  , .scalar (.binop 23 .mul (.reg 21) (.lit c.segLen))
  , .scalar (.binop rW .add (.reg rW) (.reg 23)) ]

def Cfg.body (c : Cfg) : List AInstr := c.markBody ++ c.classBody ++ c.tailBody

/-- On every live classification round, the complete loop body retains the
exact candidate `windowBase + (round-markSteps)` and the live gate.  The mark
core and tail are discharged purely by destination framing. -/
theorem Cfg.body_candidate_run (c : Cfg) (k : Nat) (s : AState)
    (hTword : c.markSteps < M)
    (hclass : c.markSteps ≤ s.regs rR)
    (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.body
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 := by
  let marked := arun k s c.markBody
  let classified := arun k marked c.classBody
  have hmphase := Cfg.markBody_phase_run c k s hTword
  dsimp only at hmphase
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR c.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW c.markBody (by rfl) s
  have hm11 : marked.regs 11 = 1 := by
    rw [hmphase.2, if_pos hclass]
  have hc := Cfg.classBody_candidate_run c k marked hm11
    (by simpa [hmR] using hclass) (by simpa [hmR] using hR)
    (by simpa [hmR, hmW] using hsum)
  dsimp only at hc
  have ht132 : (arun k classified c.tailBody).regs 132 = classified.regs 132 :=
    arun_frame k 132 c.tailBody (by rfl) classified
  have ht11 : (arun k classified c.tailBody).regs 11 = classified.regs 11 :=
    arun_frame k 11 c.tailBody (by rfl) classified
  rw [Cfg.body, arun_append, arun_append]
  constructor
  · rw [ht132, hc.1, hmR, hmW]
  · rw [ht11, hc.2]

def Cfg.tableCells (c : Cfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [(c.tableBase + c.tableLen, 1)]

def Cfg.init (c : Cfg) : List AInstr :=
  storeLits c.tableCells ++ seedRegs [(rW, c.lo)]

def Cfg.epilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov 20 (.lit c.resultBase)), .store 20 rViol
  , .scalar (.mov 20 (.lit (c.resultBase + 1))), .store 20 rSeen
  , .scalar (.mov 20 (.lit (c.resultBase + 2))), .store 20 rVMark
  , .scalar (.mov 20 (.lit (c.resultBase + 3))), .store 20 rVShape ]

def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-! ## Verified compiler package -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem seed_all :
    (seedRegs [(rW, 0)]).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem body_all (c : Cfg) : c.body.all (ainstrWFB regCount) = true := by rfl

theorem init_all (c : Cfg) : c.init.all (ainstrWFB regCount) = true := by
  unfold Cfg.init
  apply all_append (storeLits_all _)
  rfl

theorem epilogue_all (c : Cfg) :
    c.epilogue.all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : Cfg) : (program c).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- The generated CCIR trace, and hence the verified emitted C fragment,
returns exactly the guard count denoted by the segmented classifier. -/
theorem program_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (program c).arrayLen base)
    (n : Nat) (hDenote : (program c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c).initialMCC base) (program c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c) base hBase n hDenote

/-! A kernel-sized control covering primes, prime powers, two-prime cells and
cells with at least three distinct factors. -/

def smokeCfg : Cfg := {
  lo := 11, segLen := 20, segCount := 1, tableHi := 30
  markSteps := 48, table := [2, 3, 5] }

def smokeProbe (out : Nat) : AProgram := { program smokeCfg with output := out }

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
