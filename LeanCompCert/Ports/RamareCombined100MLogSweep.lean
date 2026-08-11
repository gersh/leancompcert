import LeanCompCert.Ports.RamareCombined100MLogSweepUpperB

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

/-- The complete 26-instruction candidate suffix computes both RS62
increments and commits exactly the classification-gated contributions. -/
theorem candidateBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hLM : s.regs 11 * incLWord (s.regs 132) < M)
    (hLA : s.regs rLogL + s.regs 11 * incLWord (s.regs 132) < M)
    (hUM : s.regs 11 * incUWord (s.regs 132) < M)
    (hUA : s.regs rLogU + s.regs 11 * incUWord (s.regs 132) < M) :
    let out := arun k s candidateBody
    out.regs rLogL =
        s.regs rLogL + s.regs 11 * incLWord (s.regs 132) ∧
      out.regs rLogU =
        s.regs rLogU + s.regs 11 * incUWord (s.regs 132) ∧
      out.regs rIL = incLWord (s.regs 132) ∧
      out.regs rIU = incUWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let l := arun k s (lift lowerScalarBody)
  let u := arun k l (lift upperScalarBody)
  let out := arun k u (lift commitScalarBody)
  have hl := lowerScalarBody_run k s hn2 hn40
  change l.regs rIL = incLWord (s.regs 132) ∧
    l.regs 132 = s.regs 132 ∧ l.arr = s.arr at hl
  have hu := upperScalarBody_run k l (by rw [hl.2.1]; exact hn2)
    (by rw [hl.2.1]; exact hn40)
  change u.regs rIU = incUWord (l.regs 132) ∧
    u.regs 132 = l.regs 132 ∧ u.arr = l.arr at hu
  have huIL : u.regs rIL = incLWord (s.regs 132) := by
    rw [scalarBody_frame k rIL upperScalarBody (by decide) l, hl.1]
  have huIU : u.regs rIU = incUWord (s.regs 132) := by
    rw [hu.1, hl.2.1]
  have huGate : u.regs 11 = s.regs 11 := by
    rw [scalarBody_frame k 11 upperScalarBody (by decide) l,
      scalarBody_frame k 11 lowerScalarBody (by decide) s]
  have huLogL : u.regs rLogL = s.regs rLogL := by
    rw [scalarBody_frame k rLogL upperScalarBody (by decide) l,
      scalarBody_frame k rLogL lowerScalarBody (by decide) s]
  have huLogU : u.regs rLogU = s.regs rLogU := by
    rw [scalarBody_frame k rLogU upperScalarBody (by decide) l,
      scalarBody_frame k rLogU lowerScalarBody (by decide) s]
  have hc := commitScalarBody_run k u (by rw [huGate, huIL]; exact hLM)
    (by rw [huLogL, huGate, huIL]; exact hLA)
    (by rw [huGate, huIU]; exact hUM)
    (by rw [huLogU, huGate, huIU]; exact hUA)
  change out.regs rLogL = u.regs rLogL + u.regs 11 * u.regs rIL ∧
    out.regs rLogU = u.regs rLogU + u.regs 11 * u.regs rIU ∧
    out.regs 132 = u.regs 132 ∧ out.arr = u.arr at hc
  have houtIL : out.regs rIL = u.regs rIL :=
    scalarBody_frame k rIL commitScalarBody (by decide) u
  have houtIU : out.regs rIU = u.regs rIU :=
    scalarBody_frame k rIU commitScalarBody (by decide) u
  have hout :
      out.regs rLogL =
          s.regs rLogL + s.regs 11 * incLWord (s.regs 132) ∧
        out.regs rLogU =
          s.regs rLogU + s.regs 11 * incUWord (s.regs 132) ∧
        out.regs rIL = incLWord (s.regs 132) ∧
        out.regs rIU = incUWord (s.regs 132) ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hc.1, huLogL, huGate, huIL, hc.2.1, huLogU, huGate, huIU,
      houtIL, huIL, houtIU, huIU, hc.2.2.1, hu.2.1, hl.2.1,
      hc.2.2.2, hu.2.2, hl.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa only [candidateBody, arun_append] using hout

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

end LeanCompCert.Ports.RamareCombined100M.LogSweep
