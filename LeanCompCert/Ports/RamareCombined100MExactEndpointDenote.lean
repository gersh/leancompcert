import LeanCompCert.Ports.RamareCombined100MSeamBlock

/-!
# Denotation of the exact Ramaré 100-million endpoint blocks

This module deliberately sits outside `RamareCombined100MSeamBlock`.  The
emitter file contains the concrete instruction lists and their small primitive
lemmas; keeping the composite proofs here prevents edits to a denotation proof
from re-elaborating the large emitter as one monolithic declaration.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge

/-- The emitted ungated select reconstructs the model's `pLog32` pair from
the pre-increment carried log and the selected table row. -/
theorem pLogRecompute_run (k : Nat) (s : AState)
    (hOldL : s.regs sOldL < M) (hOldU : s.regs sOldU < M)
    (hTabL : s.regs sTabL < M) (hTabU : s.regs sTabU < M)
    (hOldUAdd : s.regs sOldU + 65535 < M)
    (hTabUAdd : s.regs sTabU + 65535 < M) :
    let out := arun k s pLogRecompute
    out.regs rPLo =
        (if s.regs sShapeP = s.regs sCand then
          s.regs sOldL / 65536 else s.regs sTabL / 65536) ∧
      out.regs rPHi =
        (if s.regs sShapeP = s.regs sCand then
          (s.regs sOldU + 65535) / 65536
         else (s.regs sTabU + 65535) / 65536) := by
  dsimp only
  let cmpBlock : List AInstr :=
    [.scalar (.binop rC .eq (.reg sShapeP) (.reg sCand))]
  let s0 := arun k s cmpBlock
  let s1 := arun k s0 (movReg rX sOldL)
  let s2 := arun k s1 (movReg rY sTabL)
  let s3 := arun k s2 selectBlock
  let s4 := arun k s3 (movReg rPLo rSel)
  let s4lo := arun k s4 (shrReg rPLo rPLo 16)
  let s5 := arun k s4lo (movReg rX sOldU)
  let s6 := arun k s5 (movReg rY sTabU)
  let s7 := arun k s6 selectBlock
  let s8 := arun k s7 (movReg rPHi rSel)
  let s9 := arun k s8 (ceilShift16Reg rPHi rPHi)
  have hc : s0.regs rC =
      (if s.regs sShapeP = s.regs sCand then 1 else 0) := by
    simp [s0, cmpBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, rC, sShapeP, sCand,
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide),
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  have hc1 : s2.regs rC = s0.regs rC := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hx1 : s2.regs rX = s.regs sOldL := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hy1 : s2.regs rY = s.regs sTabL := by
    rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hsel1 : s3.regs rSel =
      (if s.regs sShapeP = s.regs sCand then s.regs sOldL else s.regs sTabL) := by
    rw [selectBlock_run k s2
      (by rw [hc1, hc]; exact ite_bit _)
      (by rw [hx1]; exact hOldL) (by rw [hy1]; exact hTabL),
      hc1, hc, hx1, hy1]
    by_cases h : s.regs sShapeP = s.regs sCand <;> simp [h]
  have hplo4 : s4.regs rPLo =
      (if s.regs sShapeP = s.regs sCand then s.regs sOldL else s.regs sTabL) :=
    (movReg_run k s3 rPLo rSel).trans hsel1
  have hrawLo : s4.regs rPLo < M := by
    rw [hplo4]
    split <;> assumption
  have hplo4lo : s4lo.regs rPLo =
      (if s.regs sShapeP = s.regs sCand then
        s.regs sOldL / 65536 else s.regs sTabL / 65536) := by
    rw [shrReg_run k s4 rPLo rPLo 16 (by decide) hrawLo, hplo4]
    split <;> rfl
  have hc2 : s6.regs rC = s0.regs rC := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hx2 : s6.regs rX = s.regs sOldU := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      movReg_run]
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hy2 : s6.regs rY = s.regs sTabU := by
    rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hsel2 : s7.regs rSel =
      (if s.regs sShapeP = s.regs sCand then s.regs sOldU else s.regs sTabU) := by
    rw [selectBlock_run k s6
      (by rw [hc2, hc]; exact ite_bit _)
      (by rw [hx2]; exact hOldU) (by rw [hy2]; exact hTabU),
      hc2, hc, hx2, hy2]
    by_cases h : s.regs sShapeP = s.regs sCand <;> simp [h]
  have hphi8 : s8.regs rPHi =
      (if s.regs sShapeP = s.regs sCand then s.regs sOldU else s.regs sTabU) :=
    (movReg_run k s7 rPHi rSel).trans hsel2
  have hplo8 : s8.regs rPLo = s4lo.regs rPLo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hplo9 : s9.regs rPLo = s8.regs rPLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hphiAdd : s8.regs rPHi + 65535 < M := by
    rw [hphi8]
    split <;> assumption
  have hphi9 : s9.regs rPHi =
      (if s.regs sShapeP = s.regs sCand then
        (s.regs sOldU + 65535) / 65536
       else (s.regs sTabU + 65535) / 65536) := by
    rw [ceilShift16Reg_run k s8 rPHi rPHi hphiAdd, hphi8]
    split <;> rfl
  change s9.regs rPLo = _ ∧ s9.regs rPHi = _
  exact ⟨hplo9.trans (hplo8.trans hplo4lo), hphi9⟩

theorem lowerFoldBExact_run (k : Nat) (s : AState)
    (logLen loBase sink : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rQLo)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rPLo) (s.regs rQLo) < M) :
    (arun k s (lowerFoldBExact logLen loBase sink)).regs rY =
      (if s.regs sShapeTail = 1 then
        Section413Cells.encodeZ
          (2 * ((mulLower (s.regs rPLo) (s.regs rQLo) : Nat) : Int))
       else 0) := by
  rw [lowerFoldBExact, arun_append, arun_append, arun_append, arun_append]
  let seeded := arun k s (movLit rY 0)
  have hy0 : seeded.regs rY = 0 := movLit_run _ _ _ _ (by decide)
  have ePLo : seeded.regs rPLo = s.regs rPLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eQLo : seeded.regs rQLo = s.regs rQLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eT : seeded.regs sShapeTail = s.regs sShapeTail :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eArr : seeded.arr = s.arr := by
    simp [seeded, movLit, arun, astep, AState.writeReg]
  have hw' : ∀ j, seeded.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k (movLit rY 0) s hw haW).1
  have hbb := branchBLowerExact_run k seeded logLen loBase sink hw'
    (by simpa [eArr] using haW) hlen hsink
    (by exact hsum)
    (by rw [ePLo, eQLo]; exact hfit)
    (by rw [ePLo, eQLo]; exact hout)
  rw [ePLo, eQLo] at hbb
  let branched := arun k seeded (branchBLowerExact logLen loBase sink)
  let staged := arun k branched (movReg rX rProd)
  have hx : staged.regs rX =
      Section413Cells.encodeZ
        (2 * ((mulLower (s.regs rPLo) (s.regs rQLo) : Nat) : Int)) := by
    exact (movReg_run k branched rX rProd).trans hbb
  have hy : staged.regs rY = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hy0]
  have ht : staged.regs sShapeTail = s.regs sShapeTail := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eT]
  have hc := tailEqOneToC_run k staged
  rw [ht] at hc
  let guarded := arun k staged tailEqOneToC
  have hxc : guarded.regs rX = staged.regs rX :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : guarded.regs rY = staged.regs rY :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; decide),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeTail = 1 <;> simp [h]

theorem lowerFoldAExact_run (k : Nat) (s : AState) (prev : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hprev : s.regs rY = prev) (hprevM : prev < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rPHi)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rPHi) (s.regs rPHi) < M) :
    (arun k s lowerFoldAExact).regs rY =
      (if s.regs sShapeRest = 1 then
        Section413Cells.encodeZ
          (-((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int))
       else prev) := by
  rw [lowerFoldAExact, arun_append, arun_append, arun_append]
  have hbb := branchALowerExact_run k s hw haW hfit hout
  let branched := arun k s branchALowerExact
  let staged := arun k branched (movReg rX rProd)
  have hx : staged.regs rX = Section413Cells.encodeZ
      (-((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)) :=
    (movReg_run k branched rX rProd).trans hbb
  have hy : staged.regs rY = prev := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hprev]
  have hr : staged.regs sShapeRest = s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  have hc := restEqOneToC_run k staged
  rw [hr] at hc
  let guarded := arun k staged restEqOneToC
  have hxc : guarded.regs rX = staged.regs rX :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : guarded.regs rY = staged.regs rY :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; exact hprevM),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeRest = 1 <;> simp [h]

theorem upperFoldBExact_run (k : Nat) (s : AState)
    (logLen hiBase sink : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rQHi)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rPHi) (s.regs rQHi) < M) :
    (arun k s (upperFoldBExact logLen hiBase sink)).regs rY =
      (if s.regs sShapeTail = 1 then
        Section413Cells.encodeZ
          (2 * ((mulUpper (s.regs rPHi) (s.regs rQHi) : Nat) : Int))
       else 0) := by
  rw [upperFoldBExact, arun_append, arun_append, arun_append, arun_append]
  let seeded := arun k s (movLit rY 0)
  have hy0 : seeded.regs rY = 0 := movLit_run _ _ _ _ (by decide)
  have ePHi : seeded.regs rPHi = s.regs rPHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eQHi : seeded.regs rQHi = s.regs rQHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eT : seeded.regs sShapeTail = s.regs sShapeTail :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have eArr : seeded.arr = s.arr := by
    simp [seeded, movLit, arun, astep, AState.writeReg]
  have hw' : ∀ j, seeded.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k (movLit rY 0) s hw haW).1
  have hbb := branchBUpperExact_run k seeded logLen hiBase sink hw'
    (by simpa [eArr] using haW) hlen hsink
    (by exact hsum)
    (by rw [ePHi, eQHi]; exact hfit)
    (by rw [ePHi, eQHi]; exact hout)
  rw [ePHi, eQHi] at hbb
  let branched := arun k seeded (branchBUpperExact logLen hiBase sink)
  let staged := arun k branched (movReg rX rProd)
  have hx : staged.regs rX =
      Section413Cells.encodeZ
        (2 * ((mulUpper (s.regs rPHi) (s.regs rQHi) : Nat) : Int)) := by
    exact (movReg_run k branched rX rProd).trans hbb
  have hy : staged.regs rY = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hy0]
  have ht : staged.regs sShapeTail = s.regs sShapeTail := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eT]
  have hc := tailEqOneToC_run k staged
  rw [ht] at hc
  let guarded := arun k staged tailEqOneToC
  have hxc : guarded.regs rX = staged.regs rX :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : guarded.regs rY = staged.regs rY :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; decide),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeTail = 1 <;> simp [h]

theorem upperFoldAExact_run (k : Nat) (s : AState) (prev : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hprev : s.regs rY = prev) (hprevM : prev < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rPLo)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rPLo) (s.regs rPLo) < M) :
    (arun k s upperFoldAExact).regs rY =
      (if s.regs sShapeRest = 1 then
        Section413Cells.encodeZ
          (-((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int))
       else prev) := by
  rw [upperFoldAExact, arun_append, arun_append, arun_append]
  have hbb := branchAUpperExact_run k s hw haW hfit hout
  let branched := arun k s branchAUpperExact
  let staged := arun k branched (movReg rX rProd)
  have hx : staged.regs rX = Section413Cells.encodeZ
      (-((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)) :=
    (movReg_run k branched rX rProd).trans hbb
  have hy : staged.regs rY = prev := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hprev]
  have hr : staged.regs sShapeRest = s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  have hc := restEqOneToC_run k staged
  rw [hr] at hc
  let guarded := arun k staged restEqOneToC
  have hxc : guarded.regs rX = staged.regs rX :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : guarded.regs rY = staged.regs rY :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; exact hprevM),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeRest = 1 <;> simp [h]

/-- End-to-end denotation of the exact lower endpoint, including the running
signed accumulator and the per-candidate endpoint snapshot. -/
theorem lowerEndpointExactBlock_run (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hacc : s.regs rAccLo = Section413Cells.encodeZ acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hfitB : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rQLo)).2 < 2 ^ 32)
    (houtB : mulLower (s.regs rPLo) (s.regs rQLo) < M)
    (hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rPHi)).2 < 2 ^ 32)
    (houtA : mulUpper (s.regs rPHi) (s.regs rPHi) < M)
    (hgamma : gammaLo < LeanCompCert.Verified.MulWide.B64) :
    let branchB : Int :=
      if s.regs sShapeTail = 1 then
        2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
      else 0
    let branch : Int :=
      if s.regs sShapeRest = 1 then
        -(mulUpper (s.regs rPHi) (s.regs rPHi) : Nat)
      else branchB
    let endpoint := branch + (gammaLo : Int)
    let out := arun k s (lowerEndpointExactBlock logLen loBase sink gammaLo)
    out.regs rIlo = Section413Cells.encodeZ endpoint ∧
      out.regs rAccLo = Section413Cells.encodeZ (acc + endpoint) := by
  dsimp only
  let foldB := arun k s (lowerFoldBExact logLen loBase sink)
  let bB : Int :=
    if s.regs sShapeTail = 1 then
      2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
    else 0
  have hB0 := lowerFoldBExact_run k s logLen loBase sink hw haW hlen hsink
    hsum hfitB houtB
  have hB : foldB.regs rY = Section413Cells.encodeZ bB := by
    rw [hB0]
    by_cases h : s.regs sShapeTail = 1
    · simp [bB, h]
    · simp only [bB, h, if_false]
      exact (encodeZ_ofNat (show (0 : Nat) < M by decide)).symm
  have hwB : ∀ j, foldB.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (lowerFoldBExact logLen loBase sink) s hw haW).1
  have haB : ∀ j, foldB.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (lowerFoldBExact logLen loBase sink) s hw haW).2
  have epHi : foldB.regs rPHi = s.regs rPHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eRest : foldB.regs sShapeRest = s.regs sShapeRest :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eAcc : foldB.regs rAccLo = s.regs rAccLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  let foldA := arun k foldB lowerFoldAExact
  have hA0 := lowerFoldAExact_run k foldB (Section413Cells.encodeZ bB)
    hwB haB hB (M_eq_B64 ▸ Section413Cells.encodeZ_lt bB)
    (by rw [epHi]; exact hfitA) (by rw [epHi]; exact houtA)
  let branch : Int :=
    if s.regs sShapeRest = 1 then
      -(mulUpper (s.regs rPHi) (s.regs rPHi) : Nat)
    else bB
  have hA : foldA.regs rY = Section413Cells.encodeZ branch := by
    rw [hA0, eRest, epHi]
    by_cases h : s.regs sShapeRest = 1 <;> simp [branch, h]
  have eAccA : foldA.regs rAccLo = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      eAcc, hacc]
  let gamma := arun k foldA (lowerGammaStep gammaLo)
  have hGamma : gamma.regs rY =
      Section413Cells.encodeZ (branch + (gammaLo : Int)) :=
    lowerGammaStep_run k foldA gammaLo branch hA hgamma
  have eAccG : gamma.regs rAccLo = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eAccA]
  let staged := arun k gamma (movReg rIlo rY)
  have hI : staged.regs rIlo =
      Section413Cells.encodeZ (branch + (gammaLo : Int)) :=
    (movReg_run k gamma rIlo rY).trans hGamma
  have hY : staged.regs rY =
      Section413Cells.encodeZ (branch + (gammaLo : Int)) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hGamma]
  have eAccS : staged.regs rAccLo = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eAccG]
  have hAcc := accumulateLo_run k staged (branch + (gammaLo : Int)) acc eAccS hY
  have hIout : (arun k staged accumulateLo).regs rIlo = staged.regs rIlo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simp only [lowerEndpointExactBlock, arun_append]
  change (arun k staged accumulateLo).regs rIlo = _ ∧
    (arun k staged accumulateLo).regs rAccLo = _
  exact ⟨hIout.trans hI, hAcc⟩

/-- End-to-end denotation of the exact upper endpoint. -/
theorem upperEndpointExactBlock_run (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hacc : s.regs rAccHi = Section413Cells.encodeZ acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hfitB : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rQHi)).2 < 2 ^ 32)
    (houtB : mulUpper (s.regs rPHi) (s.regs rQHi) < M)
    (hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rPLo)).2 < 2 ^ 32)
    (houtA : mulLower (s.regs rPLo) (s.regs rPLo) < M)
    (hgamma : gammaHi < LeanCompCert.Verified.MulWide.B64) :
    let branchB : Int :=
      if s.regs sShapeTail = 1 then
        2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
      else 0
    let branch : Int :=
      if s.regs sShapeRest = 1 then
        -(mulLower (s.regs rPLo) (s.regs rPLo) : Nat)
      else branchB
    let endpoint := branch + (gammaHi : Int)
    let out := arun k s (upperEndpointExactBlock logLen hiBase sink gammaHi)
    out.regs rIhi = Section413Cells.encodeZ endpoint ∧
      out.regs rAccHi = Section413Cells.encodeZ (acc + endpoint) := by
  dsimp only
  let foldB := arun k s (upperFoldBExact logLen hiBase sink)
  let bB : Int :=
    if s.regs sShapeTail = 1 then
      2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
    else 0
  have hB0 := upperFoldBExact_run k s logLen hiBase sink hw haW hlen hsink
    hsum hfitB houtB
  have hB : foldB.regs rY = Section413Cells.encodeZ bB := by
    rw [hB0]
    by_cases h : s.regs sShapeTail = 1
    · simp [bB, h]
    · simp only [bB, h, if_false]
      exact (encodeZ_ofNat (show (0 : Nat) < M by decide)).symm
  have hwB : ∀ j, foldB.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (upperFoldBExact logLen hiBase sink) s hw haW).1
  have haB : ∀ j, foldB.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (upperFoldBExact logLen hiBase sink) s hw haW).2
  have epLo : foldB.regs rPLo = s.regs rPLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eRest : foldB.regs sShapeRest = s.regs sShapeRest :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eAcc : foldB.regs rAccHi = s.regs rAccHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  let foldA := arun k foldB upperFoldAExact
  have hA0 := upperFoldAExact_run k foldB (Section413Cells.encodeZ bB)
    hwB haB hB (M_eq_B64 ▸ Section413Cells.encodeZ_lt bB)
    (by rw [epLo]; exact hfitA) (by rw [epLo]; exact houtA)
  let branch : Int :=
    if s.regs sShapeRest = 1 then
      -(mulLower (s.regs rPLo) (s.regs rPLo) : Nat)
    else bB
  have hA : foldA.regs rY = Section413Cells.encodeZ branch := by
    rw [hA0, eRest, epLo]
    by_cases h : s.regs sShapeRest = 1 <;> simp [branch, h]
  have eAccA : foldA.regs rAccHi = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      eAcc, hacc]
  let gamma := arun k foldA (lowerGammaStep gammaHi)
  have hGamma : gamma.regs rY =
      Section413Cells.encodeZ (branch + (gammaHi : Int)) :=
    lowerGammaStep_run k foldA gammaHi branch hA hgamma
  have eAccG : gamma.regs rAccHi = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eAccA]
  let staged := arun k gamma (movReg rIhi rY)
  have hI : staged.regs rIhi =
      Section413Cells.encodeZ (branch + (gammaHi : Int)) :=
    (movReg_run k gamma rIhi rY).trans hGamma
  have hY : staged.regs rY =
      Section413Cells.encodeZ (branch + (gammaHi : Int)) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hGamma]
  have eAccS : staged.regs rAccHi = Section413Cells.encodeZ acc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), eAccG]
  have hAcc := accumulateHi_run k staged (branch + (gammaHi : Int)) acc eAccS hY
  have hIout : (arun k staged accumulateHi).regs rIhi = staged.regs rIhi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simp only [upperEndpointExactBlock, upperEndpointTail, arun_append]
  change (arun k staged accumulateHi).regs rIhi = _ ∧
    (arun k staged accumulateHi).regs rAccHi = _
  exact ⟨hIout.trans hI, hAcc⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock
