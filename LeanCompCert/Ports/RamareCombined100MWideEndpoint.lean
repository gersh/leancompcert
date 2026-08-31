import LeanCompCert.Ports.RamareCombined100MExactEndpointDenote
import LeanCompCert.Ports.RamareCombined100MWideSigned

/-!
# Exact endpoint accumulation without a one-word wrap

The coefficient of one candidate is a signed 64-bit value, but its running
sum is not.  These blocks retain the already-proved exact endpoint arithmetic
and change only the persistent update to signed two-limb addition.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WideEndpoint

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.SeamBlock

/-- High limbs added to the two existing persistent endpoint registers. -/
def rAccLoHi : Nat := 327
def rAccHiHi : Nat := 328

/-- Scratch shared by the two signed additions. -/
def rExt : Nat := 329
def rSign : Nat := 330
def rCarry : Nat := 331

def lowerValue (logLen loBase sink gammaLo : Nat) : List AInstr :=
  lowerFoldBExact logLen loBase sink ++ lowerFoldAExact ++
    lowerGammaStep gammaLo

def upperValue (logLen hiBase sink gammaHi : Nat) : List AInstr :=
  upperFoldBExact logLen hiBase sink ++ upperFoldAExact ++
    lowerGammaStep gammaHi

def lowerEndpoint (logLen loBase sink gammaLo : Nat) : List AInstr :=
  lowerValue logLen loBase sink gammaLo ++ movReg rIlo rY ++
    WideSigned.addSigned64Block rAccLo rAccLoHi rY rExt rSign rCarry

def upperEndpoint (logLen hiBase sink gammaHi : Nat) : List AInstr :=
  upperValue logLen hiBase sink gammaHi ++ movReg rIhi rY ++
    WideSigned.addSigned64Block rAccHi rAccHiHi rY rExt rSign rCarry

theorem lowerValue_run (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
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
    (arun k s (lowerValue logLen loBase sink gammaLo)).regs rY =
      Section413Cells.encodeZ (branch + (gammaLo : Int)) := by
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
  simp only [lowerValue, arun_append]
  exact lowerGammaStep_run k foldA gammaLo branch hA hgamma

theorem upperValue_run (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
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
    (arun k s (upperValue logLen hiBase sink gammaHi)).regs rY =
      Section413Cells.encodeZ (branch + (gammaHi : Int)) := by
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
  simp only [upperValue, arun_append]
  exact lowerGammaStep_run k foldA gammaHi branch hA hgamma

/-- Generic tail theorem: a proved signed-word endpoint value is accumulated
into an exact signed two-limb state. -/
theorem accumulateValue_run (k : Nat) (s : AState)
    (valueBlock : List AInstr) (iReg lo hi : Nat) (acc inc : Int)
    (hvalue : (arun k s valueBlock).regs rY = Section413Cells.encodeZ inc)
    (hlo : (arun k s valueBlock).regs lo = s.regs lo)
    (hhi : (arun k s valueBlock).regs hi = s.regs hi)
    (hrep : WideSigned.rep (s.regs lo) (s.regs hi) acc)
    (hw : ∀ j, s.regs j < M)
    (hincLo : -(Section413Cells.H63 : Int) ≤ inc)
    (hincHi : inc < (Section413Cells.H63 : Int))
    (hregs : LeanCompCert.Ports.AddWidePort.WideRegs
      lo hi rCarry rY rExt)
    (hsep : rY ≠ rExt ∧ rY ≠ rSign ∧ lo ≠ rSign ∧ hi ≠ rSign)
    (hiFrame : iReg ≠ rY ∧ iReg ≠ lo ∧ iReg ≠ hi ∧
      iReg ≠ rCarry ∧ iReg ≠ rExt ∧ iReg ≠ rSign) :
    let out := arun k s (valueBlock ++ movReg iReg rY ++
      WideSigned.addSigned64Block lo hi rY rExt rSign rCarry)
    out.regs iReg = Section413Cells.encodeZ inc ∧
      WideSigned.rep (out.regs lo) (out.regs hi) (acc + inc) := by
  dsimp only
  let valued := arun k s valueBlock
  let staged := arun k valued (movReg iReg rY)
  have hI : staged.regs iReg = Section413Cells.encodeZ inc :=
    (movReg_run k valued iReg rY).trans hvalue
  have hY : staged.regs rY = Section413Cells.encodeZ inc := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, movReg]
      exact hiFrame.1), hvalue]
  have hlo' : staged.regs lo = s.regs lo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, movReg]
      exact hiFrame.2.1), hlo]
  have hhi' : staged.regs hi = s.regs hi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, movReg]
      exact hiFrame.2.2.1), hhi]
  have hAdd := WideSigned.addSigned64Block_rep k staged lo hi rY rExt rSign rCarry
    acc inc hregs hsep.1 hsep.2.1 hsep.2.2.1 hsep.2.2.2
    (by rw [hlo']; exact hw lo) (by rw [hhi']; exact hw hi)
    (by rw [hlo', hhi']; exact hrep) hY hincLo hincHi
  have hIout :
      (arun k staged (WideSigned.addSigned64Block lo hi rY rExt rSign rCarry)).regs iReg
        = staged.regs iReg :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      simp [WideSigned.addSigned64Block, WideSigned.signExtendBlock,
        LeanCompCert.Ports.AddWidePort.addWideABody,
        LeanCompCert.Ports.AddWidePort.addWideBody,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest]
      exact ⟨Ne.symm hiFrame.2.2.2.2.2, Ne.symm hiFrame.2.2.2.2.1,
        Ne.symm hiFrame.2.1, Ne.symm hiFrame.2.2.2.1,
        Ne.symm hiFrame.2.2.1⟩) _
  simp only [arun_append]
  exact ⟨hIout.trans hI, hAdd⟩

theorem lowerEndpoint_run (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccLo) (s.regs rAccLoHi) acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hfitB : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rQLo)).2 < 2 ^ 32)
    (houtB : mulLower (s.regs rPLo) (s.regs rQLo) < M)
    (hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rPHi)).2 < 2 ^ 32)
    (houtA : mulUpper (s.regs rPHi) (s.regs rPHi) < M)
    (hgamma : gammaLo < LeanCompCert.Verified.MulWide.B64)
    (hincLo :
      -(Section413Cells.H63 : Int) ≤
        ((if s.regs sShapeRest = 1 then
          -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
        else if s.regs sShapeTail = 1 then
          2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
        else 0) + (gammaLo : Int)))
    (hincHi :
      ((if s.regs sShapeRest = 1 then
          -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
        else if s.regs sShapeTail = 1 then
          2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
        else 0) + (gammaLo : Int)) < (Section413Cells.H63 : Int)) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
      else 0) + (gammaLo : Int)
    let out := arun k s (lowerEndpoint logLen loBase sink gammaLo)
    out.regs rIlo = Section413Cells.encodeZ endpoint ∧
      WideSigned.rep (out.regs rAccLo) (out.regs rAccLoHi)
        (acc + endpoint) := by
  dsimp only
  let endpoint : Int :=
    (if s.regs sShapeRest = 1 then
      -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
    else if s.regs sShapeTail = 1 then
      2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
    else 0) + (gammaLo : Int)
  have hv : (arun k s (lowerValue logLen loBase sink gammaLo)).regs rY =
      Section413Cells.encodeZ endpoint := by
    simpa only [endpoint] using lowerValue_run k s logLen loBase sink gammaLo
      hw haW hlen hsink hsum hfitB houtB hfitA houtA hgamma
  have hlo : (arun k s (lowerValue logLen loBase sink gammaLo)).regs rAccLo =
      s.regs rAccLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhi : (arun k s (lowerValue logLen loBase sink gammaLo)).regs rAccLoHi =
      s.regs rAccLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simpa only [lowerEndpoint] using
    accumulateValue_run k s (lowerValue logLen loBase sink gammaLo)
      rIlo rAccLo rAccLoHi acc endpoint hv hlo hhi hrep hw hincLo hincHi
      (by exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩) (by decide) (by decide)

theorem upperEndpoint_run (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccHi) (s.regs rAccHiHi) acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hfitB : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rQHi)).2 < 2 ^ 32)
    (houtB : mulUpper (s.regs rPHi) (s.regs rQHi) < M)
    (hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rPLo)).2 < 2 ^ 32)
    (houtA : mulLower (s.regs rPLo) (s.regs rPLo) < M)
    (hgamma : gammaHi < LeanCompCert.Verified.MulWide.B64)
    (hincLo :
      -(Section413Cells.H63 : Int) ≤
        ((if s.regs sShapeRest = 1 then
          -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
        else if s.regs sShapeTail = 1 then
          2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
        else 0) + (gammaHi : Int)))
    (hincHi :
      ((if s.regs sShapeRest = 1 then
          -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
        else if s.regs sShapeTail = 1 then
          2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
        else 0) + (gammaHi : Int)) < (Section413Cells.H63 : Int)) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
      else 0) + (gammaHi : Int)
    let out := arun k s (upperEndpoint logLen hiBase sink gammaHi)
    out.regs rIhi = Section413Cells.encodeZ endpoint ∧
      WideSigned.rep (out.regs rAccHi) (out.regs rAccHiHi)
        (acc + endpoint) := by
  dsimp only
  let endpoint : Int :=
    (if s.regs sShapeRest = 1 then
      -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
    else if s.regs sShapeTail = 1 then
      2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
    else 0) + (gammaHi : Int)
  have hv : (arun k s (upperValue logLen hiBase sink gammaHi)).regs rY =
      Section413Cells.encodeZ endpoint := by
    simpa only [endpoint] using upperValue_run k s logLen hiBase sink gammaHi
      hw haW hlen hsink hsum hfitB houtB hfitA houtA hgamma
  have hlo : (arun k s (upperValue logLen hiBase sink gammaHi)).regs rAccHi =
      s.regs rAccHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhi : (arun k s (upperValue logLen hiBase sink gammaHi)).regs rAccHiHi =
      s.regs rAccHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simpa only [upperEndpoint] using
    accumulateValue_run k s (upperValue logLen hiBase sink gammaHi)
      rIhi rAccHi rAccHiHi acc endpoint hv hlo hhi hrep hw hincLo hincHi
      (by exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩) (by decide) (by decide)

theorem endpoints_wf (logLen loBase hiBase sink gammaLo gammaHi : Nat) :
    (lowerEndpoint logLen loBase sink gammaLo).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true ∧
    (upperEndpoint logLen hiBase sink gammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  have hOld := exactEndpointAssembly_wf logLen loBase hiBase sink gammaLo gammaHi
  have hLower340 : (lowerValue logLen loBase sink gammaLo).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
    have h := hOld.1
    change ((lowerValue logLen loBase sink gammaLo ++ movReg rIlo rY ++
      accumulateLo).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true) at h
    simp only [List.all_append, Bool.and_eq_true] at h
    exact h.1.1
  have hUpper340 : (upperValue logLen hiBase sink gammaHi).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
    have h := hOld.2
    change ((upperValue logLen hiBase sink gammaHi ++ movReg rIhi rY ++
      accumulateHi).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true) at h
    simp only [List.all_append, Bool.and_eq_true] at h
    exact h.1.1
  have hLower := all_ainstrWFB_mono (show 340 ≤ 384 by decide) hLower340
  have hUpper := all_ainstrWFB_mono (show 340 ≤ 384 by decide) hUpper340
  constructor
  · rw [lowerEndpoint, List.all_append, List.all_append, hLower]
    rw [WideSigned.addSigned64Block_wf 384 rAccLo rAccLoHi rY rExt rSign rCarry
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  · rw [upperEndpoint, List.all_append, List.all_append, hUpper]
    rw [WideSigned.addSigned64Block_wf 384 rAccHi rAccHiHi rY rExt rSign rCarry
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl

end LeanCompCert.Ports.RamareCombined100M.WideEndpoint
