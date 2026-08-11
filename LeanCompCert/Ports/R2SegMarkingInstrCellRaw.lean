import LeanCompCert.Ports.R2SegMarkingInstrWeight
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Literal three-plane marking-cell refinement

This module composes the separately checked product, logarithmic-sum, and
packed-weight stages.  The proof keeps the three array writes abstract and
uses register-frame lemmas between stages, avoiding normalization of the
complete 22-instruction stream.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- Read the three physical words addressed by registers 30--32. -/
def loadedPlaneWords (s : AState) : PlaneWords :=
  ⟨s.arr (s.regs 30), s.arr (s.regs 31), s.arr (s.regs 32)⟩

/-- Write a physical three-plane cell back to the addressed array. -/
def writeLoadedPlaneWords (s : AState) (x : PlaneWords) : AState :=
  ((s.writeArr (s.regs 30) x.prod).writeArr
    (s.regs 31) x.lsum).writeArr (s.regs 32) x.weights

/-- The literal production slice implements one raw three-plane update when
the decoded packed count is supplied explicitly.  Distinctness is exactly
the layout fact later discharged from the positive segment length. -/
theorem markCellBody_rawMarkCount_run (k : Nat) (s : AState)
    (d p wt : Nat) (first : Bool)
    (h30ne31 : s.regs 30 ≠ s.regs 31)
    (h30ne32 : s.regs 30 ≠ s.regs 32)
    (h31ne32 : s.regs 31 ≠ s.regs 32)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hcount : s.arr (s.regs 32) >>> 56 = d)
    (hp0 : 0 < p) (hpM : p < M) (hd : d ≤ 3)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (s.regs 30) +
      markBit (s.arr (s.regs 30) = 0)) * p < M)
    (hlsum : s.arr (s.regs 31) + wt < M)
    (hweights : s.arr (s.regs 32) +
      (if first then markWeightAdd d wt else 0) < M) :
    let next := (loadedPlaneWords s).rawMarkCount d p wt first
    let out := arun k s markCellBody
    out.arr = (writeLoadedPlaneWords s next).arr := by
  let s1 := arun k s markProductBody
  let s2 := arun k s1 markLogBody
  have hproduct := markProductBody_run k s p hp hp0 hpM hprod
  dsimp only at hproduct
  rcases hproduct with ⟨harr1, _h36, h30, _hbp⟩
  have frame1 (r : Nat) (h : writes r markProductBody = false) :
      s1.regs r = s.regs r := arun_frame k r markProductBody h s
  have h31 : s1.regs 31 = s.regs 31 := frame1 31 (by rfl)
  have h32 : s1.regs 32 = s.regs 32 := frame1 32 (by rfl)
  have hwt1 : s1.regs rWt = wt :=
    (frame1 rWt (by rfl)).trans hwt
  have hfs1 : s1.regs rFs = if first then 1 else 0 :=
    (frame1 rFs (by rfl)).trans hfirst
  have harr31 : s1.arr (s1.regs 31) = s.arr (s.regs 31) := by
    rw [h31, congrFun harr1 (s.regs 31)]
    exact AState.writeArr_arr_ne s _ h30ne31.symm
  have hlog := markLogBody_run k s1 wt hwt1 (by
    rw [harr31]
    exact hlsum)
  dsimp only at hlog
  rcases hlog with ⟨harr2, _h38, h31', _hwt2⟩
  have frame2 (r : Nat) (h : writes r markLogBody = false) :
      s2.regs r = s1.regs r := arun_frame k r markLogBody h s1
  have h32' : s2.regs 32 = s.regs 32 :=
    (frame2 32 (by rfl)).trans h32
  have hwt2 : s2.regs rWt = wt :=
    (frame2 rWt (by rfl)).trans hwt1
  have hfs2 : s2.regs rFs = if first then 1 else 0 :=
    (frame2 rFs (by rfl)).trans hfs1
  have harr32 : s2.arr (s2.regs 32) = s.arr (s.regs 32) := by
    rw [h32', congrFun harr2 (s.regs 32)]
    rw [AState.writeArr_arr_ne s1 _ (by
      rw [h31]
      exact h31ne32.symm)]
    rw [congrFun harr1 (s.regs 32)]
    exact AState.writeArr_arr_ne s _ h30ne32.symm
  have hweight := markWeightBody_run k s2 d wt first (by
      rw [harr32]
      exact hcount)
    hwt2 hfs2 hd hwtBound (by
      rw [harr32]
      exact hweights)
  dsimp only at hweight
  rcases hweight with ⟨harr3, _h51, _h32out, _hwtout, _hfsout⟩
  simp only [markCellBody, arun_append]
  simp only [AState.writeArr] at harr1 harr2 harr3 ⊢
  rw [h31, harr1] at harr2
  rw [h32', harr2] at harr3
  simp [s1, s2, loadedPlaneWords, PlaneWords.rawMarkCount,
    writeLoadedPlaneWords, AState.writeArr, markWeightAdd,
    h30ne31.symm, h30ne32.symm, h31ne32.symm] at harr3 ⊢
  rw [harr3]
  congr

#print axioms markCellBody_rawMarkCount_run

end LeanCompCert.Ports.R2SegSieve
