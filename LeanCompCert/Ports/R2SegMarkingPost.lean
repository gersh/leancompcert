import LeanCompCert.Ports.R2SegMarkingTail

/-! # Post-mark schedule semantics for an `R₂*` marking round -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

/-- The classifier, disabled logarithm block, and loop tail that follow the
marking instruction block in one scheduled machine round. -/
def markPostBody (c : R2Cfg) : List AInstr :=
  c.classBody ++ c.logBody ++ c.tailBody

theorem body_eq_mark_post (c : R2Cfg) :
    c.body = c.markBody ++ markPostBody c := by
  rfl

set_option maxRecDepth 2000 in
/-- In a marking round, the complete post-mark schedule frames the live mark
cell and persistent marking state, clears the classifier scratch sinks, and
advances the round position exactly once. -/
theorem markPostBody_run (c : R2Cfg) (k : Nat) (s : AState) (a : Nat)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (h9 : s.regs 9 = 0) (h15 : s.regs 15 = 0)
    (hzero : s.regs rZero = 0)
    (hrT : r < c.markSteps) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hwM : w < M)
    (h5 : 5 * c.segLen < M) (hsink1 : c.streamSink + 1 < M)
    (hviol : s.regs rViol < M) (hvcap : s.regs rVCap < M)
    (hvdrain : s.regs rVDrain < M) (hwc : s.regs rWc < M)
    (hec : s.regs rEc < M)
    (ha3 : a ≠ 3 * c.segLen) (ha4 : a ≠ 4 * c.segLen)
    (ha5 : a ≠ 5 * c.segLen)
    (ha0 : a ≠ c.streamSink) (ha1 : a ≠ c.streamSink + 1) :
    let out := arun k s (markPostBody c)
    out.arr a = s.arr a ∧ out.arr (3 * c.segLen) = 0 ∧
      out.arr (4 * c.segLen) = 0 ∧ out.arr (5 * c.segLen) = 0 ∧
      out.regs rPi = s.regs rPi ∧ out.regs rQ = s.regs rQ ∧
      out.regs rBp = s.regs rBp ∧ out.regs rWt = s.regs rWt ∧
      out.regs rFs = s.regs rFs ∧ out.regs rJ = s.regs rJ ∧
      out.regs rR = r + 1 ∧ out.regs rW = w ∧
      out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark ∧
      out.regs rVCap = s.regs rVCap ∧
      out.regs rVDrain = s.regs rVDrain ∧
      out.regs rWc = s.regs rWc ∧ out.regs rEc = s.regs rEc ∧
      out.regs rK = 0 := by
  let classified := arun k s c.classBody
  have hc := classBody_mark_frame c k s a h9 hzero h5 hsink1
    hviol hvcap hwc ha3 ha4 ha5 ha0 ha1
  dsimp only at hc
  rcases hc with ⟨hcA, hc3, hc4, hc5, hcPi, hcQ, hcBp, hcWt, hcFs,
    hcJ, hcR, hcW, hcViol, hcVMark, hcVCap, hcWc⟩
  have classFrame (x : Nat) (h : writes x c.classBody = false) :
      classified.regs x = s.regs x :=
    arun_frame k x c.classBody h s
  have hc15 : classified.regs 15 = 0 :=
    (classFrame 15 (by rfl)).trans h15
  have hcVDrain : classified.regs rVDrain = s.regs rVDrain :=
    classFrame rVDrain (by rfl)
  have hcEc : classified.regs rEc = s.regs rEc :=
    classFrame rEc (by rfl)
  let logged := arun k classified c.logBody
  have hl := logBody_mark_frame c k classified hc15
    (by rw [hcViol]; exact hviol) (by rw [hcEc]; exact hec)
  dsimp only at hl
  rcases hl with ⟨hlA, hlPi, hlQ, hlBp, hlWt, hlFs, hlJ, hlR, hlW,
    hlViol, hlVMark, hlVCap, hlWc, hlEc, hlK⟩
  have logFrame (x : Nat) (h : writes x c.logBody = false) :
      logged.regs x = classified.regs x :=
    arun_frame k x c.logBody h classified
  have hlVDrain : logged.regs rVDrain = s.regs rVDrain :=
    (logFrame rVDrain (by rfl)).trans hcVDrain
  have hlEcS : logged.regs rEc = s.regs rEc := hlEc.trans hcEc
  have hzeroM : 0 < M := by decide
  have ht := tailBody_mark_run c k logged r w
    (hlR.trans (hcR.trans hr)) (hlW.trans (hcW.trans hw)) hrT hL
    hperiod hwM
    (by rw [hlViol, hcViol]; exact hviol)
    (by rw [hlVDrain]; exact hvdrain)
    (by rw [hlWc, hcWc]; exact hwc)
    (by rw [hlEcS]; exact hec) (by rw [hlK]; exact hzeroM)
  dsimp only at ht
  rcases ht with ⟨htA, htPi, htQ, htBp, htWt, htFs, htJ, htR, htW,
    htViol, htVMark, htVCap, htVDrain, htWc, htEc, htK⟩
  rw [markPostBody, arun_append, arun_append]
  exact ⟨
    (congrFun htA a).trans ((congrFun hlA a).trans hcA),
    (congrFun htA (3 * c.segLen)).trans
      ((congrFun hlA (3 * c.segLen)).trans hc3),
    (congrFun htA (4 * c.segLen)).trans
      ((congrFun hlA (4 * c.segLen)).trans hc4),
    (congrFun htA (5 * c.segLen)).trans
      ((congrFun hlA (5 * c.segLen)).trans hc5),
    htPi.trans (hlPi.trans hcPi), htQ.trans (hlQ.trans hcQ),
    htBp.trans (hlBp.trans hcBp), htWt.trans (hlWt.trans hcWt),
    htFs.trans (hlFs.trans hcFs), htJ.trans (hlJ.trans hcJ),
    htR, htW, htViol.trans (hlViol.trans hcViol),
    htVMark.trans (hlVMark.trans hcVMark),
    htVCap.trans (hlVCap.trans hcVCap), htVDrain.trans hlVDrain,
    htWc.trans (hlWc.trans hcWc), htEc.trans hlEcS, htK.trans hlK⟩

#print axioms body_eq_mark_post
#print axioms markPostBody_run

end LeanCompCert.Ports.R2SegSieve
