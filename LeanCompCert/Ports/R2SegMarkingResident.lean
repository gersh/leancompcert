import LeanCompCert.Ports.R2SegMarkingPrelude

/-! # Complete resident-hit array semantics for `R₂*` marking -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markResidentBody (c : R2Cfg) : List AInstr :=
  markAddressCellBody c ++ markAdvanceStepBody c

def markFullBody (c : R2Cfg) : List AInstr :=
  markPreludeBody c ++ markResidentBody c

theorem markResidentBody_eq_suffix (c : R2Cfg) :
    c.markBody.drop 23 = markResidentBody c := by
  rfl

theorem markFullBody_eq_markBody (c : R2Cfg) :
    markFullBody c = c.markBody := by
  rfl

/-- The post-store cursor suffix is array-free, so an active resident hit has
the logical `markPower` array effect across all 78 remaining instructions. -/
theorem markResidentBody_markPower_run (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen j = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr j + markBit (s.arr j = 0)) * p < M)
    (hlsum : s.arr (j + c.segLen) + wt < M)
    (hweights : s.arr (j + 2 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s (markResidentBody c)
    out.arr =
      (writePlaneWordsAt s c.segLen j
        ((x.markPower p wt first).encode)).arr := by
  let hit := arun k s (markAddressCellBody c)
  have hhit := markAddressCellBody_markPower_run c k s x j p wt first
    hL hj hactive hjL haddr hloaded hx hp hwt hfirst hp0 hpM hwtBound
    hprod hlsum hweights
  dsimp only at hhit
  have hframe : (arun k hit (markAdvanceStepBody c)).arr = hit.arr := by
    rw [markAdvanceStepBody_eq_advance]
    exact markAdvanceBody_arr_frame c k hit
  simp only [markResidentBody, arun_append]
  exact hframe.trans hhit

/-- A cursor past the window updates only the three scratch sinks across the
complete address/cell/cursor suffix. -/
theorem markResidentBody_past_run (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : c.segLen ≤ j) (haddr : 5 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * p < M)
    (hlsum : s.arr (4 * c.segLen) + wt < M)
    (hweights : s.arr (5 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s (markResidentBody c)
    out.arr =
      (writePlaneWordsAt s c.segLen (3 * c.segLen)
        ((x.markPower p wt first).encode)).arr := by
  let hit := arun k s (markAddressCellBody c)
  have hhit := markAddressCellBody_past_run c k s x j p wt first hL hj
    hactive hjL haddr hloaded hx hp hwt hfirst hp0 hpM hwtBound hprod
    hlsum hweights
  dsimp only at hhit
  have hframe : (arun k hit (markAdvanceStepBody c)).arr = hit.arr := by
    rw [markAdvanceStepBody_eq_advance]
    exact markAdvanceBody_arr_frame c k hit
  simp only [markResidentBody, arun_append]
  exact hframe.trans hhit

/-- Consequently every resident plane word (all addresses below `3L`) is
framed by an out-of-window marking suffix. -/
theorem markResidentBody_past_live_frame (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt a : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : c.segLen ≤ j) (haddr : 5 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * p < M)
    (hlsum : s.arr (4 * c.segLen) + wt < M)
    (hweights : s.arr (5 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M)
    (ha : a < 3 * c.segLen) :
    (arun k s (markResidentBody c)).arr a = s.arr a := by
  have hrun := markResidentBody_past_run c k s x j p wt first hL hj
    hactive hjL haddr hloaded hx hp hwt hfirst hp0 hpM hwtBound hprod
    hlsum hweights
  dsimp only at hrun
  rw [hrun]
  simp only [writePlaneWordsAt]
  rw [AState.writeArr_arr_ne _ _ (by omega),
    AState.writeArr_arr_ne _ _ (by omega),
    AState.writeArr_arr_ne _ _ (by omega)]

/-- At a window boundary, the complete literal `markBody` installs the first
table entry and performs its resident logical hit. -/
theorem markFullBody_start_resident_run (c : R2Cfg) (k : Nat) (s : AState)
    (w : Nat) (x : MarkCell)
    (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hT0 : 0 < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M)
    (hL : 0 < c.segLen)
    (hjL : resetOffset c.q0 w < c.segLen)
    (haddr : resetOffset c.q0 w + 2 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (resetOffset c.q0 w) = x.encode)
    (hx : x.Inv) (hwtBound : c.w0 < 2 ^ wtBits)
    (hprod : (s.arr (resetOffset c.q0 w) +
      markBit (s.arr (resetOffset c.q0 w) = 0)) * c.q0 < M)
    (hlsum : s.arr (resetOffset c.q0 w + c.segLen) + c.w0 < M)
    (hweights : s.arr (resetOffset c.q0 w + 2 * c.segLen) +
      markWeightAdd x.count c.w0 < M) :
    let out := arun k s c.markBody
    out.arr =
      (writePlaneWordsAt s c.segLen (resetOffset c.q0 w)
        ((x.markPower c.q0 c.w0 true).encode)).arr := by
  let pre := arun k s (markPreludeBody c)
  have hpre := markPreludeBody_start_run c k s w hr hw hT0 hperiod
    hq0 hq0M hw0M
  dsimp only at hpre
  rcases hpre with
    ⟨h8, _h14, _h9, _h15, _hpi, hq, hbp, hwt, hfs, hj,
      _hr, _hw, harr0⟩
  have hresident := markResidentBody_markPower_run c k pre x
    (resetOffset c.q0 w) c.q0 c.w0 true hL hj h8 hjL haddr
    (by rw [planeWordsAt, harr0]; exact hloaded) hx hbp hwt
    (by simpa using hfs) hq0 hq0M hwtBound
    (by rw [harr0]; exact hprod)
    (by rw [harr0]; exact hlsum)
    (by rw [harr0]; simpa using hweights)
  dsimp only at hresident
  change pre.arr = s.arr at harr0
  have hwrite :
      (writePlaneWordsAt pre c.segLen (resetOffset c.q0 w)
        ((x.markPower c.q0 c.w0 true).encode)).arr =
      (writePlaneWordsAt s c.segLen (resetOffset c.q0 w)
        ((x.markPower c.q0 c.w0 true).encode)).arr := by
    simp [writePlaneWordsAt, AState.writeArr, harr0]
  rw [← markFullBody_eq_markBody]
  simpa only [markFullBody, arun_append] using hresident.trans hwrite

/-- Away from a window boundary, the complete literal `markBody` preserves
the incoming cursor through its prelude and performs its resident logical
hit. -/
theorem markFullBody_nonstart_resident_run (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (r j p wt : Nat) (first : Bool)
    (hr : s.regs rR = r) (hr0 : r ≠ 0) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQ < M)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M) (hjM : s.regs rJ < M)
    (hL : 0 < c.segLen) (hj : s.regs rJ = j)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen j = x.encode) (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M) (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr j + markBit (s.arr j = 0)) * p < M)
    (hlsum : s.arr (j + c.segLen) + wt < M)
    (hweights : s.arr (j + 2 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s c.markBody
    out.arr =
      (writePlaneWordsAt s c.segLen j
        ((x.markPower p wt first).encode)).arr := by
  let pre := arun k s (markPreludeBody c)
  have hpre := markPreludeBody_nonstart_run c k s r hr hr0 hrT hperiod
    hq0 hq0M hpiM hqM hbpM hwtM hfsM hjM
  dsimp only at hpre
  rcases hpre with
    ⟨h8, _h14, _h9, _h15, _hpi, _hq, hbp, hwt', hfs, hj',
      _hr, _hw, harr0⟩
  have hresident := markResidentBody_markPower_run c k pre x j p wt first
    hL (hj'.trans hj) h8 hjL haddr
    (by rw [planeWordsAt, harr0]; exact hloaded) hx
    (hbp.trans hp) (hwt'.trans hwt) (hfs.trans hfirst)
    hp0 hpM hwtBound
    (by rw [harr0]; exact hprod)
    (by rw [harr0]; exact hlsum)
    (by rw [harr0]; exact hweights)
  dsimp only at hresident
  change pre.arr = s.arr at harr0
  have hwrite :
      (writePlaneWordsAt pre c.segLen j
        ((x.markPower p wt first).encode)).arr =
      (writePlaneWordsAt s c.segLen j
        ((x.markPower p wt first).encode)).arr := by
    simp [writePlaneWordsAt, AState.writeArr, harr0]
  rw [← markFullBody_eq_markBody]
  simpa only [markFullBody, arun_append] using hresident.trans hwrite

/-- At a window boundary whose first multiple is already past this short
window, the complete `markBody` touches only the sinks and frames every live
plane address. -/
theorem markFullBody_start_past_live_frame (c : R2Cfg) (k : Nat)
    (s : AState) (w a : Nat) (x : MarkCell)
    (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hT0 : 0 < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M)
    (hL : 0 < c.segLen)
    (hjL : c.segLen ≤ resetOffset c.q0 w)
    (haddr : 5 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = x.encode)
    (hx : x.Inv) (hwtBound : c.w0 < 2 ^ wtBits)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * c.q0 < M)
    (hlsum : s.arr (4 * c.segLen) + c.w0 < M)
    (hweights : s.arr (5 * c.segLen) +
      markWeightAdd x.count c.w0 < M)
    (ha : a < 3 * c.segLen) :
    (arun k s c.markBody).arr a = s.arr a := by
  let pre := arun k s (markPreludeBody c)
  have hpre := markPreludeBody_start_run c k s w hr hw hT0 hperiod
    hq0 hq0M hw0M
  dsimp only at hpre
  rcases hpre with
    ⟨h8, _h14, _h9, _h15, _hpi, _hq, hbp, hwt, hfs, hj,
      _hr, _hw, harr0⟩
  have hframe := markResidentBody_past_live_frame c k pre x
    (resetOffset c.q0 w) c.q0 c.w0 a true hL hj h8 hjL haddr
    (by rw [planeWordsAt, harr0]; exact hloaded) hx hbp hwt
    (by simpa using hfs) hq0 hq0M hwtBound
    (by rw [harr0]; exact hprod)
    (by rw [harr0]; exact hlsum)
    (by rw [harr0]; simpa using hweights) ha
  rw [← markFullBody_eq_markBody]
  simp only [markFullBody, arun_append]
  exact hframe.trans (congrFun harr0 a)

/-- On every later past-window marking round, the complete `markBody` also
frames every live plane address. -/
theorem markFullBody_nonstart_past_live_frame (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (r j p wt a : Nat) (first : Bool)
    (hr : s.regs rR = r) (hr0 : r ≠ 0) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQ < M)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M) (hjM : s.regs rJ < M)
    (hL : 0 < c.segLen) (hj : s.regs rJ = j)
    (hjL : c.segLen ≤ j) (haddr : 5 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M) (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * p < M)
    (hlsum : s.arr (4 * c.segLen) + wt < M)
    (hweights : s.arr (5 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M)
    (ha : a < 3 * c.segLen) :
    (arun k s c.markBody).arr a = s.arr a := by
  let pre := arun k s (markPreludeBody c)
  have hpre := markPreludeBody_nonstart_run c k s r hr hr0 hrT hperiod
    hq0 hq0M hpiM hqM hbpM hwtM hfsM hjM
  dsimp only at hpre
  rcases hpre with
    ⟨h8, _h14, _h9, _h15, _hpi, _hq, hbp, hwt', hfs, hj',
      _hr, _hw, harr0⟩
  have hframe := markResidentBody_past_live_frame c k pre x j p wt a first
    hL (hj'.trans hj) h8 hjL haddr
    (by rw [planeWordsAt, harr0]; exact hloaded) hx
    (hbp.trans hp) (hwt'.trans hwt) (hfs.trans hfirst)
    hp0 hpM hwtBound
    (by rw [harr0]; exact hprod)
    (by rw [harr0]; exact hlsum)
    (by rw [harr0]; exact hweights) ha
  rw [← markFullBody_eq_markBody]
  simp only [markFullBody, arun_append]
  exact hframe.trans (congrFun harr0 a)

#print axioms markResidentBody_eq_suffix
#print axioms markFullBody_eq_markBody
#print axioms markResidentBody_markPower_run
#print axioms markResidentBody_past_run
#print axioms markResidentBody_past_live_frame
#print axioms markFullBody_start_resident_run
#print axioms markFullBody_nonstart_resident_run
#print axioms markFullBody_start_past_live_frame
#print axioms markFullBody_nonstart_past_live_frame

end LeanCompCert.Ports.R2SegSieve
