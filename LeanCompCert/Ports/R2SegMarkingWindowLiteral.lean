import LeanCompCert.Ports.R2SegMarkingWindowModel

/-!
# Literal compiled marking step refines the pure window model

This file removes the last abstract seam for a non-boundary resident marking
round.  The hypotheses are precisely the arithmetic room conditions used by
the literal 101-instruction block; the conclusion is the compact whole-window
representation used by the finite telescope.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.Reflect

/-- At a window boundary the literal prelude installs the initial cursor and
the resident suffix performs exactly its first pure window step.  Only the
cell planes, not the stale incoming cursor registers, represent the new
window before this reset. -/
theorem markBody_start_resident_refines_window
    (c : R2Cfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : R2MarkWindow)
    (hCells : w.CellsRep c s)
    (hInit : w.cursor =
      { pi := 0, power := c.q0, base := c.q0, weight := c.w0,
        first := 1, offset := resetOffset c.q0 windowBase })
    (hr : s.regs rR = 0) (hw : s.regs rW = windowBase)
    (hT0 : 0 < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M)
    (hL : 0 < c.segLen)
    (hResident : resetOffset c.q0 windowBase < c.segLen)
    (haddr : resetOffset c.q0 windowBase + 2 * c.segLen < M)
    (hCell : (w.cells (resetOffset c.q0 windowBase)).Inv)
    (hwtBound : c.w0 < 2 ^ wtBits)
    (hprod : (s.arr (resetOffset c.q0 windowBase) +
      markBit (s.arr (resetOffset c.q0 windowBase) = 0)) * c.q0 < M)
    (hlsum : s.arr (resetOffset c.q0 windowBase + c.segLen) + c.w0 < M)
    (hweights : s.arr (resetOffset c.q0 windowBase + 2 * c.segLen) +
      markWeightAdd (w.cells (resetOffset c.q0 windowBase)).count c.w0 < M)
    (hmul : c.q0 * c.q0 < M) (hhi : c.hi < M)
    (htableAddr : c.tableBase < M)
    (hword : (arun k (arun k s (markPreludeBody c))
      (markAddressCellBody c)).arr c.tableBase < M)
    (hjQ : resetOffset c.q0 windowBase + c.q0 < M)
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure 0 0 < M)
    (hvmark : s.regs rVMark + c.budgetFailure 0 0 < M) :
    (w.step c windowBase tableWord).Rep c (arun k s c.markBody) := by
  let j := resetOffset c.q0 windowBase
  let out := arun k s c.markBody
  have hloaded : planeWordsAt s c.segLen j = (w.cells j).encode :=
    hCells j hResident
  have hArray := markFullBody_start_resident_run c k s windowBase
    (w.cells j) hr hw hT0 hperiod hq0 hq0M hw0M hL hResident haddr
    hloaded hCell hwtBound hprod hlsum hweights
  dsimp only at hArray
  have hRegs := markFullBody_start_resident_cursor_run c k s windowBase
    hr hw hT0 hperiod hq0 hq0M hw0M hResident haddr hmul hhi
    htableAddr hword hjQ hK hL1 hviol hvmark
  dsimp only at hRegs
  have hCursor : R2MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord := by
    rw [show w.cursor.step c windowBase tableWord =
        { w.cursor with offset := w.cursor.offset + w.cursor.power } by
      simp [R2MarkCursor.step, hInit, hResident]]
    apply R2MarkCursor.ext
    · simpa [R2MarkCursor.ofState, out, hInit] using hRegs.2.2.2.2.2.1
    · simpa [R2MarkCursor.ofState, out, hInit] using hRegs.1
    · simpa [R2MarkCursor.ofState, out, hInit] using hRegs.2.1
    · simpa [R2MarkCursor.ofState, out, hInit] using hRegs.2.2.1
    · simpa [R2MarkCursor.ofState, out, hInit] using hRegs.2.2.2.1
    · simpa [R2MarkCursor.ofState, out, hInit, j] using
        hRegs.2.2.2.2.1
  constructor
  · exact hCursor
  · apply hCells.residentStep hL (by simpa [hInit, j] using hResident)
    simpa [out, hInit, j] using hArray

/-- A non-boundary resident execution of the literal `markBody` is one exact
step of `R2MarkWindow`.  In particular, this theorem combines the independently
proved three-plane store and six-register cursor theorems; it does not execute
the instruction list in the kernel. -/
theorem markBody_nonstart_resident_refines_window
    (c : R2Cfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : R2MarkWindow) (first : Bool)
    (hRep : w.Rep c s) (hBounds : w.cursor.Bounds c)
    (hResident : w.cursor.offset < c.segLen)
    (hRound0 : s.regs rR ≠ 0) (hRound : s.regs rR < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : w.cursor.pi < M) (hqM : w.cursor.power < M)
    (hbpM : w.cursor.base < M) (hwtM : w.cursor.weight < M)
    (hfsM : w.cursor.first < M) (hjM : w.cursor.offset < M)
    (haddr : w.cursor.offset + 2 * c.segLen < M)
    (hmul : w.cursor.power * w.cursor.base < M) (hhi : c.hi < M)
    (htableAddr : w.cursor.pi + c.tableBase < M)
    (hword : (arun k (arun k s (markPreludeBody c))
      (markAddressCellBody c)).arr (w.cursor.pi + c.tableBase) < M)
    (hjQ : w.cursor.offset + w.cursor.power < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL : 0 < c.segLen) (hL1 : c.segLen + 1 < M)
    (hFirst : w.cursor.first = if first then 1 else 0)
    (hprod : (s.arr w.cursor.offset +
      markBit (s.arr w.cursor.offset = 0)) * w.cursor.base < M)
    (hlsum : s.arr (w.cursor.offset + c.segLen) + w.cursor.weight < M)
    (hweights : s.arr (w.cursor.offset + 2 * c.segLen) +
      (if first then
        markWeightAdd (w.cells w.cursor.offset).count w.cursor.weight
      else 0) < M)
    (hviol : s.regs rViol +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hCell : (w.cells w.cursor.offset).Inv) :
    (w.step c windowBase tableWord).Rep c (arun k s c.markBody) := by
  have hpi : s.regs rPi = w.cursor.pi := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.pi hRep.1
  have hq : s.regs rQ = w.cursor.power := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.power hRep.1
  have hbp : s.regs rBp = w.cursor.base := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.base hRep.1
  have hwt : s.regs rWt = w.cursor.weight := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.weight hRep.1
  have hfs : s.regs rFs = w.cursor.first := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.first hRep.1
  have hj : s.regs rJ = w.cursor.offset := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.offset hRep.1
  let out := arun k s c.markBody
  have hArray := markFullBody_nonstart_resident_run c k s
    (w.cells w.cursor.offset) (s.regs rR) w.cursor.offset w.cursor.base
    w.cursor.weight first rfl hRound0 hRound hperiod hq0 hq0M
    (by simpa [hpi] using hpiM) (by simpa [hq] using hqM)
    (by simpa [hbp] using hbpM) (by simpa [hwt] using hwtM)
    (by simpa [hfs] using hfsM) (by simpa [hj] using hjM)
    hL hj hResident haddr (hRep.2 w.cursor.offset hResident) hCell
    hbp hwt (hfs.trans hFirst) hBounds.base_pos hbpM hBounds.weight_lt
    hprod hlsum hweights
  dsimp only at hArray
  have hRegs := markFullBody_nonstart_resident_cursor_run c k s
    (s.regs rR) rfl hRound0 hRound hperiod hq0 hq0M
    (by simpa [hpi] using hpiM) (by simpa [hpi] using hBounds.pi_le)
    (by simpa [hq] using hqM)
    (by simpa [hq] using Nat.ne_of_gt hBounds.power_pos)
    (by simpa [hbp] using hbpM) (by simpa [hwt] using hwtM)
    (by simpa [hfs] using hfsM) (by simpa [hj] using hjM)
    (by simpa [hj] using hResident) (by simpa [hj] using haddr)
    (by simpa [hq, hbp] using hmul) hhi
    (by simpa [hpi] using htableAddr)
    (by simpa [hpi] using hword)
    (by simpa [hj, hq] using hjQ) hT hK hL1 hviol hvmark
  dsimp only at hRegs
  have hCursor : R2MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord := by
    rw [← hRep.1]
    apply residentResult_refines_cursor c windowBase tableWord s out
    · simpa [hj] using hResident
    · exact hRegs.1
    · exact hRegs.2.1
    · exact hRegs.2.2.1
    · exact hRegs.2.2.2.1
    · exact hRegs.2.2.2.2.1
    · exact hRegs.2.2.2.2.2.1
  apply R2MarkWindow.Rep.residentStep hL hRep hResident hCursor
  cases first <;> simp_all [out]

/-- The literal post-prelude suffix in the past-window branch advances the
pure cursor, leaves every live marking plane unchanged, and may write only to
the three designated sink cells.  `hTable` identifies the compiled load with
the abstract packed table used by `R2MarkWindow.step`. -/
theorem markResidentBody_past_refines_window
    (c : R2Cfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : R2MarkWindow) (sinkCell : MarkCell) (first : Bool)
    (hRep : w.Rep c s) (hBounds : w.cursor.Bounds c)
    (hTableBounds : R2MarkTableBounds c tableWord)
    (hTableRep : R2MarkTableRep c tableWord s)
    (hTableWord : ∀ i, i ≤ c.tableLen → tableWord i < M)
    (hPast : c.segLen ≤ w.cursor.offset) (hw : s.regs rW = windowBase)
    (hactive : s.regs 8 = 1)
    (hL : 0 < c.segLen) (hsink : 5 * c.segLen < M)
    (hmul : w.cursor.power * w.cursor.base < M)
    (hhi0 : 0 < c.hi) (hhi : c.hi < M) (hwtWord : 2 ^ wtBits < M)
    (hsum : s.regs rPi + c.stepPrime 1 1
      (s.regs rQ) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp)) +
        c.tableBase < M)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))) < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = sinkCell.encode)
    (hCell : sinkCell.Inv)
    (hFirst : w.cursor.first = if first then 1 else 0)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * w.cursor.base < M)
    (hlsum : s.arr (4 * c.segLen) + w.cursor.weight < M)
    (hweights : s.arr (5 * c.segLen) +
      (if first then markWeightAdd sinkCell.count w.cursor.weight else 0) < M) :
    (w.step c windowBase tableWord).Rep c
      (arun k s (markResidentBody c)) := by
  have hq : s.regs rQ = w.cursor.power := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.power hRep.1
  have hbp : s.regs rBp = w.cursor.base := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.base hRep.1
  have hwt : s.regs rWt = w.cursor.weight := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.weight hRep.1
  have hfs : s.regs rFs = w.cursor.first := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.first hRep.1
  have hj : s.regs rJ = w.cursor.offset := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.offset hRep.1
  have hpi : s.regs rPi = w.cursor.pi := by
    simpa [R2MarkCursor.ofState] using congrArg R2MarkCursor.pi hRep.1
  let piOut := clampPi c.tableLen
    (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
  have hpiOut : piOut ≤ c.tableLen := by
    simp only [piOut, clampPi]
    split <;> omega
  have hhit := markAddressCellBody_past_run c k s sinkCell w.cursor.offset
    w.cursor.base w.cursor.weight first hL hj hactive hPast hsink hloaded
    hCell hbp hwt (hfs.trans hFirst) hBounds.base_pos
    (Nat.lt_of_le_of_lt hBounds.base_le hhi) hBounds.weight_lt
    hprod hlsum hweights
  dsimp only at hhit
  have hTable : (arun k s (markAddressCellBody c)).arr
      (piOut + c.tableBase) = tableWord piOut := by
    rw [hhit]
    rw [writePlaneWordsAt_table_frame c s (3 * c.segLen)
      ((sinkCell.markPower w.cursor.base w.cursor.weight first).encode)
      (by simp only [R2Cfg.tableBase]; omega)]
    exact hTableRep piOut hpiOut
  have hword : (arun k s (markAddressCellBody c)).arr
      (piOut + c.tableBase) < M := by
    rw [hTable]
    exact hTableWord piOut hpiOut
  have hguards := hBounds.past_output_guards (windowBase := windowBase)
    hPast hTableBounds hhi0 hhi hwtWord
  dsimp only at hguards
  rcases hguards with ⟨hqOut, hqOut0, hbpOut, hwtOut, hfsOut⟩
  change (arun k s (markAddressCellBody c)).arr
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp)) +
          c.tableBase) =
      tableWord (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))) at hTable
  change (arun k s (markAddressCellBody c)).arr
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1 (s.regs rQ) (s.regs rBp)) +
          c.tableBase) < M at hword
  rw [← hq, ← hbp, ← hpi, ← hTable] at hqOut hqOut0 hbpOut
  rw [← hq, ← hbp, ← hpi, ← hwt, ← hTable] at hwtOut
  rw [← hq, ← hbp, ← hfs] at hfsOut
  let out := arun k s (markResidentBody c)
  have hrun := markResidentBody_past_cursor_run c k s w.cursor.offset
    hj hactive hPast hsink (by simpa [hq, hbp] using hmul) hhi hsum hK
    haddr hword hjQ hqOut hqOut0 hbpOut hwtOut hfsOut hT hL1 hviol hvmark
  dsimp only at hrun
  have hLive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a := by
    intro a ha
    exact markResidentBody_past_live_frame c k s sinkCell w.cursor.offset
      w.cursor.base w.cursor.weight a first hL hj hactive hPast hsink hloaded
      hCell hbp hwt (hfs.trans hFirst) hBounds.base_pos
      (Nat.lt_of_le_of_lt hBounds.base_le hhi) hBounds.weight_lt
      hprod hlsum hweights ha
  rcases hrun with
    ⟨oq, obp, owt, ofs, oj, opi, _ow, _orr, _ov, _ovm, _oarr⟩
  dsimp only [out] at oq obp owt ofs oj opi hLive
  rw [hTable] at oq obp owt oj
  rw [hw] at oj
  apply hRep.pastComponentsStep hPast hBounds.pi_le oq obp owt ofs oj opi hLive

#print axioms markBody_nonstart_resident_refines_window
#print axioms markResidentBody_past_refines_window
#print axioms markBody_start_resident_refines_window

end LeanCompCert.Ports.R2SegSieve
