import LeanCompCert.Ports.Prop1224CellMarkAddressCellArray
import LeanCompCert.Ports.Prop1224CellMarkCursorPast

/-!
# Literal Proposition 12.2.4 marker refines the pure window step

Theorems in this file compose the separately proved literal array and cursor
results.  Production fuel, the prime table, and the window contents remain
symbolic; the statements only expose the word-arithmetic side conditions that
the compiled instruction block needs.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- One active resident execution of the literal post-prelude suffix is one
exact step of the source window model. -/
theorem p1224MarkResidentBody_resident_refines_window
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow) (first : Bool)
    (hRep : w.Rep c s) (hResident : w.cursor.offset < c.segLen)
    (hactive : s.regs 10 = 1)
    (hL : 0 < c.segLen)
    (haddr : w.cursor.offset + 2 * c.segLen < M)
    (hp2 : 2 ≤ w.cursor.base) (hbpM : w.cursor.base < M)
    (hFirst : w.cursor.first = if first then 1 else 0)
    (hrad : (w.cells w.cursor.offset).radical *
      (if first then w.cursor.base else 1) < M)
    (hphi : (w.cells w.cursor.offset).phiSmall *
      (if first then w.cursor.base - 1 else 1) < M)
    (hsqfBit : (w.cells w.cursor.offset).sqf ≤ 1)
    (hsqf : (w.cells w.cursor.offset).sqf < M)
    (hhi : c.hi < M) (hpiM : w.cursor.pi < M)
    (htableAddr : w.cursor.pi + c.tableBase < M)
    (hword : (arun k s (p1224MarkAddressCellBody c)).arr
      (w.cursor.pi + c.tableBase) < M)
    (hjQ : w.cursor.offset + w.cursor.power < M)
    (hq0 : 0 < w.cursor.power) (hqM : w.cursor.power < M)
    (hfsM : w.cursor.first < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hpiK : w.cursor.pi ≤ c.tableLen)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M) :
    (w.step c windowBase tableWord).Rep c
      (arun k s (p1224MarkResidentBody c)) := by
  have hpi : s.regs rPi = w.cursor.pi := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.pi hRep.1
  have hq : s.regs rQp = w.cursor.power := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.power hRep.1
  have hbp : s.regs rBp = w.cursor.base := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.base hRep.1
  have hfs : s.regs rFs = w.cursor.first := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.first hRep.1
  have hj : s.regs rJ = w.cursor.offset := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.offset hRep.1
  let out := arun k s (p1224MarkResidentBody c)
  have hArray := p1224MarkResidentBody_markPower_run c k s
    (w.cells w.cursor.offset) w.cursor.offset w.cursor.base first hL hj
    hactive hResident haddr (hRep.2 w.cursor.offset hResident) hbp
    (hfs.trans hFirst) hp2 hbpM hrad hphi hsqfBit hsqf
  have hRegs := p1224MarkResidentBody_resident_cursor_run c k s
    w.cursor.offset hj hactive hResident haddr
    (by rw [hbp]; omega) hhi
    (by simpa [hpi] using hpiM) (by simpa [hpi] using hpiK)
    (by simpa [hpi] using htableAddr)
    (by simpa [hpi] using hword)
    (by simpa [hj, hq] using hjQ)
    (by simpa [hq] using Nat.ne_of_gt hq0)
    (by simpa [hq] using hqM) (by simpa [hbp] using hbpM)
    (by simpa [hfs] using hfsM) hT hK hL1 hviol hvmark
  dsimp only at hRegs
  have hCursor : P1224MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord := by
    rw [← hRep.1]
    apply p1224ResidentResult_refines_cursor c windowBase tableWord s out
    · simpa [hj] using hResident
    · exact hRegs.1
    · exact hRegs.2.1
    · exact hRegs.2.2.1
    · exact hRegs.2.2.2.1
    · exact hRegs.2.2.2.2.1
  apply P1224MarkWindow.Rep.residentStep hL hRep hResident hCursor
  cases first <;> simp_all [out]

/-- One active past-window execution advances the abstract cursor, preserves
all live cells, and observes exactly the symbolic resident table. -/
theorem p1224MarkResidentBody_past_refines_window
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (sinkCell : P1224MarkCell) (first : Bool)
    (hRep : w.Rep c s) (hBounds : w.cursor.Bounds c)
    (hTableBounds : P1224MarkTableBounds c tableWord)
    (hTableRep : P1224MarkTableRep c tableWord s)
    (hTableWord : ∀ i, i ≤ c.tableLen → tableWord i < M)
    (hPast : c.segLen ≤ w.cursor.offset)
    (hw : s.regs rW = windowBase) (hactive : s.regs 10 = 1)
    (hL : 0 < c.segLen) (hsink : 6 * c.segLen < M)
    (hroot : c.root ≤ c.hi) (hhi0 : 0 < c.hi) (hhi : c.hi < M)
    (hsum : s.regs rPi + c.p1224StepPrime 1 1
      (s.regs rQp) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime 1 1
        (s.regs rQp) (s.regs rBp)) + c.tableBase < M)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp))) < M)
    (hloaded : p1224PlaneWordsAt s c.segLen (4 * c.segLen) =
      sinkCell.encode)
    (hp2 : 2 ≤ w.cursor.base)
    (hFirst : w.cursor.first = if first then 1 else 0)
    (hrad : sinkCell.radical *
      (if first then w.cursor.base else 1) < M)
    (hphi : sinkCell.phiSmall *
      (if first then w.cursor.base - 1 else 1) < M)
    (hsqfBit : sinkCell.sqf ≤ 1) (hsqf : sinkCell.sqf < M) :
    (w.step c windowBase tableWord).Rep c
      (arun k s (p1224MarkResidentBody c)) := by
  have hq : s.regs rQp = w.cursor.power := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.power hRep.1
  have hbp : s.regs rBp = w.cursor.base := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.base hRep.1
  have hfs : s.regs rFs = w.cursor.first := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.first hRep.1
  have hj : s.regs rJ = w.cursor.offset := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.offset hRep.1
  have hpi : s.regs rPi = w.cursor.pi := by
    simpa [P1224MarkCursor.ofState] using
      congrArg P1224MarkCursor.pi hRep.1
  have hbpM : w.cursor.base < M :=
    Nat.lt_of_le_of_lt (Nat.le_trans hBounds.base_le_root hroot) hhi
  let piOut := p1224ClampPi c.tableLen
    (s.regs rPi + c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
  have hpiOut : piOut ≤ c.tableLen := by
    simp only [piOut, p1224ClampPi]
    split <;> omega
  have hhit := p1224MarkAddressCellBody_past_run c k s sinkCell
    w.cursor.offset w.cursor.base first hL hj hactive hPast hsink hloaded
    hbp (hfs.trans hFirst) hp2 hbpM hrad hphi hsqfBit hsqf
  have hTable : (arun k s (p1224MarkAddressCellBody c)).arr
      (piOut + c.tableBase) = tableWord piOut := by
    rw [hhit]
    rw [writeP1224PlaneWordsAt_table_frame c s (4 * c.segLen)
      ((sinkCell.markPower w.cursor.base first).encode)
      (by simp only [CellCfg.tableBase]; omega)]
    exact hTableRep piOut hpiOut
  have hword : (arun k s (p1224MarkAddressCellBody c)).arr
      (piOut + c.tableBase) < M := by
    rw [hTable]
    exact hTableWord piOut hpiOut
  have hguards := hBounds.past_output_guards (windowBase := windowBase)
    hPast hTableBounds hroot hhi0 hhi
  dsimp only at hguards
  rcases hguards with ⟨hqOut, hqOut0, hbpOut, hfsOut⟩
  change (arun k s (p1224MarkAddressCellBody c)).arr
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp)) + c.tableBase) =
      tableWord (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp))) at hTable
  change (arun k s (p1224MarkAddressCellBody c)).arr
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp)) + c.tableBase) < M at hword
  rw [← hq, ← hbp, ← hpi, ← hTable] at hqOut hqOut0 hbpOut
  rw [← hq, ← hbp, ← hfs] at hfsOut
  let out := arun k s (p1224MarkResidentBody c)
  have hrun := p1224MarkResidentBody_past_cursor_run c k s
    w.cursor.offset hj hactive hPast hsink
    (by simpa [hbp] using hBounds.base_pos)
    (by simpa [hbp] using hbpM) hhi hsum hK haddr hword hjQ
    hqOut hqOut0 hbpOut hfsOut hT hL1 hviol hvmark
  dsimp only at hrun
  have hLive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a := by
    intro a ha
    exact p1224MarkResidentBody_past_live_frame c k s sinkCell
      w.cursor.offset w.cursor.base a first hL hj hactive hPast hsink
      hloaded hbp (hfs.trans hFirst) hp2 hbpM hrad hphi hsqfBit hsqf ha
  rcases hrun with
    ⟨oq, obp, ofs, oj, opi, _ow, _orr, _ov, _ovm, _oarr⟩
  dsimp only [out] at oq obp ofs oj opi hLive
  rw [hTable] at oq obp oj
  rw [hw] at oj
  have hCursor : P1224MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord := by
    rw [← hRep.1]
    apply p1224PastResult_refines_cursor c windowBase tableWord s out
    · simpa [hj] using hPast
    · simpa [hpi] using hBounds.pi_le
    · exact oq
    · exact obp
    · exact ofs
    · exact oj
    · exact opi
  exact hRep.pastStep hPast hCursor hLive

#print axioms p1224MarkResidentBody_resident_refines_window
#print axioms p1224MarkResidentBody_past_refines_window

end LeanCompCert.Ports.Prop1224Cell
