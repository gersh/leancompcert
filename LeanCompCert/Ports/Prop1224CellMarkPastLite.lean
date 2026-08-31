import LeanCompCert.Ports.Prop1224CellMarkStepReady
import LeanCompCert.Ports.Prop1224CellAccWindowTelescope

/-!
# Value-independent past-window marking refinement

When the prime-power cursor is already beyond the live window, the literal
marker redirects its three stores to scratch addresses `4L`, `5L`, and `6L`.
Their values are dead.  This module proves the past branch without decoding
or bounding those scratch values, while retaining the exact cursor/table and
budget semantics needed by the next source step.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- In the past branch, address-and-cell execution frames every address other
than the three scratch destinations, independently of the loaded scratch
contents and multipliers. -/
theorem p1224MarkAddressCellBody_past_arr_frame_at
    (c : CellCfg) (k : Nat) (s : AState) (j x : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 10 = 1)
    (hpast : c.segLen ≤ j) (hsink : 6 * c.segLen < M)
    (hx4 : x ≠ 4 * c.segLen) (hx5 : x ≠ 5 * c.segLen)
    (hx6 : x ≠ 6 * c.segLen) :
    (arun k s (p1224MarkAddressCellBody c)).arr x = s.arr x := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have had := p1224MarkAddressBody_past_run c k s j hj hactive hpast hsink
  dsimp only at had
  rcases had with ⟨_h27, h30, h31, h32, harr⟩
  have hcell := p1224MarkCellBody_arr_frame k addressed
    (4 * c.segLen) (5 * c.segLen) (6 * c.segLen) x
    h30 h31 h32 hx4 hx5 hx6
  simp only [p1224MarkAddressCellBody, arun_append]
  exact hcell.trans (congrFun harr x)

/-- The complete post-prelude marking suffix has the same value-independent
frame property; its cursor/budget tail performs no stores. -/
theorem p1224MarkResidentBody_past_arr_frame_at
    (c : CellCfg) (k : Nat) (s : AState) (j x : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 10 = 1)
    (hpast : c.segLen ≤ j) (hsink : 6 * c.segLen < M)
    (hx4 : x ≠ 4 * c.segLen) (hx5 : x ≠ 5 * c.segLen)
    (hx6 : x ≠ 6 * c.segLen) :
    (arun k s (p1224MarkResidentBody c)).arr x = s.arr x := by
  let hit := arun k s (p1224MarkAddressCellBody c)
  have hhit := p1224MarkAddressCellBody_past_arr_frame_at
    c k s j x hj hactive hpast hsink hx4 hx5 hx6
  have htail := p1224MarkAdvanceBody_arr_frame c k hit
  rw [show p1224MarkResidentBody c =
      p1224MarkAddressCellBody c ++ p1224MarkAdvanceBody c by rfl,
    arun_append, congrFun htail x]
  exact hhit

/-- Fixed-width/source obligations for a past-window transition, with no
logical scratch cell and no arithmetic facts about scratch values. -/
structure P1224PastStepReadyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow) : Prop where
  bounds : w.cursor.Bounds c
  table_bounds : P1224MarkTableBounds c tableWord
  table_rep : P1224MarkTableRep c tableWord s
  table_words : ∀ i, i ≤ c.tableLen → tableWord i < M
  past : c.segLen ≤ w.cursor.offset
  window_eq : s.regs rW = windowBase
  active : s.regs 10 = 1
  seg_pos : 0 < c.segLen
  sink_word : 6 * c.segLen < M
  root_le_hi : c.root ≤ c.hi
  hi_pos : 0 < c.hi
  hi_word : c.hi < M
  pi_sum_word : s.regs rPi + c.p1224StepPrime 1 1
    (s.regs rQp) (s.regs rBp) < M
  table_len_word : c.tableLen < M
  table_address_word : p1224ClampPi c.tableLen
    (s.regs rPi + c.p1224StepPrime 1 1
      (s.regs rQp) (s.regs rBp)) + c.tableBase < M
  next_offset_word : s.regs rJ + s.regs rQp < M
  steps_word : c.markSteps < M
  segment_sentinel_word : c.segLen + 1 < M
  violation_word : s.regs rViol + c.p1224BudgetFailure (s.regs rR)
    (p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime 1 1
        (s.regs rQp) (s.regs rBp))) < M
  mark_violation_word : s.regs rVMark + c.p1224BudgetFailure (s.regs rR)
    (p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime 1 1
        (s.regs rQp) (s.regs rBp))) < M

/-- Exact past-window refinement without interpreting scratch values. -/
theorem p1224MarkResidentBody_past_refines_window_lite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c s)
    (h : P1224PastStepReadyLite c k windowBase tableWord s w) :
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
  let piOut := p1224ClampPi c.tableLen
    (s.regs rPi + c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
  have hpiOut : piOut ≤ c.tableLen := by
    simp only [piOut, p1224ClampPi]
    split <;> omega
  have htableAddrSep :
      piOut + c.tableBase ≠ 4 * c.segLen ∧
      piOut + c.tableBase ≠ 5 * c.segLen ∧
      piOut + c.tableBase ≠ 6 * c.segLen := by
    simp only [CellCfg.tableBase]
    omega
  have hTable : (arun k s (p1224MarkAddressCellBody c)).arr
      (piOut + c.tableBase) = tableWord piOut := by
    rw [p1224MarkAddressCellBody_past_arr_frame_at c k s
      w.cursor.offset (piOut + c.tableBase) hj h.active h.past h.sink_word
      htableAddrSep.1 htableAddrSep.2.1 htableAddrSep.2.2]
    exact h.table_rep piOut hpiOut
  have hword : (arun k s (p1224MarkAddressCellBody c)).arr
      (piOut + c.tableBase) < M := by
    rw [hTable]
    exact h.table_words piOut hpiOut
  have hguards := h.bounds.past_output_guards (windowBase := windowBase)
    h.past h.table_bounds h.root_le_hi h.hi_pos h.hi_word
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
  have hbaseWord : w.cursor.base < M :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans h.bounds.base_le_root h.root_le_hi) h.hi_word
  let out := arun k s (p1224MarkResidentBody c)
  have hrun := p1224MarkResidentBody_past_cursor_run c k s
    w.cursor.offset hj h.active h.past h.sink_word
    (by simpa [hbp] using h.bounds.base_pos)
    (by simpa [hbp] using hbaseWord)
    h.hi_word h.pi_sum_word h.table_len_word h.table_address_word hword
    h.next_offset_word hqOut hqOut0 hbpOut hfsOut h.steps_word
    h.segment_sentinel_word h.violation_word h.mark_violation_word
  dsimp only at hrun
  have hLive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a := by
    intro a ha
    exact p1224MarkResidentBody_past_arr_frame_at c k s
      w.cursor.offset a hj h.active h.past h.sink_word
      (by omega) (by omega) (by omega)
  rcases hrun with
    ⟨oq, obp, ofs, oj, opi, _ow, _orr, _ov, _ovm, _oarr⟩
  dsimp only [out] at oq obp ofs oj opi hLive
  rw [hTable] at oq obp oj
  rw [h.window_eq] at oj
  have hCursor : P1224MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord := by
    rw [← hRep.1]
    apply p1224PastResult_refines_cursor c windowBase tableWord s out
    · simpa [hj] using h.past
    · simpa [hpi] using h.bounds.pi_le
    · exact oq
    · exact obp
    · exact ofs
    · exact oj
    · exact opi
  exact hRep.pastStep h.past hCursor hLive

/-- Compact readiness with a value-independent past branch. -/
inductive P1224MarkStepReadyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow) : Prop where
  | resident (first : Bool)
      (h : P1224ResidentStepReady c k s w first)
  | past (h : P1224PastStepReadyLite c k windowBase tableWord s w)

theorem p1224MarkResidentBody_refines_window_of_readyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c s)
    (ready : P1224MarkStepReadyLite c k windowBase tableWord s w) :
    (w.step c windowBase tableWord).Rep c
      (arun k s (p1224MarkResidentBody c)) := by
  cases ready with
  | resident first h =>
      exact p1224MarkResidentBody_refines_window_of_ready c k windowBase
        tableWord s w hRep (.resident first h)
  | past h =>
      exact p1224MarkResidentBody_past_refines_window_lite
        c k windowBase tableWord s w hRep h

#print axioms p1224MarkAddressCellBody_past_arr_frame_at
#print axioms p1224MarkResidentBody_past_arr_frame_at
#print axioms p1224MarkResidentBody_past_refines_window_lite
#print axioms p1224MarkResidentBody_refines_window_of_readyLite

end LeanCompCert.Ports.Prop1224Cell
