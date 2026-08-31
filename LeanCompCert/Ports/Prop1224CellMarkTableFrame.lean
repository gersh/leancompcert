import LeanCompCert.Ports.Prop1224CellMarkIndexedTelescopeLite

/-!
# Prime-table preservation through a literal marking round

The positional prime table is immutable source input.  Marking stores touch
only the three live planes or their scratch sinks, and the inactive
accumulator touches only its four scratch sinks.  These lemmas make that
separation explicit so a symbolic marking telescope can carry the table
representation without evaluating a table or a sweep.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- A ready post-prelude marking transition frames the immutable positional
prime table.  The resident branch uses its exact three-plane update; the
past branch uses the value-independent scratch frame. -/
theorem p1224MarkBody_tableRep_of_readyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hTable : P1224MarkTableRep c tableWord s)
    (hRep : w.Rep c (arun k s (p1224MarkPreludeBody c)))
    (ready : P1224MarkStepReadyLite c k windowBase tableWord
      (arun k s (p1224MarkPreludeBody c)) w) :
    P1224MarkTableRep c tableWord (arun k s c.markBody) := by
  let pre := arun k s (p1224MarkPreludeBody c)
  have hPreTable : P1224MarkTableRep c tableWord pre := by
    simpa only [pre] using
      p1224MarkPreludeBody_table_frame c k s tableWord hTable
  cases ready with
  | resident first h =>
      have hj : pre.regs rJ = w.cursor.offset := by
        simpa [P1224MarkCursor.ofState, pre] using
          congrArg P1224MarkCursor.offset hRep.1
      have hbp : pre.regs rBp = w.cursor.base := by
        simpa [P1224MarkCursor.ofState, pre] using
          congrArg P1224MarkCursor.base hRep.1
      have hfs : pre.regs rFs = w.cursor.first := by
        simpa [P1224MarkCursor.ofState, pre] using
          congrArg P1224MarkCursor.first hRep.1
      have harr := p1224MarkResidentBody_markPower_run c k pre
        (w.cells w.cursor.offset) w.cursor.offset w.cursor.base first
        h.seg_pos hj h.active h.resident h.address_word
        (hRep.2 w.cursor.offset h.resident) hbp (hfs.trans h.first_eq)
        h.base_two h.base_word h.radical_word h.phi_word h.sqf_bit h.sqf_word
      intro i hi
      have hresident := h.resident
      have hframe := writeP1224PlaneWordsAt_table_frame c pre
        w.cursor.offset
        (((w.cells w.cursor.offset).markPower w.cursor.base first).encode)
        (by simp only [CellCfg.tableBase]; omega) i
      rw [← p1224MarkFullBody_eq_markBody c, p1224MarkFullBody,
        arun_append, harr, hframe]
      exact hPreTable i hi
  | past h =>
      have hj : pre.regs rJ = w.cursor.offset := by
        simpa [P1224MarkCursor.ofState, pre] using
          congrArg P1224MarkCursor.offset hRep.1
      intro i hi
      have hframe := p1224MarkResidentBody_past_arr_frame_at c k pre
        w.cursor.offset (i + c.tableBase) hj h.active h.past h.sink_word
        (by simp only [CellCfg.tableBase]; omega)
        (by simp only [CellCfg.tableBase]; omega)
        (by simp only [CellCfg.tableBase]; omega)
      rw [← p1224MarkFullBody_eq_markBody c, p1224MarkFullBody,
        arun_append, hframe]
      exact hPreTable i hi

/-- A complete literal body in the marking phase frames the positional
prime table.  The accumulator is disabled on such a round and writes only
the four scratch cells at offsets `4L` through `7L`, below `tableBase`.
The logarithm and tail blocks contain no stores. -/
theorem p1224FullBody_tableRep_of_readyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hTable : P1224MarkTableRep c tableWord s)
    (hRep : w.Rep c (arun k s (p1224MarkPreludeBody c)))
    (ready : P1224MarkStepReadyLite c k windowBase tableWord
      (arun k s (p1224MarkPreludeBody c)) w)
    (r : Nat) (hr : s.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hOne : s.regs rOne = 1) (hZero : s.regs rZero = 0)
    (h7L : 7 * c.segLen < M) :
    P1224MarkTableRep c tableWord (arun k s c.body) := by
  let marked := arun k s c.markBody
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  have hMarkedTable : P1224MarkTableRep c tableWord marked := by
    simpa only [marked] using p1224MarkBody_tableRep_of_readyLite c k
      windowBase tableWord s w hTable hRep ready
  have hgate : marked.regs 12 = 0 := by
    simpa only [marked] using markBody_mark_acc_gate c k r s hr hrT hperiod
  have hMarkedOne : marked.regs rOne = 1 :=
    (arun_frame k rOne c.markBody (by rfl) s).trans hOne
  have hMarkedZero : marked.regs rZero = 0 :=
    (arun_frame k rZero c.markBody (by rfl) s).trans hZero
  have haccArr := accBody_inactive_arr_eq c k marked hgate hMarkedOne
    hMarkedZero h7L
  dsimp only at haccArr
  have hAccumulatedTable : P1224MarkTableRep c tableWord accumulated := by
    intro i hi
    have hframe := writeP1224AccCell_frame marked c.segLen
      (4 * c.segLen) (accumulated.regs rG) (i + c.tableBase)
      (by simp only [CellCfg.tableBase]; omega)
      (by simp only [CellCfg.tableBase]; omega)
      (by simp only [CellCfg.tableBase]; omega)
      (by simp only [CellCfg.tableBase]; omega)
    rw [haccArr, hframe]
    exact hMarkedTable i hi
  have hLoggedTable : P1224MarkTableRep c tableWord logged := by
    intro i hi
    rw [logBody_arr_frame c k accumulated]
    exact hAccumulatedTable i hi
  have hOutTable : P1224MarkTableRep c tableWord
      (arun k logged c.tailBody) := by
    intro i hi
    rw [tailBody_arr_frame c k logged]
    exact hLoggedTable i hi
  simpa only [CellCfg.body, arun_append, marked, accumulated, logged] using
    hOutTable

#print axioms p1224MarkBody_tableRep_of_readyLite
#print axioms p1224FullBody_tableRep_of_readyLite

end LeanCompCert.Ports.Prop1224Cell
