import LeanCompCert.Ports.Prop1224CellMarkPreludeRep

/-!
# Compact readiness interface for literal Proposition 12.2.4 marking

The large fixed-width premise lists belong at the one-step boundary, not in a
production trace term.  These records package those local obligations so a
source invariant can discharge them once and the generic finite telescope can
reuse the resulting literal-step theorem.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- Immediate fixed-width obligations for a resident source-cursor hit. -/
structure P1224ResidentStepReady
    (c : CellCfg) (k : Nat) (s : AState) (w : P1224MarkWindow)
    (first : Bool) : Prop where
  resident : w.cursor.offset < c.segLen
  active : s.regs 10 = 1
  seg_pos : 0 < c.segLen
  address_word : w.cursor.offset + 2 * c.segLen < M
  base_two : 2 ≤ w.cursor.base
  base_word : w.cursor.base < M
  first_eq : w.cursor.first = if first then 1 else 0
  radical_word : (w.cells w.cursor.offset).radical *
    (if first then w.cursor.base else 1) < M
  phi_word : (w.cells w.cursor.offset).phiSmall *
    (if first then w.cursor.base - 1 else 1) < M
  sqf_bit : (w.cells w.cursor.offset).sqf ≤ 1
  sqf_word : (w.cells w.cursor.offset).sqf < M
  hi_word : c.hi < M
  pi_word : w.cursor.pi < M
  table_address_word : w.cursor.pi + c.tableBase < M
  table_word : (arun k s (p1224MarkAddressCellBody c)).arr
    (w.cursor.pi + c.tableBase) < M
  next_offset_word : w.cursor.offset + w.cursor.power < M
  power_pos : 0 < w.cursor.power
  power_word : w.cursor.power < M
  first_word : w.cursor.first < M
  steps_word : c.markSteps < M
  table_len_word : c.tableLen < M
  pi_le : w.cursor.pi ≤ c.tableLen
  segment_sentinel_word : c.segLen + 1 < M
  violation_word : s.regs rViol +
    c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M
  mark_violation_word : s.regs rVMark +
    c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M

/-- Immediate fixed-width and resident-table obligations for a past-window
source-cursor transition. -/
structure P1224PastStepReady
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (sinkCell : P1224MarkCell) (first : Bool) : Prop where
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
  sink_loaded : p1224PlaneWordsAt s c.segLen (4 * c.segLen) =
    sinkCell.encode
  base_two : 2 ≤ w.cursor.base
  first_eq : w.cursor.first = if first then 1 else 0
  radical_word : sinkCell.radical *
    (if first then w.cursor.base else 1) < M
  phi_word : sinkCell.phiSmall *
    (if first then w.cursor.base - 1 else 1) < M
  sqf_bit : sinkCell.sqf ≤ 1
  sqf_word : sinkCell.sqf < M

/-- Exactly the two source branches of one literal post-prelude marking
transition. -/
inductive P1224MarkStepReady
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow) : Prop where
  | resident (first : Bool)
      (h : P1224ResidentStepReady c k s w first)
  | past (sinkCell : P1224MarkCell) (first : Bool)
      (h : P1224PastStepReady c k windowBase tableWord s w sinkCell first)

/-- The compact readiness interface is sufficient for the exact literal
post-prelude denotation. -/
theorem p1224MarkResidentBody_refines_window_of_ready
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c s)
    (ready : P1224MarkStepReady c k windowBase tableWord s w) :
    (w.step c windowBase tableWord).Rep c
      (arun k s (p1224MarkResidentBody c)) := by
  cases ready with
  | resident first h =>
      exact p1224MarkResidentBody_resident_refines_window c k windowBase
        tableWord s w first hRep h.resident h.active h.seg_pos
        h.address_word h.base_two h.base_word h.first_eq h.radical_word
        h.phi_word h.sqf_bit h.sqf_word h.hi_word
        h.pi_word h.table_address_word h.table_word h.next_offset_word
        h.power_pos h.power_word h.first_word h.steps_word
        h.table_len_word h.pi_le h.segment_sentinel_word h.violation_word
        h.mark_violation_word
  | past sinkCell first h =>
      exact p1224MarkResidentBody_past_refines_window c k windowBase
        tableWord s w sinkCell first hRep h.bounds h.table_bounds
        h.table_rep h.table_words h.past h.window_eq h.active h.seg_pos
        h.sink_word h.root_le_hi h.hi_pos h.hi_word
        h.pi_sum_word h.table_len_word h.table_address_word
        h.next_offset_word h.steps_word h.segment_sentinel_word
        h.violation_word h.mark_violation_word h.sink_loaded h.base_two
        h.first_eq h.radical_word h.phi_word h.sqf_bit h.sqf_word

/-- Lift the compact post-prelude theorem to the actual complete
`CellCfg.markBody`. -/
theorem p1224MarkBody_refines_window_of_prelude_ready
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c (arun k s (p1224MarkPreludeBody c)))
    (ready : P1224MarkStepReady c k windowBase tableWord
      (arun k s (p1224MarkPreludeBody c)) w) :
    (w.step c windowBase tableWord).Rep c (arun k s c.markBody) := by
  have hstep := p1224MarkResidentBody_refines_window_of_ready c k
    windowBase tableWord (arun k s (p1224MarkPreludeBody c)) w hRep ready
  rw [← p1224MarkFullBody_eq_markBody c]
  simpa only [p1224MarkFullBody, arun_append] using hstep

/-- Symbolic telescope for the actual literal marking body.  The invariant
supplies source arithmetic readiness at each prefix; no production list or
table is reduced by this theorem. -/
theorem foldl_p1224MarkBody_refinement
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : AState → P1224MarkWindow → Prop) (indices : List Nat)
    (s : AState) (w : P1224MarkWindow) (hinv : Inv s w)
    (hrep : w.Rep c s)
    (hpreRep : ∀ k st model, Inv st model → model.Rep c st →
      model.Rep c (arun k st (p1224MarkPreludeBody c)))
    (hready : ∀ k st model, Inv st model → model.Rep c st →
      P1224MarkStepReady c k windowBase tableWord
        (arun k st (p1224MarkPreludeBody c)) model)
    (hpreserve : ∀ k st model, Inv st model → model.Rep c st →
      Inv (arun k st c.markBody) (model.step c windowBase tableWord)) :
    let out := indices.foldl (fun st k => arun k st c.markBody) s
    let modelOut := w.run indices.length c windowBase tableWord
    Inv out modelOut ∧ modelOut.Rep c out := by
  apply foldl_p1224MarkWindow_refinement c windowBase tableWord
    (fun k st => arun k st c.markBody) Inv indices s w hinv hrep
  · intro k st model hi hr
    exact p1224MarkBody_refines_window_of_prelude_ready c k windowBase
      tableWord st model (hpreRep k st model hi hr)
      (hready k st model hi hr)
  · exact hpreserve

#print axioms p1224MarkResidentBody_refines_window_of_ready
#print axioms p1224MarkBody_refines_window_of_prelude_ready
#print axioms foldl_p1224MarkBody_refinement

end LeanCompCert.Ports.Prop1224Cell
