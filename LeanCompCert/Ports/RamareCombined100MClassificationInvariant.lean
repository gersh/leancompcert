import LeanCompCert.Ports.RamareCombined100MClassGuardRefinement
import LeanCompCert.Ports.RamareCombined100MBodyRefinement

/-!
# Live classification invariant for the Ramaré combined sweep

This module lifts the exact scalar guard theorem through the physical seven
plane loads.  The source `markCell` invariants discharge every guard and word
premise, leaving the counter equations needed by the production loop.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100MSeg
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append astep)
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)
open LeanCompCert.Verified.InstrBlock

/-! ## Classification-phase mark framing -/

/-- All instructions in the mark block before its only counter-writing
suffix. -/
def Cfg.markBeforeBudgetBody (c : Cfg) :
    List LeanCompCert.Verified.ArrayState.AInstr :=
  lift c.markPhaseBody ++ c.markResetBody ++ c.markAddressBody ++
    Cfg.markLoadBody ++ Cfg.markCellBody ++ c.markAdvanceSelectBody ++
    c.markAdvanceLoadBody ++ c.markAdvanceCursorBody

theorem Cfg.markBody_eq_beforeBudget_append (c : Cfg) :
    c.markBody = c.markBeforeBudgetBody ++ c.markBudgetBody := by
  simp [Cfg.markBody, Cfg.markCoreBody, Cfg.markAdvanceBody,
    Cfg.markBeforeBudgetBody, List.append_assoc]

/-- Outside the mark rounds, the budget-failure selector is zero, so its two
physical counter additions are exact frames. -/
theorem Cfg.markBudgetBody_class_counter_frame
    (c : Cfg) (k : Nat) (s : AState)
    (hTpos : 0 < c.markSteps) (hT : c.markSteps ≤ s.regs rR)
    (hTM : c.markSteps < M)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    let out := arun k s c.markBudgetBody
    out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark := by
  have hne : s.regs rR ≠ c.markSteps - 1 := by omega
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hTM
  have hTmod : (c.markSteps - 1) % M = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1
  have hTmodN : (c.markSteps - 1) % 18446744073709551616 =
      c.markSteps - 1 := by simpa [M] using hTmod
  have hne5 : s.regs 5 ≠ c.markSteps - 1 := by
    simpa [rR] using hne
  simp [Cfg.markBudgetBody, arun, astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, rR, rViol, rVMark,
    hne5, hTmodN, M]
  exact ⟨by simpa [rViol, M] using hviol,
    by simpa [rVMark, M] using hvmark⟩

/-- The complete phase-gated mark block preserves all three classification
counters once the round cursor has entered the classification phase. -/
theorem Cfg.markBody_class_counter_frame
    (c : Cfg) (k : Nat) (s : AState)
    (hTpos : 0 < c.markSteps) (hT : c.markSteps ≤ s.regs rR)
    (hTM : c.markSteps < M)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    let out := arun k s c.markBody
    out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark ∧
      out.regs rSeen = s.regs rSeen := by
  let before := arun k s c.markBeforeBudgetBody
  have hbR : before.regs rR = s.regs rR :=
    arun_frame k rR c.markBeforeBudgetBody (by rfl) s
  have hbViol : before.regs rViol = s.regs rViol :=
    arun_frame k rViol c.markBeforeBudgetBody (by rfl) s
  have hbVMark : before.regs rVMark = s.regs rVMark :=
    arun_frame k rVMark c.markBeforeBudgetBody (by rfl) s
  have hbSeen : before.regs rSeen = s.regs rSeen :=
    arun_frame k rSeen c.markBeforeBudgetBody (by rfl) s
  have hbudget := c.markBudgetBody_class_counter_frame k before hTpos
    (by rw [hbR]; exact hT) hTM
    (hbViol.symm ▸ hviol) (hbVMark.symm ▸ hvmark)
  dsimp only at hbudget
  have houtSeen :
      (arun k before c.markBudgetBody).regs rSeen = before.regs rSeen :=
    arun_frame k rSeen c.markBudgetBody (by rfl) before
  rw [c.markBody_eq_beforeBudget_append, arun_append]
  exact ⟨hbudget.1.trans hbViol,
    hbudget.2.trans hbVMark, houtSeen.trans hbSeen⟩

/-- With the mark gate disabled, all seven unconditional memory operations
select the dedicated sink planes, independently of the cursor offset. -/
theorem Cfg.markAddressBody_inactive_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 0)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let out := arun k s c.markAddressBody
    out.regs 30 = 7 * c.segLen ∧ out.regs 31 = 8 * c.segLen ∧
      out.regs 32 = 9 * c.segLen ∧ out.regs 33 = 10 * c.segLen ∧
      out.regs 34 = 11 * c.segLen ∧ out.regs 35 = 12 * c.segLen ∧
      out.regs 36 = 13 * c.segLen ∧ out.arr = s.arr := by
  have h8' : (8 * c.segLen) % M = 8 * c.segLen := Nat.mod_eq_of_lt h8
  have h9' : (9 * c.segLen) % M = 9 * c.segLen := Nat.mod_eq_of_lt h9
  have h10' : (10 * c.segLen) % M = 10 * c.segLen := Nat.mod_eq_of_lt h10
  have h11' : (11 * c.segLen) % M = 11 * c.segLen := Nat.mod_eq_of_lt h11
  have h12' : (12 * c.segLen) % M = 12 * c.segLen := Nat.mod_eq_of_lt h12
  have h13' : (13 * c.segLen) % M = 13 * c.segLen := Nat.mod_eq_of_lt h13
  have h8raw : (7 * c.segLen + c.segLen) % M = 8 * c.segLen := by
    rw [show 7 * c.segLen + c.segLen = 8 * c.segLen by omega, h8']
  have h9raw : (7 * c.segLen + 2 * c.segLen) % M = 9 * c.segLen := by
    rw [show 7 * c.segLen + 2 * c.segLen = 9 * c.segLen by omega, h9']
  have h10raw : (7 * c.segLen + 3 * c.segLen) % M = 10 * c.segLen := by
    rw [show 7 * c.segLen + 3 * c.segLen = 10 * c.segLen by omega, h10']
  have h11raw : (7 * c.segLen + 4 * c.segLen) % M = 11 * c.segLen := by
    rw [show 7 * c.segLen + 4 * c.segLen = 11 * c.segLen by omega, h11']
  have h12raw : (7 * c.segLen + 5 * c.segLen) % M = 12 * c.segLen := by
    rw [show 7 * c.segLen + 5 * c.segLen = 12 * c.segLen by omega, h12']
  have h13raw : (7 * c.segLen + 6 * c.segLen) % M = 13 * c.segLen := by
    rw [show 7 * c.segLen + 6 * c.segLen = 13 * c.segLen by omega, h13']
  simp [Cfg.markAddressBody, arun, astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, hphase, Cfg.sink, M]
  exact ⟨by simpa [M] using h7,
    by simpa [M] using h8raw,
    by simpa [M] using h9raw,
    by simpa [M] using h10raw,
    by simpa [M] using h11raw,
    by simpa [M] using h12raw,
    by simpa [M] using h13raw⟩

/-- In a classification round the complete mark block writes only sink
planes, hence every live seven-plane cell is an exact frame. -/
theorem Cfg.markBody_class_plane_frame
    (c : Cfg) (k : Nat) (s : AState) (i : Nat)
    (hclass : c.markSteps ≤ s.regs rR) (hTM : c.markSteps < M)
    (hi : i < c.segLen)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    c.readPlaneCell i (arun k s c.markBody) = c.readPlaneCell i s := by
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let addressed := arun k reset c.markAddressBody
  let loaded := arun k addressed Cfg.markLoadBody
  let marked := arun k loaded Cfg.markCellBody
  let advanced := arun k marked c.markAdvanceBody
  have hp := c.markPhaseBody_run k s hTM
  dsimp only at hp
  have hp10 : phased.regs 10 = 0 := by
    rw [hp.1, if_neg (Nat.not_lt_of_ge hclass)]
  have hr10 : reset.regs 10 = 0 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  have ha := c.markAddressBody_inactive_run k reset hr10
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha
  rcases ha with ⟨ha30, ha31, ha32, ha33, ha34, ha35, ha36, _⟩
  have loadFrame (r : Nat) (hw : writes r Cfg.markLoadBody = false) :
      loaded.regs r = addressed.regs r :=
    arun_frame k r Cfg.markLoadBody hw addressed
  have h30 : loaded.regs 30 = 7 * c.segLen :=
    (loadFrame 30 (by rfl)).trans ha30
  have h31 : loaded.regs 31 = 8 * c.segLen :=
    (loadFrame 31 (by rfl)).trans ha31
  have h32 : loaded.regs 32 = 9 * c.segLen :=
    (loadFrame 32 (by rfl)).trans ha32
  have h33 : loaded.regs 33 = 10 * c.segLen :=
    (loadFrame 33 (by rfl)).trans ha33
  have h34 : loaded.regs 34 = 11 * c.segLen :=
    (loadFrame 34 (by rfl)).trans ha34
  have h35 : loaded.regs 35 = 12 * c.segLen :=
    (loadFrame 35 (by rfl)).trans ha35
  have h36 : loaded.regs 36 = 13 * c.segLen :=
    (loadFrame 36 (by rfl)).trans ha36
  have sinkNe (a b : Nat) (ha6 : a ≤ 6) (hb6 : b ≤ 6) :
      i + a * c.segLen ≠ (7 + b) * c.segLen := by
    intro heq
    have hleft : i + a * c.segLen < (a + 1) * c.segLen := by
      simpa [Nat.add_mul, Nat.add_comm] using
        Nat.add_lt_add_right hi (a * c.segLen)
    have hright : (a + 1) * c.segLen ≤ (7 + b) * c.segLen := by
      calc
        (a + 1) * c.segLen ≤ 7 * c.segLen :=
          Nat.mul_le_mul_right c.segLen (by omega)
        _ ≤ (7 + b) * c.segLen :=
          Nat.mul_le_mul_right c.segLen (by omega)
    exact (Nat.not_lt_of_ge hright) (heq ▸ hleft)
  have frameAt (a : Nat) (ha6 : a ≤ 6) :
      marked.arr (i + a * c.segLen) =
        loaded.arr (i + a * c.segLen) := by
    apply Cfg.markCellBody_arr_frame
    · rw [h30]
      simpa using sinkNe a 0 ha6 (by omega)
    · rw [h31]
      simpa using sinkNe a 1 ha6 (by omega)
    · rw [h32]
      simpa using sinkNe a 2 ha6 (by omega)
    · rw [h33]
      simpa using sinkNe a 3 ha6 (by omega)
    · rw [h34]
      simpa using sinkNe a 4 ha6 (by omega)
    · rw [h35]
      simpa using sinkNe a 5 ha6 (by omega)
    · rw [h36]
      simpa using sinkNe a 6 ha6 (by omega)
  have hpArr : phased.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (lift c.markPhaseBody) s (by rfl)
  have hrArr : reset.arr = phased.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markResetBody phased (by rfl)
  have haArr : addressed.arr = reset.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markAddressBody reset (by rfl)
  have hlArr : loaded.arr = addressed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k Cfg.markLoadBody addressed (by rfl)
  have hprefixArr : loaded.arr = s.arr :=
    hlArr.trans (haArr.trans (hrArr.trans hpArr))
  have hadvArr : advanced.arr = marked.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markAdvanceBody marked (by rfl)
  have hrun : arun k s c.markBody = advanced := by
    simp only [Cfg.markBody, Cfg.markCoreBody, Cfg.markAdvanceBody,
      arun_append]
    rfl
  rw [hrun]
  apply PlaneCell.ext
  · change advanced.arr i = s.arr i
    rw [hadvArr]
    have hf := frameAt 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero] at hf
    exact hf.trans (congrFun hprefixArr i)
  · change advanced.arr (i + c.segLen) = s.arr (i + c.segLen)
    rw [hadvArr]
    have hf := frameAt 1 (by omega)
    simp only [Nat.one_mul] at hf
    exact hf.trans (congrFun hprefixArr (i + c.segLen))
  · change advanced.arr (i + 2 * c.segLen) = s.arr (i + 2 * c.segLen)
    rw [hadvArr]
    exact (frameAt 2 (by omega)).trans
      (congrFun hprefixArr (i + 2 * c.segLen))
  · change advanced.arr (i + 3 * c.segLen) = s.arr (i + 3 * c.segLen)
    rw [hadvArr]
    exact (frameAt 3 (by omega)).trans
      (congrFun hprefixArr (i + 3 * c.segLen))
  · change advanced.arr (i + 4 * c.segLen) = s.arr (i + 4 * c.segLen)
    rw [hadvArr]
    exact (frameAt 4 (by omega)).trans
      (congrFun hprefixArr (i + 4 * c.segLen))
  · change advanced.arr (i + 5 * c.segLen) = s.arr (i + 5 * c.segLen)
    rw [hadvArr]
    exact (frameAt 5 (by omega)).trans
      (congrFun hprefixArr (i + 5 * c.segLen))
  · change advanced.arr (i + 6 * c.segLen) = s.arr (i + 6 * c.segLen)
    rw [hadvArr]
    exact (frameAt 6 (by omega)).trans
      (congrFun hprefixArr (i + 6 * c.segLen))

/-- In a classification round the complete mark block can write only the
seven sink planes below `tableBase`.  Hence every initialized table or
later read-only cell is an exact frame. -/
theorem Cfg.markBody_class_table_frame
    (c : Cfg) (k : Nat) (s : AState) (q : Nat)
    (hclass : c.markSteps ≤ s.regs rR) (hTM : c.markSteps < M)
    (hLPos : 0 < c.segLen)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M)
    (hq : c.tableBase ≤ q) :
    (arun k s c.markBody).arr q = s.arr q := by
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let addressed := arun k reset c.markAddressBody
  let loaded := arun k addressed Cfg.markLoadBody
  let marked := arun k loaded Cfg.markCellBody
  let advanced := arun k marked c.markAdvanceBody
  have hp := c.markPhaseBody_run k s hTM
  dsimp only at hp
  have hp10 : phased.regs 10 = 0 := by
    rw [hp.1, if_neg (Nat.not_lt_of_ge hclass)]
  have hr10 : reset.regs 10 = 0 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  have ha := c.markAddressBody_inactive_run k reset hr10
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha
  rcases ha with ⟨ha30, ha31, ha32, ha33, ha34, ha35, ha36, _⟩
  have loadFrame (r : Nat) (hw : writes r Cfg.markLoadBody = false) :
      loaded.regs r = addressed.regs r :=
    arun_frame k r Cfg.markLoadBody hw addressed
  have h30 : loaded.regs 30 = 7 * c.segLen :=
    (loadFrame 30 (by rfl)).trans ha30
  have h31 : loaded.regs 31 = 8 * c.segLen :=
    (loadFrame 31 (by rfl)).trans ha31
  have h32 : loaded.regs 32 = 9 * c.segLen :=
    (loadFrame 32 (by rfl)).trans ha32
  have h33 : loaded.regs 33 = 10 * c.segLen :=
    (loadFrame 33 (by rfl)).trans ha33
  have h34 : loaded.regs 34 = 11 * c.segLen :=
    (loadFrame 34 (by rfl)).trans ha34
  have h35 : loaded.regs 35 = 12 * c.segLen :=
    (loadFrame 35 (by rfl)).trans ha35
  have h36 : loaded.regs 36 = 13 * c.segLen :=
    (loadFrame 36 (by rfl)).trans ha36
  have hq7 : q ≠ 7 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq8 : q ≠ 8 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq9 : q ≠ 9 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq10 : q ≠ 10 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq11 : q ≠ 11 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq12 : q ≠ 12 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hq13 : q ≠ 13 * c.segLen := by
    unfold Cfg.tableBase at hq
    omega
  have hframe : marked.arr q = loaded.arr q := by
    apply Cfg.markCellBody_arr_frame
    · rw [h30]; exact hq7
    · rw [h31]; exact hq8
    · rw [h32]; exact hq9
    · rw [h33]; exact hq10
    · rw [h34]; exact hq11
    · rw [h35]; exact hq12
    · rw [h36]; exact hq13
  have hpArr : phased.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (lift c.markPhaseBody) s (by rfl)
  have hrArr : reset.arr = phased.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markResetBody phased (by rfl)
  have haArr : addressed.arr = reset.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markAddressBody reset (by rfl)
  have hlArr : loaded.arr = addressed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k Cfg.markLoadBody addressed (by rfl)
  have hadvArr : advanced.arr = marked.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markAdvanceBody marked (by rfl)
  have hrun : arun k s c.markBody = advanced := by
    simp only [Cfg.markBody, Cfg.markCoreBody, Cfg.markAdvanceBody,
      arun_append]
    rfl
  rw [hrun, congrFun hadvArr q, hframe, congrFun hlArr q,
    congrFun haArr q, congrFun hrArr q, congrFun hpArr q]

/-! ## Classification-phase plane framing -/

/-- The store-free active classifier address prefix selects the seven planes
of the current live offset.  This theorem exposes only addresses and the
array frame, avoiding any reduction of the scalar decoder. -/
theorem Cfg.classAddressBody_class_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.markSteps + c.segLen < M)
    (h2 : s.regs rR - c.markSteps + 2 * c.segLen < M)
    (h3 : s.regs rR - c.markSteps + 3 * c.segLen < M)
    (h4 : s.regs rR - c.markSteps + 4 * c.segLen < M)
    (h5 : s.regs rR - c.markSteps + 5 * c.segLen < M)
    (h6 : s.regs rR - c.markSteps + 6 * c.segLen < M) :
    let j := s.regs rR - c.markSteps
    let out := arun k s c.classAddressBody
    out.regs 131 = j ∧ out.regs 133 = j + c.segLen ∧
      out.regs 134 = j + 2 * c.segLen ∧
      out.regs 135 = j + 3 * c.segLen ∧
      out.regs 136 = j + 4 * c.segLen ∧
      out.regs 137 = j + 5 * c.segLen ∧
      out.regs 138 = j + 6 * c.segLen ∧ out.arr = s.arr := by
  let j := s.regs rR - c.markSteps
  let offset := arun k s (lift c.classOffsetBody)
  let indexed := arun k s c.classIndexBody
  let planed := arun k indexed (lift c.classPlaneBody)
  let sinked := arun k planed (lift c.classSinkBody)
  have ho := c.classOffsetBody_run k s hclass hT hR
  dsimp only at ho
  have hi := c.classIndexBody_run k s hclass hT hR hsum
  dsimp only at hi
  have hI131 : indexed.regs 131 = j := by
    have hframe :
        (arun k offset (lift Cfg.classCandidateBody)).regs 131 =
          offset.regs 131 :=
      arun_frame k 131 (lift Cfg.classCandidateBody) (by rfl) offset
    change (arun k s
      (lift c.classOffsetBody ++ lift Cfg.classCandidateBody)).regs 131 = j
    rw [arun_append]
    exact hframe.trans ho.2.1
  have hI10 : indexed.regs 10 = 0 :=
    (arun_frame k 10 c.classIndexBody (by rfl) s).trans hphase
  have hp := c.classPlaneBody_run k indexed
    (by rw [hI131]; exact h1)
    (by rw [hI131]; exact h2)
    (by rw [hI131]; exact h3)
    (by rw [hI131]; exact h4)
    (by rw [hI131]; exact h5)
    (by rw [hI131]; exact h6)
  dsimp only at hp
  have hp10 : planed.regs 10 = 0 :=
    (arun_frame k 10 (lift c.classPlaneBody) (by rfl) indexed).trans hI10
  have hs := c.classSinkBody_run k planed hp10
    (by rw [hp.2.2.2.2.2.2.1, hI131]; omega)
    (by rw [hp.1, hI131]; exact h1)
    (by rw [hp.2.1, hI131]; exact h2)
    (by rw [hp.2.2.1, hI131]; exact h3)
    (by rw [hp.2.2.2.1, hI131]; exact h4)
    (by rw [hp.2.2.2.2.1, hI131]; exact h5)
    (by rw [hp.2.2.2.2.2.1, hI131]; exact h6)
  dsimp only at hs
  have hrun : arun k s c.classAddressBody = sinked := by
    simp only [Cfg.classAddressBody, arun_append]
    rfl
  rw [hrun]
  exact ⟨by rw [hs.2.1, hp.2.2.2.2.2.2.1, hI131],
    by rw [hs.2.2.1, hp.1, hI131],
    by rw [hs.2.2.2.1, hp.2.1, hI131],
    by rw [hs.2.2.2.2.1, hp.2.2.1, hI131],
    by rw [hs.2.2.2.2.2.1, hp.2.2.2.1, hI131],
    by rw [hs.2.2.2.2.2.2.1, hp.2.2.2.2.1, hI131],
    by rw [hs.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.1, hI131],
    hs.2.2.2.2.2.2.2.2.trans
      (hp.2.2.2.2.2.2.2.trans hi.2.2)⟩

/-- Loads and scalar decoding are store-free, so the complete active prefix
before the seven clears retains the selected live addresses and array. -/
theorem Cfg.classBeforeClearBody_class_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.markSteps + c.segLen < M)
    (h2 : s.regs rR - c.markSteps + 2 * c.segLen < M)
    (h3 : s.regs rR - c.markSteps + 3 * c.segLen < M)
    (h4 : s.regs rR - c.markSteps + 4 * c.segLen < M)
    (h5 : s.regs rR - c.markSteps + 5 * c.segLen < M)
    (h6 : s.regs rR - c.markSteps + 6 * c.segLen < M) :
    let j := s.regs rR - c.markSteps
    let out := arun k s c.classBeforeClearBody
    out.regs 131 = j ∧ out.regs 133 = j + c.segLen ∧
      out.regs 134 = j + 2 * c.segLen ∧
      out.regs 135 = j + 3 * c.segLen ∧
      out.regs 136 = j + 4 * c.segLen ∧
      out.regs 137 = j + 5 * c.segLen ∧
      out.regs 138 = j + 6 * c.segLen ∧ out.arr = s.arr := by
  let addressed := arun k s c.classAddressBody
  have ha := c.classAddressBody_class_run k s hphase hclass hT hR hsum
    h1 h2 h3 h4 h5 h6
  dsimp only at ha
  have frame (r : Nat) (hw : writes r Cfg.classAfterAddressBody = false) :
      (arun k addressed Cfg.classAfterAddressBody).regs r = addressed.regs r :=
    arun_frame k r Cfg.classAfterAddressBody hw addressed
  have harr : (arun k addressed Cfg.classAfterAddressBody).arr =
      addressed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k Cfg.classAfterAddressBody addressed (by rfl)
  rw [Cfg.classBeforeClearBody, arun_append]
  exact ⟨(frame 131 (by rfl)).trans ha.1,
    (frame 133 (by rfl)).trans ha.2.1,
    (frame 134 (by rfl)).trans ha.2.2.1,
    (frame 135 (by rfl)).trans ha.2.2.2.1,
    (frame 136 (by rfl)).trans ha.2.2.2.2.1,
    (frame 137 (by rfl)).trans ha.2.2.2.2.2.1,
    (frame 138 (by rfl)).trans ha.2.2.2.2.2.2.1,
    harr.trans ha.2.2.2.2.2.2.2⟩

/-- Distinct offsets in the live segment remain distinct in every pair of
the seven disjoint planes. -/
theorem livePlaneCell_ne_livePlaneCell
    (segLen i j a b : Nat) (hi : i < segLen) (hj : j < segLen)
    (hne : i ≠ j) : i + a * segLen ≠ j + b * segLen := by
  intro heq
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have hleft : i + a * segLen < (a + 1) * segLen := by
      simpa [Nat.add_mul, Nat.add_comm] using
        Nat.add_lt_add_right hi (a * segLen)
    have hboundary : (a + 1) * segLen ≤ b * segLen :=
      Nat.mul_le_mul_right segLen (Nat.succ_le_iff.mpr hab)
    have : j + b * segLen < b * segLen := by
      rw [← heq]
      exact Nat.lt_of_lt_of_le hleft hboundary
    omega
  · subst b
    exact hne (Nat.add_right_cancel heq)
  · have hright : j + b * segLen < (b + 1) * segLen := by
      simpa [Nat.add_mul, Nat.add_comm] using
        Nat.add_lt_add_right hj (b * segLen)
    have hboundary : (b + 1) * segLen ≤ a * segLen :=
      Nat.mul_le_mul_right segLen (Nat.succ_le_iff.mpr hab)
    have : i + a * segLen < a * segLen := by
      rw [heq]
      exact Nat.lt_of_lt_of_le hright hboundary
    omega

/-- The active classifier clears only its current cell.  Every distinct live
seven-plane cell is an exact array frame. -/
theorem Cfg.classBody_other_plane_frame
    (c : Cfg) (k : Nat) (s : AState) (i : Nat)
    (hi : i < c.segLen)
    (hj : s.regs rR - c.markSteps < c.segLen)
    (hne : i ≠ s.regs rR - c.markSteps)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.markSteps + c.segLen < M)
    (h2 : s.regs rR - c.markSteps + 2 * c.segLen < M)
    (h3 : s.regs rR - c.markSteps + 3 * c.segLen < M)
    (h4 : s.regs rR - c.markSteps + 4 * c.segLen < M)
    (h5 : s.regs rR - c.markSteps + 5 * c.segLen < M)
    (h6 : s.regs rR - c.markSteps + 6 * c.segLen < M) :
    c.readPlaneCell i (arun k s c.classBody) = c.readPlaneCell i s := by
  let j := s.regs rR - c.markSteps
  let before := arun k s c.classBeforeClearBody
  have hb := c.classBeforeClearBody_class_run k s hphase hclass hT hR hsum
    h1 h2 h3 h4 h5 h6
  dsimp only at hb
  have frameAt (a : Nat) :
      (arun k before Cfg.classClearBody).arr (i + a * c.segLen) =
        before.arr (i + a * c.segLen) := by
    apply Cfg.classClearBody_arr_frame
    · rw [hb.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 0 hi hj hne
    · rw [hb.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 1 hi hj hne
    · rw [hb.2.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 2 hi hj hne
    · rw [hb.2.2.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 3 hi hj hne
    · rw [hb.2.2.2.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 4 hi hj hne
    · rw [hb.2.2.2.2.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 5 hi hj hne
    · rw [hb.2.2.2.2.2.2.1]
      simpa [j] using
        livePlaneCell_ne_livePlaneCell c.segLen i j a 6 hi hj hne
  have hrun : arun k s c.classBody = arun k before Cfg.classClearBody := by
    rw [c.classBody_eq_beforeClear_append, arun_append]
  rw [hrun]
  apply PlaneCell.ext
  · change (arun k before Cfg.classClearBody).arr i = s.arr i
    have hf := frameAt 0
    simp only [Nat.zero_mul, Nat.add_zero] at hf
    exact hf.trans (congrFun hb.2.2.2.2.2.2.2 i)
  · change (arun k before Cfg.classClearBody).arr (i + c.segLen) =
      s.arr (i + c.segLen)
    have hf := frameAt 1
    simp only [Nat.one_mul] at hf
    exact hf.trans (congrFun hb.2.2.2.2.2.2.2 (i + c.segLen))
  · exact (frameAt 2).trans
      (congrFun hb.2.2.2.2.2.2.2 (i + 2 * c.segLen))
  · exact (frameAt 3).trans
      (congrFun hb.2.2.2.2.2.2.2 (i + 3 * c.segLen))
  · exact (frameAt 4).trans
      (congrFun hb.2.2.2.2.2.2.2 (i + 4 * c.segLen))
  · exact (frameAt 5).trans
      (congrFun hb.2.2.2.2.2.2.2 (i + 5 * c.segLen))
  · exact (frameAt 6).trans
      (congrFun hb.2.2.2.2.2.2.2 (i + 6 * c.segLen))

/-- The active classifier writes only the current seven plane cells, all
strictly below `tableBase`; every table or later read-only cell is framed. -/
theorem Cfg.classBody_table_frame
    (c : Cfg) (k : Nat) (s : AState) (q : Nat)
    (hj : s.regs rR - c.markSteps < c.segLen)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.markSteps + c.segLen < M)
    (h2 : s.regs rR - c.markSteps + 2 * c.segLen < M)
    (h3 : s.regs rR - c.markSteps + 3 * c.segLen < M)
    (h4 : s.regs rR - c.markSteps + 4 * c.segLen < M)
    (h5 : s.regs rR - c.markSteps + 5 * c.segLen < M)
    (h6 : s.regs rR - c.markSteps + 6 * c.segLen < M)
    (hq : c.tableBase ≤ q) :
    (arun k s c.classBody).arr q = s.arr q := by
  let before := arun k s c.classBeforeClearBody
  have hb := c.classBeforeClearBody_class_run k s hphase hclass hT hR hsum
    h1 h2 h3 h4 h5 h6
  dsimp only at hb
  have hne (a : Nat) (ha : a ≤ 6) :
      q ≠ s.regs rR - c.markSteps + a * c.segLen := by
    have hsmall : s.regs rR - c.markSteps + a * c.segLen <
        c.tableBase := by
      change s.regs rR - c.markSteps + a * c.segLen < 14 * c.segLen
      calc
        s.regs rR - c.markSteps + a * c.segLen <
            c.segLen + a * c.segLen := Nat.add_lt_add_right hj _
        _ = (a + 1) * c.segLen := by
          simp only [Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _
        _ ≤ 14 * c.segLen :=
          Nat.mul_le_mul_right c.segLen
            (Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt ha (by decide)))
    intro heq
    rw [← heq] at hsmall
    exact (Nat.not_lt_of_ge hq) hsmall
  have hc := Cfg.classClearBody_arr_frame k before q
    (by rw [hb.1]; simpa using hne 0 (by omega))
    (by rw [hb.2.1]; simpa using hne 1 (by omega))
    (by rw [hb.2.2.1]; exact hne 2 (by omega))
    (by rw [hb.2.2.2.1]; exact hne 3 (by omega))
    (by rw [hb.2.2.2.2.1]; exact hne 4 (by omega))
    (by rw [hb.2.2.2.2.2.1]; exact hne 5 (by omega))
    (by rw [hb.2.2.2.2.2.2.1]; exact hne 6 (by omega))
  rw [c.classBody_eq_beforeClear_append, arun_append]
  exact hc.trans (congrFun hb.2.2.2.2.2.2.2 q)

/-- Through the literal mark/class/tail/arithmetic instruction order, a live
classification body preserves every plane cell other than the candidate it
consumes.  The arithmetic invariant is irrelevant here because both the tail
and arithmetic suffixes are syntactically store-free. -/
theorem LambdaPsiSweep.body_class_other_plane_frame
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState) (i : Nat)
    (hi : i < c.shape.segLen)
    (hj : s.regs rR - c.shape.markSteps < c.shape.segLen)
    (hne : i ≠ s.regs rR - c.shape.markSteps)
    (hclass : c.shape.markSteps ≤ s.regs rR)
    (hTM : c.shape.markSteps < M) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.shape.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.shape.markSteps + c.shape.segLen < M)
    (h2 : s.regs rR - c.shape.markSteps + 2 * c.shape.segLen < M)
    (h3 : s.regs rR - c.shape.markSteps + 3 * c.shape.segLen < M)
    (h4 : s.regs rR - c.shape.markSteps + 4 * c.shape.segLen < M)
    (h5 : s.regs rR - c.shape.markSteps + 5 * c.shape.segLen < M)
    (h6 : s.regs rR - c.shape.markSteps + 6 * c.shape.segLen < M)
    (h7 : 7 * c.shape.segLen < M) (h8 : 8 * c.shape.segLen < M)
    (h9 : 9 * c.shape.segLen < M) (h10 : 10 * c.shape.segLen < M)
    (h11 : 11 * c.shape.segLen < M) (h12 : 12 * c.shape.segLen < M)
    (h13 : 13 * c.shape.segLen < M) :
    c.shape.readPlaneCell i (arun k s (LambdaPsiSweep.body c)) =
      c.shape.readPlaneCell i s := by
  let marked := arun k s c.shape.markBody
  let classified := arun k marked c.shape.classBody
  let tailed := arun k classified c.shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  have hmarkCell := c.shape.markBody_class_plane_frame k s i hclass hTM hi
    h7 h8 h9 h10 h11 h12 h13
  have hphase := c.shape.markBody_phase_run k s hTM
  dsimp only at hphase
  have hm10 : marked.regs 10 = 0 := by
    rw [hphase.1, if_neg (by omega : ¬s.regs rR < c.shape.markSteps)]
  have hm11 : marked.regs 11 = 1 := by
    rw [hphase.2, if_pos hclass]
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR c.shape.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW c.shape.markBody (by rfl) s
  have hclassCell := c.shape.classBody_other_plane_frame k marked i hi
    (by simpa only [hmR] using hj)
    (by simpa only [hmR] using hne)
    hm10 hm11
    (by simpa only [hmR] using hclass)
    (by simpa only [hmR] using hR)
    (by simpa only [hmR, hmW] using hsum)
    (by simpa only [hmR] using h1)
    (by simpa only [hmR] using h2)
    (by simpa only [hmR] using h3)
    (by simpa only [hmR] using h4)
    (by simpa only [hmR] using h5)
    (by simpa only [hmR] using h6)
  have htailArr : tailed.arr = classified.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.shape.tailBody classified (by rfl)
  have harithArr : out.arr = tailed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (LambdaPsiSweep.arithmeticBody c) tailed (by rfl)
  have hbody : arun k s (LambdaPsiSweep.body c) = out := by
    rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
    simp only [arun_append]
    rfl
  rw [hbody]
  exact (c.shape.readPlaneCell_congr i out tailed harithArr).trans
    ((c.shape.readPlaneCell_congr i tailed classified htailArr).trans
      (hclassCell.trans hmarkCell))

/-- Through the literal mark/class/tail/arithmetic instruction order, a live
classification body preserves every initialized table and later read-only
cell. -/
theorem LambdaPsiSweep.body_class_table_frame
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState) (q : Nat)
    (hj : s.regs rR - c.shape.markSteps < c.shape.segLen)
    (hclass : c.shape.markSteps ≤ s.regs rR)
    (hTM : c.shape.markSteps < M) (hLPos : 0 < c.shape.segLen)
    (hR : s.regs rR < M)
    (hsum : s.regs rR - c.shape.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.shape.markSteps + c.shape.segLen < M)
    (h2 : s.regs rR - c.shape.markSteps + 2 * c.shape.segLen < M)
    (h3 : s.regs rR - c.shape.markSteps + 3 * c.shape.segLen < M)
    (h4 : s.regs rR - c.shape.markSteps + 4 * c.shape.segLen < M)
    (h5 : s.regs rR - c.shape.markSteps + 5 * c.shape.segLen < M)
    (h6 : s.regs rR - c.shape.markSteps + 6 * c.shape.segLen < M)
    (h7 : 7 * c.shape.segLen < M) (h8 : 8 * c.shape.segLen < M)
    (h9 : 9 * c.shape.segLen < M) (h10 : 10 * c.shape.segLen < M)
    (h11 : 11 * c.shape.segLen < M) (h12 : 12 * c.shape.segLen < M)
    (h13 : 13 * c.shape.segLen < M)
    (hq : c.shape.tableBase ≤ q) :
    (arun k s (LambdaPsiSweep.body c)).arr q = s.arr q := by
  let marked := arun k s c.shape.markBody
  let classified := arun k marked c.shape.classBody
  let tailed := arun k classified c.shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  have hmark := c.shape.markBody_class_table_frame k s q hclass hTM hLPos
    h7 h8 h9 h10 h11 h12 h13 hq
  have hphase := c.shape.markBody_phase_run k s hTM
  dsimp only at hphase
  have hm10 : marked.regs 10 = 0 := by
    rw [hphase.1, if_neg (Nat.not_lt_of_ge hclass)]
  have hm11 : marked.regs 11 = 1 := by
    rw [hphase.2, if_pos hclass]
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR c.shape.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW c.shape.markBody (by rfl) s
  have hclassified := c.shape.classBody_table_frame k marked q
    (by simpa only [hmR] using hj) hm10 hm11
    (by simpa only [hmR] using hclass)
    (by simpa only [hmR] using hR)
    (by simpa only [hmR, hmW] using hsum)
    (by simpa only [hmR] using h1)
    (by simpa only [hmR] using h2)
    (by simpa only [hmR] using h3)
    (by simpa only [hmR] using h4)
    (by simpa only [hmR] using h5)
    (by simpa only [hmR] using h6) hq
  have htailArr : tailed.arr = classified.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.shape.tailBody classified (by rfl)
  have harithArr : out.arr = tailed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (LambdaPsiSweep.arithmeticBody c) tailed (by rfl)
  have hbody : arun k s (LambdaPsiSweep.body c) = out := by
    rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
    simp only [arun_append]
    rfl
  rw [hbody, congrFun harithArr q, congrFun htailArr q, hclassified, hmark]

/-- Starting from the seven selected live-plane addresses, the actual loads
and scalar decoder preserve both violation counters and advance `seen` once.
All arithmetic premises are derived from the finite production `markCell`.
-/
theorem ofChain_classAfterAddressDecode_counters
    (lo segLen segCount tableHi k : Nat) (s : AState)
    (j n : Nat)
    (hrel : CellRel
      ((Cfg.ofChain lo segLen segCount tableHi).readPlaneCell j s)
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n))
    (hn : 0 < n) (hN : n ≤ 100000000)
    (hphase : s.regs 11 = 1)
    (h132 : s.regs 132 = n)
    (h131 : s.regs 131 = j)
    (h133 : s.regs 133 = j + segLen)
    (h134 : s.regs 134 = j + 2 * segLen)
    (h135 : s.regs 135 = j + 3 * segLen)
    (h136 : s.regs 136 = j + 4 * segLen)
    (h137 : s.regs 137 = j + 5 * segLen)
    (h138 : s.regs 138 = j + 6 * segLen)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    let out := arun k s Cfg.classAfterAddressBody
    ClassDecodeResult s out := by
  let c := Cfg.ofChain lo segLen segCount tableHi
  let rows := factorRows c.table
  let cell := markCell rows n
  let x := c.readPlaneCell j s
  let loaded := arun k s Cfg.classLoadBody
  let decoded := arun k loaded (lift Cfg.classDecodeBody)
  have hload := Cfg.classLoadBody_run k s
  dsimp only at hload
  rcases hload with
    ⟨hl140, hl141, hl142, hl143, hl144, hl145, hl146,
      _, _, _, _, _, _, _, hloadArray⟩
  have h140 : loaded.regs 140 = x.prod := by
    rw [hl140, h131]
    rfl
  have h141 : loaded.regs 141 = x.p := by
    rw [hl141, h133]
    rfl
  have h142 : loaded.regs 142 = x.pe := by
    rw [hl142, h134]
    rfl
  have h143 : loaded.regs 143 = x.pProd := by
    rw [hl143, h135]
    rfl
  have h144 : loaded.regs 144 = x.q := by
    rw [hl144, h136]
    rfl
  have h145 : loaded.regs 145 = x.qe := by
    rw [hl145, h137]
    rfl
  have h146 : loaded.regs 146 = x.qProd := by
    rw [hl146, h138]
    rfl
  have loadedFrame (r : Nat) (hw : writes r Cfg.classLoadBody = false) :
      loaded.regs r = s.regs r := arun_frame k r Cfg.classLoadBody hw s
  have h132' : loaded.regs 132 = n :=
    (loadedFrame 132 (by rfl)).trans h132
  have hphase' : loaded.regs 11 = 1 :=
    (loadedFrame 11 (by rfl)).trans hphase
  have hviol' : loaded.regs rViol = s.regs rViol :=
    loadedFrame rViol (by rfl)
  have hvshape' : loaded.regs rVShape = s.regs rVShape :=
    loadedFrame rVShape (by rfl)
  have hseen' : loaded.regs rSeen = s.regs rSeen :=
    loadedFrame rSeen (by rfl)
  have hvalid : ValidRows rows := by
    apply factorRows_valid
    intro p hp
    exact trialPrimesBelow_two_le _ p hp
  have hpair : PairwiseCoprimeRows rows :=
    ofChain_factorRows_pairwiseCoprime lo segLen segCount tableHi
  have hdiv : CellDivisorBounds n cell :=
    markCell_divisorBounds rows n hn hpair
  have hshape : CellFactorShape cell := markCell_factorShape rows n hvalid
  have hpre : CellClassifyPre n cell :=
    markCell_classifyPre rows n hn hvalid hpair
  have hcell : CellProductionBounds cell := hdiv.productionBounds hn hN
  have hx : PlaneCellProductionBounds x := hrel.productionBounds hcell
  have hword : 100000000 < M := by decide
  have hxprod : x.prod < M :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_add_right x.prod (zeroBit x.prod)) hx.prod)
      hword
  have hdecode := c.classDecodeBody_correct k loaded n x cell hrel hdiv
    hshape hpre h132' h140 h141 h142 h143 h144 h145 h146
    (Nat.lt_of_le_of_lt hN hword) hxprod
    (Nat.lt_of_le_of_lt hx.p hword)
    (Nat.lt_of_le_of_lt hx.pe (by omega))
    (Nat.lt_of_le_of_lt hx.pProd hword)
    (Nat.lt_of_le_of_lt hx.q hword)
    (Nat.lt_of_le_of_lt hx.qe (by omega))
    (Nat.lt_of_le_of_lt hx.qProd hword) hphase'
    (hviol'.symm ▸ hviol) (hvshape'.symm ▸ hvshape)
    (hseen'.symm ▸ hseen)
  have hout : arun k s Cfg.classAfterAddressBody = decoded := by
    simp only [Cfg.classAfterAddressBody, arun_append]
    rfl
  refine {
    viol := by rw [hout, hdecode.viol, hviol']
    vshape := by rw [hout, hdecode.vshape, hvshape']
    seen := by rw [hout, hdecode.seen, hseen']
    array := by rw [hout, hdecode.array, hloadArray] }

/-- Counter-only result used after the physical clear stores. -/
structure ClassCounterResult (before out : AState) : Prop where
  viol : out.regs rViol = before.regs rViol
  vshape : out.regs rVShape = before.regs rVShape
  seen : out.regs rSeen = before.regs rSeen + 1

/-- The seven clear stores do not disturb the verified decode counter effect.
-/
theorem ofChain_classAfterAddressClear_counters
    (lo segLen segCount tableHi k : Nat) (s : AState)
    (j n : Nat)
    (hrel : CellRel
      ((Cfg.ofChain lo segLen segCount tableHi).readPlaneCell j s)
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n))
    (hn : 0 < n) (hN : n ≤ 100000000)
    (hphase : s.regs 11 = 1)
    (h132 : s.regs 132 = n)
    (h131 : s.regs 131 = j)
    (h133 : s.regs 133 = j + segLen)
    (h134 : s.regs 134 = j + 2 * segLen)
    (h135 : s.regs 135 = j + 3 * segLen)
    (h136 : s.regs 136 = j + 4 * segLen)
    (h137 : s.regs 137 = j + 5 * segLen)
    (h138 : s.regs 138 = j + 6 * segLen)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    let out := arun k s
      (Cfg.classAfterAddressBody ++ Cfg.classClearBody)
    ClassCounterResult s out := by
  let decoded := arun k s Cfg.classAfterAddressBody
  let cleared := arun k decoded Cfg.classClearBody
  have hdecode := ofChain_classAfterAddressDecode_counters
    lo segLen segCount tableHi k s j n hrel hn hN hphase h132
    h131 h133 h134 h135 h136 h137 h138 hviol hvshape hseen
  dsimp only at hdecode
  have hclearViol : cleared.regs rViol = decoded.regs rViol :=
    arun_frame k rViol Cfg.classClearBody (by rfl) decoded
  have hclearVShape : cleared.regs rVShape = decoded.regs rVShape :=
    arun_frame k rVShape Cfg.classClearBody (by rfl) decoded
  have hclearSeen : cleared.regs rSeen = decoded.regs rSeen :=
    arun_frame k rSeen Cfg.classClearBody (by rfl) decoded
  simp only [arun_append]
  exact {
    viol := hclearViol.trans hdecode.viol
    vshape := hclearVShape.trans hdecode.vshape
    seen := hclearSeen.trans hdecode.seen }

/-- From a retained live offset and candidate, the complete post-candidate
classifier preserves both violation counters and advances `seen`. -/
theorem ofChain_classPostCandidateBody_counters
    (lo segLen segCount tableHi k : Nat) (s : AState)
    (j n : Nat)
    (hrel : CellRel
      ((Cfg.ofChain lo segLen segCount tableHi).readPlaneCell j s)
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n))
    (hn : 0 < n) (hN : n ≤ 100000000)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (h132 : s.regs 132 = n) (h131 : s.regs 131 = j)
    (h1 : j + segLen < M) (h2 : j + 2 * segLen < M)
    (h3 : j + 3 * segLen < M) (h4 : j + 4 * segLen < M)
    (h5 : j + 5 * segLen < M) (h6 : j + 6 * segLen < M)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    let c := Cfg.ofChain lo segLen segCount tableHi
    ClassCounterResult s (arun k s c.classPostCandidateBody) := by
  let c := Cfg.ofChain lo segLen segCount tableHi
  let planed := arun k s (lift c.classPlaneBody)
  let sinked := arun k planed (lift c.classSinkBody)
  have hp := c.classPlaneBody_run k s
    (by simpa [c, Cfg.ofChain, h131] using h1)
    (by simpa [c, Cfg.ofChain, h131] using h2)
    (by simpa [c, Cfg.ofChain, h131] using h3)
    (by simpa [c, Cfg.ofChain, h131] using h4)
    (by simpa [c, Cfg.ofChain, h131] using h5)
    (by simpa [c, Cfg.ofChain, h131] using h6)
  dsimp only at hp
  have planeFrame (r : Nat)
      (hw : writes r (lift c.classPlaneBody) = false) :
      planed.regs r = s.regs r :=
    arun_frame k r (lift c.classPlaneBody) hw s
  have hp10 : planed.regs 10 = 0 :=
    (planeFrame 10 (by rfl)).trans hphase
  have hs := c.classSinkBody_run k planed hp10
    (by rw [hp.2.2.2.2.2.2.1, h131]; omega)
    (by rw [hp.1, h131]; simpa [c, Cfg.ofChain] using h1)
    (by rw [hp.2.1, h131]; simpa [c, Cfg.ofChain] using h2)
    (by rw [hp.2.2.1, h131]; simpa [c, Cfg.ofChain] using h3)
    (by rw [hp.2.2.2.1, h131]; simpa [c, Cfg.ofChain] using h4)
    (by rw [hp.2.2.2.2.1, h131]; simpa [c, Cfg.ofChain] using h5)
    (by rw [hp.2.2.2.2.2.1, h131]; simpa [c, Cfg.ofChain] using h6)
  dsimp only at hs
  have sinkFrame (r : Nat)
      (hw : writes r (lift c.classSinkBody) = false) :
      sinked.regs r = planed.regs r :=
    arun_frame k r (lift c.classSinkBody) hw planed
  have hS132 : sinked.regs 132 = n :=
    (sinkFrame 132 (by rfl)).trans
      ((planeFrame 132 (by rfl)).trans h132)
  have hS11 : sinked.regs 11 = 1 :=
    (sinkFrame 11 (by rfl)).trans
      ((planeFrame 11 (by rfl)).trans hclass)
  have hS131 : sinked.regs 131 = j := by
    rw [hs.2.1, hp.2.2.2.2.2.2.1, h131]
  have hS133 : sinked.regs 133 = j + segLen := by
    rw [hs.2.2.1, hp.1, h131]
    rfl
  have hS134 : sinked.regs 134 = j + 2 * segLen := by
    rw [hs.2.2.2.1, hp.2.1, h131]
    rfl
  have hS135 : sinked.regs 135 = j + 3 * segLen := by
    rw [hs.2.2.2.2.1, hp.2.2.1, h131]
    rfl
  have hS136 : sinked.regs 136 = j + 4 * segLen := by
    rw [hs.2.2.2.2.2.1, hp.2.2.2.1, h131]
    rfl
  have hS137 : sinked.regs 137 = j + 5 * segLen := by
    rw [hs.2.2.2.2.2.2.1, hp.2.2.2.2.1, h131]
    rfl
  have hS138 : sinked.regs 138 = j + 6 * segLen := by
    rw [hs.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.1, h131]
    rfl
  have harr : sinked.arr = s.arr :=
    hs.2.2.2.2.2.2.2.2.trans hp.2.2.2.2.2.2.2
  have hrel' : CellRel (c.readPlaneCell j sinked)
      (markCell (factorRows c.table) n) := by
    rw [c.readPlaneCell_congr j sinked s harr]
    exact hrel
  have hSViol : sinked.regs rViol = s.regs rViol :=
    (sinkFrame rViol (by rfl)).trans (planeFrame rViol (by rfl))
  have hSVShape : sinked.regs rVShape = s.regs rVShape :=
    (sinkFrame rVShape (by rfl)).trans (planeFrame rVShape (by rfl))
  have hSSeen : sinked.regs rSeen = s.regs rSeen :=
    (sinkFrame rSeen (by rfl)).trans (planeFrame rSeen (by rfl))
  have hout := ofChain_classAfterAddressClear_counters
    lo segLen segCount tableHi k sinked j n hrel' hn hN hS11 hS132
    hS131 hS133 hS134 hS135 hS136 hS137 hS138
    (hSViol.symm ▸ hviol) (hSVShape.symm ▸ hvshape)
    (hSSeen.symm ▸ hseen)
  dsimp only at hout
  have hrun : arun k s c.classPostCandidateBody =
      arun k sinked (Cfg.classAfterAddressBody ++ Cfg.classClearBody) := by
    simp only [Cfg.classPostCandidateBody, Cfg.classAfterAddressBody,
      arun_append]
    rfl
  exact {
    viol := by rw [hrun, hout.viol, hSViol]
    vshape := by rw [hrun, hout.vshape, hSVShape]
    seen := by rw [hrun, hout.seen, hSSeen] }

set_option maxRecDepth 2000 in
/-- The complete live classifier, including offset recovery, preserves both
violation counters and advances the exact number of classified candidates.
-/
theorem ofChain_classBody_counters
    (lo segLen segCount tableHi k : Nat) (s : AState)
    (hrel : CellRel
      ((Cfg.ofChain lo segLen segCount tableHi).readPlaneCell
        (s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps) s)
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table)
        (s.regs rR -
            (Cfg.ofChain lo segLen segCount tableHi).markSteps +
          s.regs rW)))
    (hn : 0 < s.regs rR -
        (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW)
    (hN : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW ≤
        100000000)
    (hphase : s.regs 10 = 0) (hclass : s.regs 11 = 1)
    (hT : (Cfg.ofChain lo segLen segCount tableHi).markSteps ≤ s.regs rR)
    (hR : s.regs rR < M)
    (hsum : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW < M)
    (h1 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + segLen < M)
    (h2 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        2 * segLen < M)
    (h3 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        3 * segLen < M)
    (h4 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        4 * segLen < M)
    (h5 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        5 * segLen < M)
    (h6 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        6 * segLen < M)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    let c := Cfg.ofChain lo segLen segCount tableHi
    ClassCounterResult s (arun k s c.classBody) := by
  let c := Cfg.ofChain lo segLen segCount tableHi
  let j := s.regs rR - c.markSteps
  let n := j + s.regs rW
  let offset := arun k s (lift c.classOffsetBody)
  let indexed := arun k s c.classIndexBody
  have ho := c.classOffsetBody_run k s hclass hT hR
  dsimp only at ho
  have hindex := c.classIndexBody_run k s hclass hT hR hsum
  dsimp only at hindex
  have hI131 : indexed.regs 131 = j := by
    have hframe :
        (arun k offset (lift Cfg.classCandidateBody)).regs 131 =
          offset.regs 131 :=
      arun_frame k 131 (lift Cfg.classCandidateBody) (by rfl) offset
    change (arun k s
      (lift c.classOffsetBody ++ lift Cfg.classCandidateBody)).regs 131 = j
    rw [arun_append]
    exact hframe.trans ho.2.1
  have hI132 : indexed.regs 132 = n := hindex.1
  have indexFrame (r : Nat) (hw : writes r c.classIndexBody = false) :
      indexed.regs r = s.regs r :=
    arun_frame k r c.classIndexBody hw s
  have hI10 : indexed.regs 10 = 0 :=
    (indexFrame 10 (by rfl)).trans hphase
  have hI11 : indexed.regs 11 = 1 := hindex.2.1
  have hrel' : CellRel (c.readPlaneCell j indexed)
      (markCell (factorRows c.table) n) := by
    rw [c.readPlaneCell_congr j indexed s hindex.2.2]
    exact hrel
  have hIViol : indexed.regs rViol = s.regs rViol :=
    indexFrame rViol (by rfl)
  have hIVShape : indexed.regs rVShape = s.regs rVShape :=
    indexFrame rVShape (by rfl)
  have hISeen : indexed.regs rSeen = s.regs rSeen :=
    indexFrame rSeen (by rfl)
  have hout := ofChain_classPostCandidateBody_counters
    lo segLen segCount tableHi k indexed j n hrel' hn hN hI10 hI11
    hI132 hI131 h1 h2 h3 h4 h5 h6
    (hIViol.symm ▸ hviol) (hIVShape.symm ▸ hvshape)
    (hISeen.symm ▸ hseen)
  dsimp only at hout
  have houtViol :
      (arun k indexed c.classPostCandidateBody).regs rViol =
        s.regs rViol := hout.viol.trans hIViol
  have houtVShape :
      (arun k indexed c.classPostCandidateBody).regs rVShape =
        s.regs rVShape := hout.vshape.trans hIVShape
  have houtSeen :
      (arun k indexed c.classPostCandidateBody).regs rSeen =
        s.regs rSeen + 1 :=
    hout.seen.trans (congrArg (· + 1) hISeen)
  simp only [Cfg.classBody, arun_append]
  exact {
    viol := houtViol
    vshape := houtVShape
    seen := houtSeen }

/-! ## Literal complete-body counter effect -/

/-- Counter effect of one complete emitted body in the classification phase.
-/
structure BodyClassCounterResult (before out : AState) : Prop where
  viol : out.regs rViol = before.regs rViol
  vmark : out.regs rVMark = before.regs rVMark
  vshape : out.regs rVShape = before.regs rVShape
  seen : out.regs rSeen = before.regs rSeen + 1

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
/-- The inactive mark block, live classifier, position tail, and complete
log/lambda/psi arithmetic compose to one exact classification counter step.
The arithmetic suffix is framed syntactically, so this theorem does not need
`ArithmeticPre`. -/
theorem ofChain_body_classification_counters
    (lo segLen segCount tableHi k : Nat)
    (logs : List LogCell) (s : AState)
    (hTpos : 0 <
      (Cfg.ofChain lo segLen segCount tableHi).markSteps)
    (hclass :
      (Cfg.ofChain lo segLen segCount tableHi).markSteps ≤ s.regs rR)
    (hrel :
      let shape := Cfg.ofChain lo segLen segCount tableHi
      let marked := arun k s shape.markBody
      CellRel
        (shape.readPlaneCell
          (marked.regs rR - shape.markSteps) marked)
        (markCell (factorRows shape.table)
          (marked.regs rR - shape.markSteps + marked.regs rW)))
    (hn : 0 < s.regs rR -
        (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW)
    (hN : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW ≤
        100000000)
    (hR : s.regs rR < M)
    (hsum : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW < M)
    (h1 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + segLen < M)
    (h2 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        2 * segLen < M)
    (h3 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        3 * segLen < M)
    (h4 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        4 * segLen < M)
    (h5 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        5 * segLen < M)
    (h6 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        6 * segLen < M)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    let shape := Cfg.ofChain lo segLen segCount tableHi
    let c : LambdaPsiSweep.Cfg := { shape, logs }
    BodyClassCounterResult s (arun k s (LambdaPsiSweep.body c)) := by
  let shape := Cfg.ofChain lo segLen segCount tableHi
  let c : LambdaPsiSweep.Cfg := { shape, logs }
  let marked := arun k s shape.markBody
  let classified := arun k marked shape.classBody
  let tailed := arun k classified shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  dsimp only at hrel
  have hTM : shape.markSteps < M :=
    Cfg.ofChain_markSteps_lt_word lo segLen segCount tableHi
  have hclassShape : shape.markSteps ≤ s.regs rR := hclass
  have hmark := shape.markBody_class_counter_frame k s hTpos hclass hTM
    hviol hvmark
  dsimp only at hmark
  have hphase := shape.markBody_phase_run k s hTM
  dsimp only at hphase
  have hm10 : marked.regs 10 = 0 := by
    rw [hphase.1, if_neg (by omega : ¬s.regs rR < shape.markSteps)]
  have hm11 : marked.regs 11 = 1 := by
    rw [hphase.2, if_pos hclass]
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR shape.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW shape.markBody (by rfl) s
  have hmVShape : marked.regs rVShape = s.regs rVShape :=
    arun_frame k rVShape shape.markBody (by rfl) s
  have hmSeen : marked.regs rSeen = s.regs rSeen := hmark.2.2
  have hclassRun := ofChain_classBody_counters
    lo segLen segCount tableHi k marked hrel
    (by simpa only [hmR, hmW] using hn)
    (by simpa only [hmR, hmW] using hN)
    hm10 hm11 (by simpa only [hmR] using hclass)
    (by simpa only [hmR] using hR)
    (by simpa only [hmR, hmW] using hsum)
    (by simpa only [hmR] using h1)
    (by simpa only [hmR] using h2)
    (by simpa only [hmR] using h3)
    (by simpa only [hmR] using h4)
    (by simpa only [hmR] using h5)
    (by simpa only [hmR] using h6)
    (hmark.1.symm ▸ hviol) (hmVShape.symm ▸ hvshape)
    (hmSeen.symm ▸ hseen)
  dsimp only at hclassRun
  have tailFrame (r : Nat) (hw : writes r shape.tailBody = false) :
      tailed.regs r = classified.regs r :=
    arun_frame k r shape.tailBody hw classified
  have arithFrame (r : Nat)
      (hw : writes r (LambdaPsiSweep.arithmeticBody c) = false) :
      out.regs r = tailed.regs r :=
    arun_frame k r (LambdaPsiSweep.arithmeticBody c) hw tailed
  have houtEq : arun k s (LambdaPsiSweep.body c) = out := by
    rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
    simp only [arun_append]
    rfl
  refine {
    viol := by
      rw [houtEq, arithFrame rViol (by rfl), tailFrame rViol (by rfl),
        hclassRun.viol, hmark.1]
    vmark := by
      rw [houtEq, arithFrame rVMark (by rfl), tailFrame rVMark (by rfl),
        arun_frame k rVMark shape.classBody (by rfl) marked, hmark.2.1]
    vshape := by
      rw [houtEq, arithFrame rVShape (by rfl),
        tailFrame rVShape (by rfl), hclassRun.vshape, hmVShape]
    seen := by
      rw [houtEq, arithFrame rSeen (by rfl), tailFrame rSeen (by rfl),
        hclassRun.seen, hmSeen] }

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
