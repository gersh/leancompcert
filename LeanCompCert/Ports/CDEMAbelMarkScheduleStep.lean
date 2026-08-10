import LeanCompCert.Ports.CDEMAbelMarkSchedule

/-!
# Non-start CDEM marking schedule steps

This module factors the common selector/sieve prelude and inactive
accumulator/tail suffix used by every non-start active marking transition.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkScheduleStep

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Ports.CDEMAbelMarkSchedule

def markPreludeRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (arun idx st c.selectors) c.sieveBody

structure MarkPreludeSpec (c : Cfg) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  phase : after.regs 41 = 1
  markGate : after.regs 42 = 1
  accGate : after.regs 43 = 0
  zero : after.regs rZero = 0
  periodCursor : after.regs rR = before.regs rR
  divisor : after.regs rD = before.regs rD
  sign : after.regs rSg = before.regs rSg
  multiple : after.regs rJ = before.regs rJ
  cell : after.regs rC = before.regs rC
  window : after.regs rW = before.regs rW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem markPrelude_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : st.regs rR < c.markSteps) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    MarkPreludeSpec c st (markPreludeRun c idx st) := by
  let selected := arun idx st c.selectors
  have hsel := selectors_mark_run c idx st hidxM hsieveM hsieve hmarkM hR
  change selected.regs 40 = 0 ∧ selected.regs 41 = 1 ∧
      selected.regs 42 = 1 ∧ selected.regs 43 = 0 ∧
      selected.arr = st.arr at hsel
  have selectedFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.selectors = false) :
      selected.regs j = st.regs j :=
    ArrayRegFrame.arun_frame idx j c.selectors hwrites st
  have hselectedZero : selected.regs rZero = 0 :=
    (selectedFrame rZero (by rfl)).trans hzero
  let sieved := arun idx selected c.sieveBody
  have hsieveLive := sieve_inactive_live_frame c idx selected hsel.1
    hselectedZero hsinkM
  have sieveFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.sieveBody = false) :
      sieved.regs j = selected.regs j :=
    ArrayRegFrame.arun_frame idx j c.sieveBody hwrites selected
  have hall : MarkPreludeSpec c st sieved :=
    { live := fun j hj => (hsieveLive j hj).trans
        (congrFun hsel.2.2.2.2 j)
      phase := (sieveFrame 41 (by rfl)).trans hsel.2.1
      markGate := (sieveFrame 42 (by rfl)).trans hsel.2.2.1
      accGate := (sieveFrame 43 (by rfl)).trans hsel.2.2.2.1
      zero := (sieveFrame rZero (by rfl)).trans hselectedZero
      periodCursor := (sieveFrame rR (by rfl)).trans
        (selectedFrame rR (by rfl))
      divisor := (sieveFrame rD (by rfl)).trans
        (selectedFrame rD (by rfl))
      sign := (sieveFrame rSg (by rfl)).trans
        (selectedFrame rSg (by rfl))
      multiple := (sieveFrame rJ (by rfl)).trans
        (selectedFrame rJ (by rfl))
      cell := (sieveFrame rC (by rfl)).trans
        (selectedFrame rC (by rfl))
      window := (sieveFrame rW (by rfl)).trans
        (selectedFrame rW (by rfl)) }
  simpa [markPreludeRun, selected, sieved] using hall

set_option maxRecDepth 4096 in
theorem markBody_active_cell_frame (c : Cfg) (idx : Nat) (st : AState)
    (hphase : st.regs 41 = 1) (hR : st.regs rR ≠ 0)
    (hcellM : st.regs rC < M) :
    (arun idx st c.markBody).regs rC = st.regs rC := by
  let pre := arun idx st (c.markBody.take 21)
  have hR2 : st.regs 2 ≠ 0 := by simpa [rR] using hR
  have hCmod : st.regs 15 % M = st.regs 15 := by
    exact Nat.mod_eq_of_lt (by simpa [rC] using hcellM)
  have hpre : pre.regs rC = st.regs rC := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rSg, rJ, hphase, hR2, hCmod]
  have htail : (arun idx pre (c.markBody.drop 21)).regs rC = pre.regs rC :=
    ArrayRegFrame.arun_frame idx rC (c.markBody.drop 21) (by rfl) pre
  rw [← List.take_append_drop 21 c.markBody, arun_append]
  exact htail.trans hpre

structure MarkSuffixSpec (c : Cfg) (target : Nat → Nat)
    (d sign multiple cell nextR window : Nat) (after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = target j
  divisor : after.regs rD = d
  sign : after.regs rSg = sign
  multiple : after.regs rJ = multiple
  cell : after.regs rC = cell
  periodCursor : after.regs rR = nextR
  window : after.regs rW = window

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markSuffix_run (c : Cfg) (idx : Nat) (marked : AState)
    (target : Nat → Nat) (d sign multiple cell r window : Nat)
    (hlive : ∀ j, j ≠ c.sink → marked.arr j = target j)
    (hD : marked.regs rD = d) (hSg : marked.regs rSg = sign)
    (hJ : marked.regs rJ = multiple) (hC : marked.regs rC = cell)
    (hphase : marked.regs 41 = 1) (hgate : marked.regs 43 = 0)
    (hzero : marked.regs rZero = 0) (hR : marked.regs rR = r)
    (hW : marked.regs rW = window) (hcellZero : cell = 0)
    (hnext : r + 1 < c.period) (hnextM : r + 1 < M)
    (hperiodM : c.period < M) (hsegM : c.segLen < M)
    (hsinkM : c.sink < M) (hwindowM : window < M) :
    MarkSuffixSpec c target d sign multiple cell (r + 1) window
      (arun idx (arun idx marked c.accBody) c.tailBody) := by
  have haccCursor := accBody_cursor_frame c idx marked
  have haccLive := accBody_inactive_live_frame c idx marked hgate hzero
    hsinkM
  have haccD : (arun idx marked c.accBody).regs rD = d :=
    (accBody_divisor_frame c idx marked).trans hD
  have haccSg : (arun idx marked c.accBody).regs rSg = sign :=
    (accBody_sign_frame c idx marked).trans hSg
  have haccJ : (arun idx marked c.accBody).regs rJ = multiple :=
    (accBody_multiple_frame c idx marked).trans hJ
  have haccC : (arun idx marked c.accBody).regs rC = cell := by
    have hC0 : marked.regs rC = 0 := hC.trans hcellZero
    exact (accBody_inactive_cell_zero c idx marked hgate hzero
      hsinkM hC0).trans hcellZero.symm
  have haccPhase : (arun idx marked c.accBody).regs 41 = 1 :=
    haccCursor.phase.trans hphase
  have haccR : (arun idx marked c.accBody).regs rR = r :=
    haccCursor.cursor.trans hR
  have haccW : (arun idx marked c.accBody).regs rW = window :=
    haccCursor.window.trans hW
  have ht := tail_continue_window_run c idx (arun idx marked c.accBody)
    haccPhase
    (by rw [haccR]; exact hnext) (by rw [haccR]; exact hnextM)
    hperiodM hsegM (by rw [haccW]; exact hwindowM)
  dsimp only at ht
  have htailArr := arun_store_free_arr idx c.tailBody
    (arun idx marked c.accBody) (by rfl)
  have tailFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.tailBody = false) :
      (arun idx (arun idx marked c.accBody) c.tailBody).regs j =
        (arun idx marked c.accBody).regs j :=
    ArrayRegFrame.arun_frame idx j c.tailBody hwrites
      (arun idx marked c.accBody)
  exact
    { live := fun j hj => by
        rw [congrFun htailArr j]
        exact (haccLive j hj).trans (hlive j hj)
      divisor := (tailFrame rD (by rfl)).trans haccD
      sign := (tailFrame rSg (by rfl)).trans haccSg
      multiple := (tailFrame rJ (by rfl)).trans haccJ
      cell := (tailFrame rC (by rfl)).trans haccC
      periodCursor := ht.1.trans (by rw [haccR])
      window := ht.2.trans haccW }

theorem body_mark_step_run (c : Cfg) (idx : Nat) (st : AState) :
    arun idx st c.body =
      arun idx (arun idx (arun idx (markPreludeRun c idx st) c.markBody)
        c.accBody) c.tailBody := by
  rw [body_mark_split, arun_append, arun_append, arun_append, arun_append]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem body_active_resident_scheduled (c : Cfg) (idx : Nat) (st : AState)
    (r d cell sign w : Nat)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : st.regs rR = r) (hrPos : 0 < r) (hrMark : r < c.markSteps)
    (hzero : st.regs rZero = 0) (hC : st.regs rC = 0)
    (hD : st.regs rD = d) (hJ : st.regs rJ = cell)
    (hSg : st.regs rSg = sign) (hW : st.regs rW = w)
    (hcellSeg : cell < c.segLen) (hdK : d ≤ c.kBound)
    (hdM : d < M) (hcellM : cell < M) (hsignM : sign < M)
    (hmultipleM : cell + d < M) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (haddrM : cell + c.winBase < M) (hsinkM : c.sink < M)
    (hperiodM : c.period < M) (hwM : w < M) :
    MarkSuffixSpec c
      (fun j => if j = cell + c.winBase then
        (st.arr (cell + c.winBase) + sign) % M else st.arr j)
      d sign (cell + d) 0 (r + 1) w (arun idx st c.body) := by
  let pre := markPreludeRun c idx st
  have hp := markPrelude_run c idx st hidxM hsieveM hsieve hmarkM
    (by rw [hR]; exact hrMark) hzero hsinkM
  change MarkPreludeSpec c st pre at hp
  have hpreRne : pre.regs rR ≠ 0 := by rw [hp.periodCursor, hR]; omega
  let marked := arun idx pre c.markBody
  have hm := markBody_active_resident_transition c idx pre d cell sign
    hp.phase hp.markGate hpreRne hp.zero (hp.divisor.trans hD)
    (hp.multiple.trans hJ) (hp.sign.trans hSg) hcellSeg hdK hdM
    hcellM hsignM hmultipleM hsegM hkM haddrM
  have haddrNe : cell + c.winBase ≠ c.sink := by
    unfold Cfg.sink
    omega
  have hmarkedLive : ∀ j, j ≠ c.sink → marked.arr j =
      if j = cell + c.winBase then
        (st.arr (cell + c.winBase) + sign) % M else st.arr j := by
    intro j hj
    rw [hm.array j]
    by_cases ha : j = cell + c.winBase
    · subst j
      rw [if_pos rfl, if_pos rfl, hp.live _ haddrNe]
    · rw [if_neg ha, if_neg ha, hp.live j hj]
  have markedFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.markBody = false) :
      marked.regs j = pre.regs j :=
    ArrayRegFrame.arun_frame idx j c.markBody hwrites pre
  have hmarkedC : marked.regs rC = 0 := by
    rw [show marked.regs rC = pre.regs rC from
      markBody_active_cell_frame c idx pre hp.phase hpreRne
        (by rw [hp.cell, hC]; decide), hp.cell, hC]
  have hnext : r + 1 < c.period := by
    simp only [Cfg.period, Cfg.accSteps]
    have : 0 < c.segLen * (c.bsSteps + 1) :=
      Nat.mul_pos hsegPos (by omega)
    omega
  have hnextM : r + 1 < M := by omega
  have hs := markSuffix_run c idx marked
    (fun j => if j = cell + c.winBase then
      (st.arr (cell + c.winBase) + sign) % M else st.arr j)
    d sign (cell + d) 0 r w hmarkedLive hm.divisor hm.sign hm.multiple
    hmarkedC ((markedFrame 41 (by rfl)).trans hp.phase)
    ((markedFrame 43 (by rfl)).trans hp.accGate)
    ((markedFrame rZero (by rfl)).trans hp.zero)
    ((markedFrame rR (by rfl)).trans (hp.periodCursor.trans hR))
    ((markedFrame rW (by rfl)).trans (hp.window.trans hW)) rfl
    hnext hnextM hperiodM hsegM hsinkM hwM
  rw [body_mark_step_run]
  exact hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem body_active_cursor_advance_scheduled (c : Cfg) (idx : Nat)
    (st : AState) (r d cell sign w code : Nat)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : st.regs rR = r) (hrPos : 0 < r) (hrMark : r < c.markSteps)
    (hzero : st.regs rZero = 0) (hC : st.regs rC = 0)
    (hD : st.regs rD = d) (hJ : st.regs rJ = cell)
    (hSg : st.regs rSg = sign) (hW : st.regs rW = w)
    (houtside : c.segLen ≤ cell) (hdK : d < c.kBound)
    (hcellM : cell < M) (hsignM : sign < M)
    (hdNextM : d + 1 < M) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hsinkM : c.sink < M) (haddrM : d + 1 + c.muBase < M)
    (htable : st.arr (d + 1 + c.muBase) = code)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2)
    (hperiodM : c.period < M) (hwM : w < M) :
    MarkSuffixSpec c st.arr (d + 1) (markSignOfCode code)
      (markCellOfCode c w (d + 1) code) 0 (r + 1) w
      (arun idx st c.body) := by
  let pre := markPreludeRun c idx st
  have hp := markPrelude_run c idx st hidxM hsieveM hsieve hmarkM
    (by rw [hR]; exact hrMark) hzero hsinkM
  change MarkPreludeSpec c st pre at hp
  have hpreRne : pre.regs rR ≠ 0 := by rw [hp.periodCursor, hR]; omega
  have haddrNe : d + 1 + c.muBase ≠ c.sink := by
    simp only [Cfg.sink, Cfg.winBase, Cfg.k1]
    omega
  have htablePre : pre.arr (d + 1 + c.muBase) = code :=
    (hp.live _ haddrNe).trans htable
  let marked := arun idx pre c.markBody
  have hm := markBody_active_cursor_advance c idx pre d cell sign w code
    hp.phase hp.markGate hpreRne hp.zero (hp.divisor.trans hD)
    (hp.multiple.trans hJ) (hp.sign.trans hSg) (hp.window.trans hW)
    houtside hdK hcellM hsignM hdNextM hsegM hkM hsinkM haddrM
    htablePre hcode
  have hmarkedLive : ∀ j, j ≠ c.sink → marked.arr j = st.arr j :=
    fun j hj => (hm.live j hj).trans (hp.live j hj)
  have markedFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.markBody = false) :
      marked.regs j = pre.regs j :=
    ArrayRegFrame.arun_frame idx j c.markBody hwrites pre
  have hmarkedC : marked.regs rC = 0 := by
    rw [show marked.regs rC = pre.regs rC from
      markBody_active_cell_frame c idx pre hp.phase hpreRne
        (by rw [hp.cell, hC]; decide), hp.cell, hC]
  have hnext : r + 1 < c.period := by
    simp only [Cfg.period, Cfg.accSteps]
    have : 0 < c.segLen * (c.bsSteps + 1) :=
      Nat.mul_pos hsegPos (by omega)
    omega
  have hnextM : r + 1 < M := by omega
  have hs := markSuffix_run c idx marked st.arr (d + 1)
    (markSignOfCode code) (markCellOfCode c w (d + 1) code) 0 r w
    hmarkedLive hm.divisor hm.sign hm.multiple hmarkedC
    ((markedFrame 41 (by rfl)).trans hp.phase)
    ((markedFrame 43 (by rfl)).trans hp.accGate)
    ((markedFrame rZero (by rfl)).trans hp.zero)
    ((markedFrame rR (by rfl)).trans (hp.periodCursor.trans hR))
    ((markedFrame rW (by rfl)).trans (hp.window.trans hW)) rfl
    hnext hnextM hperiodM hsegM hsinkM hwM
  rw [body_mark_step_run]
  exact hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem body_active_cursor_terminal_scheduled (c : Cfg) (idx : Nat)
    (st : AState) (r cell sign w : Nat)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : st.regs rR = r) (hrPos : 0 < r) (hrMark : r < c.markSteps)
    (hzero : st.regs rZero = 0) (hC : st.regs rC = 0)
    (hD : st.regs rD = c.kBound) (hJ : st.regs rJ = cell)
    (hSg : st.regs rSg = sign) (hW : st.regs rW = w)
    (houtside : c.segLen ≤ cell) (hcellM : cell < M)
    (hsignM : sign < M) (hkPos : 0 < c.kBound)
    (hkNextM : c.kBound + 1 < M) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hsinkM : c.sink < M)
    (hperiodM : c.period < M) (hwM : w < M) :
    MarkSuffixSpec c st.arr c.kBound 0 c.segLen 0 (r + 1) w
      (arun idx st c.body) := by
  let pre := markPreludeRun c idx st
  have hp := markPrelude_run c idx st hidxM hsieveM hsieve hmarkM
    (by rw [hR]; exact hrMark) hzero hsinkM
  change MarkPreludeSpec c st pre at hp
  have hpreRne : pre.regs rR ≠ 0 := by rw [hp.periodCursor, hR]; omega
  let marked := arun idx pre c.markBody
  have hm := markBody_active_cursor_terminal c idx pre cell sign hp.phase
    hp.markGate hpreRne hp.zero (hp.divisor.trans hD)
    (hp.multiple.trans hJ) (hp.sign.trans hSg) houtside hcellM hsignM
    hkPos hkNextM hsegM hsinkM
  have hmarkedLive : ∀ j, j ≠ c.sink → marked.arr j = st.arr j :=
    fun j hj => (hm.live j hj).trans (hp.live j hj)
  have markedFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.markBody = false) :
      marked.regs j = pre.regs j :=
    ArrayRegFrame.arun_frame idx j c.markBody hwrites pre
  have hmarkedC : marked.regs rC = 0 := by
    rw [show marked.regs rC = pre.regs rC from
      markBody_active_cell_frame c idx pre hp.phase hpreRne
        (by rw [hp.cell, hC]; decide), hp.cell, hC]
  have hnext : r + 1 < c.period := by
    simp only [Cfg.period, Cfg.accSteps]
    have : 0 < c.segLen * (c.bsSteps + 1) :=
      Nat.mul_pos hsegPos (by omega)
    omega
  have hnextM : r + 1 < M := by omega
  have hs := markSuffix_run c idx marked st.arr c.kBound 0 c.segLen 0 r w
    hmarkedLive hm.divisor hm.sign hm.multiple hmarkedC
    ((markedFrame 41 (by rfl)).trans hp.phase)
    ((markedFrame 43 (by rfl)).trans hp.accGate)
    ((markedFrame rZero (by rfl)).trans hp.zero)
    ((markedFrame rR (by rfl)).trans (hp.periodCursor.trans hR))
    ((markedFrame rW (by rfl)).trans (hp.window.trans hW)) rfl
    hnext hnextM hperiodM hsegM hsinkM hwM
  rw [body_mark_step_run]
  exact hs

end LeanCompCert.Ports.CDEMAbelMarkScheduleStep
