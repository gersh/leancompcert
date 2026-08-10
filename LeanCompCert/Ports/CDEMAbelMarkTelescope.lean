import LeanCompCert.Ports.CDEMAbelMarkScheduleStep

/-!
# Finite CDEM marking telescope

An executable pure cursor mirrors the three scheduled non-start machine
branches.  The representation theorem below telescopes literal `body`
execution; identifying the resulting plane with `Ref.deltaF` is deliberately
left as a separate arithmetic theorem.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkTelescope

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Ports.CDEMAbelMarkSchedule
open LeanCompCert.Ports.CDEMAbelMarkScheduleStep

structure MarkState where
  arr : Nat → Nat
  divisor : Nat
  sign : Nat
  multiple : Nat

def MarkState.step (c : Cfg) (w : Nat) (s : MarkState) : MarkState :=
  if s.multiple < c.segLen then
    { arr := fun j => if j = s.multiple + c.winBase then
        (s.arr (s.multiple + c.winBase) + s.sign) % M else s.arr j
      divisor := s.divisor
      sign := s.sign
      multiple := s.multiple + s.divisor }
  else if s.divisor < c.kBound then
    let d := s.divisor + 1
    let code := s.arr (d + c.muBase)
    { arr := s.arr
      divisor := d
      sign := markSignOfCode code
      multiple := markCellOfCode c w d code }
  else
    { arr := s.arr
      divisor := c.kBound
      sign := 0
      multiple := c.segLen }

def MarkState.iter (c : Cfg) (w : Nat) : Nat → MarkState → MarkState
  | 0, s => s
  | n + 1, s => (MarkState.iter c w n s).step c w

def MarkState.first (c : Cfg) (st : AState) : MarkState :=
  { arr := fun j => if j = c.winBase then
      (st.arr c.winBase + 1) % M else st.arr j
    divisor := 1
    sign := 1
    multiple := 1 }

structure MarkStateRep (c : Cfg) (w r : Nat) (model : MarkState)
    (machine : AState) : Prop where
  live : ∀ j, j ≠ c.sink → machine.arr j = model.arr j
  divisor : machine.regs rD = model.divisor
  sign : machine.regs rSg = model.sign
  multiple : machine.regs rJ = model.multiple
  cell : machine.regs rC = 0
  zero : machine.regs rZero = 0
  periodCursor : machine.regs rR = r
  window : machine.regs rW = w

inductive MarkStepReady (c : Cfg) (model : MarkState) : Prop where
  | resident
      (hcell : model.multiple < c.segLen)
      (hdK : model.divisor ≤ c.kBound)
      (hdM : model.divisor < M)
      (hcellM : model.multiple < M)
      (hsignM : model.sign < M)
      (hnextM : model.multiple + model.divisor < M)
      (haddrM : model.multiple + c.winBase < M)
  | advance
      (houtside : c.segLen ≤ model.multiple)
      (hdK : model.divisor < c.kBound)
      (hcellM : model.multiple < M)
      (hsignM : model.sign < M)
      (hnextM : model.divisor + 1 < M)
      (haddrM : model.divisor + 1 + c.muBase < M)
      (hcode : model.arr (model.divisor + 1 + c.muBase) = 0 ∨
        model.arr (model.divisor + 1 + c.muBase) = 1 ∨
        model.arr (model.divisor + 1 + c.muBase) = 2)
  | terminal
      (houtside : c.segLen ≤ model.multiple)
      (hd : model.divisor = c.kBound)
      (hcellM : model.multiple < M)
      (hsignM : model.sign < M)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem body_markState_step (c : Cfg) (idx : Nat) (st : AState)
    (w r : Nat) (model : MarkState)
    (hrep : MarkStateRep c w r model st)
    (hready : MarkStepReady c model)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hrPos : 0 < r) (hrMark : r < c.markSteps)
    (hsegPos : 0 < c.segLen) (hsegM : c.segLen < M)
    (hkPos : 0 < c.kBound) (hkM : c.kBound < M)
    (hkNextM : c.kBound + 1 < M) (hsinkM : c.sink < M)
    (hperiodM : c.period < M) (hwM : w < M) :
    MarkStateRep c w (r + 1) (model.step c w) (arun idx st c.body) := by
  cases hready with
  | resident hcell hdK hdM hcellM hsignM hnextM haddrM =>
      have hs := body_active_resident_scheduled c idx st r model.divisor
        model.multiple model.sign w hidxM hsieveM hsieve hmarkM
        hrep.periodCursor hrPos hrMark hrep.zero hrep.cell hrep.divisor
        hrep.multiple hrep.sign hrep.window hcell hdK hdM hcellM hsignM
        hnextM hsegPos hsegM hkM haddrM hsinkM hperiodM hwM
      exact
        { live := by
            intro j hj
            rw [hs.live j hj]
            simp only [MarkState.step, hcell, ↓reduceIte]
            by_cases ha : j = model.multiple + c.winBase
            · subst j
              rw [if_pos rfl, if_pos rfl, hrep.live _ (by
                unfold Cfg.sink
                omega)]
            · rw [if_neg ha, if_neg ha, hrep.live j hj]
          divisor := by simpa [MarkState.step, hcell] using hs.divisor
          sign := by simpa [MarkState.step, hcell] using hs.sign
          multiple := by simpa [MarkState.step, hcell] using hs.multiple
          cell := hs.cell
          zero := ArrayRegFrame.arun_frame idx rZero c.body (by rfl) st |>.trans
            hrep.zero
          periodCursor := hs.periodCursor
          window := hs.window }
  | advance houtside hdK hcellM hsignM hnextM haddrM hcode =>
      have haddrNe : model.divisor + 1 + c.muBase ≠ c.sink := by
        simp only [Cfg.sink, Cfg.winBase, Cfg.k1]
        omega
      have htable : st.arr (model.divisor + 1 + c.muBase) =
          model.arr (model.divisor + 1 + c.muBase) :=
        hrep.live _ haddrNe
      have hs := body_active_cursor_advance_scheduled c idx st r
        model.divisor model.multiple model.sign w
        (model.arr (model.divisor + 1 + c.muBase)) hidxM hsieveM hsieve
        hmarkM hrep.periodCursor hrPos hrMark hrep.zero hrep.cell
        hrep.divisor hrep.multiple hrep.sign hrep.window houtside hdK
        hcellM hsignM hnextM hsegPos hsegM hkM hsinkM haddrM htable
        hcode hperiodM hwM
      exact
        { live := by
            intro j hj
            rw [hs.live j hj, hrep.live j hj]
            simp [MarkState.step, Nat.not_lt.mpr houtside, hdK]
          divisor := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hdK] using
              hs.divisor
          sign := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hdK] using hs.sign
          multiple := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hdK] using
              hs.multiple
          cell := hs.cell
          zero := ArrayRegFrame.arun_frame idx rZero c.body (by rfl) st |>.trans
            hrep.zero
          periodCursor := hs.periodCursor
          window := hs.window }
  | terminal houtside hd hcellM hsignM =>
      have hs := body_active_cursor_terminal_scheduled c idx st r
        model.multiple model.sign w hidxM hsieveM hsieve hmarkM
        hrep.periodCursor hrPos hrMark hrep.zero hrep.cell
        (hrep.divisor.trans hd) hrep.multiple hrep.sign hrep.window
        houtside hcellM hsignM hkPos hkNextM hsegPos hsegM hsinkM
        hperiodM hwM
      exact
        { live := by
            intro j hj
            rw [hs.live j hj, hrep.live j hj]
            simp [MarkState.step, Nat.not_lt.mpr houtside, hd]
          divisor := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hd] using
              hs.divisor
          sign := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hd] using hs.sign
          multiple := by
            simpa [MarkState.step, Nat.not_lt.mpr houtside, hd] using
              hs.multiple
          cell := hs.cell
          zero := ArrayRegFrame.arun_frame idx rZero c.body (by rfl) st |>.trans
            hrep.zero
          periodCursor := hs.periodCursor
          window := hs.window }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem bodyIter_markState_refines (c : Cfg) (idx n : Nat) (st : AState)
    (w r : Nat) (model : MarkState)
    (hrep : MarkStateRep c w r model st)
    (hready : ∀ i, i < n → MarkStepReady c (model.iter c w i))
    (hspan : r + n ≤ c.markSteps)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hrPos : 0 < r) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hkPos : 0 < c.kBound)
    (hkM : c.kBound < M) (hkNextM : c.kBound + 1 < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M) (hwM : w < M) :
    MarkStateRep c w (r + n) (model.iter c w n)
      (bodyIter c idx n st) := by
  induction n with
  | zero => simpa [MarkState.iter, bodyIter] using hrep
  | succ n ih =>
      have hpre := ih
        (fun i hi => hready i (by omega)) (by omega)
      have hs := body_markState_step c idx (bodyIter c idx n st) w (r + n)
        (model.iter c w n) hpre (hready n (by omega)) hidxM hsieveM
        hsieve hmarkM (by omega) (by omega) hsegPos hsegM hkPos hkM
        hkNextM hsinkM hperiodM hwM
      simpa [MarkState.iter, bodyIter, Nat.add_assoc] using hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem body_first_markState_rep (c : Cfg) (idx : Nat) (st : AState)
    (w : Nat) (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hperiodM : c.period < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hsegPos : 0 < c.segLen) (hkPos : 0 < c.kBound)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hwinM : c.winBase < M) (hsinkM : c.sink < M)
    (hW : st.regs rW = w) (hwM : w < M) :
    MarkStateRep c w 1 (MarkState.first c st) (arun idx st c.body) := by
  have hf := body_first_scheduled_mark c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hperiodM hR hzero hsegPos hkPos hsegM hkM hwinM
    hsinkM (by rw [hW]; exact hwM)
  exact
    { live := by
        intro j hj
        simpa [MarkState.first] using hf.live j hj
      divisor := by simpa [MarkState.first] using hf.divisor
      sign := by simpa [MarkState.first] using hf.sign
      multiple := by simpa [MarkState.first] using hf.multiple
      cell := hf.cell
      zero := (ArrayRegFrame.arun_frame idx rZero c.body (by rfl) st).trans
        hzero
      periodCursor := hf.periodCursor
      window := by rw [hf.window, hW] }

theorem bodyIter_succ_seed (c : Cfg) (idx n : Nat) (st : AState) :
    bodyIter c idx (n + 1) st =
      bodyIter c idx n (arun idx st c.body) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change arun idx (bodyIter c idx (n + 1) st) c.body =
        arun idx (bodyIter c idx n (arun idx st c.body)) c.body
      exact congrArg (fun s => arun idx s c.body) ih

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem bodyIter_markState_from_start (c : Cfg) (idx n : Nat) (st : AState)
    (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (arun idx st c.body))
    (hready : ∀ i, i < n →
      MarkStepReady c ((MarkState.first c st).iter c w i))
    (hspan : 1 + n ≤ c.markSteps)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hsegPos : 0 < c.segLen) (hsegM : c.segLen < M)
    (hkPos : 0 < c.kBound) (hkM : c.kBound < M)
    (hkNextM : c.kBound + 1 < M) (hsinkM : c.sink < M)
    (hperiodM : c.period < M) (hwM : w < M) :
    MarkStateRep c w (1 + n)
      ((MarkState.first c st).iter c w n) (bodyIter c idx (n + 1) st) := by
  have htrace := bodyIter_markState_refines c idx n (arun idx st c.body)
    w 1 (MarkState.first c st) hfirst hready hspan hidxM hsieveM hsieve
    hmarkM (by omega) hsegPos hsegM hkPos hkM hkNextM hsinkM hperiodM hwM
  rw [bodyIter_succ_seed]
  exact htrace

end LeanCompCert.Ports.CDEMAbelMarkTelescope
