import LeanCompCert.Ports.CDEMAbelOuter

namespace LeanCompCert.Ports.CDEMAbelOuterSchedule

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelSchedule
open LeanCompCert.Ports.CDEMAbelOuter

structure AccBodyCursorFrame (before after : AState) : Prop where
  phase : after.regs 41 = before.regs 41
  cursor : after.regs rR = before.regs rR
  window : after.regs rW = before.regs rW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem accBody_cursor_frame (c : Cfg) (idx : Nat) (st : AState) :
    AccBodyCursorFrame st (arun idx st c.accBody) :=
  { phase := LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 41 c.accBody
      (by rfl) st
    cursor := LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rR c.accBody
      (by rfl) st
    window := LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rW c.accBody
      (by rfl) st }

theorem tail_continue_window_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hnext : st.regs rR + 1 < c.period)
    (hnextM : st.regs rR + 1 < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hWword : st.regs rW < M) :
    let out := arun idx st c.tailBody
    out.regs rR = st.regs rR + 1 ∧ out.regs rW = st.regs rW := by
  rw [tail_lift, arun_lift]
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiodM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hwMod' : st.regs 3 % M = st.regs 3 := by
    exact Nat.mod_eq_of_lt (by simpa [rW] using hWword)
  have hne : st.regs rR + 1 ≠ c.period := by omega
  have hnextM' : st.regs 2 + 1 < M := by simpa [rR] using hnextM
  have hnextMod' : (st.regs 2 + 1) % M = st.regs 2 + 1 := by
    exact Nat.mod_eq_of_lt hnextM'
  have hne' : st.regs 2 + 1 ≠ c.period := by simpa [rR] using hne
  simp [tailS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, rW, hgate, hnextMod', hperiodMod, hsegMod, hwMod', hne']

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem body_cursor_continue_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hmarkPos : 0 < c.markSteps) (hR : c.markSteps ≤ st.regs rR)
    (hnext : st.regs rR + 1 < c.period)
    (hnextM : st.regs rR + 1 < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) :
    let out := arun idx st c.body
    out.regs rR = st.regs rR + 1 ∧ out.regs rW = st.regs rW := by
  let prefixed := arun idx st (accPrefix c)
  let accumulated := arun idx prefixed c.accBody
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR hword harrword
  have hp41 : prefixed.regs 41 = 1 := by simpa [prefixed] using hp.phase
  have ha := accBody_cursor_frame c idx prefixed
  have ha41 : accumulated.regs 41 = 1 := by
    rw [show accumulated.regs 41 = prefixed.regs 41 from ha.phase, hp41]
  have prefR : prefixed.regs rR = st.regs rR := by
    simpa [prefixed] using hp.cursor
  have accR : accumulated.regs rR = prefixed.regs rR := ha.cursor
  have prefW : prefixed.regs rW = st.regs rW := by
    simpa [prefixed] using hp.window
  have accW : accumulated.regs rW = prefixed.regs rW := ha.window
  have haccWword : accumulated.regs rW < M := by
    rw [accW, prefW]
    exact hword rW
  have ht := tail_continue_window_run c idx accumulated ha41
    (by rw [accR, prefR]; exact hnext)
    (by rw [accR, prefR]; exact hnextM) hperiodM hsegM haccWword
  dsimp only at ht
  rw [body_acc_run_decomp]
  exact ⟨ht.1.trans (by rw [accR, prefR]),
    ht.2.trans (accW.trans prefW)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem body_cursor_wrap_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hmarkPos : 0 < c.markSteps) (hR : c.markSteps ≤ st.regs rR)
    (hnext : st.regs rR + 1 = c.period)
    (hperiodM : c.period < M) (hsegM : c.segLen < M)
    (hWnext : st.regs rW + c.segLen < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    let out := arun idx st c.body
    out.regs rR = 0 ∧ out.regs rW = st.regs rW + c.segLen := by
  let prefixed := arun idx st (accPrefix c)
  let accumulated := arun idx prefixed c.accBody
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR hword harrword
  have hp41 : prefixed.regs 41 = 1 := by simpa [prefixed] using hp.phase
  have ha := accBody_cursor_frame c idx prefixed
  have ha41 : accumulated.regs 41 = 1 := by
    rw [show accumulated.regs 41 = prefixed.regs 41 from ha.phase, hp41]
  have prefR : prefixed.regs rR = st.regs rR := by
    simpa [prefixed] using hp.cursor
  have accR : accumulated.regs rR = prefixed.regs rR := ha.cursor
  have prefW : prefixed.regs rW = st.regs rW := by
    simpa [prefixed] using hp.window
  have accW : accumulated.regs rW = prefixed.regs rW := ha.window
  have ht := tail_wrap_run c idx accumulated ha41
    (by rw [accR, prefR]; exact hnext) hperiodM hsegM
    (by rw [accW, prefW]; exact hWnext)
  dsimp only at ht
  rw [body_acc_run_decomp]
  exact ⟨ht.1, ht.2.1.trans (by rw [accW, prefW])⟩

def bodyIter (c : Cfg) (idx : Nat) : Nat → AState → AState
  | 0, st => st
  | n + 1, st => arun idx (bodyIter c idx n st) c.body

structure OuterMiddleTraceSpec (c : Cfg) (k : Nat) (p : Bracket)
    (n : Nat) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  sink_zero : n ≠ 0 → after.arr c.sink = 0
  f : after.regs rF = before.regs rF
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  low : after.regs rSl = (forwardIter c.wScale k n p).lo
  high : after.regs rSh = (forwardIter c.wScale k n p).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + n
  cell : after.regs rC = before.regs rC

theorem bodyIter_middle_contracts (c : Cfg) (idx n : Nat) (st : AState)
    (k : Nat) (p : Bracket)
    (hlo : st.regs rSl = p.lo) (hhi : st.regs rSh = p.hi)
    (hcontract : ∀ i, i < n →
      OuterMiddleSpec c k (forwardIter c.wScale k i p)
        (bodyIter c idx i st) (bodyIter c idx (i + 1) st)) :
    OuterMiddleTraceSpec c k p n st (bodyIter c idx n st) := by
  induction n with
  | zero =>
      exact
        { live := by intro j _; rfl
          sink_zero := by simp
          f := rfl
          t := rfl
          t2 := rfl
          e := rfl
          tv := rfl
          low := hlo
          high := hhi
          uPos := rfl
          uNeg := rfl
          viol := rfl
          vDiv := rfl
          vBisect := rfl
          v := rfl
          round := by simp [bodyIter]
          cell := rfl }
  | succ n ih =>
      have hpre : ∀ i, i < n →
          OuterMiddleSpec c k (forwardIter c.wScale k i p)
            (bodyIter c idx i st) (bodyIter c idx (i + 1) st) :=
        fun i hi => hcontract i (by omega)
      have hi := ih hpre
      have hs := hcontract n (by omega)
      exact
        { live := by
            intro j hj
            exact (hs.arr.live j hj).trans (hi.live j hj)
          sink_zero := by intro _; exact hs.arr.sink_zero
          f := hs.f.trans hi.f
          t := hs.t.trans hi.t
          t2 := hs.t2.trans hi.t2
          e := hs.e.trans hi.e
          tv := hs.tv.trans hi.tv
          low := hs.low
          high := hs.high
          uPos := hs.uPos.trans hi.uPos
          uNeg := hs.uNeg.trans hi.uNeg
          viol := hs.viol.trans hi.viol
          vDiv := hs.vDiv.trans hi.vDiv
          vBisect := hs.vBisect.trans hi.vBisect
          v := hs.v.trans hi.v
          round := by rw [hs.round, hi.round]; omega
          cell := hs.cell.trans hi.cell }

def bodySchedule (c : Cfg) (idx middleCount : Nat) (st : AState) : AState :=
  arun idx (bodyIter c idx middleCount (arun idx st c.body)) c.body

structure OuterFullAccSpec (c : Cfg) (k dp dn ceil floor root d : Nat)
    (before after : AState) : Prop where
  sink_zero : after.arr c.sink = 0
  live : ∀ j, j ≠ c.sink → after.arr j =
    if j = before.regs rC + c.winBase then 0 else before.arr j
  f : after.regs rF =
    (before.regs rF + before.arr (before.regs rC + c.winBase)) % M
  t : after.regs rT =
    if before.regs rW + before.regs rC < before.regs rT2 then
      before.regs rT else before.regs rT + 1
  t2 : after.regs rT2 =
    if before.regs rW + before.regs rC < before.regs rT2 then
      before.regs rT2
    else before.regs rT2 + (2 * (before.regs rT + 1) + 1)
  e : after.regs rE = headG
    ((before.regs rF + before.arr (before.regs rC + c.winBase)) % M)
  tv : after.regs rTv = before.regs rTv + dp + dn
  low : after.regs rSl = root
  high : after.regs rSh = root
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi) + dp * ceil
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi) + dn * floor
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * root
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

theorem bodySchedule_of_contracts (c : Cfg) (idx middleCount : Nat)
    (st : AState) (k dp dn ceil floor root d : Nat)
    (hf : OuterFirstSpec c k dp dn ceil floor st (arun idx st c.body))
    (hm : OuterMiddleTraceSpec c k (initial c.wScale k) middleCount
      (arun idx st c.body)
      (bodyIter c idx middleCount (arun idx st c.body)))
    (hl : OuterFinalSpec c root d
      (bodyIter c idx middleCount (arun idx st c.body))
      (bodySchedule c idx middleCount st)) :
    OuterFullAccSpec c k dp dn ceil floor root d st
      (bodySchedule c idx middleCount st) := by
  exact
    { sink_zero := hl.arr.sink_zero
      live := by
        intro j hj
        exact (hl.arr.live j hj).trans ((hm.live j hj).trans (hf.arr.live j hj))
      f := hl.f.trans (hm.f.trans hf.f)
      t := hl.t.trans (hm.t.trans hf.t)
      t2 := hl.t2.trans (hm.t2.trans hf.t2)
      e := hl.e.trans (hm.e.trans hf.e)
      tv := hl.tv.trans (hm.tv.trans hf.tv)
      low := hl.low
      high := hl.high
      uPos := hl.uPos.trans (hm.uPos.trans hf.uPos)
      uNeg := hl.uNeg.trans (hm.uNeg.trans hf.uNeg)
      viol := hl.viol.trans (hm.viol.trans hf.viol)
      vDiv := hl.vDiv.trans (hm.vDiv.trans hf.vDiv)
      vBisect := hl.vBisect.trans (hm.vBisect.trans hf.vBisect)
      v := by rw [hl.v, hm.v, hf.v]
      round := hl.round
      cell := by rw [hl.cell, hm.cell, hf.cell] }

end LeanCompCert.Ports.CDEMAbelOuterSchedule
