import LeanCompCert.Ports.CDEMAbelSourceReady

/-!
# Interior source-state step for the CDEM Abel scan

This module turns the complete literal cell contract into the source-shaped
state needed by the following cell.  It deliberately treats only an interior
cell: at a window boundary the emitted marking phase resets the cell cursor
and installs a new resident floor-convolution window.
-/

namespace LeanCompCert.Ports.CDEMAbelSourceTelescope

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
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelOuterReady
open LeanCompCert.Ports.CDEMAbelSourceReady

/-- Source-visible state after one complete interior production cell.  The
next resident array cell is unchanged, so the following `nextF` is exactly the
current prefix plus that pre-marked increment. -/
structure InteriorStreamStepSpec (c : Cfg) (dp dn : Nat)
    (before after : AState) : Prop where
  window : after.regs rW = before.regs rW
  cell : after.regs rC = before.regs rC + 1
  f : after.regs rF = nextF c before
  e : after.regs rE = headG (nextF c before)
  tv : after.regs rTv = before.regs rTv + dp + dn
  nextCell : after.arr (after.regs rC + c.winBase) =
    before.arr (before.regs rC + 1 + c.winBase)
  nextF : nextF c after =
    (nextF c before +
      before.arr (before.regs rC + 1 + c.winBase)) % M
  sqrt : SqrtStreamInv after

/-- Square-root stream state indexed by a logical paper key.  Unlike
`SqrtStreamInv`, this remains meaningful during the transient window-wrap
state where `rW` has advanced but `rC` has not yet been reset. -/
structure SqrtStreamInvAt (key : Nat) (st : AState) : Prop where
  nextSquare : st.regs rT2 = (st.regs rT + 1) * (st.regs rT + 1)
  lower : st.regs rT * st.regs rT ≤ key
  oneBump : key < (st.regs rT + 2) * (st.regs rT + 2)

theorem sqrtStreamInvAt_of_full (c : Cfg) (before after : AState)
    (k dp dn ceil floor root d : Nat)
    (hentry : FirstEntryInv c before)
    (hfull : OuterFullAccSpec c k dp dn ceil floor root d before after) :
    SqrtStreamInvAt (nextKey before + 1) after := by
  have ht : after.regs rT = Nat.sqrt (nextKey before) := by
    rw [hfull.t]
    exact sqrtStream_step before hentry.sqrt
  have ht2 : after.regs rT2 =
      (after.regs rT + 1) * (after.regs rT + 1) := by
    by_cases hlt : nextKey before < before.regs rT2
    · rw [hfull.t, hfull.t2]
      simp only [nextKey] at hlt
      rw [if_pos hlt, if_pos hlt, hentry.sqrt.nextSquare]
    · rw [hfull.t, hfull.t2]
      simp only [nextKey] at hlt
      rw [if_neg hlt, if_neg hlt, hentry.sqrt.nextSquare]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
  have hlower :
      after.regs rT * after.regs rT ≤
        nextKey before + 1 := by
    rw [ht]
    exact Nat.le_trans (Nat.sqrt_le (nextKey before))
      (Nat.le_add_right _ _)
  have honeBump :
      nextKey before + 1 <
        (after.regs rT + 2) * (after.regs rT + 2) := by
    rw [ht]
    have hs := Nat.lt_succ_sqrt (nextKey before)
    have hq : Nat.sqrt (nextKey before) + 1 <
        Nat.sqrt (nextKey before) + 2 := by omega
    have hsq :
        (Nat.sqrt (nextKey before) + 1) *
            (Nat.sqrt (nextKey before) + 1) <
          (Nat.sqrt (nextKey before) + 2) *
            (Nat.sqrt (nextKey before) + 2) :=
      Nat.mul_lt_mul_of_lt_of_lt hq hq
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hs) hsq
  exact ⟨ht2, hlower, honeBump⟩

theorem interior_stream_step_of_full (c : Cfg) (before after : AState)
    (k dp dn ceil floor root d cell startR startW : Nat)
    (hentry : FirstEntryInv c before)
    (hfull : OuterFullAccSpec c k dp dn ceil floor root d before after)
    (hcursor : ProductionCellCursorSpec c cell startR startW after)
    (hcell : before.regs rC = cell)
    (hstartW : before.regs rW = startW)
    (hinterior : cell + 1 < c.segLen) :
    InteriorStreamStepSpec c dp dn before after := by
  have hnotLast : cell + 1 ≠ c.segLen := by omega
  have hwindow : after.regs rW = before.regs rW := by
    rw [hcursor.window, if_neg hnotLast, ← hstartW]
  have hcellAfter : after.regs rC = before.regs rC + 1 := hfull.cell
  have hnextAddrNeSink :
      before.regs rC + 1 + c.winBase ≠ c.sink := by
    unfold Cfg.sink
    rw [hcell]
    omega
  have hnextAddrNeCurrent :
      before.regs rC + 1 + c.winBase ≠
        before.regs rC + c.winBase := by omega
  have hnextCell : after.arr (after.regs rC + c.winBase) =
      before.arr (before.regs rC + 1 + c.winBase) := by
    rw [hcellAfter]
    have hlive := hfull.live
      (before.regs rC + 1 + c.winBase) hnextAddrNeSink
    rw [if_neg hnextAddrNeCurrent] at hlive
    exact hlive
  have ht : after.regs rT = Nat.sqrt (nextKey before) := by
    rw [hfull.t]
    exact sqrtStream_step before hentry.sqrt
  have ht2 : after.regs rT2 =
      (after.regs rT + 1) * (after.regs rT + 1) := by
    by_cases hlt : nextKey before < before.regs rT2
    · rw [hfull.t, hfull.t2]
      simp only [nextKey] at hlt
      rw [if_pos hlt, if_pos hlt, hentry.sqrt.nextSquare]
    · rw [hfull.t, hfull.t2]
      simp only [nextKey] at hlt
      rw [if_neg hlt, if_neg hlt, hentry.sqrt.nextSquare]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
  have hkeyAfter :
      after.regs rW + after.regs rC = nextKey before + 1 := by
    rw [hwindow, hcellAfter]
    simp only [nextKey]
    omega
  have hlower :
      after.regs rT * after.regs rT ≤
        after.regs rW + after.regs rC := by
    rw [ht, hkeyAfter]
    exact Nat.le_trans (Nat.sqrt_le (nextKey before)) (Nat.le_add_right _ _)
  have honeBump :
      after.regs rW + after.regs rC <
        (after.regs rT + 2) * (after.regs rT + 2) := by
    rw [hkeyAfter, ht]
    have hs := Nat.lt_succ_sqrt (nextKey before)
    have hq : Nat.sqrt (nextKey before) + 1 <
        Nat.sqrt (nextKey before) + 2 := by omega
    have hsq :
        (Nat.sqrt (nextKey before) + 1) *
            (Nat.sqrt (nextKey before) + 1) <
          (Nat.sqrt (nextKey before) + 2) *
            (Nat.sqrt (nextKey before) + 2) :=
      Nat.mul_lt_mul_of_lt_of_lt hq hq
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hs) hsq
  exact
    { window := hwindow
      cell := hcellAfter
      f := hfull.f
      e := hfull.e
      tv := hfull.tv
      nextCell := hnextCell
      nextF := by
        change (after.regs rF +
          after.arr (after.regs rC + c.winBase)) %
            LeanCompCert.Verified.Reflect.M = _
        rw [hfull.f, hnextCell]
        rfl
      sqrt :=
        { nextSquare := ht2
          lower := hlower
          oneBump := honeBump } }

/-- A register not written by the literal body is preserved by every finite
body iteration. -/
theorem bodyIter_reg_frame (c : Cfg) (idx n j : Nat) (st : AState)
    (hw : ArrayRegFrame.writes j c.body = false) :
    (bodyIter c idx n st).regs j = st.regs j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bodyIter]
      exact (ArrayRegFrame.arun_frame idx j c.body hw
        (bodyIter c idx n st)).trans ih

/-- Machine-word bounds are invariant under the finite body iterator. -/
theorem bodyIter_word (c : Cfg) (idx n : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (bodyIter c idx n st).regs j < M) ∧
      ∀ j, (bodyIter c idx n st).arr j < M := by
  induction n with
  | zero => exact ⟨hword, harrword⟩
  | succ n ih =>
      rw [bodyIter]
      exact arun_word idx c.body (bodyIter c idx n st) ih.1 ih.2

set_option maxHeartbeats 1000000 in
theorem bodySchedule_reg_frame (c : Cfg) (idx middleCount j : Nat)
    (st : AState) (hw : ArrayRegFrame.writes j c.body = false) :
    (bodySchedule c idx middleCount st).regs j = st.regs j := by
  unfold bodySchedule
  exact (ArrayRegFrame.arun_frame idx j c.body hw
    (bodyIter c idx middleCount (arun idx st c.body))).trans
      ((bodyIter_reg_frame c idx middleCount j (arun idx st c.body) hw).trans
        (ArrayRegFrame.arun_frame idx j c.body hw st))

theorem bodySchedule_word (c : Cfg) (idx middleCount : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (bodySchedule c idx middleCount st).regs j < M) ∧
      ∀ j, (bodySchedule c idx middleCount st).arr j < M := by
  have hfirst := arun_word idx c.body st hword harrword
  have hmiddle := bodyIter_word c idx middleCount (arun idx st c.body)
    hfirst.1 hfirst.2
  unfold bodySchedule
  exact arun_word idx c.body
    (bodyIter c idx middleCount (arun idx st c.body)) hmiddle.1 hmiddle.2

/-- The genuinely numerical obligations needed at the next interior cell.
Structural stream state, word bounds, the zero register, and cursor arithmetic
are derived by `interior_firstEntry_of_full`. -/
structure InteriorNextBounds (c : Cfg) (st : AState) : Prop where
  key_word : nextKey st < M
  t_word : st.regs rT + 1 < M
  double_word : 2 * (st.regs rT + 1) + 1 < M
  t2_word : st.regs rT2 + (2 * (st.regs rT + 1) + 1) < M
  delta_sum_word : nextDPos c st + nextDNeg c st < M
  tv_word : st.regs rTv + (nextDPos c st + nextDNeg c st) < M
  ceil_word : c.wScale - 1 + nextKey st < M
  scale_plus_sqrt_word : c.wScale + Nat.sqrt (nextKey st) < M
  uPos_fit : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
    nextDPos c st * nextCeil c st < AddWide.B128
  uNeg_fit : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
    nextDNeg c st * nextFloor c st < AddWide.B128

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem interior_firstEntry_of_full (c : Cfg) (idx middleCount : Nat)
    (before : AState) (k dp dn ceil floor root d cell startR startW : Nat)
    (hentry : FirstEntryInv c before)
    (hfull : OuterFullAccSpec c k dp dn ceil floor root d before
      (bodySchedule c idx middleCount before))
    (hcursor : ProductionCellCursorSpec c cell startR startW
      (bodySchedule c idx middleCount before))
    (hcell : before.regs rC = cell)
    (hstartW : before.regs rW = startW)
    (hinterior : cell + 1 < c.segLen) (hsinkM : c.sink < M)
    (hnext : InteriorNextBounds c
      (bodySchedule c idx middleCount before)) :
    FirstEntryInv c (bodySchedule c idx middleCount before) := by
  let after := bodySchedule c idx middleCount before
  have hstream : InteriorStreamStepSpec c dp dn before after := by
    exact interior_stream_step_of_full c before after k dp dn ceil floor
      root d cell startR startW hentry hfull hcursor hcell hstartW hinterior
  have hwordAfter := bodySchedule_word c idx middleCount before
    hentry.regs_word hentry.arr_word
  have hkeyAfter : nextKey after = nextKey before + 1 := by
    unfold nextKey
    rw [hstream.window, hstream.cell]
    omega
  exact
    { round0 := hfull.round
      zero := by
        exact (bodySchedule_reg_frame c idx middleCount rZero before
          (by rfl)).trans hentry.zero
      cell_range := by rw [hstream.cell, hcell]; omega
      sqrt := hstream.sqrt
      steps_pos := hentry.steps_pos
      steps_word := hentry.steps_word
      addr_word := by
        rw [hstream.cell, hcell]
        unfold Cfg.sink at hsinkM
        omega
      regs_word := hwordAfter.1
      arr_word := hwordAfter.2
      key_pos := by rw [hkeyAfter]; exact Nat.zero_lt_succ _
      key_word := hnext.key_word
      t_word := hnext.t_word
      double_word := hnext.double_word
      t2_word := hnext.t2_word
      scale_pos := hentry.scale_pos
      scale_word := hentry.scale_word
      delta_sum_word := hnext.delta_sum_word
      tv_word := hnext.tv_word
      ceil_word := hnext.ceil_word
      scale_plus_sqrt_word := hnext.scale_plus_sqrt_word
      uPos_fit := hnext.uPos_fit
      uNeg_fit := hnext.uNeg_fit }

end LeanCompCert.Ports.CDEMAbelSourceTelescope
