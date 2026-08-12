import LeanCompCert.Ports.CDEMAbelInactiveSuffix
import LeanCompCert.Ports.CDEMAbelOuter
import LeanCompCert.Ports.CDEMAbelOuterSchedule

/-! # Complete inactive CDEM body source frame -/

namespace LeanCompCert.Ports.CDEMAbelInactiveBody

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelInactiveSource
open LeanCompCert.Ports.CDEMAbelInactivePrelude
open LeanCompCert.Ports.CDEMAbelInactiveSuffix

/-- The compact phase boundary is definitionally the complete emitted body. -/
theorem body_run_eq_afterAccRun (c : Cfg) (idx : Nat) (st : AState) :
    arun idx st c.body = afterAccRun c idx st := by
  rw [body_acc_run_decomp, afterAccRun, inactiveAccRun, beforeAccRun,
    accPrefix, arun_append, arun_append]

/-- Persistent source state carried by an iteration whose accumulation
selector is off. -/
structure InactiveBodySourceSpec (before after : AState) : Prop where
  f : after.regs rF = before.regs rF
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  k : after.regs rK = before.regs rK
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  zero : after.regs rZero = before.regs rZero

theorem InactiveBodySourceSpec.trans {first middle last : AState}
    (h₁ : InactiveBodySourceSpec first middle)
    (h₂ : InactiveBodySourceSpec middle last) :
    InactiveBodySourceSpec first last :=
  { f := h₂.f.trans h₁.f
    t := h₂.t.trans h₁.t
    t2 := h₂.t2.trans h₁.t2
    e := h₂.e.trans h₁.e
    tv := h₂.tv.trans h₁.tv
    k := h₂.k.trans h₁.k
    dPos := h₂.dPos.trans h₁.dPos
    dNeg := h₂.dNeg.trans h₁.dNeg
    zero := h₂.zero.trans h₁.zero }

theorem body_inactive_source_run (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodySourceSpec st (arun idx st c.body) := by
  have hs := afterAccRun_stream c idx st hselected43 hzero hsinkM hword
    harrword hk hWM hsum hceilFit
  have hc := afterAccRun_carry c idx st hselected43 hzero hsinkM hword
    harrword hk hWM hsum hceilFit
  rw [body_run_eq_afterAccRun]
  exact
    { f := hs.1
      t := hs.2.1
      t2 := hs.2.2.1
      e := hs.2.2.2.1
      tv := hs.2.2.2.2
      k := hc.1
      dPos := hc.2.1
      dNeg := hc.2.2.1
      zero := hc.2.2.2 }

/-- Compact word-bound interface for the complete emitted body. -/
theorem body_run_word (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (arun idx st c.body).regs j < M) ∧
      ∀ j, (arun idx st c.body).arr j < M :=
  arun_word idx c.body st hword harrword

/-- Opaque body result used by finite telescopes so type normalization does
not expand the instruction list at every induction step. -/
def inactiveBodyRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx st c.body

attribute [irreducible] inactiveBodyRun

theorem body_run_eq_inactiveBodyRun (c : Cfg) (idx : Nat) (st : AState) :
    arun idx st c.body = inactiveBodyRun c idx st := by
  rw [inactiveBodyRun]

theorem inactiveBodyRun_source (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodySourceSpec st (inactiveBodyRun c idx st) := by
  rw [inactiveBodyRun]
  exact body_inactive_source_run c idx st hselected43 hzero hsinkM hword
    harrword hk hWM hsum hceilFit

theorem inactiveBodyRun_word (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (inactiveBodyRun c idx st).regs j < M) ∧
      ∀ j, (inactiveBodyRun c idx st).arr j < M := by
  rw [inactiveBodyRun]
  exact body_run_word c idx st hword harrword

/-- During marking, every block before the tail frames the period cursor and
the tail advances it by one. -/
theorem inactiveBodyRun_mark_cursor (c : Cfg) (idx : Nat) (st : AState)
    (hselected41 : (arun idx st c.selectors).regs 41 = 1)
    (hnext : st.regs rR + 1 < c.period)
    (hnextM : st.regs rR + 1 < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) :
    (inactiveBodyRun c idx st).regs rR = st.regs rR + 1 := by
  let pre := beforeAccRun c idx st
  let accumulated := inactiveAccRun c idx pre
  have hpR : pre.regs rR = st.regs rR :=
    beforeAccRun_frame c idx st rR (by rfl) (by rfl) (by rfl)
  have hp41 : pre.regs 41 = 1 := by
    change (beforeAccRun c idx st).regs 41 = 1
    rw [beforeAccRun,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 41 c.markBody
        (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 41 c.sieveBody
        (by rfl), hselected41]
  have ha := inactiveAccRun_cursor c idx pre
  have haR : accumulated.regs rR = pre.regs rR := ha.1
  have ha41 : accumulated.regs 41 = pre.regs 41 := ha.2
  have hpword := beforeAccRun_word c idx st hword harrword
  have haword := inactiveAccRun_word c idx pre hpword.1 hpword.2
  have ht := tail_continue_window_run c idx accumulated
    (by rw [ha41, hp41])
    (by rw [haR, hpR]; exact hnext)
    (by rw [haR, hpR]; exact hnextM) hperiodM hsegM (haword.1 rW)
  rw [inactiveBodyRun, body_run_eq_afterAccRun, afterAccRun]
  exact ht.1.trans (by rw [haR, hpR])

end LeanCompCert.Ports.CDEMAbelInactiveBody
