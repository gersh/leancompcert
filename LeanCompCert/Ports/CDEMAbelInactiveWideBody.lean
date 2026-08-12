import LeanCompCert.Ports.CDEMAbelInactiveWide
import LeanCompCert.Ports.CDEMAbelInactiveBody

/-! # Wide-accumulator frame through a complete inactive CDEM body -/

namespace LeanCompCert.Ports.CDEMAbelInactiveWideBody

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelInactiveSource
open LeanCompCert.Ports.CDEMAbelInactivePrelude
open LeanCompCert.Ports.CDEMAbelInactiveSuffix
open LeanCompCert.Ports.CDEMAbelInactiveBody
open LeanCompCert.Ports.CDEMAbelInactiveWide

structure InactiveBodyWideSpec (before after : AState) : Prop where
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr

theorem InactiveBodyWideSpec.trans {first middle last : AState}
    (h₁ : InactiveBodyWideSpec first middle)
    (h₂ : InactiveBodyWideSpec middle last) :
    InactiveBodyWideSpec first last :=
  { uPos := h₂.uPos.trans h₁.uPos
    uNeg := h₂.uNeg.trans h₁.uNeg
    v := h₂.v.trans h₁.v
    round := h₂.round.trans h₁.round }

theorem body_inactive_wide_run (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodyWideSpec st (arun idx st c.body) := by
  let pre := beforeAccRun c idx st
  let accumulated := inactiveAccRun c idx pre
  let out := arun idx accumulated c.tailBody
  have hp := beforeAccRun_source c idx st
  change BeforeInactiveAccumSpec st pre at hp
  have hpword := beforeAccRun_word c idx st hword harrword
  have hpgate : pre.regs 43 = 0 := beforeAccRun_gate c idx st hselected43
  have hw := inactiveAccRun_wide c idx pre hpgate (hp.zero.trans hzero)
    hsinkM hpword.1 hpword.2 (by rw [hp.k]; exact hk) hWM
    (by rw [hp.dPos, hp.dNeg]; exact hsum)
    (by rw [hp.k]; exact hceilFit)
  change InactiveAccumWideSpec pre accumulated at hw
  have preKeep (j : Nat)
      (hs : LeanCompCert.Verified.ArrayRegFrame.writes j c.selectors = false)
      (hv : LeanCompCert.Verified.ArrayRegFrame.writes j c.sieveBody = false)
      (hm : LeanCompCert.Verified.ArrayRegFrame.writes j c.markBody = false) :
      pre.regs j = st.regs j := beforeAccRun_frame c idx st j hs hv hm
  have tailFrame (j : Nat)
      (hwrite : LeanCompCert.Verified.ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx j c.tailBody
      hwrite accumulated
  have hall : InactiveBodyWideSpec st out :=
    { uPos := by
        rw [tailFrame rUpLo (by rfl), tailFrame rUpHi (by rfl), hw.uPos,
          preKeep rUpLo (by rfl) (by rfl) (by rfl),
          preKeep rUpHi (by rfl) (by rfl) (by rfl)]
      uNeg := by
        rw [tailFrame rUnLo (by rfl), tailFrame rUnHi (by rfl), hw.uNeg,
          preKeep rUnLo (by rfl) (by rfl) (by rfl),
          preKeep rUnHi (by rfl) (by rfl) (by rfl)]
      v := by
        rw [tailFrame rVLo (by rfl), tailFrame rVHi (by rfl), hw.v,
          preKeep rVLo (by rfl) (by rfl) (by rfl),
          preKeep rVHi (by rfl) (by rfl) (by rfl)]
      round := by
        rw [tailFrame rKr (by rfl), hw.round,
          preKeep rKr (by rfl) (by rfl) (by rfl)] }
  rw [body_run_eq_afterAccRun, afterAccRun]
  exact hall

theorem inactiveBodyRun_wide (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodyWideSpec st (inactiveBodyRun c idx st) := by
  rw [inactiveBodyRun]
  exact body_inactive_wide_run c idx st hselected43 hzero hsinkM hword
    harrword hk hWM hsum hceilFit

end LeanCompCert.Ports.CDEMAbelInactiveWideBody
