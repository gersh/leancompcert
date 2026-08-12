import LeanCompCert.Ports.CDEMAbelInactivePrelude

/-! # CDEM inactive accumulator and tail source frame -/

namespace LeanCompCert.Ports.CDEMAbelInactiveSuffix

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelBody
open LeanCompCert.Ports.CDEMAbelInactiveSource
open LeanCompCert.Ports.CDEMAbelInactivePrelude

def afterAccRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (inactiveAccRun c idx (beforeAccRun c idx st)) c.tailBody

attribute [irreducible] afterAccRun

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem afterAccRun_stream (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    let out := afterAccRun c idx st
    out.regs rF = st.regs rF ∧ out.regs rT = st.regs rT ∧
      out.regs rT2 = st.regs rT2 ∧ out.regs rE = st.regs rE ∧
      out.regs rTv = st.regs rTv := by
  rw [afterAccRun]
  let pre := beforeAccRun c idx st
  let accumulated := inactiveAccRun c idx pre
  let out := arun idx accumulated c.tailBody
  have hp := beforeAccRun_source c idx st
  change BeforeInactiveAccumSpec st pre at hp
  have hpword := beforeAccRun_word c idx st hword harrword
  have hpgate : pre.regs 43 = 0 := beforeAccRun_gate c idx st hselected43
  have hs := inactiveAccRun_stream c idx pre hpgate
    (hp.zero.trans hzero) hsinkM hpword.1 hpword.2
    (by rw [hp.k]; exact hk) hWM
    (by rw [hp.dPos, hp.dNeg]; exact hsum)
    (by rw [hp.k]; exact hceilFit)
  change accumulated.regs rF = pre.regs rF ∧
    accumulated.regs rT = pre.regs rT ∧
    accumulated.regs rT2 = pre.regs rT2 ∧
    accumulated.regs rE = pre.regs rE ∧
    accumulated.regs rTv = pre.regs rTv at hs
  have tailFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j :=
    ArrayRegFrame.arun_frame idx j c.tailBody hw accumulated
  change out.regs rF = st.regs rF ∧ out.regs rT = st.regs rT ∧
    out.regs rT2 = st.regs rT2 ∧ out.regs rE = st.regs rE ∧
    out.regs rTv = st.regs rTv
  exact ⟨by rw [tailFrame rF (by rfl), hs.1, hp.f],
    by rw [tailFrame rT (by rfl), hs.2.1, hp.t],
    by rw [tailFrame rT2 (by rfl), hs.2.2.1, hp.t2],
    by rw [tailFrame rE (by rfl), hs.2.2.2.1, hp.e],
    by rw [tailFrame rTv (by rfl), hs.2.2.2.2, hp.tv]⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem afterAccRun_carry (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    let out := afterAccRun c idx st
    out.regs rK = st.regs rK ∧ out.regs rDp = st.regs rDp ∧
      out.regs rDn = st.regs rDn ∧ out.regs rZero = st.regs rZero := by
  rw [afterAccRun]
  let pre := beforeAccRun c idx st
  let accumulated := inactiveAccRun c idx pre
  let out := arun idx accumulated c.tailBody
  have hp := beforeAccRun_source c idx st
  change BeforeInactiveAccumSpec st pre at hp
  have hpword := beforeAccRun_word c idx st hword harrword
  have hpgate : pre.regs 43 = 0 := beforeAccRun_gate c idx st hselected43
  have hc := inactiveAccRun_carry c idx pre hpgate
    (hp.zero.trans hzero) hsinkM hpword.1 hpword.2
    (by rw [hp.k]; exact hk) hWM
    (by rw [hp.dPos, hp.dNeg]; exact hsum)
    (by rw [hp.k]; exact hceilFit)
  change accumulated.regs rK = pre.regs rK ∧
    accumulated.regs rDp = pre.regs rDp ∧
    accumulated.regs rDn = pre.regs rDn ∧
    accumulated.regs rZero = pre.regs rZero at hc
  have tailFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j :=
    ArrayRegFrame.arun_frame idx j c.tailBody hw accumulated
  change out.regs rK = st.regs rK ∧ out.regs rDp = st.regs rDp ∧
    out.regs rDn = st.regs rDn ∧ out.regs rZero = st.regs rZero
  exact ⟨by rw [tailFrame rK (by rfl), hc.1, hp.k],
    by rw [tailFrame rDp (by rfl), hc.2.1, hp.dPos],
    by rw [tailFrame rDn (by rfl), hc.2.2.1, hp.dNeg],
    by rw [tailFrame rZero (by rfl), hc.2.2.2, hp.zero]⟩

theorem afterAccRun_word (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (afterAccRun c idx st).regs j < M) ∧
      ∀ j, (afterAccRun c idx st).arr j < M := by
  rw [afterAccRun]
  have hp := beforeAccRun_word c idx st hword harrword
  have ha := inactiveAccRun_word c idx (beforeAccRun c idx st) hp.1 hp.2
  exact arun_word idx c.tailBody
    (inactiveAccRun c idx (beforeAccRun c idx st)) ha.1 ha.2

end LeanCompCert.Ports.CDEMAbelInactiveSuffix
