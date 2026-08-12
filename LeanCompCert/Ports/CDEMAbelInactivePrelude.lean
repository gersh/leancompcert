import LeanCompCert.Ports.CDEMAbelInactiveSource

/-! # CDEM source frame before inactive accumulation -/

namespace LeanCompCert.Ports.CDEMAbelInactivePrelude

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan

def beforeAccRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (arun idx (arun idx st c.selectors) c.sieveBody) c.markBody

theorem beforeAccRun_frame (c : Cfg) (idx : Nat) (st : AState) (j : Nat)
    (hs : ArrayRegFrame.writes j c.selectors = false)
    (hv : ArrayRegFrame.writes j c.sieveBody = false)
    (hm : ArrayRegFrame.writes j c.markBody = false) :
    (beforeAccRun c idx st).regs j = st.regs j := by
  rw [beforeAccRun,
    ArrayRegFrame.arun_frame idx j c.markBody hm,
    ArrayRegFrame.arun_frame idx j c.sieveBody hv,
    ArrayRegFrame.arun_frame idx j c.selectors hs]

theorem beforeAccRun_word (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    (∀ j, (beforeAccRun c idx st).regs j < M) ∧
      ∀ j, (beforeAccRun c idx st).arr j < M := by
  have hs := arun_word idx c.selectors st hword harrword
  have hv := arun_word idx c.sieveBody (arun idx st c.selectors) hs.1 hs.2
  have hm := arun_word idx c.markBody
    (arun idx (arun idx st c.selectors) c.sieveBody) hv.1 hv.2
  exact hm

structure BeforeInactiveAccumSpec (before after : AState) : Prop where
  f : after.regs rF = before.regs rF
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  k : after.regs rK = before.regs rK
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  zero : after.regs rZero = before.regs rZero

set_option maxRecDepth 4096 in
/-- Selector, sieve, and mark instructions do not alter the source stream or
its persistent inactive-phase latches. -/
theorem beforeAccRun_source (c : Cfg) (idx : Nat) (st : AState) :
    BeforeInactiveAccumSpec st (beforeAccRun c idx st) :=
  { f := beforeAccRun_frame c idx st rF (by rfl) (by rfl) (by rfl)
    t := beforeAccRun_frame c idx st rT (by rfl) (by rfl) (by rfl)
    t2 := beforeAccRun_frame c idx st rT2 (by rfl) (by rfl) (by rfl)
    e := beforeAccRun_frame c idx st rE (by rfl) (by rfl) (by rfl)
    tv := beforeAccRun_frame c idx st rTv (by rfl) (by rfl) (by rfl)
    k := beforeAccRun_frame c idx st rK (by rfl) (by rfl) (by rfl)
    dPos := beforeAccRun_frame c idx st rDp (by rfl) (by rfl) (by rfl)
    dNeg := beforeAccRun_frame c idx st rDn (by rfl) (by rfl) (by rfl)
    zero := beforeAccRun_frame c idx st rZero (by rfl) (by rfl) (by rfl) }

theorem beforeAccRun_gate (c : Cfg) (idx : Nat) (st : AState)
    (hselected43 : (arun idx st c.selectors).regs 43 = 0) :
    (beforeAccRun c idx st).regs 43 = 0 := by
  rw [beforeAccRun,
    ArrayRegFrame.arun_frame idx 43 c.markBody (by rfl),
    ArrayRegFrame.arun_frame idx 43 c.sieveBody (by rfl), hselected43]

end LeanCompCert.Ports.CDEMAbelInactivePrelude
