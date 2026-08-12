import LeanCompCert.Ports.CDEMAbelInactiveSource

/-! # Wide-accumulator frame for inactive CDEM bisection -/

namespace LeanCompCert.Ports.CDEMAbelInactiveWide

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelBody
open LeanCompCert.Ports.CDEMAbelInactiveSource

structure InactiveBisectWideSpec (before after : AState) : Prop where
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr

/-- With all three bisection selectors off, the literal open/round/close
sequence preserves the wide `V` accumulator and round counter. -/
theorem accBisect_inactive_wide_round (c : Cfg) (idx : Nat) (st : AState)
    (h140 : st.regs 140 = 0) (h142 : st.regs 142 = 0)
    (h141 : st.regs 141 = 0) (h43 : st.regs 43 = 0)
    (hword : ∀ j, st.regs j < M) :
    InactiveBisectWideSpec st (arun idx st c.accBisect) := by
  let o := srun idx st.regs (openS c)
  let rd := srun idx o (roundS c)
  let out := srun idx rd closeS
  have ho := open_gate0_run c idx st.regs h140 hword
  change o rSl = st.regs rSl ∧ o rSh = st.regs rSh ∧ o 140 = 0 at ho
  have howord : ∀ j, o j < M := srun_lt_of_lt idx _ st.regs hword
  have openKeep (j : Nat) (hw : RegFrame.writes j (openS c) = false) :
      o j = st.regs j := RegFrame.srun_frame idx j (openS c) hw st.regs
  have ho142 : o 142 = 0 := by rw [openKeep 142 (by rfl), h142]
  have hr := round_gate0_run c idx o ho142 howord
  change rd rSl = o rSl ∧ rd rSh = o rSh ∧ rd 142 = 0 ∧
    rd rViol = o rViol ∧ rd rVDiv = o rVDiv at hr
  have hrdword : ∀ j, rd j < M := srun_lt_of_lt idx _ o howord
  have roundKeep (j : Nat) (hw : RegFrame.writes j (roundS c) = false) :
      rd j = o j := RegFrame.srun_frame idx j (roundS c) hw o
  have hrd141 : rd 141 = 0 := by
    rw [roundKeep 141 (by rfl), openKeep 141 (by rfl), h141]
  have hrdKr : rd rKr = st.regs rKr := by
    rw [roundKeep rKr (by rfl), openKeep rKr (by rfl)]
  have hrd43 : rd 43 = 0 := by
    rw [roundKeep 43 (by rfl), openKeep 43 (by rfl), h43]
  have hrdVLo : rd rVLo = st.regs rVLo := by
    rw [roundKeep rVLo (by rfl), openKeep rVLo (by rfl)]
  have hrdVHi : rd rVHi = st.regs rVHi := by
    rw [roundKeep rVHi (by rfl), openKeep rVHi (by rfl)]
  have hc := close_gate0_run idx rd hrd141
    (by rw [hrdKr, hrd43, Nat.add_zero]; exact hword rKr) hrdword
  change out rViol = rd rViol ∧ out rVBisect = rd rVBisect ∧
    AddWide.wval (out rVLo, out rVHi) =
      AddWide.wval (rd rVLo, rd rVHi) ∧
    out rKr = rd rKr + rd 43 ∧ out rC = rd rC ∧
    out rSl = rd rSl ∧ out rSh = rd rSh at hc
  have hall : InactiveBisectWideSpec st ⟨out, st.arr⟩ :=
    { v := by
        change AddWide.wval (out rVLo, out rVHi) = _
        rw [hc.2.2.1, hrdVLo, hrdVHi]
      round := by
        change out rKr = st.regs rKr
        rw [hc.2.2.2.1, hrdKr, hrd43, Nat.add_zero] }
  rw [accBisect_arun]
  simpa [accBisectScalarS, srun_append, o, rd, out] using hall

structure InactiveAccumWideSpec (before after : AState) : Prop where
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr

def inactiveHeadProdRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (arun idx st c.accHead) c.accProd

attribute [irreducible] inactiveHeadProdRun

structure InactiveHeadProdSpec (before after : AState) : Prop where
  first : after.regs 140 = 0
  last : after.regs 141 = 0
  bisect : after.regs 142 = 0
  gate : after.regs 43 = 0
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  vLo : after.regs rVLo = before.regs rVLo
  vHi : after.regs rVHi = before.regs rVHi
  round : after.regs rKr = before.regs rKr
  word : ∀ j, after.regs j < M

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Compact head-plus-product boundary for an inactive accumulator. -/
theorem inactiveHeadProd_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveHeadProdSpec st (inactiveHeadProdRun c idx st) := by
  rw [inactiveHeadProdRun]
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  have hh := accHead_inactive_source_run c idx st hgate hzero hsinkM
    hword harrword hk hWM hsum hceilFit
  change InactiveHeadSourceSpec st h at hh
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have harrH : ∀ j, h.arr j < M :=
    (arun_word idx c.accHead st hword harrword).2
  have hz := accProd_zero_run c idx h hwordH hh.posGate hh.negGate
  change ZeroProdSpec h p at hz
  have prodKeep (j : Nat)
      (hj : j ≠ 171 ∧ j ≠ 172 ∧ j ≠ 173 ∧ j ≠ 174 ∧
        Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 ∧
        j ≠ rUpLo ∧ j ≠ rUpHi ∧ j ≠ rUnLo ∧ j ≠ rUnHi ∧
        j ≠ 188) : p.regs j = h.regs j := by
    rcases hj with ⟨h171, h172, h173, h174, hjs, hupl, huph,
      hunl, hunh, h188⟩
    exact hz.frame j h171 h172 h173 h174 hjs hupl huph hunl hunh h188
  have headKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      h.regs j = st.regs j := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame idx j c.accHead hw st
  have hp140 : p.regs 140 = 0 := by
    rw [prodKeep 140 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh.first]
  have hp142 : p.regs 142 = 0 := by
    rw [prodKeep 142 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh.bisect]
  have hp141 : p.regs 141 = 0 := by
    rw [prodKeep 141 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh.last]
  have hp43 : p.regs 43 = 0 := by
    rw [prodKeep 43 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), headKeep 43 (by rfl), hgate]
  have hwordP : ∀ j, p.regs j < M :=
    (arun_word idx c.accProd h hwordH harrH).1
  exact
    { first := hp140
      last := hp141
      bisect := hp142
      gate := hp43
      uPos := by
        rw [hz.uPos,
          headKeep rUpLo (by rfl), headKeep rUpHi (by rfl)]
      uNeg := by
        rw [hz.uNeg,
          headKeep rUnLo (by rfl), headKeep rUnHi (by rfl)]
      vLo := (prodKeep rVLo (by simp [rVLo, Section413G1Denote.NotIn8,
          rUpLo, rUpHi, rUnLo, rUnHi])).trans (headKeep rVLo (by rfl))
      vHi := (prodKeep rVHi (by simp [rVHi, Section413G1Denote.NotIn8,
          rUpLo, rUpHi, rUnLo, rUnHi])).trans (headKeep rVHi (by rfl))
      round := by
        rw [prodKeep rKr (by simp [rKr, Section413G1Denote.NotIn8,
            rUpLo, rUpHi, rUnLo, rUnHi]), hh.round]
      word := hwordP }

def inactiveAccumRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (inactiveHeadProdRun c idx st) c.accBisect

attribute [irreducible] inactiveAccumRun

theorem inactiveAccumRun_eq_accBody (c : Cfg) (idx : Nat) (st : AState) :
    inactiveAccumRun c idx st = arun idx st c.accBody := by
  rw [inactiveAccumRun, inactiveHeadProdRun, arun_accBody_eq_parts]

theorem inactiveAccumRun_u_frame (c : Cfg) (idx : Nat) (st : AState) :
    let before := inactiveHeadProdRun c idx st
    let after := inactiveAccumRun c idx st
    after.regs rUpLo = before.regs rUpLo ∧
      after.regs rUpHi = before.regs rUpHi ∧
      after.regs rUnLo = before.regs rUnLo ∧
      after.regs rUnHi = before.regs rUnHi := by
  rw [inactiveAccumRun]
  exact accBisect_u_frame c idx (inactiveHeadProdRun c idx st)

theorem inactiveAccumRun_bisect_wide (c : Cfg) (idx : Nat) (st : AState)
    (h : InactiveHeadProdSpec st (inactiveHeadProdRun c idx st)) :
    InactiveBisectWideSpec (inactiveHeadProdRun c idx st)
      (inactiveAccumRun c idx st) := by
  rw [inactiveAccumRun]
  exact accBisect_inactive_wide_round c idx (inactiveHeadProdRun c idx st)
    h.first h.bisect h.last h.gate h.word

/-- The complete inactive accumulator preserves all three wide sums and the
bisection round counter. -/
theorem inactiveAccumRun_wide (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveAccumWideSpec st (inactiveAccumRun c idx st) := by
  let p := inactiveHeadProdRun c idx st
  have hp := inactiveHeadProd_run c idx st hgate hzero hsinkM hword
    harrword hk hWM hsum hceilFit
  change InactiveHeadProdSpec st p at hp
  have hb := inactiveAccumRun_bisect_wide c idx st hp
  have hu := inactiveAccumRun_u_frame c idx st
  exact
    { uPos := by rw [hu.1, hu.2.1, hp.uPos]
      uNeg := by rw [hu.2.2.1, hu.2.2.2, hp.uNeg]
      v := by rw [hb.v, hp.vLo, hp.vHi]
      round := hb.round.trans hp.round }

theorem inactiveAccRun_eq_inactiveAccumRun (c : Cfg) (idx : Nat)
    (st : AState) :
    inactiveAccRun c idx st = inactiveAccumRun c idx st := by
  rw [inactiveAccRun, inactiveAccumRun_eq_accBody]

theorem inactiveAccRun_wide (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveAccumWideSpec st (inactiveAccRun c idx st) := by
  rw [inactiveAccRun_eq_inactiveAccumRun]
  exact inactiveAccumRun_wide c idx st hgate hzero hsinkM hword harrword
    hk hWM hsum hceilFit

end LeanCompCert.Ports.CDEMAbelInactiveWide
