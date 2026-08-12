import LeanCompCert.Ports.CDEMAbelMarkSchedule

/-! # Source-register frame through inactive CDEM phases -/

namespace LeanCompCert.Ports.CDEMAbelInactiveSource

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
open LeanCompCert.Ports.CDEMAbelMarkSchedule

/-- Source-facing state left unchanged when the accumulation selector is
off.  Scratch registers are deliberately absent. -/
structure InactiveHeadSourceSpec (before after : AState) : Prop where
  first : after.regs 140 = 0
  last : after.regs 141 = 0
  bisect : after.regs 142 = 0
  f : after.regs rF = before.regs rF
  k : after.regs rK = before.regs rK
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  posGate : after.regs 169 = 0
  negGate : after.regs 170 = 0
  round : after.regs rKr = before.regs rKr
  cell : after.regs rC = before.regs rC

set_option maxRecDepth 4096 in
theorem accHead_inactive_source_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveHeadSourceSpec st (arun idx st c.accHead) := by
  let pre := srun idx st.regs (headPreS c)
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  let post := srun idx loaded (headPostS c)
  have hpre := headPre_inactive_run c idx st hgate hzero hsinkM
  change pre 140 = 0 ∧ pre 141 = 0 ∧ pre 144 = c.sink at hpre
  have hpre142 : pre 142 = 0 := by
    have h0M : (0 : Nat) % M = 0 := by decide
    simp [pre, headPreS, Section413G1Denote.muxS, srun, sdest, sval,
      denoteOperand, denoteOp, RegState.set, rC, rZero, hgate, h0M]
  have preKeep (j : Nat) (hw : RegFrame.writes j (headPreS c) = false) :
      pre j = st.regs j :=
    RegFrame.srun_frame idx j (headPreS c) hw st.regs
  have loadedKeep (j : Nat) (hj : j ≠ 148) : loaded j = pre j := by
    simp [loaded, RegState.set, hj]
  have loadedToBefore (j : Nat) (hj : j ≠ 148)
      (hw : RegFrame.writes j (headPreS c) = false) :
      loaded j = st.regs j := by rw [loadedKeep j hj, preKeep j hw]
  have hloadedword : ∀ j, loaded j < M := by
    intro j
    by_cases hj : j = 148
    · subst j
      simp [loaded, RegState.set]
      exact harrword (pre 144)
    · rw [loadedKeep j hj]
      exact srun_lt_of_lt idx (headPreS c) st.regs hword j
  have hloadedK : loaded rK = st.regs rK :=
    loadedToBefore rK (by simp [rK]) (by rfl)
  have hloadedDp : loaded rDp = st.regs rDp :=
    loadedToBefore rDp (by simp [rDp]) (by rfl)
  have hloadedDn : loaded rDn = st.regs rDn :=
    loadedToBefore rDn (by simp [rDn]) (by rfl)
  have hp := headPost_middle_run c idx loaded
    (by rw [loadedKeep 140 (by decide), hpre.1])
    (by rw [hloadedK]; exact hk) hloadedword hWM
    (by rw [hloadedDp, hloadedDn]; exact hsum)
    (by rw [hloadedK]; exact hceilFit)
  dsimp only at hp
  change post rF = loaded rF ∧ post rK = loaded rK ∧
    post rT = loaded rT ∧ post rT2 = loaded rT2 ∧
    post rViol = loaded rViol ∧ post rVSqrt = loaded rVSqrt ∧
    post rDp = loaded rDp ∧ post rDn = loaded rDn ∧
    post rE = loaded rE ∧ post rTv = loaded rTv ∧
    post 165 = loaded rDp + loaded rDn ∧
    post 167 = (c.wScale - 1 + loaded rK) / loaded rK ∧
    post 168 = c.wScale / loaded rK ∧ post 169 = 0 ∧
    post 170 = 0 ∧ post 140 = 0 at hp
  rcases hp with ⟨hpF, hpK, hpT, hpT2, _, _, hpDp, hpDn, hpE, hpTv,
    _, _, _, hpPos, hpNeg, hpFirst⟩
  have postKeep (j : Nat) (hw : RegFrame.writes j (headPostS c) = false) :
      post j = loaded j := RegFrame.srun_frame idx j (headPostS c) hw loaded
  have hhead := accHead_arun c idx st
  dsimp only at hhead
  rw [hhead]
  change InactiveHeadSourceSpec st (⟨post, cleared⟩ : AState)
  exact
    { first := by change post 140 = 0; exact hpFirst
      last := by
        change post 141 = 0
        rw [postKeep 141 (by rfl), loadedKeep 141 (by decide), hpre.2.1]
      bisect := by
        change post 142 = 0
        rw [postKeep 142 (by rfl), loadedKeep 142 (by decide), hpre142]
      f := by
        change post rF = st.regs rF
        rw [hpF, loadedToBefore rF (by simp [rF]) (by rfl)]
      k := by change post rK = st.regs rK; rw [hpK, hloadedK]
      t := by
        change post rT = st.regs rT
        rw [hpT, loadedToBefore rT (by simp [rT]) (by rfl)]
      t2 := by
        change post rT2 = st.regs rT2
        rw [hpT2, loadedToBefore rT2 (by simp [rT2]) (by rfl)]
      dPos := by change post rDp = st.regs rDp; rw [hpDp, hloadedDp]
      dNeg := by change post rDn = st.regs rDn; rw [hpDn, hloadedDn]
      e := by
        change post rE = st.regs rE
        rw [hpE, loadedToBefore rE (by simp [rE]) (by rfl)]
      tv := by
        change post rTv = st.regs rTv
        rw [hpTv, loadedToBefore rTv (by simp [rTv]) (by rfl)]
      posGate := by change post 169 = 0; exact hpPos
      negGate := by change post 170 = 0; exact hpNeg
      round := by
        change post rKr = st.regs rKr
        rw [postKeep rKr (by rfl),
          loadedToBefore rKr (by simp [rKr]) (by rfl)]
      cell := by
        change post rC = st.regs rC
        rw [postKeep rC (by rfl),
          loadedToBefore rC (by simp [rC]) (by rfl)] }

/-- The inactive full accumulator preserves the persistent floor-convolution
stream.  This compact composition uses the already framed product/bisection
suffix instead of re-elaborating those instruction blocks. -/
theorem accBody_inactive_stream_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    let out := arun idx st c.accBody
    out.regs rF = st.regs rF ∧ out.regs rT = st.regs rT ∧
      out.regs rT2 = st.regs rT2 ∧ out.regs rE = st.regs rE ∧
      out.regs rTv = st.regs rTv := by
  have hh := accHead_inactive_source_run c idx st hgate hzero hsinkM
    hword harrword hk hWM hsum hceilFit
  exact accBody_stream_frame_of_head c idx st hh.f hh.t hh.t2 hh.e hh.tv

end LeanCompCert.Ports.CDEMAbelInactiveSource
