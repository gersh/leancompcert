import LeanCompCert.Ports.CDEMAbelAccumulation

namespace LeanCompCert.Ports.CDEMAbelAccumulation

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives

def headPreS (c : Cfg) : List Instr :=
  [ .binop 140 .eq (.reg rKr) (.lit 0)
  , .binop 140 .mul (.reg 140) (.reg 43)
  , .binop 141 .eq (.reg rKr) (.lit c.bsSteps)
  , .binop 141 .mul (.reg 141) (.reg 43)
  , .binop 142 .sub (.reg 43) (.reg 140)
  , .binop 143 .add (.reg rC) (.lit c.winBase) ] ++
  Section413G1Denote.muxS 144 140 143 rZero 145 ++
  [ .binop 146 .sub (.lit 1) (.reg 140)
  , .binop 147 .mul (.reg 146) (.lit c.sink)
  , .binop 144 .add (.reg 144) (.reg 147) ]

def headPostS (c : Cfg) : List Instr :=
  let W := c.wScale
  [ .binop 149 .mul (.reg 148) (.reg 140)
  , .binop rF .add (.reg rF) (.reg 149)
  , .binop 150 .add (.reg rW) (.reg rC) ] ++
  Section413G1Denote.muxS rK 140 150 rK 151 ++
  [ .binop 152 .ge (.reg rK) (.reg rT2)
  , .binop 152 .mul (.reg 152) (.reg 140)
  , .binop rT .add (.reg rT) (.reg 152)
  , .binop 153 .mul (.reg rT) (.lit 2)
  , .binop 153 .add (.reg 153) (.lit 1)
  , .binop 153 .mul (.reg 153) (.reg 152)
  , .binop rT2 .add (.reg rT2) (.reg 153)
  , .binop 154 .ge (.reg rK) (.reg rT2)
  , .binop 154 .mul (.reg 154) (.reg 140)
  , .binop rViol .add (.reg rViol) (.reg 154)
  , .binop rVSqrt .add (.reg rVSqrt) (.reg 154)
  , .binop 155 .sub (.lit 1) (.reg rF)
  , .binop 156 .ge (.reg 155) (.lit 9223372036854775808)
  , .binop 157 .sub (.lit 0) (.reg 155) ] ++
  Section413G1Denote.muxS 158 156 157 155 159 ++
  [ .binop 160 .gt (.reg 158) (.reg rE)
  , .binop 161 .sub (.reg 158) (.reg rE)
  , .binop 161 .mul (.reg 161) (.reg 160)
  , .binop 162 .gt (.reg rE) (.reg 158)
  , .binop 163 .sub (.reg rE) (.reg 158)
  , .binop 163 .mul (.reg 163) (.reg 162) ] ++
  Section413G1Denote.muxS rDp 140 161 rDp 164 ++
  Section413G1Denote.muxS rDn 140 163 rDn 164 ++
  Section413G1Denote.muxS rE 140 158 rE 164 ++
  [ .binop 165 .add (.reg rDp) (.reg rDn)
  , .binop 166 .mul (.reg 165) (.reg 140)
  , .binop rTv .add (.reg rTv) (.reg 166)
  , .binop 167 .add (.lit (W - 1)) (.reg rK)
  , .binop 167 .udiv (.reg 167) (.reg rK)
  , .binop 168 .udiv (.lit W) (.reg rK)
  , .binop 169 .mul (.reg rDp) (.reg 140)
  , .binop 170 .mul (.reg rDn) (.reg 140) ]

set_option maxRecDepth 8192 in
theorem accHead_decomp (c : Cfg) :
    c.accHead = lift (headPreS c) ++
      ([.load 148 144, .store 144 rZero] ++ lift (headPostS c)) := by
  simp [Cfg.accHead, headPreS, headPostS,
    Section413G1Denote.muxBody_lift, lift_append, List.append_assoc]

theorem accHead_arun (c : Cfg) (idx : Nat) (st : AState) :
    let pre := srun idx st.regs (headPreS c)
    let loaded := RegState.set pre 148 (st.arr (pre 144))
    let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
    arun idx st c.accHead =
      ⟨srun idx loaded (headPostS c), cleared⟩ := by
  let pre := srun idx st.regs (headPreS c)
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  have hload : astep idx ⟨pre, st.arr⟩ (.load 148 144) =
      ⟨loaded, st.arr⟩ := rfl
  have hstore : astep idx ⟨loaded, st.arr⟩ (.store 144 rZero) =
      ⟨loaded, cleared⟩ := rfl
  rw [accHead_decomp, arun_append, arun_lift,
    arun_append, arun_cons, hload, arun_cons, hstore, arun_lift]
  change (⟨srun idx loaded (headPostS c), cleared⟩ : AState) = _
  rfl

theorem headPre_middle_run (c : Cfg) (idx : Nat) (r : RegState)
    (hkr0 : r rKr ≠ 0) (hkrLast : r rKr ≠ c.bsSteps)
    (hgate : r 43 = 1) (hzero : r rZero = 0) (hbsM : c.bsSteps < M)
    (hsink : c.sink < M) :
    let out := srun idx r (headPreS c)
    out 140 = 0 ∧ out 141 = 0 ∧ out 142 = 1 ∧ out 144 = c.sink := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hkr0' : r 14 ≠ 0 := by simpa [rKr] using hkr0
  have hkrLast' : r 14 ≠ c.bsSteps := by simpa [rKr] using hkrLast
  have hzero' : r 1 = 0 := by simpa [rZero] using hzero
  simp [headPreS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rKr, rC, rZero,
    hkr0', hkrLast', hgate, hzero', h0M, h1M,
    Nat.mod_eq_of_lt hbsM, Nat.mod_eq_of_lt hsink]

theorem headPre_last_run (c : Cfg) (idx : Nat) (r : RegState)
    (hkrLast : r rKr = c.bsSteps) (hbsPos : 0 < c.bsSteps)
    (hgate : r 43 = 1) (hzero : r rZero = 0) (hbsM : c.bsSteps < M)
    (hsink : c.sink < M) :
    let out := srun idx r (headPreS c)
    out 140 = 0 ∧ out 141 = 1 ∧ out 142 = 1 ∧ out 144 = c.sink := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hkrLast' : r 14 = c.bsSteps := by simpa [rKr] using hkrLast
  have hbs0 : c.bsSteps ≠ 0 := Nat.ne_of_gt hbsPos
  have hzero' : r 1 = 0 := by simpa [rZero] using hzero
  simp [headPreS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rKr, rC, rZero,
    hkrLast', hbs0, hgate, hzero', h0M, h1M,
    Nat.mod_eq_of_lt hbsM, Nat.mod_eq_of_lt hsink]

def headFrontS (_c : Cfg) : List Instr :=
  [ .binop 149 .mul (.reg 148) (.reg 140)
  , .binop rF .add (.reg rF) (.reg 149)
  , .binop 150 .add (.reg rW) (.reg rC) ] ++
  Section413G1Denote.muxS rK 140 150 rK 151 ++
  [ .binop 152 .ge (.reg rK) (.reg rT2)
  , .binop 152 .mul (.reg 152) (.reg 140)
  , .binop rT .add (.reg rT) (.reg 152)
  , .binop 153 .mul (.reg rT) (.lit 2)
  , .binop 153 .add (.reg 153) (.lit 1)
  , .binop 153 .mul (.reg 153) (.reg 152)
  , .binop rT2 .add (.reg rT2) (.reg 153)
  , .binop 154 .ge (.reg rK) (.reg rT2)
  , .binop 154 .mul (.reg 154) (.reg 140)
  , .binop rViol .add (.reg rViol) (.reg 154)
  , .binop rVSqrt .add (.reg rVSqrt) (.reg 154)
  , .binop 155 .sub (.lit 1) (.reg rF)
  , .binop 156 .ge (.reg 155) (.lit 9223372036854775808)
  , .binop 157 .sub (.lit 0) (.reg 155) ] ++
  Section413G1Denote.muxS 158 156 157 155 159 ++
  [ .binop 160 .gt (.reg 158) (.reg rE)
  , .binop 161 .sub (.reg 158) (.reg rE)
  , .binop 161 .mul (.reg 161) (.reg 160)
  , .binop 162 .gt (.reg rE) (.reg 158)
  , .binop 163 .sub (.reg rE) (.reg 158)
  , .binop 163 .mul (.reg 163) (.reg 162) ]

def headLatchS : List Instr :=
  Section413G1Denote.muxS rDp 140 161 rDp 164 ++
  Section413G1Denote.muxS rDn 140 163 rDn 164 ++
  Section413G1Denote.muxS rE 140 158 rE 164

def headRecipS (c : Cfg) : List Instr :=
  [ .binop 165 .add (.reg rDp) (.reg rDn)
  , .binop 166 .mul (.reg 165) (.reg 140)
  , .binop rTv .add (.reg rTv) (.reg 166)
  , .binop 167 .add (.lit (c.wScale - 1)) (.reg rK)
  , .binop 167 .udiv (.reg 167) (.reg rK)
  , .binop 168 .udiv (.lit c.wScale) (.reg rK)
  , .binop 169 .mul (.reg rDp) (.reg 140)
  , .binop 170 .mul (.reg rDn) (.reg 140) ]

theorem headPostS_decomp (c : Cfg) :
    headPostS c = headFrontS c ++ headLatchS ++ headRecipS c := by
  simp [headPostS, headFrontS, headLatchS, headRecipS, List.append_assoc]

theorem headFront_middle_run (c : Cfg) (idx : Nat) (r : RegState)
    (h140 : r 140 = 0) (hword : ∀ j, r j < M) :
    let out := srun idx r (headFrontS c)
    out rF = r rF ∧ out rK = r rK ∧ out rT = r rT ∧
      out rT2 = r rT2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out 140 = 0 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  simp [headFrontS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rF, rK, rT, rT2, rViol, rVSqrt,
    rW, rC, h140, h0M]
  exact ⟨Nat.mod_eq_of_lt (hword 12), Nat.mod_eq_of_lt (hword 30),
    Nat.mod_eq_of_lt (hword 20), Nat.mod_eq_of_lt (hword 21),
    Nat.mod_eq_of_lt (hword 22), Nat.mod_eq_of_lt (hword 247)⟩

theorem headLatch_middle_run (idx : Nat) (r : RegState)
    (h140 : r 140 = 0) (hword : ∀ j, r j < M) :
    let out := srun idx r headLatchS
    out rDp = r rDp ∧ out rDn = r rDn ∧ out rE = r rE ∧
      out 140 = 0 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  simp [headLatchS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rDp, rDn, rE, h140, h0M]
  exact ⟨Nat.mod_eq_of_lt (hword 16), Nat.mod_eq_of_lt (hword 17),
    Nat.mod_eq_of_lt (hword 13)⟩

theorem headRecip_middle_run (c : Cfg) (idx : Nat) (r : RegState)
    (h140 : r 140 = 0) (hk : 0 < r rK) (hword : ∀ j, r j < M)
    (hWM : c.wScale < M) (hsum : r rDp + r rDn < M)
    (hceilFit : c.wScale - 1 + r rK < M) :
    let out := srun idx r (headRecipS c)
    out 165 = r rDp + r rDn ∧ out rTv = r rTv ∧
      out 167 = (c.wScale - 1 + r rK) / r rK ∧
      out 168 = c.wScale / r rK ∧ out 169 = 0 ∧ out 170 = 0 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have hk0 : r rK ≠ 0 := Nat.ne_of_gt hk
  have hdivM : (c.wScale - 1 + r rK) / r rK < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by exact hceilFit)
  have hfloorM : c.wScale / r rK < M := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hWM
  have hk0' : r 30 ≠ 0 := by simpa [rK] using hk0
  have hsum' : r 16 + r 17 < M := by simpa [rDp, rDn] using hsum
  have hceilFit' : c.wScale - 1 + r 30 < M := by
    simpa [rK] using hceilFit
  have hdivM' : (c.wScale - 1 + r 30) / r 30 < M := by
    simpa [rK] using hdivM
  have hfloorM' : c.wScale / r 30 < M := by simpa [rK] using hfloorM
  simp [headRecipS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rDp, rDn, rTv, rK, h140, h0M]
  refine ⟨Nat.mod_eq_of_lt hsum', Nat.mod_eq_of_lt (hword 29), ?_, ?_⟩
  · simp [hk0', Nat.mod_eq_of_lt hceilFit',
      Nat.mod_eq_of_lt hdivM']
  · simp [hk0', Nat.mod_eq_of_lt hWM, Nat.mod_eq_of_lt hfloorM']

theorem headPost_middle_run (c : Cfg) (idx : Nat) (r : RegState)
    (h140 : r 140 = 0) (hk : 0 < r rK) (hword : ∀ j, r j < M)
    (hWM : c.wScale < M) (hsum : r rDp + r rDn < M)
    (hceilFit : c.wScale - 1 + r rK < M) :
    let out := srun idx r (headPostS c)
    out rF = r rF ∧ out rK = r rK ∧ out rT = r rT ∧
      out rT2 = r rT2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out rDp = r rDp ∧
      out rDn = r rDn ∧ out rE = r rE ∧ out rTv = r rTv ∧
      out 165 = r rDp + r rDn ∧
      out 167 = (c.wScale - 1 + r rK) / r rK ∧
      out 168 = c.wScale / r rK ∧ out 169 = 0 ∧ out 170 = 0 ∧
      out 140 = 0 := by
  let f := srun idx r (headFrontS c)
  let l := srun idx f headLatchS
  let out := srun idx l (headRecipS c)
  have hf := headFront_middle_run c idx r h140 hword
  dsimp only at hf
  change f rF = r rF ∧ f rK = r rK ∧ f rT = r rT ∧
    f rT2 = r rT2 ∧ f rViol = r rViol ∧
    f rVSqrt = r rVSqrt ∧ f 140 = 0 at hf
  have hfword : ∀ j, f j < M := srun_lt_of_lt idx _ r hword
  have hfDp : f rDp = r rDp :=
    RegFrame.srun_frame idx rDp (headFrontS c) (by rfl) r
  have hfDn : f rDn = r rDn :=
    RegFrame.srun_frame idx rDn (headFrontS c) (by rfl) r
  have hfE : f rE = r rE :=
    RegFrame.srun_frame idx rE (headFrontS c) (by rfl) r
  have hfTv : f rTv = r rTv :=
    RegFrame.srun_frame idx rTv (headFrontS c) (by rfl) r
  have hl := headLatch_middle_run idx f hf.2.2.2.2.2.2 hfword
  dsimp only at hl
  change l rDp = f rDp ∧ l rDn = f rDn ∧ l rE = f rE ∧
    l 140 = 0 at hl
  have hlword : ∀ j, l j < M := srun_lt_of_lt idx _ f hfword
  have hlK : l rK = r rK := by
    rw [show l rK = f rK from
      RegFrame.srun_frame idx rK headLatchS (by rfl) f, hf.2.1]
  have hlTv : l rTv = r rTv := by
    rw [show l rTv = f rTv from
      RegFrame.srun_frame idx rTv headLatchS (by rfl) f, hfTv]
  have hl140 : l 140 = 0 := by
    exact hl.2.2.2
  have hlsum : l rDp + l rDn < M := by rw [hl.1, hl.2.1, hfDp, hfDn]; exact hsum
  have hlceil : c.wScale - 1 + l rK < M := by rw [hlK]; exact hceilFit
  have hlk : 0 < l rK := by rw [hlK]; exact hk
  have hr := headRecip_middle_run c idx l hl140 hlk hlword hWM hlsum hlceil
  dsimp only at hr
  change out 165 = l rDp + l rDn ∧ out rTv = l rTv ∧
    out 167 = (c.wScale - 1 + l rK) / l rK ∧
    out 168 = c.wScale / l rK ∧ out 169 = 0 ∧ out 170 = 0 at hr
  have keepRecip (j : Nat) (hw : RegFrame.writes j (headRecipS c) = false) :
      out j = l j := by
    exact RegFrame.srun_frame idx j (headRecipS c) hw l
  have houtF : out rF = r rF := by
    rw [keepRecip rF (by rfl), show l rF = f rF from
      RegFrame.srun_frame idx rF headLatchS (by rfl) f, hf.1]
  have houtK : out rK = r rK := by rw [keepRecip rK (by rfl), hlK]
  have houtT : out rT = r rT := by
    rw [keepRecip rT (by rfl), show l rT = f rT from
      RegFrame.srun_frame idx rT headLatchS (by rfl) f, hf.2.2.1]
  have houtT2 : out rT2 = r rT2 := by
    rw [keepRecip rT2 (by rfl), show l rT2 = f rT2 from
      RegFrame.srun_frame idx rT2 headLatchS (by rfl) f, hf.2.2.2.1]
  have houtViol : out rViol = r rViol := by
    rw [keepRecip rViol (by rfl), show l rViol = f rViol from
      RegFrame.srun_frame idx rViol headLatchS (by rfl) f, hf.2.2.2.2.1]
  have houtVSqrt : out rVSqrt = r rVSqrt := by
    rw [keepRecip rVSqrt (by rfl), show l rVSqrt = f rVSqrt from
      RegFrame.srun_frame idx rVSqrt headLatchS (by rfl) f,
      hf.2.2.2.2.2.1]
  have houtDp : out rDp = r rDp := by
    rw [keepRecip rDp (by rfl), hl.1, hfDp]
  have houtDn : out rDn = r rDn := by
    rw [keepRecip rDn (by rfl), hl.2.1, hfDn]
  have houtE : out rE = r rE := by
    rw [keepRecip rE (by rfl), hl.2.2.1, hfE]
  have hout140 : out 140 = 0 := by rw [keepRecip 140 (by rfl), hl140]
  have houtTv : out rTv = r rTv := by rw [hr.2.1, hlTv]
  have hout165 : out 165 = r rDp + r rDn := by
    rw [hr.1, hl.1, hl.2.1, hfDp, hfDn]
  have hout167 : out 167 = (c.wScale - 1 + r rK) / r rK := by
    rw [hr.2.2.1, hlK]
  have hout168 : out 168 = c.wScale / r rK := by
    rw [hr.2.2.2.1, hlK]
  have hall : out rF = r rF ∧ out rK = r rK ∧ out rT = r rT ∧
      out rT2 = r rT2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out rDp = r rDp ∧
      out rDn = r rDn ∧ out rE = r rE ∧ out rTv = r rTv ∧
      out 165 = r rDp + r rDn ∧
      out 167 = (c.wScale - 1 + r rK) / r rK ∧
      out 168 = c.wScale / r rK ∧ out 169 = 0 ∧ out 170 = 0 ∧
      out 140 = 0 :=
    ⟨houtF, houtK, houtT, houtT2, houtViol, houtVSqrt,
      houtDp, houtDn, houtE, houtTv, hout165, hout167, hout168,
      hr.2.2.2.2.1, hr.2.2.2.2.2, hout140⟩
  simpa [headPostS_decomp, srun_append, f, l, out] using hall

structure MiddleHeadSpec (c : Cfg) (before after : AState) : Prop where
  arr : after.arr = before.arr
  round0 : after.regs 140 = 0
  last : after.regs 141 = 0
  bisect : after.regs 142 = 1
  f : after.regs rF = before.regs rF
  k : after.regs rK = before.regs rK
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  viol : after.regs rViol = before.regs rViol
  vSqrt : after.regs rVSqrt = before.regs rVSqrt
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  sum : after.regs 165 = before.regs rDp + before.regs rDn
  ceil : after.regs 167 =
    (c.wScale - 1 + before.regs rK) / before.regs rK
  floor : after.regs 168 = c.wScale / before.regs rK
  posGate : after.regs 169 = 0
  negGate : after.regs 170 = 0
  low : after.regs rSl = before.regs rSl
  high : after.regs rSh = before.regs rSh
  cell : after.regs rC = before.regs rC
  round : after.regs rKr = before.regs rKr

set_option maxRecDepth 2048 in
theorem accHead_middle_run (c : Cfg) (idx : Nat) (st : AState)
    (hkr0 : st.regs rKr ≠ 0) (hkrLast : st.regs rKr ≠ c.bsSteps)
    (hgate : st.regs 43 = 1) (hzero : st.regs rZero = 0)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsink0 : st.arr c.sink = 0) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    MiddleHeadSpec c st (arun idx st c.accHead) := by
  let pre := srun idx st.regs (headPreS c)
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  let post := srun idx loaded (headPostS c)
  let out : AState := ⟨post, cleared⟩
  have ha := accHead_arun c idx st
  dsimp only at ha
  change arun idx st c.accHead = out at ha
  have hp := headPre_middle_run c idx st.regs hkr0 hkrLast hgate hzero
    hbsM hsinkM
  dsimp only at hp
  change pre 140 = 0 ∧ pre 141 = 0 ∧ pre 142 = 1 ∧
    pre 144 = c.sink at hp
  have preKeep (j : Nat) (hw : RegFrame.writes j (headPreS c) = false) :
      pre j = st.regs j :=
    RegFrame.srun_frame idx j (headPreS c) hw st.regs
  have hpreword : ∀ j, pre j < M := srun_lt_of_lt idx _ st.regs hword
  have loadedKeep (j : Nat) (hj : j ≠ 148) : loaded j = pre j := by
    simp [loaded, RegState.set, hj]
  have hloaded144 : loaded 144 = c.sink := by
    rw [loadedKeep 144 (by decide), hp.2.2.2]
  have hloadedZero : loaded rZero = 0 := by
    rw [loadedKeep rZero (by simp [rZero]), preKeep rZero (by rfl), hzero]
  have hloadedword : ∀ j, loaded j < M := by
    intro j
    by_cases hj : j = 148
    · subst j
      simp [loaded, RegState.set]
      exact harrword (pre 144)
    · rw [loadedKeep j hj]
      exact hpreword j
  have hcleared : cleared = st.arr := by
    funext j
    simp only [cleared, hloaded144, hloadedZero]
    by_cases hj : j = c.sink
    · rw [if_pos hj, hj, hsink0]
    · rw [if_neg hj]
  have hloaded140 : loaded 140 = 0 := by
    rw [loadedKeep 140 (by decide), hp.1]
  have hloadedK : loaded rK = st.regs rK := by
    rw [loadedKeep rK (by simp [rK]), preKeep rK (by rfl)]
  have hloadedDp : loaded rDp = st.regs rDp := by
    rw [loadedKeep rDp (by simp [rDp]), preKeep rDp (by rfl)]
  have hloadedDn : loaded rDn = st.regs rDn := by
    rw [loadedKeep rDn (by simp [rDn]), preKeep rDn (by rfl)]
  have hpost := headPost_middle_run c idx loaded hloaded140
    (by rw [hloadedK]; exact hk) hloadedword hWM
    (by rw [hloadedDp, hloadedDn]; exact hsum)
    (by rw [hloadedK]; exact hceilFit)
  dsimp only at hpost
  change post rF = loaded rF ∧ post rK = loaded rK ∧
    post rT = loaded rT ∧ post rT2 = loaded rT2 ∧
    post rViol = loaded rViol ∧ post rVSqrt = loaded rVSqrt ∧
    post rDp = loaded rDp ∧ post rDn = loaded rDn ∧
    post rE = loaded rE ∧ post rTv = loaded rTv ∧
    post 165 = loaded rDp + loaded rDn ∧
    post 167 = (c.wScale - 1 + loaded rK) / loaded rK ∧
    post 168 = c.wScale / loaded rK ∧ post 169 = 0 ∧
    post 170 = 0 ∧ post 140 = 0 at hpost
  rcases hpost with ⟨hPF, hPK, hPT, hPT2, hPV, hPVS, hPDp, hPDn,
    hPE, hPTv, hPSum, hPCeil, hPFloor, hPPos, hPNeg, hP140⟩
  have loadedToBefore (j : Nat) (hj148 : j ≠ 148)
      (hw : RegFrame.writes j (headPreS c) = false) :
      loaded j = st.regs j := by rw [loadedKeep j hj148, preKeep j hw]
  have postKeep (j : Nat) (hw : RegFrame.writes j (headPostS c) = false) :
      post j = loaded j := RegFrame.srun_frame idx j (headPostS c) hw loaded
  rw [ha]
  dsimp only [out]
  refine
    { arr := hcleared
      round0 := hP140
      last := ?_
      bisect := ?_
      f := ?_
      k := ?_
      t := ?_
      t2 := ?_
      viol := ?_
      vSqrt := ?_
      dPos := ?_
      dNeg := ?_
      e := ?_
      tv := ?_
      sum := ?_
      ceil := ?_
      floor := ?_
      posGate := hPPos
      negGate := hPNeg
      low := ?_
      high := ?_
      cell := ?_
      round := ?_ }
  · change post 141 = 0
    rw [postKeep 141 (by rfl), loadedKeep 141 (by decide), hp.2.1]
  · change post 142 = 1
    rw [postKeep 142 (by rfl), loadedKeep 142 (by decide), hp.2.2.1]
  · change post rF = st.regs rF
    rw [hPF, loadedToBefore rF (by simp [rF]) (by rfl)]
  · change post rK = st.regs rK
    rw [hPK, hloadedK]
  · change post rT = st.regs rT
    rw [hPT, loadedToBefore rT (by simp [rT]) (by rfl)]
  · change post rT2 = st.regs rT2
    rw [hPT2, loadedToBefore rT2 (by simp [rT2]) (by rfl)]
  · change post rViol = st.regs rViol
    rw [hPV,
      loadedToBefore rViol (by simp [rViol]) (by rfl)]
  · change post rVSqrt = st.regs rVSqrt
    rw [hPVS,
      loadedToBefore rVSqrt (by simp [rVSqrt]) (by rfl)]
  · change post rDp = st.regs rDp
    rw [hPDp, hloadedDp]
  · change post rDn = st.regs rDn
    rw [hPDn, hloadedDn]
  · change post rE = st.regs rE
    rw [hPE,
      loadedToBefore rE (by simp [rE]) (by rfl)]
  · change post rTv = st.regs rTv
    rw [hPTv,
      loadedToBefore rTv (by simp [rTv]) (by rfl)]
  · change post 165 = st.regs rDp + st.regs rDn
    rw [hPSum, hloadedDp, hloadedDn]
  · change post 167 = (c.wScale - 1 + st.regs rK) / st.regs rK
    rw [hPCeil, hloadedK]
  · change post 168 = c.wScale / st.regs rK
    rw [hPFloor, hloadedK]
  · change post rSl = st.regs rSl
    rw [postKeep rSl (by rfl),
      loadedToBefore rSl (by simp [rSl]) (by rfl)]
  · change post rSh = st.regs rSh
    rw [postKeep rSh (by rfl),
      loadedToBefore rSh (by simp [rSh]) (by rfl)]
  · change post rC = st.regs rC
    rw [postKeep rC (by rfl),
      loadedToBefore rC (by simp [rC]) (by rfl)]
  · change post rKr = st.regs rKr
    rw [postKeep rKr (by rfl),
      loadedToBefore rKr (by simp [rKr]) (by rfl)]

structure LastHeadSpec (before after : AState) : Prop where
  arr : after.arr = before.arr
  round0 : after.regs 140 = 0
  last : after.regs 141 = 1
  bisect : after.regs 142 = 1
  f : after.regs rF = before.regs rF
  k : after.regs rK = before.regs rK
  t : after.regs rT = before.regs rT
  t2 : after.regs rT2 = before.regs rT2
  viol : after.regs rViol = before.regs rViol
  vSqrt : after.regs rVSqrt = before.regs rVSqrt
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  e : after.regs rE = before.regs rE
  tv : after.regs rTv = before.regs rTv
  posGate : after.regs 169 = 0
  negGate : after.regs 170 = 0
  low : after.regs rSl = before.regs rSl
  high : after.regs rSh = before.regs rSh
  cell : after.regs rC = before.regs rC
  round : after.regs rKr = before.regs rKr

set_option maxRecDepth 2048 in
theorem accHead_last_run (c : Cfg) (idx : Nat) (st : AState)
    (hkrLast : st.regs rKr = c.bsSteps) (hbsPos : 0 < c.bsSteps)
    (hgate : st.regs 43 = 1) (hzero : st.regs rZero = 0)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsink0 : st.arr c.sink = 0) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    LastHeadSpec st (arun idx st c.accHead) := by
  let pre := srun idx st.regs (headPreS c)
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  let post := srun idx loaded (headPostS c)
  let out : AState := ⟨post, cleared⟩
  have ha := accHead_arun c idx st
  dsimp only at ha
  change arun idx st c.accHead = out at ha
  have hp := headPre_last_run c idx st.regs hkrLast hbsPos hgate hzero
    hbsM hsinkM
  dsimp only at hp
  change pre 140 = 0 ∧ pre 141 = 1 ∧ pre 142 = 1 ∧
    pre 144 = c.sink at hp
  have preKeep (j : Nat) (hw : RegFrame.writes j (headPreS c) = false) :
      pre j = st.regs j :=
    RegFrame.srun_frame idx j (headPreS c) hw st.regs
  have hpreword : ∀ j, pre j < M := srun_lt_of_lt idx _ st.regs hword
  have loadedKeep (j : Nat) (hj : j ≠ 148) : loaded j = pre j := by
    simp [loaded, RegState.set, hj]
  have hloaded144 : loaded 144 = c.sink := by
    rw [loadedKeep 144 (by decide), hp.2.2.2]
  have hloadedZero : loaded rZero = 0 := by
    rw [loadedKeep rZero (by simp [rZero]), preKeep rZero (by rfl), hzero]
  have hloadedword : ∀ j, loaded j < M := by
    intro j
    by_cases hj : j = 148
    · subst j
      simp [loaded, RegState.set]
      exact harrword (pre 144)
    · rw [loadedKeep j hj]
      exact hpreword j
  have hcleared : cleared = st.arr := by
    funext j
    simp only [cleared, hloaded144, hloadedZero]
    by_cases hj : j = c.sink
    · rw [if_pos hj, hj, hsink0]
    · rw [if_neg hj]
  have loadedToBefore (j : Nat) (hj148 : j ≠ 148)
      (hw : RegFrame.writes j (headPreS c) = false) :
      loaded j = st.regs j := by rw [loadedKeep j hj148, preKeep j hw]
  have hloaded140 : loaded 140 = 0 := by
    rw [loadedKeep 140 (by decide), hp.1]
  have hloadedK : loaded rK = st.regs rK :=
    loadedToBefore rK (by simp [rK]) (by rfl)
  have hloadedDp : loaded rDp = st.regs rDp :=
    loadedToBefore rDp (by simp [rDp]) (by rfl)
  have hloadedDn : loaded rDn = st.regs rDn :=
    loadedToBefore rDn (by simp [rDn]) (by rfl)
  have hpost := headPost_middle_run c idx loaded hloaded140
    (by rw [hloadedK]; exact hk) hloadedword hWM
    (by rw [hloadedDp, hloadedDn]; exact hsum)
    (by rw [hloadedK]; exact hceilFit)
  dsimp only at hpost
  change post rF = loaded rF ∧ post rK = loaded rK ∧
    post rT = loaded rT ∧ post rT2 = loaded rT2 ∧
    post rViol = loaded rViol ∧ post rVSqrt = loaded rVSqrt ∧
    post rDp = loaded rDp ∧ post rDn = loaded rDn ∧
    post rE = loaded rE ∧ post rTv = loaded rTv ∧
    post 165 = loaded rDp + loaded rDn ∧
    post 167 = (c.wScale - 1 + loaded rK) / loaded rK ∧
    post 168 = c.wScale / loaded rK ∧ post 169 = 0 ∧
    post 170 = 0 ∧ post 140 = 0 at hpost
  rcases hpost with ⟨hPF, hPK, hPT, hPT2, hPV, hPVS, hPDp, hPDn,
    hPE, hPTv, _, _, _, hPPos, hPNeg, hP140⟩
  have postKeep (j : Nat) (hw : RegFrame.writes j (headPostS c) = false) :
      post j = loaded j := RegFrame.srun_frame idx j (headPostS c) hw loaded
  rw [ha]
  refine
    { arr := hcleared
      round0 := hP140
      last := ?_
      bisect := ?_
      f := ?_
      k := ?_
      t := ?_
      t2 := ?_
      viol := ?_
      vSqrt := ?_
      dPos := ?_
      dNeg := ?_
      e := ?_
      tv := ?_
      posGate := hPPos
      negGate := hPNeg
      low := ?_
      high := ?_
      cell := ?_
      round := ?_ }
  · change post 141 = 1
    rw [postKeep 141 (by rfl), loadedKeep 141 (by decide), hp.2.1]
  · change post 142 = 1
    rw [postKeep 142 (by rfl), loadedKeep 142 (by decide), hp.2.2.1]
  · change post rF = st.regs rF
    rw [hPF, loadedToBefore rF (by simp [rF]) (by rfl)]
  · change post rK = st.regs rK
    rw [hPK, hloadedK]
  · change post rT = st.regs rT
    rw [hPT, loadedToBefore rT (by simp [rT]) (by rfl)]
  · change post rT2 = st.regs rT2
    rw [hPT2, loadedToBefore rT2 (by simp [rT2]) (by rfl)]
  · change post rViol = st.regs rViol
    rw [hPV, loadedToBefore rViol (by simp [rViol]) (by rfl)]
  · change post rVSqrt = st.regs rVSqrt
    rw [hPVS, loadedToBefore rVSqrt (by simp [rVSqrt]) (by rfl)]
  · change post rDp = st.regs rDp
    rw [hPDp, hloadedDp]
  · change post rDn = st.regs rDn
    rw [hPDn, hloadedDn]
  · change post rE = st.regs rE
    rw [hPE, loadedToBefore rE (by simp [rE]) (by rfl)]
  · change post rTv = st.regs rTv
    rw [hPTv, loadedToBefore rTv (by simp [rTv]) (by rfl)]
  · change post rSl = st.regs rSl
    rw [postKeep rSl (by rfl),
      loadedToBefore rSl (by simp [rSl]) (by rfl)]
  · change post rSh = st.regs rSh
    rw [postKeep rSh (by rfl),
      loadedToBefore rSh (by simp [rSh]) (by rfl)]
  · change post rC = st.regs rC
    rw [postKeep rC (by rfl),
      loadedToBefore rC (by simp [rC]) (by rfl)]
  · change post rKr = st.regs rKr
    rw [postKeep rKr (by rfl),
      loadedToBefore rKr (by simp [rKr]) (by rfl)]

end LeanCompCert.Ports.CDEMAbelAccumulation
