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

theorem headPre_first_run (c : Cfg) (idx : Nat) (r : RegState)
    (hkr : r rKr = 0) (hbsPos : 0 < c.bsSteps)
    (hbsM : c.bsSteps < M) (hgate : r 43 = 1)
    (haddr : r rC + c.winBase < M) :
    let out := srun idx r (headPreS c)
    out 140 = 1 ∧ out 141 = 0 ∧ out 142 = 0 ∧
      out 144 = r rC + c.winBase := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hkr' : r 14 = 0 := by simpa [rKr] using hkr
  have hbs0 : c.bsSteps ≠ 0 := Nat.ne_of_gt hbsPos
  have h0bs : 0 ≠ c.bsSteps := Ne.symm hbs0
  have hcoeff : 1 + (M - 1) = M := by decide
  have haddr' : r 15 + c.winBase < M := by simpa [rC] using haddr
  simp [headPreS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rKr, rC, rZero,
    hkr', hgate, h0M, h1M, hcoeff, Nat.mod_eq_of_lt hbsM]
  exact ⟨by simp [h0bs, h0M], Nat.mod_eq_of_lt haddr'⟩

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

def headTailS (c : Cfg) : List Instr := headLatchS ++ headRecipS c

theorem headPostS_tail_decomp (c : Cfg) :
    headPostS c = headFrontS c ++ headTailS c := by
  simp [headPostS_decomp, headTailS, List.append_assoc]

def headFKS : List Instr :=
  [ .binop 149 .mul (.reg 148) (.reg 140)
  , .binop rF .add (.reg rF) (.reg 149)
  , .binop 150 .add (.reg rW) (.reg rC) ] ++
  Section413G1Denote.muxS rK 140 150 rK 151

def headSqrtS : List Instr :=
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
  , .binop rVSqrt .add (.reg rVSqrt) (.reg 154) ]

def headDeltaS : List Instr :=
  [ .binop 155 .sub (.lit 1) (.reg rF)
  , .binop 156 .ge (.reg 155) (.lit 9223372036854775808)
  , .binop 157 .sub (.lit 0) (.reg 155) ] ++
  Section413G1Denote.muxS 158 156 157 155 159 ++
  [ .binop 160 .gt (.reg 158) (.reg rE)
  , .binop 161 .sub (.reg 158) (.reg rE)
  , .binop 161 .mul (.reg 161) (.reg 160)
  , .binop 162 .gt (.reg rE) (.reg 158)
  , .binop 163 .sub (.reg rE) (.reg 158)
  , .binop 163 .mul (.reg 163) (.reg 162) ]

theorem headFrontS_decomp (c : Cfg) :
    headFrontS c = headFKS ++ headSqrtS ++ headDeltaS := by
  simp [headFrontS, headFKS, headSqrtS, headDeltaS, List.append_assoc]

theorem headFK_first_run (idx : Nat) (r : RegState)
    (h140 : r 140 = 1) (hkFit : r rW + r rC < M) :
    let out := srun idx r headFKS
    out rF = (r rF + r 148) % M ∧ out rK = r rW + r rC ∧
      out 140 = 1 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcoeff : 1 + (M - 1) = M := by decide
  have hkFit' : r 3 + r 15 < M := by simpa [rW, rC] using hkFit
  simp [headFKS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rF, rK, rW, rC,
    h140, h0M, h1M, hcoeff]
  exact Nat.mod_eq_of_lt hkFit'

theorem headSqrt_noBump_run (idx : Nat) (r : RegState) (k t t2 : Nat)
    (h140 : r 140 = 1) (hK : r rK = k) (hT : r rT = t)
    (hT2 : r rT2 = t2) (hklt : k < t2) (hword : ∀ j, r j < M) :
    let out := srun idx r headSqrtS
    out rT = t ∧ out rT2 = t2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out 140 = 1 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have hK' : r 30 = k := by simpa [rK] using hK
  have hT' : r 20 = t := by simpa [rT] using hT
  have hT2' : r 21 = t2 := by simpa [rT2] using hT2
  have ht2M : t2 % M = t2 :=
    Nat.mod_eq_of_lt (by simpa [hT2'] using hword 21)
  have htM : t % M = t :=
    Nat.mod_eq_of_lt (by simpa [hT'] using hword 20)
  simp [headSqrtS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rK, rT, rT2, rViol, rVSqrt, h140, hK', hT', hT2',
    Nat.not_le_of_gt hklt, h0M, htM, ht2M,
    Nat.mod_eq_of_lt (hword 22), Nat.mod_eq_of_lt (hword 247)]

theorem headSqrt_bump_run (idx : Nat) (r : RegState) (k t t2 : Nat)
    (h140 : r 140 = 1) (hK : r rK = k) (hT : r rT = t)
    (hT2 : r rT2 = t2) (ht2k : t2 ≤ k)
    (hkclosed : k < t2 + (2 * (t + 1) + 1))
    (htFit : t + 1 < M) (hdoubleFit : 2 * (t + 1) + 1 < M)
    (ht2Fit : t2 + (2 * (t + 1) + 1) < M)
    (hword : ∀ j, r j < M) :
    let out := srun idx r headSqrtS
    out rT = t + 1 ∧ out rT2 = t2 + (2 * (t + 1) + 1) ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧ out 140 = 1 := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hK' : r 30 = k := by simpa [rK] using hK
  have hT' : r 20 = t := by simpa [rT] using hT
  have hT2' : r 21 = t2 := by simpa [rT2] using hT2
  have hform : t2 + ((t + 1) * 2 + 1) = t2 + (2 * (t + 1) + 1) := by
    omega
  have hdoubleFit' : (t + 1) * 2 + 1 < M := by omega
  have hnewM : (t2 + (2 * (t + 1) + 1)) % M =
      t2 + (2 * (t + 1) + 1) := Nat.mod_eq_of_lt ht2Fit
  have hnle : ¬ t2 + (2 * (t + 1) + 1) ≤ k := Nat.not_le_of_gt hkclosed
  simp [headSqrtS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rK, rT, rT2, rViol, rVSqrt, h140, hK', hT', hT2', ht2k,
    h0M, h1M, Nat.mod_eq_of_lt htFit,
    Nat.mod_eq_of_lt hdoubleFit', hform,
    hnewM, hnle, Nat.mod_eq_of_lt (hword 22), Nat.mod_eq_of_lt (hword 247)]

def headX (f : Nat) : Nat := (1 + (M - f)) % M

def headG (f : Nat) : Nat :=
  if 9223372036854775808 ≤ headX f then (M - headX f) % M else headX f

def headDPos (g e : Nat) : Nat := if e < g then g - e else 0

def headDNeg (g e : Nat) : Nat := if g < e then e - g else 0

def headAbsPreS : List Instr :=
  [ .binop 155 .sub (.lit 1) (.reg rF)
  , .binop 156 .ge (.reg 155) (.lit 9223372036854775808)
  , .binop 157 .sub (.lit 0) (.reg 155) ]

def headIncS : List Instr :=
  [ .binop 160 .gt (.reg 158) (.reg rE)
  , .binop 161 .sub (.reg 158) (.reg rE)
  , .binop 161 .mul (.reg 161) (.reg 160)
  , .binop 162 .gt (.reg rE) (.reg 158)
  , .binop 163 .sub (.reg rE) (.reg 158)
  , .binop 163 .mul (.reg 163) (.reg 162) ]

theorem headDeltaS_decomp : headDeltaS = headAbsPreS ++
    Section413G1Denote.muxS 158 156 157 155 159 ++ headIncS := by
  rfl

theorem headAbsPre_run (idx : Nat) (r : RegState) (f : Nat)
    (hF : r rF = f) :
    let out := srun idx r headAbsPreS
    out 155 = headX f ∧
      out 156 = (if 9223372036854775808 ≤ headX f then 1 else 0) ∧
      out 157 = (M - headX f) % M ∧ out rF = f := by
  have hF' : r 12 = f := by simpa [rF] using hF
  have hcut : 9223372036854775808 % M = 9223372036854775808 := by decide
  simp [headAbsPreS, headX, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rF, hF', hcut]

theorem headInc_run (idx : Nat) (r : RegState) (g e : Nat)
    (hG : r 158 = g) (hE : r rE = e) (hgM : g < M) (heM : e < M) :
    let out := srun idx r headIncS
    out 161 = headDPos g e ∧ out 163 = headDNeg g e ∧
      out 158 = g ∧ out rE = e := by
  have hG' : r 158 = g := hG
  have hE' : r 13 = e := by simpa [rE] using hE
  by_cases hp : e < g
  · have hn : ¬ g < e := by omega
    have hsub := msub_exact g e (Nat.le_of_lt hp) hgM
    have hsubM : (g - e) % M = g - e := Nat.mod_eq_of_lt (by omega)
    simp [headIncS, headDPos, headDNeg, srun, sdest, sval,
      denoteOperand, denoteOp, RegState.set, rE, hG', hE', hp, hn,
      hsub, hsubM]
  · by_cases hn : g < e
    · have hsub := msub_exact e g (Nat.le_of_lt hn) heM
      have hsubM : (e - g) % M = e - g := Nat.mod_eq_of_lt (by omega)
      simp [headIncS, headDPos, headDNeg, srun, sdest, sval,
        denoteOperand, denoteOp, RegState.set, rE, hG', hE', hp, hn,
        hsub, hsubM]
    · have hEq : g = e := by omega
      simp [headIncS, headDPos, headDNeg, srun, sdest, sval,
        denoteOperand, denoteOp, RegState.set, rE, hG', hE', hEq]

theorem headDelta_run (idx : Nat) (r : RegState) (f e : Nat)
    (hF : r rF = f) (hE : r rE = e) (hword : ∀ j, r j < M) :
    let out := srun idx r headDeltaS
    out 158 = headG f ∧ out 161 = headDPos (headG f) e ∧
      out 163 = headDNeg (headG f) e ∧ out rF = f ∧ out rE = e := by
  let q := srun idx r headAbsPreS
  let m := srun idx q (Section413G1Denote.muxS 158 156 157 155 159)
  let out := srun idx m headIncS
  have hp := headAbsPre_run idx r f hF
  dsimp only at hp
  change q 155 = headX f ∧
    q 156 = (if 9223372036854775808 ≤ headX f then 1 else 0) ∧
    q 157 = (M - headX f) % M ∧ q rF = f at hp
  have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ r hword
  have hflag : q 156 ≤ 1 := by rw [hp.2.1]; split <;> omega
  have hm0 := Section413G1Denote.muxS_spec idx q 158 156 157 155 159
    (by decide) (by decide) (by decide) (by decide) hflag hqword
  have hmG : m 158 = headG f := by
    change srun idx q (Section413G1Denote.muxS 158 156 157 155 159) 158 = _
    rw [hm0, hp.2.1, hp.1, hp.2.2.1]
    by_cases hx : 9223372036854775808 ≤ headX f <;>
      simp [headG, hx]
  have hmword : ∀ j, m j < M := srun_lt_of_lt idx _ q hqword
  have hqE : q rE = e := by
    change srun idx r headAbsPreS rE = e
    rw [RegFrame.srun_frame idx rE headAbsPreS (by rfl) r, hE]
  have hmE : m rE = e := by
    rw [show m rE = q rE from Section413G1Denote.muxS_frame idx q
      158 156 157 155 159 rE (by simp [rE]) (by simp [rE]), hqE]
  have hi := headInc_run idx m (headG f) e hmG hmE
    (by
      unfold headG
      split
      · exact Nat.mod_lt _ (by decide)
      · exact Nat.mod_lt _ (by decide))
    (by rw [← hmE]; exact hmword rE)
  dsimp only at hi
  change out 161 = headDPos (headG f) e ∧
    out 163 = headDNeg (headG f) e ∧ out 158 = headG f ∧
    out rE = e at hi
  have hmF : m rF = f := by
    rw [show m rF = q rF from Section413G1Denote.muxS_frame idx q
      158 156 157 155 159 rF (by simp [rF]) (by simp [rF]), hp.2.2.2]
  have houtF : out rF = f := by
    rw [show out rF = m rF from
      RegFrame.srun_frame idx rF headIncS (by rfl) m, hmF]
  simpa [headDeltaS_decomp, srun_append, q, m, out] using
    ⟨hi.2.2.1, hi.1, hi.2.1, houtF, hi.2.2.2⟩

theorem headLatch_first_run (idx : Nat) (r : RegState) (g dp dn : Nat)
    (h140 : r 140 = 1) (hG : r 158 = g)
    (hDp : r 161 = dp) (hDn : r 163 = dn)
    (hword : ∀ j, r j < M) :
    let out := srun idx r headLatchS
    out rDp = dp ∧ out rDn = dn ∧ out rE = g ∧ out 140 = 1 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcoeff : 1 + (M - 1) = M := by decide
  have hDpM : dp % M = dp := by
    rw [← hDp]
    exact Nat.mod_eq_of_lt (hword 161)
  have hDnM : dn % M = dn := by
    rw [← hDn]
    exact Nat.mod_eq_of_lt (hword 163)
  have hGM : g % M = g := by
    rw [← hG]
    exact Nat.mod_eq_of_lt (hword 158)
  simp [headLatchS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rDp, rDn, rE,
    h140, hG, hDp, hDn, h1M, hcoeff, hDpM, hDnM, hGM]

theorem headRecip_first_run (c : Cfg) (idx : Nat) (r : RegState)
    (h140 : r 140 = 1) (hk : 0 < r rK) (hword : ∀ j, r j < M)
    (hWM : c.wScale < M) (hsum : r rDp + r rDn < M)
    (htvFit : r rTv + (r rDp + r rDn) < M)
    (hceilFit : c.wScale - 1 + r rK < M) :
    let out := srun idx r (headRecipS c)
    out 165 = r rDp + r rDn ∧
      out rTv = r rTv + (r rDp + r rDn) ∧
      out 167 = (c.wScale - 1 + r rK) / r rK ∧
      out 168 = c.wScale / r rK ∧
      out 169 = r rDp ∧ out 170 = r rDn := by
  have hk0 : r rK ≠ 0 := Nat.ne_of_gt hk
  have hdivM : (c.wScale - 1 + r rK) / r rK < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hceilFit
  have hfloorM : c.wScale / r rK < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hWM
  have hk0' : r 30 ≠ 0 := by simpa [rK] using hk0
  have hsum' : r 16 + r 17 < M := by simpa [rDp, rDn] using hsum
  have htvFit' : r 29 + (r 16 + r 17) < M := by
    simpa [rTv, rDp, rDn] using htvFit
  have hceilFit' : c.wScale - 1 + r 30 < M := by
    simpa [rK] using hceilFit
  have hdivM' : (c.wScale - 1 + r 30) / r 30 < M := by
    simpa [rK] using hdivM
  have hfloorM' : c.wScale / r 30 < M := by simpa [rK] using hfloorM
  simp [headRecipS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rDp, rDn, rTv, rK, h140]
  refine ⟨Nat.mod_eq_of_lt hsum', Nat.mod_eq_of_lt htvFit', ?_, ?_,
    Nat.mod_eq_of_lt (hword 16), Nat.mod_eq_of_lt (hword 17)⟩
  · simp [hk0', Nat.mod_eq_of_lt hceilFit', Nat.mod_eq_of_lt hdivM']
  · simp [hk0', Nat.mod_eq_of_lt hWM, Nat.mod_eq_of_lt hfloorM']

theorem headTail_first_run (c : Cfg) (idx : Nat) (r : RegState)
    (f k t t2 g dp dn : Nat)
    (hF : r rF = f) (hK : r rK = k) (hT : r rT = t)
    (hT2 : r rT2 = t2) (hG : r 158 = g)
    (hDp : r 161 = dp) (hDn : r 163 = dn) (h140 : r 140 = 1)
    (hword : ∀ j, r j < M) (hk : 0 < k) (hWM : c.wScale < M)
    (hsum : dp + dn < M) (htvFit : r rTv + (dp + dn) < M)
    (hceilFit : c.wScale - 1 + k < M) :
    let out := srun idx r (headTailS c)
    out rF = f ∧ out rK = k ∧ out rT = t ∧ out rT2 = t2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out rDp = dp ∧ out rDn = dn ∧ out rE = g ∧
      out rTv = r rTv + (dp + dn) ∧ out 165 = dp + dn ∧
      out 167 = (c.wScale - 1 + k) / k ∧
      out 168 = c.wScale / k ∧ out 169 = dp ∧ out 170 = dn ∧
      out 140 = 1 := by
  let l := srun idx r headLatchS
  let out := srun idx l (headRecipS c)
  have hl := headLatch_first_run idx r g dp dn h140 hG hDp hDn hword
  dsimp only at hl
  change l rDp = dp ∧ l rDn = dn ∧ l rE = g ∧ l 140 = 1 at hl
  rcases hl with ⟨hlDp, hlDn, hlE, hl140⟩
  have hlword : ∀ j, l j < M := srun_lt_of_lt idx _ r hword
  have lKeep (j : Nat) (hw : RegFrame.writes j headLatchS = false) :
      l j = r j := RegFrame.srun_frame idx j headLatchS hw r
  have hlK : l rK = k := by rw [lKeep rK (by rfl), hK]
  have hlTv : l rTv = r rTv := lKeep rTv (by rfl)
  have hr := headRecip_first_run c idx l hl140
    (by rw [hlK]; exact hk) hlword hWM
    (by rw [hlDp, hlDn]; exact hsum)
    (by rw [hlTv, hlDp, hlDn]; exact htvFit)
    (by rw [hlK]; exact hceilFit)
  dsimp only at hr
  change out 165 = l rDp + l rDn ∧
    out rTv = l rTv + (l rDp + l rDn) ∧
    out 167 = (c.wScale - 1 + l rK) / l rK ∧
    out 168 = c.wScale / l rK ∧ out 169 = l rDp ∧
    out 170 = l rDn at hr
  rcases hr with ⟨hrSum, hrTv, hrCeil, hrFloor, hrPos, hrNeg⟩
  have outKeep (j : Nat) (hw : RegFrame.writes j (headRecipS c) = false) :
      out j = l j := RegFrame.srun_frame idx j (headRecipS c) hw l
  have hall : out rF = f ∧ out rK = k ∧ out rT = t ∧
      out rT2 = t2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out rDp = dp ∧ out rDn = dn ∧
      out rE = g ∧ out rTv = r rTv + (dp + dn) ∧
      out 165 = dp + dn ∧ out 167 = (c.wScale - 1 + k) / k ∧
      out 168 = c.wScale / k ∧ out 169 = dp ∧ out 170 = dn ∧
      out 140 = 1 :=
    ⟨by rw [outKeep rF (by rfl), lKeep rF (by rfl), hF],
      by rw [outKeep rK (by rfl), hlK],
      by rw [outKeep rT (by rfl), lKeep rT (by rfl), hT],
      by rw [outKeep rT2 (by rfl), lKeep rT2 (by rfl), hT2],
      by rw [outKeep rViol (by rfl), lKeep rViol (by rfl)],
      by rw [outKeep rVSqrt (by rfl), lKeep rVSqrt (by rfl)],
      by rw [outKeep rDp (by rfl), hlDp],
      by rw [outKeep rDn (by rfl), hlDn],
      by rw [outKeep rE (by rfl), hlE],
      by rw [hrTv, hlTv, hlDp, hlDn],
      by rw [hrSum, hlDp, hlDn],
      by rw [hrCeil, hlK],
      by rw [hrFloor, hlK],
      by rw [hrPos, hlDp],
      by rw [hrNeg, hlDn],
      by rw [outKeep 140 (by rfl), hl140]⟩
  simpa [headTailS, srun_append, l, out] using hall

theorem headFront_first_noBump_run (c : Cfg) (idx : Nat) (r : RegState)
    (t t2 e : Nat) (h140 : r 140 = 1)
    (hT : r rT = t) (hT2 : r rT2 = t2) (hE : r rE = e)
    (hkFit : r rW + r rC < M) (hklt : r rW + r rC < t2)
    (hword : ∀ j, r j < M) :
    let f := (r rF + r 148) % M
    let k := r rW + r rC
    let out := srun idx r (headFrontS c)
    out rF = f ∧ out rK = k ∧ out rT = t ∧ out rT2 = t2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out 158 = headG f ∧ out 161 = headDPos (headG f) e ∧
      out 163 = headDNeg (headG f) e ∧ out rE = e ∧
      out 140 = 1 := by
  let f := (r rF + r 148) % M
  let k := r rW + r rC
  let fk := srun idx r headFKS
  let sq := srun idx fk headSqrtS
  let out := srun idx sq headDeltaS
  have hfk := headFK_first_run idx r h140 hkFit
  dsimp only at hfk
  change fk rF = f ∧ fk rK = k ∧ fk 140 = 1 at hfk
  rcases hfk with ⟨hfkF, hfkK, hfk140⟩
  have hfkword : ∀ j, fk j < M := srun_lt_of_lt idx _ r hword
  have fkKeep (j : Nat) (hw : RegFrame.writes j headFKS = false) :
      fk j = r j := RegFrame.srun_frame idx j headFKS hw r
  have hfkT : fk rT = t := by rw [fkKeep rT (by rfl), hT]
  have hfkT2 : fk rT2 = t2 := by rw [fkKeep rT2 (by rfl), hT2]
  have hs := headSqrt_noBump_run idx fk k t t2 hfk140 hfkK hfkT
    hfkT2 (by simpa [k] using hklt) hfkword
  dsimp only at hs
  change sq rT = t ∧ sq rT2 = t2 ∧ sq rViol = fk rViol ∧
    sq rVSqrt = fk rVSqrt ∧ sq 140 = 1 at hs
  rcases hs with ⟨hsT, hsT2, hsViol, hsVSqrt, hs140⟩
  have hsword : ∀ j, sq j < M := srun_lt_of_lt idx _ fk hfkword
  have sqKeep (j : Nat) (hw : RegFrame.writes j headSqrtS = false) :
      sq j = fk j := RegFrame.srun_frame idx j headSqrtS hw fk
  have hsF : sq rF = f := by rw [sqKeep rF (by rfl), hfkF]
  have hsK : sq rK = k := by rw [sqKeep rK (by rfl), hfkK]
  have hsE : sq rE = e := by
    rw [sqKeep rE (by rfl), fkKeep rE (by rfl), hE]
  have hd := headDelta_run idx sq f e hsF hsE hsword
  dsimp only at hd
  change out 158 = headG f ∧ out 161 = headDPos (headG f) e ∧
    out 163 = headDNeg (headG f) e ∧ out rF = f ∧ out rE = e at hd
  rcases hd with ⟨hdG, hdDp, hdDn, hdF, hdE⟩
  have outKeep (j : Nat) (hw : RegFrame.writes j headDeltaS = false) :
      out j = sq j := RegFrame.srun_frame idx j headDeltaS hw sq
  have hall : out rF = f ∧ out rK = k ∧ out rT = t ∧
      out rT2 = t2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out 158 = headG f ∧
      out 161 = headDPos (headG f) e ∧
      out 163 = headDNeg (headG f) e ∧ out rE = e ∧ out 140 = 1 :=
    ⟨hdF,
      by rw [outKeep rK (by rfl), hsK],
      by rw [outKeep rT (by rfl), hsT],
      by rw [outKeep rT2 (by rfl), hsT2],
      by rw [outKeep rViol (by rfl), hsViol, fkKeep rViol (by rfl)],
      by rw [outKeep rVSqrt (by rfl), hsVSqrt, fkKeep rVSqrt (by rfl)],
      hdG, hdDp, hdDn, hdE,
      by rw [outKeep 140 (by rfl), hs140]⟩
  simpa [headFrontS_decomp, srun_append, f, k, fk, sq, out] using hall

theorem headFront_first_bump_run (c : Cfg) (idx : Nat) (r : RegState)
    (t t2 e : Nat) (h140 : r 140 = 1)
    (hT : r rT = t) (hT2 : r rT2 = t2) (hE : r rE = e)
    (hkFit : r rW + r rC < M) (ht2k : t2 ≤ r rW + r rC)
    (hkclosed : r rW + r rC < t2 + (2 * (t + 1) + 1))
    (htFit : t + 1 < M) (hdoubleFit : 2 * (t + 1) + 1 < M)
    (ht2Fit : t2 + (2 * (t + 1) + 1) < M)
    (hword : ∀ j, r j < M) :
    let f := (r rF + r 148) % M
    let k := r rW + r rC
    let nt := t + 1
    let nt2 := t2 + (2 * (t + 1) + 1)
    let out := srun idx r (headFrontS c)
    out rF = f ∧ out rK = k ∧ out rT = nt ∧ out rT2 = nt2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out 158 = headG f ∧ out 161 = headDPos (headG f) e ∧
      out 163 = headDNeg (headG f) e ∧ out rE = e ∧
      out 140 = 1 := by
  let f := (r rF + r 148) % M
  let k := r rW + r rC
  let nt := t + 1
  let nt2 := t2 + (2 * (t + 1) + 1)
  let fk := srun idx r headFKS
  let sq := srun idx fk headSqrtS
  let out := srun idx sq headDeltaS
  have hfk := headFK_first_run idx r h140 hkFit
  dsimp only at hfk
  change fk rF = f ∧ fk rK = k ∧ fk 140 = 1 at hfk
  rcases hfk with ⟨hfkF, hfkK, hfk140⟩
  have hfkword : ∀ j, fk j < M := srun_lt_of_lt idx _ r hword
  have fkKeep (j : Nat) (hw : RegFrame.writes j headFKS = false) :
      fk j = r j := RegFrame.srun_frame idx j headFKS hw r
  have hfkT : fk rT = t := by rw [fkKeep rT (by rfl), hT]
  have hfkT2 : fk rT2 = t2 := by rw [fkKeep rT2 (by rfl), hT2]
  have hs := headSqrt_bump_run idx fk k t t2 hfk140 hfkK hfkT hfkT2
    (by simpa [k] using ht2k) (by simpa [k] using hkclosed)
    htFit hdoubleFit ht2Fit hfkword
  dsimp only at hs
  change sq rT = nt ∧ sq rT2 = nt2 ∧ sq rViol = fk rViol ∧
    sq rVSqrt = fk rVSqrt ∧ sq 140 = 1 at hs
  rcases hs with ⟨hsT, hsT2, hsViol, hsVSqrt, hs140⟩
  have hsword : ∀ j, sq j < M := srun_lt_of_lt idx _ fk hfkword
  have sqKeep (j : Nat) (hw : RegFrame.writes j headSqrtS = false) :
      sq j = fk j := RegFrame.srun_frame idx j headSqrtS hw fk
  have hsF : sq rF = f := by rw [sqKeep rF (by rfl), hfkF]
  have hsK : sq rK = k := by rw [sqKeep rK (by rfl), hfkK]
  have hsE : sq rE = e := by
    rw [sqKeep rE (by rfl), fkKeep rE (by rfl), hE]
  have hd := headDelta_run idx sq f e hsF hsE hsword
  dsimp only at hd
  change out 158 = headG f ∧ out 161 = headDPos (headG f) e ∧
    out 163 = headDNeg (headG f) e ∧ out rF = f ∧ out rE = e at hd
  rcases hd with ⟨hdG, hdDp, hdDn, hdF, hdE⟩
  have outKeep (j : Nat) (hw : RegFrame.writes j headDeltaS = false) :
      out j = sq j := RegFrame.srun_frame idx j headDeltaS hw sq
  have hall : out rF = f ∧ out rK = k ∧ out rT = nt ∧
      out rT2 = nt2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧ out 158 = headG f ∧
      out 161 = headDPos (headG f) e ∧
      out 163 = headDNeg (headG f) e ∧ out rE = e ∧ out 140 = 1 :=
    ⟨hdF,
      by rw [outKeep rK (by rfl), hsK],
      by rw [outKeep rT (by rfl), hsT],
      by rw [outKeep rT2 (by rfl), hsT2],
      by rw [outKeep rViol (by rfl), hsViol, fkKeep rViol (by rfl)],
      by rw [outKeep rVSqrt (by rfl), hsVSqrt, fkKeep rVSqrt (by rfl)],
      hdG, hdDp, hdDn, hdE,
      by rw [outKeep 140 (by rfl), hs140]⟩
  simpa [headFrontS_decomp, srun_append, f, k, nt, nt2, fk, sq, out] using hall

theorem headPost_first_from_front (c : Cfg) (idx : Nat) (r : RegState)
    (f k nt nt2 e : Nat)
    (hfront :
      let fr := srun idx r (headFrontS c)
      fr rF = f ∧ fr rK = k ∧ fr rT = nt ∧ fr rT2 = nt2 ∧
        fr rViol = r rViol ∧ fr rVSqrt = r rVSqrt ∧
        fr 158 = headG f ∧ fr 161 = headDPos (headG f) e ∧
        fr 163 = headDNeg (headG f) e ∧ fr rE = e ∧ fr 140 = 1)
    (hword : ∀ j, r j < M) (hk : 0 < k) (hWM : c.wScale < M)
    (hsum : headDPos (headG f) e + headDNeg (headG f) e < M)
    (htvFit : r rTv +
      (headDPos (headG f) e + headDNeg (headG f) e) < M)
    (hceilFit : c.wScale - 1 + k < M) :
    let out := srun idx r (headPostS c)
    out rF = f ∧ out rK = k ∧ out rT = nt ∧ out rT2 = nt2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out rDp = headDPos (headG f) e ∧
      out rDn = headDNeg (headG f) e ∧ out rE = headG f ∧
      out rTv = r rTv +
        (headDPos (headG f) e + headDNeg (headG f) e) ∧
      out 165 = headDPos (headG f) e + headDNeg (headG f) e ∧
      out 167 = (c.wScale - 1 + k) / k ∧
      out 168 = c.wScale / k ∧
      out 169 = headDPos (headG f) e ∧
      out 170 = headDNeg (headG f) e ∧ out 140 = 1 := by
  let fr := srun idx r (headFrontS c)
  let out := srun idx fr (headTailS c)
  dsimp only at hfront
  change fr rF = f ∧ fr rK = k ∧ fr rT = nt ∧ fr rT2 = nt2 ∧
    fr rViol = r rViol ∧ fr rVSqrt = r rVSqrt ∧
    fr 158 = headG f ∧ fr 161 = headDPos (headG f) e ∧
    fr 163 = headDNeg (headG f) e ∧ fr rE = e ∧ fr 140 = 1 at hfront
  rcases hfront with ⟨hfF, hfK, hfT, hfT2, hfViol, hfVSqrt,
    hfG, hfDp, hfDn, _hfE, hf140⟩
  have hfrword : ∀ j, fr j < M := srun_lt_of_lt idx _ r hword
  have hfrTv : fr rTv = r rTv :=
    RegFrame.srun_frame idx rTv (headFrontS c) (by rfl) r
  have ht := headTail_first_run c idx fr f k nt nt2 (headG f)
    (headDPos (headG f) e) (headDNeg (headG f) e)
    hfF hfK hfT hfT2 hfG hfDp hfDn hf140 hfrword hk hWM hsum
    (by rw [hfrTv]; exact htvFit) hceilFit
  dsimp only at ht
  change out rF = f ∧ out rK = k ∧ out rT = nt ∧ out rT2 = nt2 ∧
    out rViol = fr rViol ∧ out rVSqrt = fr rVSqrt ∧
    out rDp = headDPos (headG f) e ∧
    out rDn = headDNeg (headG f) e ∧ out rE = headG f ∧
    out rTv = fr rTv +
      (headDPos (headG f) e + headDNeg (headG f) e) ∧
    out 165 = headDPos (headG f) e + headDNeg (headG f) e ∧
    out 167 = (c.wScale - 1 + k) / k ∧ out 168 = c.wScale / k ∧
    out 169 = headDPos (headG f) e ∧
    out 170 = headDNeg (headG f) e ∧ out 140 = 1 at ht
  rcases ht with ⟨htF, htK, htT, htT2, htViol, htVSqrt, htDp, htDn,
    htE, htTv, htSum, htCeil, htFloor, htPos, htNeg, ht140⟩
  have hall : out rF = f ∧ out rK = k ∧ out rT = nt ∧
      out rT2 = nt2 ∧ out rViol = r rViol ∧
      out rVSqrt = r rVSqrt ∧
      out rDp = headDPos (headG f) e ∧
      out rDn = headDNeg (headG f) e ∧ out rE = headG f ∧
      out rTv = r rTv +
        (headDPos (headG f) e + headDNeg (headG f) e) ∧
      out 165 = headDPos (headG f) e + headDNeg (headG f) e ∧
      out 167 = (c.wScale - 1 + k) / k ∧ out 168 = c.wScale / k ∧
      out 169 = headDPos (headG f) e ∧
      out 170 = headDNeg (headG f) e ∧ out 140 = 1 :=
    ⟨htF, htK, htT, htT2,
      by rw [htViol, hfViol],
      by rw [htVSqrt, hfVSqrt],
      htDp, htDn, htE,
      by rw [htTv, hfrTv],
      htSum, htCeil, htFloor, htPos, htNeg, ht140⟩
  simpa [headPostS_tail_decomp, srun_append, fr, out] using hall

theorem headPost_first_noBump_run (c : Cfg) (idx : Nat) (r : RegState)
    (t t2 e : Nat) (h140 : r 140 = 1)
    (hT : r rT = t) (hT2 : r rT2 = t2) (hE : r rE = e)
    (hkFit : r rW + r rC < M) (hklt : r rW + r rC < t2)
    (hword : ∀ j, r j < M) (hk : 0 < r rW + r rC)
    (hWM : c.wScale < M)
    (hsum : headDPos (headG ((r rF + r 148) % M)) e +
      headDNeg (headG ((r rF + r 148) % M)) e < M)
    (htvFit : r rTv +
      (headDPos (headG ((r rF + r 148) % M)) e +
        headDNeg (headG ((r rF + r 148) % M)) e) < M)
    (hceilFit : c.wScale - 1 + (r rW + r rC) < M) :
    let f := (r rF + r 148) % M
    let k := r rW + r rC
    let out := srun idx r (headPostS c)
    out rF = f ∧ out rK = k ∧ out rT = t ∧ out rT2 = t2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out rDp = headDPos (headG f) e ∧ out rDn = headDNeg (headG f) e ∧
      out rE = headG f ∧
      out rTv = r rTv + (headDPos (headG f) e + headDNeg (headG f) e) ∧
      out 165 = headDPos (headG f) e + headDNeg (headG f) e ∧
      out 167 = (c.wScale - 1 + k) / k ∧ out 168 = c.wScale / k ∧
      out 169 = headDPos (headG f) e ∧
      out 170 = headDNeg (headG f) e ∧ out 140 = 1 := by
  apply headPost_first_from_front c idx r
    ((r rF + r 148) % M) (r rW + r rC) t t2 e
  · exact headFront_first_noBump_run c idx r t t2 e h140 hT hT2 hE
      hkFit hklt hword
  · exact hword
  · exact hk
  · exact hWM
  · exact hsum
  · exact htvFit
  · exact hceilFit

theorem headPost_first_bump_run (c : Cfg) (idx : Nat) (r : RegState)
    (t t2 e : Nat) (h140 : r 140 = 1)
    (hT : r rT = t) (hT2 : r rT2 = t2) (hE : r rE = e)
    (hkFit : r rW + r rC < M) (ht2k : t2 ≤ r rW + r rC)
    (hkclosed : r rW + r rC < t2 + (2 * (t + 1) + 1))
    (htFit : t + 1 < M) (hdoubleFit : 2 * (t + 1) + 1 < M)
    (ht2Fit : t2 + (2 * (t + 1) + 1) < M)
    (hword : ∀ j, r j < M) (hk : 0 < r rW + r rC)
    (hWM : c.wScale < M)
    (hsum : headDPos (headG ((r rF + r 148) % M)) e +
      headDNeg (headG ((r rF + r 148) % M)) e < M)
    (htvFit : r rTv +
      (headDPos (headG ((r rF + r 148) % M)) e +
        headDNeg (headG ((r rF + r 148) % M)) e) < M)
    (hceilFit : c.wScale - 1 + (r rW + r rC) < M) :
    let f := (r rF + r 148) % M
    let k := r rW + r rC
    let nt := t + 1
    let nt2 := t2 + (2 * (t + 1) + 1)
    let out := srun idx r (headPostS c)
    out rF = f ∧ out rK = k ∧ out rT = nt ∧ out rT2 = nt2 ∧
      out rViol = r rViol ∧ out rVSqrt = r rVSqrt ∧
      out rDp = headDPos (headG f) e ∧ out rDn = headDNeg (headG f) e ∧
      out rE = headG f ∧
      out rTv = r rTv + (headDPos (headG f) e + headDNeg (headG f) e) ∧
      out 165 = headDPos (headG f) e + headDNeg (headG f) e ∧
      out 167 = (c.wScale - 1 + k) / k ∧ out 168 = c.wScale / k ∧
      out 169 = headDPos (headG f) e ∧
      out 170 = headDNeg (headG f) e ∧ out 140 = 1 := by
  apply headPost_first_from_front c idx r
    ((r rF + r 148) % M) (r rW + r rC)
    (t + 1) (t2 + (2 * (t + 1) + 1)) e
  · exact headFront_first_bump_run c idx r t t2 e h140 hT hT2 hE
      hkFit ht2k hkclosed htFit hdoubleFit ht2Fit hword
  · exact hword
  · exact hk
  · exact hWM
  · exact hsum
  · exact htvFit
  · exact hceilFit

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

structure FirstHeadSpec (c : Cfg) (before after : AState)
    (nextT nextT2 : Nat) : Prop where
  arr : after.arr = fun j =>
    if j = before.regs rC + c.winBase then 0 else before.arr j
  round0 : after.regs 140 = 1
  last : after.regs 141 = 0
  bisect : after.regs 142 = 0
  f : after.regs rF =
    (before.regs rF + before.arr (before.regs rC + c.winBase)) % M
  k : after.regs rK = before.regs rW + before.regs rC
  t : after.regs rT = nextT
  t2 : after.regs rT2 = nextT2
  viol : after.regs rViol = before.regs rViol
  vSqrt : after.regs rVSqrt = before.regs rVSqrt
  dPos : after.regs rDp = headDPos
    (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE)
  dNeg : after.regs rDn = headDNeg
    (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE)
  e : after.regs rE = headG
    ((before.regs rF + before.arr (before.regs rC + c.winBase)) % M)
  tv : after.regs rTv = before.regs rTv +
    (headDPos (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE) +
     headDNeg (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE))
  sum : after.regs 165 =
    headDPos (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE) +
    headDNeg (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE)
  ceil : after.regs 167 =
    (c.wScale - 1 + (before.regs rW + before.regs rC)) /
      (before.regs rW + before.regs rC)
  floor : after.regs 168 = c.wScale /
    (before.regs rW + before.regs rC)
  posGate : after.regs 169 = headDPos
    (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE)
  negGate : after.regs 170 = headDNeg
    (headG ((before.regs rF +
      before.arr (before.regs rC + c.winBase)) % M)) (before.regs rE)
  low : after.regs rSl = before.regs rSl
  high : after.regs rSh = before.regs rSh
  cell : after.regs rC = before.regs rC
  round : after.regs rKr = before.regs rKr

set_option maxRecDepth 2048 in
theorem accHead_first_run (c : Cfg) (idx : Nat) (st : AState)
    (hkr : st.regs rKr = 0) (hbsPos : 0 < c.bsSteps)
    (hbsM : c.bsSteps < M) (hgate : st.regs 43 = 1)
    (hzero : st.regs rZero = 0)
    (haddr : st.regs rC + c.winBase < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rW + st.regs rC)
    (hkFit : st.regs rW + st.regs rC < M)
    (hkclosed : st.regs rW + st.regs rC <
      st.regs rT2 + (2 * (st.regs rT + 1) + 1))
    (htFit : st.regs rT + 1 < M)
    (hdoubleFit : 2 * (st.regs rT + 1) + 1 < M)
    (ht2Fit : st.regs rT2 + (2 * (st.regs rT + 1) + 1) < M)
    (hWM : c.wScale < M)
    (hsum :
      headDPos (headG ((st.regs rF +
        st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) +
      headDNeg (headG ((st.regs rF +
        st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) < M)
    (htvFit : st.regs rTv +
      (headDPos (headG ((st.regs rF +
        st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) +
       headDNeg (headG ((st.regs rF +
        st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE)) < M)
    (hceilFit : c.wScale - 1 +
      (st.regs rW + st.regs rC) < M) :
    FirstHeadSpec c st (arun idx st c.accHead)
      (if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT else st.regs rT + 1)
      (if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT2
       else st.regs rT2 + (2 * (st.regs rT + 1) + 1)) := by
  let pre := srun idx st.regs (headPreS c)
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  let post := srun idx loaded (headPostS c)
  let out : AState := ⟨post, cleared⟩
  let addr := st.regs rC + c.winBase
  let f := (st.regs rF + st.arr addr) % M
  let k := st.regs rW + st.regs rC
  let t := st.regs rT
  let t2 := st.regs rT2
  let e := st.regs rE
  let dp := headDPos (headG f) e
  let dn := headDNeg (headG f) e
  let nt := if k < t2 then t else t + 1
  let nt2 := if k < t2 then t2 else t2 + (2 * (t + 1) + 1)
  have ha := accHead_arun c idx st
  dsimp only at ha
  change arun idx st c.accHead = out at ha
  have hp := headPre_first_run c idx st.regs hkr hbsPos hbsM hgate haddr
  dsimp only at hp
  change pre 140 = 1 ∧ pre 141 = 0 ∧ pre 142 = 0 ∧ pre 144 = addr at hp
  rcases hp with ⟨hp140, hp141, hp142, hp144⟩
  have preKeep (j : Nat) (hw : RegFrame.writes j (headPreS c) = false) :
      pre j = st.regs j := RegFrame.srun_frame idx j (headPreS c) hw st.regs
  have hpreword : ∀ j, pre j < M := srun_lt_of_lt idx _ st.regs hword
  have loadedKeep (j : Nat) (hj : j ≠ 148) : loaded j = pre j := by
    simp [loaded, RegState.set, hj]
  have loadedToBefore (j : Nat) (hj148 : j ≠ 148)
      (hw : RegFrame.writes j (headPreS c) = false) :
      loaded j = st.regs j := by rw [loadedKeep j hj148, preKeep j hw]
  have hloaded148 : loaded 148 = st.arr addr := by
    simp [loaded, RegState.set, hp144]
  have hloaded144 : loaded 144 = addr := by
    rw [loadedKeep 144 (by decide), hp144]
  have hloadedZero : loaded rZero = 0 := by
    rw [loadedToBefore rZero (by simp [rZero]) (by rfl), hzero]
  have hloadedword : ∀ j, loaded j < M := by
    intro j
    by_cases hj : j = 148
    · subst j
      rw [hloaded148]
      exact harrword addr
    · rw [loadedKeep j hj]
      exact hpreword j
  have hcleared : cleared = fun j => if j = addr then 0 else st.arr j := by
    funext j
    simp only [cleared, hloaded144, hloadedZero]
  have hloaded140 : loaded 140 = 1 := by
    rw [loadedKeep 140 (by decide), hp140]
  have hloadedF : loaded rF = st.regs rF :=
    loadedToBefore rF (by simp [rF]) (by rfl)
  have hloadedW : loaded rW = st.regs rW :=
    loadedToBefore rW (by simp [rW]) (by rfl)
  have hloadedC : loaded rC = st.regs rC :=
    loadedToBefore rC (by simp [rC]) (by rfl)
  have hloadedT : loaded rT = t := by
    rw [loadedToBefore rT (by simp [rT]) (by rfl)]
  have hloadedT2 : loaded rT2 = t2 := by
    rw [loadedToBefore rT2 (by simp [rT2]) (by rfl)]
  have hloadedE : loaded rE = e := by
    rw [loadedToBefore rE (by simp [rE]) (by rfl)]
  have hloadedTv : loaded rTv = st.regs rTv :=
    loadedToBefore rTv (by simp [rTv]) (by rfl)
  have hloadedViol : loaded rViol = st.regs rViol :=
    loadedToBefore rViol (by simp [rViol]) (by rfl)
  have hloadedVSqrt : loaded rVSqrt = st.regs rVSqrt :=
    loadedToBefore rVSqrt (by simp [rVSqrt]) (by rfl)
  have hpost :
      post rF = f ∧ post rK = k ∧ post rT = nt ∧ post rT2 = nt2 ∧
      post rViol = loaded rViol ∧ post rVSqrt = loaded rVSqrt ∧
      post rDp = dp ∧ post rDn = dn ∧ post rE = headG f ∧
      post rTv = loaded rTv + (dp + dn) ∧ post 165 = dp + dn ∧
      post 167 = (c.wScale - 1 + k) / k ∧
      post 168 = c.wScale / k ∧ post 169 = dp ∧ post 170 = dn ∧
      post 140 = 1 := by
    by_cases hlt : k < t2
    · have h := headPost_first_noBump_run c idx loaded t t2 e hloaded140
        hloadedT hloadedT2 hloadedE
        (by simpa [k, hloadedW, hloadedC] using hkFit)
        (by rw [hloadedW, hloadedC]; simpa [k] using hlt) hloadedword
        (by rw [hloadedW, hloadedC]; simpa [k] using hk) hWM
        (by simpa [f, e, dp, dn, hloadedF, hloaded148] using hsum)
        (by simpa [f, e, dp, dn, hloadedTv, hloadedF, hloaded148] using htvFit)
        (by simpa [k, hloadedW, hloadedC] using hceilFit)
      dsimp only at h
      simpa [f, k, dp, dn, nt, nt2, hlt, hloadedF, hloaded148,
        hloadedW, hloadedC] using h
    · have ht2k : t2 ≤ k := Nat.le_of_not_gt hlt
      have h := headPost_first_bump_run c idx loaded t t2 e hloaded140
        hloadedT hloadedT2 hloadedE
        (by simpa [k, hloadedW, hloadedC] using hkFit)
        (by rw [hloadedW, hloadedC]; simpa [k] using ht2k)
        (by rw [hloadedW, hloadedC]; simpa [k, t, t2] using hkclosed)
        (by simpa [t] using htFit) (by simpa [t] using hdoubleFit)
        (by simpa [t, t2] using ht2Fit) hloadedword
        (by rw [hloadedW, hloadedC]; simpa [k] using hk) hWM
        (by simpa [f, e, dp, dn, hloadedF, hloaded148] using hsum)
        (by simpa [f, e, dp, dn, hloadedTv, hloadedF, hloaded148] using htvFit)
        (by simpa [k, hloadedW, hloadedC] using hceilFit)
      dsimp only at h
      simpa [f, k, dp, dn, nt, nt2, hlt, hloadedF, hloaded148,
        hloadedW, hloadedC] using h
  rcases hpost with ⟨hPF, hPK, hPT, hPT2, hPV, hPVS, hPDp, hPDn,
    hPE, hPTv, hPSum, hPCeil, hPFloor, hPPos, hPNeg, hP140⟩
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
      sum := ?_
      ceil := ?_
      floor := ?_
      posGate := ?_
      negGate := ?_
      low := ?_
      high := ?_
      cell := ?_
      round := ?_ }
  · change post 141 = 0
    rw [postKeep 141 (by rfl), loadedKeep 141 (by decide), hp141]
  · change post 142 = 0
    rw [postKeep 142 (by rfl), loadedKeep 142 (by decide), hp142]
  · exact hPF
  · exact hPK
  · simpa [nt, k, t, t2] using hPT
  · simpa [nt2, k, t, t2] using hPT2
  · change post rViol = st.regs rViol
    rw [hPV, hloadedViol]
  · change post rVSqrt = st.regs rVSqrt
    rw [hPVS, hloadedVSqrt]
  · exact hPDp
  · exact hPDn
  · exact hPE
  · change post rTv = st.regs rTv + (dp + dn)
    rw [hPTv, hloadedTv]
  · exact hPSum
  · exact hPCeil
  · exact hPFloor
  · exact hPPos
  · exact hPNeg
  · change post rSl = st.regs rSl
    rw [postKeep rSl (by rfl),
      loadedToBefore rSl (by simp [rSl]) (by rfl)]
  · change post rSh = st.regs rSh
    rw [postKeep rSh (by rfl),
      loadedToBefore rSh (by simp [rSh]) (by rfl)]
  · change post rC = st.regs rC
    rw [postKeep rC (by rfl), hloadedC]
  · change post rKr = st.regs rKr
    rw [postKeep rKr (by rfl),
      loadedToBefore rKr (by simp [rKr]) (by rfl)]

structure SinkClearSpec (c : Cfg) (before after : AState) : Prop where
  sink_zero : after.arr c.sink = 0
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j

theorem SinkClearSpec.arr_eq (h : SinkClearSpec c before after)
    (hsink0 : before.arr c.sink = 0) : after.arr = before.arr := by
  funext j
  by_cases hj : j = c.sink
  · rw [hj, h.sink_zero, hsink0]
  · exact h.live j hj

structure MiddleHeadSpec (c : Cfg) (before after : AState) : Prop where
  arr : SinkClearSpec c before after
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
    (hword : ∀ j, st.regs j < M)
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
  have hcleared : SinkClearSpec c st ⟨post, cleared⟩ := by
    constructor
    · simp only [cleared, hloaded144, hloadedZero]
      simp
    · intro j hj
      simp only [cleared, hloaded144, hloadedZero]
      rw [if_neg hj]
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

structure LastHeadSpec (c : Cfg) (before after : AState) : Prop where
  arr : SinkClearSpec c before after
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
  sum : after.regs 165 = before.regs rDp + before.regs rDn
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
    (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    LastHeadSpec c st (arun idx st c.accHead) := by
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
  have hcleared : SinkClearSpec c st ⟨post, cleared⟩ := by
    constructor
    · simp only [cleared, hloaded144, hloadedZero]
      simp
    · intro j hj
      simp only [cleared, hloaded144, hloadedZero]
      rw [if_neg hj]
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
    hPE, hPTv, hPSum, _, _, hPPos, hPNeg, hP140⟩
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
      sum := ?_
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
  · change post 165 = st.regs rDp + st.regs rDn
    rw [hPSum, hloadedDp, hloadedDn]
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
