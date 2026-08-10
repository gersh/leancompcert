import LeanCompCert.Ports.CDEMAbelHead
import LeanCompCert.Verified.ArrayRegFrame

namespace LeanCompCert.Ports.CDEMAbelBody

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection

theorem wide_lt_of_word (r : RegState) (lo hi : Nat)
    (hword : ∀ j, r j < M) :
    AddWide.wval (r lo, r hi) < AddWide.B128 := by
  apply AddWide.wval_lt
  constructor
  · rw [← AddWidePort.M_eq_B64]
    exact hword lo
  · rw [← AddWidePort.M_eq_B64]
    exact hword hi

structure MiddleBodySpec (c : Cfg) (k : Nat) (p : Bracket)
    (before after : AState) : Prop where
  arr : after.arr = before.arr
  low : after.regs rSl = (step c.wScale k p).lo
  high : after.regs rSh = (step c.wScale k p).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + before.regs 43
  cell : after.regs rC = before.regs rC

theorem accBody_middle_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : MiddleHeadSpec c st (arun idx st c.accHead))
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hkrFit : st.regs rKr + st.regs 43 < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    MiddleBodySpec c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩ st
      (arun idx st c.accBody) := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have hh' : MiddleHeadSpec c st h := by simpa [h] using hh
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have harrH : ∀ j, h.arr j < M :=
    (arun_word idx c.accHead st hword harrword).2
  have headKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      h.regs j = st.regs j := by
    simpa [h] using LeanCompCert.Verified.ArrayRegFrame.arun_frame
      idx j c.accHead hw st
  have hpExact := accProd_run_exact c idx h hwordH
    (by simpa [hh'.posGate] using wide_lt_of_word h.regs rUpLo rUpHi hwordH)
    (by simpa [hh'.negGate] using wide_lt_of_word h.regs rUnLo rUnHi hwordH)
  dsimp only at hpExact
  change AddWide.wval (p.regs rUpLo, p.regs rUpHi) =
      AddWide.wval (h.regs rUpLo, h.regs rUpHi) +
        h.regs 169 * h.regs 167 ∧
    AddWide.wval (p.regs rUnLo, p.regs rUnHi) =
      AddWide.wval (h.regs rUnLo, h.regs rUnHi) +
        h.regs 170 * h.regs 168 ∧ p.arr = h.arr at hpExact
  have hpMod := accProd_run_mod c idx h hwordH
  dsimp only at hpMod
  change AddWide.wval (p.regs rUpLo, p.regs rUpHi) = _ ∧
    AddWide.wval (p.regs rUnLo, p.regs rUnHi) = _ ∧
    p.arr = h.arr ∧ _ at hpMod
  have prodKeep (j : Nat) (h171 : j ≠ 171) (h172 : j ≠ 172)
      (h173 : j ≠ 173) (h174 : j ≠ 174)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hupl : j ≠ rUpLo) (huph : j ≠ rUpHi)
      (hunl : j ≠ rUnLo) (hunh : j ≠ rUnHi) (h188 : j ≠ 188) :
      p.regs j = h.regs j :=
    hpMod.2.2.2 j h171 h172 h173 h174 hjs hupl huph hunl hunh h188
  have hwordP : ∀ j, p.regs j < M :=
    (arun_word idx c.accProd h hwordH harrH).1
  have hp140 : p.regs 140 = 0 := by
    rw [prodKeep 140 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.round0]
  have hp141 : p.regs 141 = 0 := by
    rw [prodKeep 141 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.last]
  have hp142 : p.regs 142 = 1 := by
    rw [prodKeep 142 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.bisect]
  have hpLo : p.regs rSl = st.regs rSl := by
    rw [prodKeep rSl (by simp [rSl]) (by simp [rSl]) (by simp [rSl])
      (by simp [rSl]) (by simp [rSl, Section413G1Denote.NotIn8])
      (by simp [rSl, rUpLo]) (by simp [rSl, rUpHi])
      (by simp [rSl, rUnLo]) (by simp [rSl, rUnHi]) (by simp [rSl]),
      hh'.low]
  have hpHi : p.regs rSh = st.regs rSh := by
    rw [prodKeep rSh (by simp [rSh]) (by simp [rSh]) (by simp [rSh])
      (by simp [rSh]) (by simp [rSh, Section413G1Denote.NotIn8])
      (by simp [rSh, rUpLo]) (by simp [rSh, rUpHi])
      (by simp [rSh, rUnLo]) (by simp [rSh, rUnHi]) (by simp [rSh]),
      hh'.high]
  have hpK : p.regs rK = st.regs rK := by
    rw [prodKeep rK (by simp [rK]) (by simp [rK]) (by simp [rK])
      (by simp [rK]) (by simp [rK, Section413G1Denote.NotIn8])
      (by simp [rK, rUpLo]) (by simp [rK, rUpHi])
      (by simp [rK, rUnLo]) (by simp [rK, rUnHi]) (by simp [rK]), hh'.k]
  have hpKr : p.regs rKr = st.regs rKr := by
    rw [prodKeep rKr (by simp [rKr]) (by simp [rKr]) (by simp [rKr])
      (by simp [rKr]) (by simp [rKr, Section413G1Denote.NotIn8])
      (by simp [rKr, rUpLo]) (by simp [rKr, rUpHi])
      (by simp [rKr, rUnLo]) (by simp [rKr, rUnHi]) (by simp [rKr]),
      hh'.round]
  have hp43 : p.regs 43 = st.regs 43 := by
    rw [prodKeep 43 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      headKeep 43 (by rfl)]
  have hb := accBisect_middle_run c idx p
    (st.regs rSl) (st.regs rSh) (st.regs rK)
    hp140 hp142 hp141 hpLo hpHi hpK hlohi hhiM hfit haLe
    (by rw [hpKr, hp43]; exact hkrFit) hwordP
  have hb' : MiddleBisectSpec c (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ p out := by simpa [out] using hb
  have hbU := accBisect_u_frame c idx p
  have hpToSt (j : Nat) (h171 : j ≠ 171) (h172 : j ≠ 172)
      (h173 : j ≠ 173) (h174 : j ≠ 174)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hupl : j ≠ rUpLo) (huph : j ≠ rUpHi)
      (hunl : j ≠ rUnLo) (hunh : j ≠ rUnHi) (h188 : j ≠ 188)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      p.regs j = st.regs j := by
    rw [prodKeep j h171 h172 h173 h174 hjs hupl huph hunl hunh h188,
      headKeep j hw]
  have hall : MiddleBodySpec c (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ st out :=
    { arr := by rw [hb'.arr, hpExact.2.2, hh'.arr]
      low := hb'.low
      high := hb'.high
      uPos := by
        rw [hbU.1, hbU.2.1, hpExact.1,
          hh'.posGate, Nat.zero_mul, Nat.add_zero,
          headKeep rUpLo (by rfl), headKeep rUpHi (by rfl)]
      uNeg := by
        rw [hbU.2.2.1, hbU.2.2.2, hpExact.2.1,
          hh'.negGate, Nat.zero_mul, Nat.add_zero,
          headKeep rUnLo (by rfl), headKeep rUnHi (by rfl)]
      viol := by
        rw [hb'.viol]
        rw [prodKeep rViol (by simp [rViol]) (by simp [rViol])
          (by simp [rViol]) (by simp [rViol])
          (by simp [rViol, Section413G1Denote.NotIn8])
          (by simp [rViol, rUpLo]) (by simp [rViol, rUpHi])
          (by simp [rViol, rUnLo]) (by simp [rViol, rUnHi])
          (by simp [rViol]), hh'.viol]
      vDiv := by
        rw [hb'.vDiv]
        exact hpToSt rVDiv (by simp [rVDiv]) (by simp [rVDiv])
          (by simp [rVDiv]) (by simp [rVDiv])
          (by simp [rVDiv, Section413G1Denote.NotIn8])
          (by simp [rVDiv, rUpLo]) (by simp [rVDiv, rUpHi])
          (by simp [rVDiv, rUnLo]) (by simp [rVDiv, rUnHi])
          (by simp [rVDiv]) (by rfl)
      vBisect := by
        rw [hb'.vBisect]
        exact hpToSt rVBisect (by simp [rVBisect]) (by simp [rVBisect])
          (by simp [rVBisect]) (by simp [rVBisect])
          (by simp [rVBisect, Section413G1Denote.NotIn8])
          (by simp [rVBisect, rUpLo]) (by simp [rVBisect, rUpHi])
          (by simp [rVBisect, rUnLo]) (by simp [rVBisect, rUnHi])
          (by simp [rVBisect]) (by rfl)
      v := by
        rw [hb'.v]
        have hlo : p.regs rVLo = st.regs rVLo :=
          hpToSt rVLo (by simp [rVLo]) (by simp [rVLo])
            (by simp [rVLo]) (by simp [rVLo])
            (by simp [rVLo, Section413G1Denote.NotIn8])
            (by simp [rVLo, rUpLo]) (by simp [rVLo, rUpHi])
            (by simp [rVLo, rUnLo]) (by simp [rVLo, rUnHi])
            (by simp [rVLo]) (by rfl)
        have hhi : p.regs rVHi = st.regs rVHi :=
          hpToSt rVHi (by simp [rVHi]) (by simp [rVHi])
            (by simp [rVHi]) (by simp [rVHi])
            (by simp [rVHi, Section413G1Denote.NotIn8])
            (by simp [rVHi, rUpLo]) (by simp [rVHi, rUpHi])
            (by simp [rVHi, rUnLo]) (by simp [rVHi, rUnHi])
            (by simp [rVHi]) (by rfl)
        rw [hlo, hhi]
      round := by rw [hb'.round, hpKr, hp43]
      cell := by
        rw [hb'.cell]
        exact hpToSt rC (by simp [rC]) (by simp [rC]) (by simp [rC])
          (by simp [rC]) (by simp [rC, Section413G1Denote.NotIn8])
          (by simp [rC, rUpLo]) (by simp [rC, rUpHi])
          (by simp [rC, rUnLo]) (by simp [rC, rUnHi])
          (by simp [rC]) (by rfl) }
  simpa [Cfg.accBody, arun_append, h, p, out] using hall

theorem accBody_middle_run (c : Cfg) (idx : Nat) (st : AState)
    (hkr0 : st.regs rKr ≠ 0) (hkrLast : st.regs rKr ≠ c.bsSteps)
    (hgate : st.regs 43 = 1) (hzero : st.regs rZero = 0)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsink0 : st.arr c.sink = 0) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M)
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hkrFit : st.regs rKr + st.regs 43 < M) :
    MiddleBodySpec c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩ st
      (arun idx st c.accBody) := by
  have hh := accHead_middle_run c idx st hkr0 hkrLast hgate hzero
    hbsM hsinkM hsink0 hword harrword hk hWM hsum hceilFit
  exact accBody_middle_of_head c idx st hh hlohi hhiM hfit haLe
    hkrFit hword harrword

end LeanCompCert.Ports.CDEMAbelBody
