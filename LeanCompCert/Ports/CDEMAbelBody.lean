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

structure ZeroProdSpec (before after : AState) : Prop where
  arr : after.arr = before.arr
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  frame : ∀ j, j ≠ 171 → j ≠ 172 → j ≠ 173 → j ≠ 174 →
    Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 →
    j ≠ rUpLo → j ≠ rUpHi → j ≠ rUnLo → j ≠ rUnHi →
    j ≠ 188 → after.regs j = before.regs j

structure ExactProdSpec (before after : AState) : Prop where
  arr : after.arr = before.arr
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi) +
      before.regs 169 * before.regs 167
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi) +
      before.regs 170 * before.regs 168
  frame : ∀ j, j ≠ 171 → j ≠ 172 → j ≠ 173 → j ≠ 174 →
    Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 →
    j ≠ rUpLo → j ≠ rUpHi → j ≠ rUnLo → j ≠ rUnHi →
    j ≠ 188 → after.regs j = before.regs j

theorem accProd_exact_frame_run (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M)
    (hfitPos : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
      st.regs 169 * st.regs 167 < AddWide.B128)
    (hfitNeg : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
      st.regs 170 * st.regs 168 < AddWide.B128) :
    ExactProdSpec st (arun idx st c.accProd) := by
  have he := accProd_run_exact c idx st hword hfitPos hfitNeg
  have hm := accProd_run_mod c idx st hword
  dsimp only at he hm
  exact
    { arr := he.2.2
      uPos := he.1
      uNeg := he.2.1
      frame := hm.2.2.2 }

theorem accProd_zero_run (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) (hpos : st.regs 169 = 0)
    (hneg : st.regs 170 = 0) :
    ZeroProdSpec st (arun idx st c.accProd) := by
  let out := arun idx st c.accProd
  have he := accProd_run_exact c idx st hword
    (by simpa [hpos] using wide_lt_of_word st.regs rUpLo rUpHi hword)
    (by simpa [hneg] using wide_lt_of_word st.regs rUnLo rUnHi hword)
  have hm := accProd_run_mod c idx st hword
  dsimp only at he hm
  change AddWide.wval (out.regs rUpLo, out.regs rUpHi) = _ ∧
    AddWide.wval (out.regs rUnLo, out.regs rUnHi) = _ ∧
    out.arr = st.arr at he
  change _ ∧ _ ∧ out.arr = st.arr ∧ _ at hm
  exact
    { arr := he.2.2
      uPos := by simpa [hpos] using he.1
      uNeg := by simpa [hneg] using he.2.1
      frame := hm.2.2.2 }

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

structure MiddleBodyLiveSpec (c : Cfg) (k : Nat) (p : Bracket)
    (before after : AState) : Prop where
  arr : SinkClearSpec c before after
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

theorem accBody_middle_live_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : MiddleHeadSpec c st (arun idx st c.accHead))
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hkrFit : st.regs rKr + st.regs 43 < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    MiddleBodyLiveSpec c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩ st
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
  have hall : MiddleBodyLiveSpec c (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ st out :=
    { arr := by
        constructor
        · rw [hb'.arr, hpExact.2.2]
          exact hh'.arr.sink_zero
        · intro j hj
          rw [hb'.arr, hpExact.2.2]
          exact hh'.arr.live j hj
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

theorem accBody_middle_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : MiddleHeadSpec c st (arun idx st c.accHead))
    (hsink0 : st.arr c.sink = 0)
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hkrFit : st.regs rKr + st.regs 43 < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    MiddleBodySpec c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩ st
      (arun idx st c.accBody) := by
  have h := accBody_middle_live_of_head c idx st hh hlohi hhiM hfit haLe
    hkrFit hword harrword
  exact
    { arr := h.arr.arr_eq hsink0
      low := h.low
      high := h.high
      uPos := h.uPos
      uNeg := h.uNeg
      viol := h.viol
      vDiv := h.vDiv
      vBisect := h.vBisect
      v := h.v
      round := h.round
      cell := h.cell }

theorem arun_accBody_eq_parts (c : Cfg) (idx : Nat) (st : AState) :
    arun idx st c.accBody =
      arun idx (arun idx (arun idx st c.accHead) c.accProd) c.accBisect := by
  rw [Cfg.accBody, arun_append, arun_append]

set_option maxHeartbeats 2000000 in
/- Registers carrying the floor-convolution stream are untouched by the
product and bisection suffixes.  Thus any head phase which preserves them
also preserves them through the complete accumulator body. -/
theorem accBody_stream_frame_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hf : (arun idx st c.accHead).regs rF = st.regs rF)
    (ht : (arun idx st c.accHead).regs rT = st.regs rT)
    (ht2 : (arun idx st c.accHead).regs rT2 = st.regs rT2)
    (he : (arun idx st c.accHead).regs rE = st.regs rE)
    (htv : (arun idx st c.accHead).regs rTv = st.regs rTv) :
    let out := arun idx st c.accBody
    out.regs rF = st.regs rF ∧ out.regs rT = st.regs rT ∧
      out.regs rT2 = st.regs rT2 ∧ out.regs rE = st.regs rE ∧
      out.regs rTv = st.regs rTv := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have prodFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.accProd = false) :
      p.regs j = h.regs j :=
    ArrayRegFrame.arun_frame idx j c.accProd hw h
  have bisectFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.accBisect = false) :
      out.regs j = p.regs j :=
    ArrayRegFrame.arun_frame idx j c.accBisect hw p
  have hall : out.regs rF = st.regs rF ∧ out.regs rT = st.regs rT ∧
      out.regs rT2 = st.regs rT2 ∧ out.regs rE = st.regs rE ∧
      out.regs rTv = st.regs rTv := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [bisectFrame rF (by rfl), prodFrame rF (by rfl)]
      simpa [h] using hf
    · rw [bisectFrame rT (by rfl), prodFrame rT (by rfl)]
      simpa [h] using ht
    · rw [bisectFrame rT2 (by rfl), prodFrame rT2 (by rfl)]
      simpa [h] using ht2
    · rw [bisectFrame rE (by rfl), prodFrame rE (by rfl)]
      simpa [h] using he
    · rw [bisectFrame rTv (by rfl), prodFrame rTv (by rfl)]
      simpa [h] using htv
  rw [arun_accBody_eq_parts]
  simpa [h, p, out] using hall

theorem accBody_sink_clear_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : SinkClearSpec c st (arun idx st c.accHead))
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    SinkClearSpec c st (arun idx st c.accBody) := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have hp := accProd_run_mod c idx h hwordH
  dsimp only at hp
  have hpArr : p.arr = h.arr := by simpa [p] using hp.2.2.1
  have hb := accBisect_arun c idx p
  have hbArr : out.arr = p.arr := by simpa [out] using congrArg AState.arr hb
  have houtArr : out.arr = h.arr := hbArr.trans hpArr
  have hh' : SinkClearSpec c st h := by simpa [h] using hh
  have hall : SinkClearSpec c st out :=
    { sink_zero := by rw [houtArr]; exact hh'.sink_zero
      live := by
        intro j hj
        rw [houtArr]
        exact hh'.live j hj }
  simpa [arun_accBody_eq_parts, h, p, out] using hall

set_option maxHeartbeats 2000000 in
theorem accBody_latch_of_head_values (c : Cfg) (idx : Nat) (st : AState)
    (hkey : (arun idx st c.accHead).regs rK = st.regs rK)
    (hdp : (arun idx st c.accHead).regs rDp = st.regs rDp)
    (hdn : (arun idx st c.accHead).regs rDn = st.regs rDn)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    let out := arun idx
      (arun idx (arun idx st c.accHead) c.accProd) c.accBisect
    out.regs rK = st.regs rK ∧
      out.regs rDp = st.regs rDp ∧
      out.regs rDn = st.regs rDn ∧
      out.regs 43 = st.regs 43 ∧
      out.regs rZero = st.regs rZero := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have headKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      h.regs j = st.regs j := by
    simpa [h] using LeanCompCert.Verified.ArrayRegFrame.arun_frame
      idx j c.accHead hw st
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have hp := accProd_run_mod c idx h hwordH
  dsimp only at hp
  change _ ∧ _ ∧ _ ∧ (∀ j, j ≠ 171 → j ≠ 172 → j ≠ 173 →
    j ≠ 174 → Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 →
    j ≠ rUpLo → j ≠ rUpHi → j ≠ rUnLo → j ≠ rUnHi → j ≠ 188 →
    p.regs j = h.regs j) at hp
  have prodKeep := hp.2.2.2
  have hb := accBisect_latch_frame c idx p
  dsimp only at hb
  change out.regs rK = p.regs rK ∧ out.regs rDp = p.regs rDp ∧
    out.regs rDn = p.regs rDn ∧ out.regs 43 = p.regs 43 ∧
    out.regs rZero = p.regs rZero at hb
  have hall : out.regs rK = st.regs rK ∧
      out.regs rDp = st.regs rDp ∧ out.regs rDn = st.regs rDn ∧
      out.regs 43 = st.regs 43 ∧ out.regs rZero = st.regs rZero := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hb.1, prodKeep rK (by simp [rK]) (by simp [rK])
        (by simp [rK]) (by simp [rK])
        (by simp [rK, Section413G1Denote.NotIn8])
        (by simp [rK, rUpLo]) (by simp [rK, rUpHi])
        (by simp [rK, rUnLo]) (by simp [rK, rUnHi]) (by simp [rK]), hkey]
    · rw [hb.2.1, prodKeep rDp (by simp [rDp]) (by simp [rDp])
        (by simp [rDp]) (by simp [rDp])
        (by simp [rDp, Section413G1Denote.NotIn8])
        (by simp [rDp, rUpLo]) (by simp [rDp, rUpHi])
        (by simp [rDp, rUnLo]) (by simp [rDp, rUnHi]) (by simp [rDp]),
        hdp]
    · rw [hb.2.2.1, prodKeep rDn (by simp [rDn]) (by simp [rDn])
        (by simp [rDn]) (by simp [rDn])
        (by simp [rDn, Section413G1Denote.NotIn8])
        (by simp [rDn, rUpLo]) (by simp [rDn, rUpHi])
        (by simp [rDn, rUnLo]) (by simp [rDn, rUnHi]) (by simp [rDn]),
        hdn]
    · rw [hb.2.2.2.1, prodKeep 43 (by decide) (by decide) (by decide)
        (by decide) (by simp [Section413G1Denote.NotIn8])
        (by simp [rUpLo]) (by simp [rUpHi]) (by simp [rUnLo])
        (by simp [rUnHi]) (by decide), headKeep 43 (by rfl)]
    · rw [hb.2.2.2.2, prodKeep rZero (by simp [rZero]) (by simp [rZero])
        (by simp [rZero]) (by simp [rZero])
        (by simp [rZero, Section413G1Denote.NotIn8])
        (by simp [rZero, rUpLo]) (by simp [rZero, rUpHi])
        (by simp [rZero, rUnLo]) (by simp [rZero, rUnHi]) (by simp [rZero]),
        headKeep rZero (by rfl)]
  simpa [h, p, out] using hall

theorem accBody_middle_latch_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : MiddleHeadSpec c st (arun idx st c.accHead))
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    let out := arun idx
      (arun idx (arun idx st c.accHead) c.accProd) c.accBisect
    out.regs rK = st.regs rK ∧
      out.regs rDp = st.regs rDp ∧
      out.regs rDn = st.regs rDn ∧
      out.regs 43 = st.regs 43 ∧
      out.regs rZero = st.regs rZero :=
  accBody_latch_of_head_values c idx st hh.k hh.dPos hh.dNeg hword harrword

/-- The final bisection body preserves the source key and signed-jump
latches just as an ordinary middle body does. -/
theorem accBody_last_latch_of_head (c : Cfg) (idx : Nat) (st : AState)
    (hh : LastHeadSpec c st (arun idx st c.accHead))
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    let out := arun idx
      (arun idx (arun idx st c.accHead) c.accProd) c.accBisect
    out.regs rK = st.regs rK ∧
      out.regs rDp = st.regs rDp ∧
      out.regs rDn = st.regs rDn ∧
      out.regs 43 = st.regs 43 ∧
      out.regs rZero = st.regs rZero :=
  accBody_latch_of_head_values c idx st hh.k hh.dPos hh.dNeg hword harrword

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
    hbsM hsinkM hword harrword hk hWM hsum hceilFit
  exact accBody_middle_of_head c idx st hh hsink0 hlohi hhiM hfit haLe
    hkrFit hword harrword

structure FinalBodySpec (s d : Nat) (before after : AState) : Prop where
  arr : after.arr = before.arr
  low : after.regs rSl = s
  high : after.regs rSh = s
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * s
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

structure FinalBodyLiveSpec (c : Cfg) (s d : Nat)
    (before after : AState) : Prop where
  arr : SinkClearSpec c before after
  low : after.regs rSl = s
  high : after.regs rSh = s
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * s
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

theorem accBody_final_live_of_head (c : Cfg) (idx : Nat) (st : AState)
    (s : Nat) (hh : LastHeadSpec c st (arun idx st c.accHead))
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hstep : step c.wScale (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ = ⟨s, s⟩)
    (hcFit : st.regs rC + 1 < M)
    (haccFit : AddWide.wval (st.regs rVLo, st.regs rVHi) +
      (st.regs rDp + st.regs rDn) * s < AddWide.B128)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    FinalBodyLiveSpec c s (st.regs rDp + st.regs rDn) st
      (arun idx st c.accBody) := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have hh' : LastHeadSpec c st h := by simpa [h] using hh
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have harrH : ∀ j, h.arr j < M :=
    (arun_word idx c.accHead st hword harrword).2
  have headKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      h.regs j = st.regs j := by
    simpa [h] using LeanCompCert.Verified.ArrayRegFrame.arun_frame
      idx j c.accHead hw st
  have hz := accProd_zero_run c idx h hwordH hh'.posGate hh'.negGate
  have hz' : ZeroProdSpec h p := by simpa [p] using hz
  have hwordP : ∀ j, p.regs j < M :=
    (arun_word idx c.accProd h hwordH harrH).1
  have pk (j : Nat) (h171 : j ≠ 171) (h172 : j ≠ 172)
      (h173 : j ≠ 173) (h174 : j ≠ 174)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hupl : j ≠ rUpLo) (huph : j ≠ rUpHi)
      (hunl : j ≠ rUnLo) (hunh : j ≠ rUnHi) (h188 : j ≠ 188) :
      p.regs j = h.regs j :=
    hz'.frame j h171 h172 h173 h174 hjs hupl huph hunl hunh h188
  have hp140 : p.regs 140 = 0 := by
    rw [pk 140 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.round0]
  have hp141 : p.regs 141 = 1 := by
    rw [pk 141 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.last]
  have hp142 : p.regs 142 = 1 := by
    rw [pk 142 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.bisect]
  have hpLo : p.regs rSl = st.regs rSl := by
    rw [pk rSl (by simp [rSl]) (by simp [rSl]) (by simp [rSl])
      (by simp [rSl]) (by simp [rSl, Section413G1Denote.NotIn8])
      (by simp [rSl, rUpLo]) (by simp [rSl, rUpHi])
      (by simp [rSl, rUnLo]) (by simp [rSl, rUnHi]) (by simp [rSl]),
      hh'.low]
  have hpHi : p.regs rSh = st.regs rSh := by
    rw [pk rSh (by simp [rSh]) (by simp [rSh]) (by simp [rSh])
      (by simp [rSh]) (by simp [rSh, Section413G1Denote.NotIn8])
      (by simp [rSh, rUpLo]) (by simp [rSh, rUpHi])
      (by simp [rSh, rUnLo]) (by simp [rSh, rUnHi]) (by simp [rSh]),
      hh'.high]
  have hpK : p.regs rK = st.regs rK := by
    rw [pk rK (by simp [rK]) (by simp [rK]) (by simp [rK]) (by simp [rK])
      (by simp [rK, Section413G1Denote.NotIn8]) (by simp [rK, rUpLo])
      (by simp [rK, rUpHi]) (by simp [rK, rUnLo])
      (by simp [rK, rUnHi]) (by simp [rK]), hh'.k]
  have hp165 : p.regs 165 = st.regs rDp + st.regs rDn := by
    rw [pk 165 (by decide) (by decide) (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
      (by simp [rUpHi]) (by simp [rUnLo]) (by simp [rUnHi]) (by decide),
      hh'.sum]
  have hpC : p.regs rC = st.regs rC := by
    rw [pk rC (by simp [rC]) (by simp [rC]) (by simp [rC]) (by simp [rC])
      (by simp [rC, Section413G1Denote.NotIn8]) (by simp [rC, rUpLo])
      (by simp [rC, rUpHi]) (by simp [rC, rUnLo])
      (by simp [rC, rUnHi]) (by simp [rC]), hh'.cell]
  have hpVLo : p.regs rVLo = st.regs rVLo := by
    rw [pk rVLo (by simp [rVLo]) (by simp [rVLo]) (by simp [rVLo])
      (by simp [rVLo]) (by simp [rVLo, Section413G1Denote.NotIn8])
      (by simp [rVLo, rUpLo]) (by simp [rVLo, rUpHi])
      (by simp [rVLo, rUnLo]) (by simp [rVLo, rUnHi]) (by simp [rVLo]),
      headKeep rVLo (by rfl)]
  have hpVHi : p.regs rVHi = st.regs rVHi := by
    rw [pk rVHi (by simp [rVHi]) (by simp [rVHi]) (by simp [rVHi])
      (by simp [rVHi]) (by simp [rVHi, Section413G1Denote.NotIn8])
      (by simp [rVHi, rUpLo]) (by simp [rVHi, rUpHi])
      (by simp [rVHi, rUnLo]) (by simp [rVHi, rUnHi]) (by simp [rVHi]),
      headKeep rVHi (by rfl)]
  have hb := accBisect_final_run c idx p (st.regs rSl) (st.regs rSh)
    (st.regs rK) s (st.regs rDp + st.regs rDn)
    hp140 hp142 hp141 hpLo hpHi hpK hp165 hlohi hhiM hfit haLe hstep
    (by rw [hpC]; exact hcFit)
    (by rw [hpVLo, hpVHi]; exact haccFit) hwordP
  have hb' : FinalBisectSpec s (st.regs rDp + st.regs rDn) p out := by
    simpa [out] using hb
  have hbU := accBisect_u_frame c idx p
  have pToSt (j : Nat)
      (hj : p.regs j = h.regs j) (hhj : h.regs j = st.regs j) :
      p.regs j = st.regs j := hj.trans hhj
  have hall : FinalBodyLiveSpec c s (st.regs rDp + st.regs rDn) st out :=
    { arr := by
        constructor
        · rw [hb'.arr, hz'.arr]
          exact hh'.arr.sink_zero
        · intro j hj
          rw [hb'.arr, hz'.arr]
          exact hh'.arr.live j hj
      low := hb'.low
      high := hb'.high
      uPos := by
        rw [hbU.1, hbU.2.1, hz'.uPos,
          headKeep rUpLo (by rfl), headKeep rUpHi (by rfl)]
      uNeg := by
        rw [hbU.2.2.1, hbU.2.2.2, hz'.uNeg,
          headKeep rUnLo (by rfl), headKeep rUnHi (by rfl)]
      viol := by
        rw [hb'.viol]
        exact pToSt rViol
          (pk rViol (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
            (by simp [rViol]) (by simp [rViol, Section413G1Denote.NotIn8])
            (by simp [rViol, rUpLo]) (by simp [rViol, rUpHi])
            (by simp [rViol, rUnLo]) (by simp [rViol, rUnHi])
            (by simp [rViol])) hh'.viol
      vDiv := by
        rw [hb'.vDiv]
        exact pToSt rVDiv
          (pk rVDiv (by simp [rVDiv]) (by simp [rVDiv]) (by simp [rVDiv])
            (by simp [rVDiv]) (by simp [rVDiv, Section413G1Denote.NotIn8])
            (by simp [rVDiv, rUpLo]) (by simp [rVDiv, rUpHi])
            (by simp [rVDiv, rUnLo]) (by simp [rVDiv, rUnHi])
            (by simp [rVDiv])) (headKeep rVDiv (by rfl))
      vBisect := by
        rw [hb'.vBisect]
        exact pToSt rVBisect
          (pk rVBisect (by simp [rVBisect]) (by simp [rVBisect])
            (by simp [rVBisect]) (by simp [rVBisect])
            (by simp [rVBisect, Section413G1Denote.NotIn8])
            (by simp [rVBisect, rUpLo]) (by simp [rVBisect, rUpHi])
            (by simp [rVBisect, rUnLo]) (by simp [rVBisect, rUnHi])
            (by simp [rVBisect])) (headKeep rVBisect (by rfl))
      v := by rw [hb'.v, hpVLo, hpVHi]
      round := hb'.round
      cell := by rw [hb'.cell, hpC] }
  simpa [Cfg.accBody, arun_append, h, p, out] using hall

theorem accBody_final_of_head (c : Cfg) (idx : Nat) (st : AState)
    (s : Nat) (hh : LastHeadSpec c st (arun idx st c.accHead))
    (hsink0 : st.arr c.sink = 0)
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hstep : step c.wScale (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ = ⟨s, s⟩)
    (hcFit : st.regs rC + 1 < M)
    (haccFit : AddWide.wval (st.regs rVLo, st.regs rVHi) +
      (st.regs rDp + st.regs rDn) * s < AddWide.B128)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    FinalBodySpec s (st.regs rDp + st.regs rDn) st
      (arun idx st c.accBody) := by
  have h := accBody_final_live_of_head c idx st s hh hlohi hhiM hfit haLe
    hstep hcFit haccFit hword harrword
  exact
    { arr := h.arr.arr_eq hsink0
      low := h.low
      high := h.high
      uPos := h.uPos
      uNeg := h.uNeg
      viol := h.viol
      vDiv := h.vDiv
      vBisect := h.vBisect
      v := h.v
      round := h.round
      cell := h.cell }

theorem accBody_final_run (c : Cfg) (idx : Nat) (st : AState)
    (s : Nat) (hkrLast : st.regs rKr = c.bsSteps)
    (hbsPos : 0 < c.bsSteps) (hgate : st.regs 43 = 1)
    (hzero : st.regs rZero = 0) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hsink0 : st.arr c.sink = 0)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M)
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hstep : step c.wScale (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ = ⟨s, s⟩)
    (hcFit : st.regs rC + 1 < M)
    (haccFit : AddWide.wval (st.regs rVLo, st.regs rVHi) +
      (st.regs rDp + st.regs rDn) * s < AddWide.B128) :
    FinalBodySpec s (st.regs rDp + st.regs rDn) st
      (arun idx st c.accBody) := by
  have hh := accHead_last_run c idx st hkrLast hbsPos hgate hzero hbsM
    hsinkM hword harrword hk hWM hsum hceilFit
  exact accBody_final_of_head c idx st s hh hsink0 hlohi hhiM hfit haLe hstep
    hcFit haccFit hword harrword

structure FirstBodySpec (c : Cfg) (k dp dn ceil floor : Nat)
    (before after : AState) : Prop where
  arr : after.arr = fun j =>
    if j = before.regs rC + c.winBase then 0 else before.arr j
  key : after.regs rK = k
  dPos : after.regs rDp = dp
  dNeg : after.regs rDn = dn
  gate : after.regs 43 = before.regs 43
  zero : after.regs rZero = before.regs rZero
  f : after.regs rF =
    (before.regs rF + before.arr (before.regs rC + c.winBase)) % M
  t : after.regs rT =
    if before.regs rW + before.regs rC < before.regs rT2 then
      before.regs rT else before.regs rT + 1
  t2 : after.regs rT2 =
    if before.regs rW + before.regs rC < before.regs rT2 then
      before.regs rT2
    else before.regs rT2 + (2 * (before.regs rT + 1) + 1)
  e : after.regs rE = headG
    ((before.regs rF + before.arr (before.regs rC + c.winBase)) % M)
  tv : after.regs rTv = before.regs rTv + dp + dn
  low : after.regs rSl = (initial c.wScale k).lo
  high : after.regs rSh = (initial c.wScale k).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi) + dp * ceil
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi) + dn * floor
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + before.regs 43
  cell : after.regs rC = before.regs rC

set_option maxHeartbeats 2000000 in
theorem accBody_first_of_head (c : Cfg) (idx : Nat) (st : AState)
    (nextT nextT2 : Nat)
    (hh : FirstHeadSpec c st (arun idx st c.accHead) nextT nextT2)
    (hnextT : nextT =
      if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT else st.regs rT + 1)
    (hnextT2 : nextT2 =
      if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT2
      else st.regs rT2 + (2 * (st.regs rT + 1) + 1))
    (hroot : nextT = Nat.sqrt (st.regs rW + st.regs rC))
    (htpos : 0 < Nat.sqrt (st.regs rW + st.regs rC))
    (hWpos : 0 < c.wScale)
    (hWtM : c.wScale + Nat.sqrt (st.regs rW + st.regs rC) < M)
    (hkrFit : st.regs rKr + st.regs 43 < M)
    (hfitPos : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
      (arun idx st c.accHead).regs 169 *
        (arun idx st c.accHead).regs 167 < AddWide.B128)
    (hfitNeg : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
      (arun idx st c.accHead).regs 170 *
        (arun idx st c.accHead).regs 168 < AddWide.B128)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    FirstBodySpec c (st.regs rW + st.regs rC)
      ((arun idx st c.accHead).regs 169)
      ((arun idx st c.accHead).regs 170)
      ((arun idx st c.accHead).regs 167)
      ((arun idx st c.accHead).regs 168) st (arun idx st c.accBody) := by
  let h := arun idx st c.accHead
  let p := arun idx h c.accProd
  let out := arun idx p c.accBisect
  have hh' : FirstHeadSpec c st h nextT nextT2 := by simpa [h] using hh
  have hwordH : ∀ j, h.regs j < M :=
    (arun_word idx c.accHead st hword harrword).1
  have harrH : ∀ j, h.arr j < M :=
    (arun_word idx c.accHead st hword harrword).2
  have headKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accHead = false) :
      h.regs j = st.regs j := by
    simpa [h] using LeanCompCert.Verified.ArrayRegFrame.arun_frame
      idx j c.accHead hw st
  have hp0 := accProd_exact_frame_run c idx h hwordH
    (by
      rw [headKeep rUpLo (by rfl), headKeep rUpHi (by rfl)]
      simpa [h] using hfitPos)
    (by
      rw [headKeep rUnLo (by rfl), headKeep rUnHi (by rfl)]
      simpa [h] using hfitNeg)
  have hp : ExactProdSpec h p := by simpa [p] using hp0
  have hwordP : ∀ j, p.regs j < M :=
    (arun_word idx c.accProd h hwordH harrH).1
  have pk (j : Nat) (h171 : j ≠ 171) (h172 : j ≠ 172)
      (h173 : j ≠ 173) (h174 : j ≠ 174)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hupl : j ≠ rUpLo) (huph : j ≠ rUpHi)
      (hunl : j ≠ rUnLo) (hunh : j ≠ rUnHi) (h188 : j ≠ 188) :
      p.regs j = h.regs j :=
    hp.frame j h171 h172 h173 h174 hjs hupl huph hunl hunh h188
  have keepH (j : Nat)
      (hj : j ≠ 171 ∧ j ≠ 172 ∧ j ≠ 173 ∧ j ≠ 174 ∧
        Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 ∧
        j ≠ rUpLo ∧ j ≠ rUpHi ∧ j ≠ rUnLo ∧ j ≠ rUnHi ∧ j ≠ 188)
      : p.regs j = h.regs j := by
    rcases hj with ⟨h171, h172, h173, h174, hjs, hupl, huph,
      hunl, hunh, h188⟩
    exact pk j h171 h172 h173 h174 hjs hupl huph hunl hunh h188
  have keep (j : Nat)
      (hj : j ≠ 171 ∧ j ≠ 172 ∧ j ≠ 173 ∧ j ≠ 174 ∧
        Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 ∧
        j ≠ rUpLo ∧ j ≠ rUpHi ∧ j ≠ rUnLo ∧ j ≠ rUnHi ∧ j ≠ 188)
      (hhj : h.regs j = st.regs j) : p.regs j = st.regs j :=
    (keepH j hj).trans hhj
  have hp140 : p.regs 140 = 1 := by
    rw [keepH 140 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh'.round0]
  have hp141 : p.regs 141 = 0 := by
    rw [keepH 141 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh'.last]
  have hp142 : p.regs 142 = 0 := by
    rw [keepH 142 (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh'.bisect]
  have hpT : p.regs rT = Nat.sqrt (st.regs rW + st.regs rC) := by
    rw [keepH rT (by simp [rT, Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi]), hh'.t, hroot]
  have hpKr : p.regs rKr = st.regs rKr := keep rKr
    (by simp [rKr, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    hh'.round
  have hp43 : p.regs 43 = st.regs 43 := keep 43
    (by simp [Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    (headKeep 43 (by rfl))
  have hb := accBisect_gate0_run c idx p (st.regs rW + st.regs rC)
    hpT hp140 hp142 hp141 htpos hWpos hWtM
    (by rw [hpKr, hp43]; exact hkrFit) hwordP
  have hb' : FirstBisectSpec c (st.regs rW + st.regs rC) p out := by
    simpa [out] using hb
  have hbl := accBisect_latch_frame c idx p
  dsimp only at hbl
  change out.regs rK = p.regs rK ∧ out.regs rDp = p.regs rDp ∧
    out.regs rDn = p.regs rDn ∧ out.regs 43 = p.regs 43 ∧
    out.regs rZero = p.regs rZero at hbl
  have hbU := accBisect_u_frame c idx p
  have bisKeep (j : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes j c.accBisect = false) :
      out.regs j = p.regs j :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx j c.accBisect hw p
  have hpViol : p.regs rViol = st.regs rViol := by
    rw [pk rViol (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol, Section413G1Denote.NotIn8])
      (by simp [rViol, rUpLo]) (by simp [rViol, rUpHi])
      (by simp [rViol, rUnLo]) (by simp [rViol, rUnHi]) (by simp [rViol]),
      hh'.viol]
  have hpDiv : p.regs rVDiv = st.regs rVDiv := keep rVDiv
    (by simp [rVDiv, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    (headKeep rVDiv (by rfl))
  have hpBis : p.regs rVBisect = st.regs rVBisect := keep rVBisect
    (by simp [rVBisect, Section413G1Denote.NotIn8, rUpLo, rUpHi,
      rUnLo, rUnHi])
    (headKeep rVBisect (by rfl))
  have hpVLo : p.regs rVLo = st.regs rVLo := keep rVLo
    (by simp [rVLo, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    (headKeep rVLo (by rfl))
  have hpVHi : p.regs rVHi = st.regs rVHi := keep rVHi
    (by simp [rVHi, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    (headKeep rVHi (by rfl))
  have hpC : p.regs rC = st.regs rC := keep rC
    (by simp [rC, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    hh'.cell
  have hpK : p.regs rK = h.regs rK := keepH rK
    (by simp [rK, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
  have hpDp : p.regs rDp = h.regs rDp := keepH rDp
    (by simp [rDp, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
  have hpDn : p.regs rDn = h.regs rDn := keepH rDn
    (by simp [rDn, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
  have hpZero : p.regs rZero = st.regs rZero := keep rZero
    (by simp [rZero, Section413G1Denote.NotIn8, rUpLo, rUpHi, rUnLo, rUnHi])
    (headKeep rZero (by rfl))
  have hall : FirstBodySpec c (st.regs rW + st.regs rC)
      (h.regs 169) (h.regs 170) (h.regs 167) (h.regs 168) st out :=
    { arr := by rw [hb'.arr, hp.arr, hh'.arr]
      key := by rw [hbl.1, hpK, hh'.k]
      dPos := by rw [hbl.2.1, hpDp, hh'.dPos, hh'.posGate]
      dNeg := by rw [hbl.2.2.1, hpDn, hh'.dNeg, hh'.negGate]
      gate := by rw [hbl.2.2.2.1, hp43]
      zero := by rw [hbl.2.2.2.2, hpZero]
      f := by rw [bisKeep rF (by rfl), keepH rF
        (by simp [rF, Section413G1Denote.NotIn8, rUpLo, rUpHi,
          rUnLo, rUnHi]), hh'.f]
      t := by rw [bisKeep rT (by rfl), keepH rT
        (by simp [rT, Section413G1Denote.NotIn8, rUpLo, rUpHi,
          rUnLo, rUnHi]), hh'.t, hnextT]
      t2 := by rw [bisKeep rT2 (by rfl), keepH rT2
        (by simp [rT2, Section413G1Denote.NotIn8, rUpLo, rUpHi,
          rUnLo, rUnHi]), hh'.t2, hnextT2]
      e := by rw [bisKeep rE (by rfl), keepH rE
        (by simp [rE, Section413G1Denote.NotIn8, rUpLo, rUpHi,
          rUnLo, rUnHi]), hh'.e]
      tv := by
        rw [bisKeep rTv (by rfl), keepH rTv
          (by simp [rTv, Section413G1Denote.NotIn8, rUpLo, rUpHi,
            rUnLo, rUnHi]), hh'.tv, hh'.posGate, hh'.negGate]
        simp only [Nat.add_assoc]
      low := hb'.low
      high := hb'.high
      uPos := by
        rw [hbU.1, hbU.2.1, hp.uPos,
          headKeep rUpLo (by rfl), headKeep rUpHi (by rfl)]
      uNeg := by
        rw [hbU.2.2.1, hbU.2.2.2, hp.uNeg,
          headKeep rUnLo (by rfl), headKeep rUnHi (by rfl)]
      viol := by rw [hb'.viol, hpViol]
      vDiv := by rw [hb'.vDiv, hpDiv]
      vBisect := by rw [hb'.vBisect, hpBis]
      v := by rw [hb'.v, hpVLo, hpVHi]
      round := by rw [hb'.round, hpKr, hp43]
      cell := by rw [hb'.cell, hpC] }
  simpa [Cfg.accBody, arun_append, h, p, out] using hall

theorem accBody_first_run (c : Cfg) (idx : Nat) (st : AState)
    (hkr : st.regs rKr = 0) (hbsPos : 0 < c.bsSteps)
    (hbsM : c.bsSteps < M) (hgate : st.regs 43 = 1)
    (hzero : st.regs rZero = 0) (haddr : st.regs rC + c.winBase < M)
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
    (hceilFit : c.wScale - 1 + (st.regs rW + st.regs rC) < M)
    (hroot : (if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT else st.regs rT + 1) =
      Nat.sqrt (st.regs rW + st.regs rC))
    (htpos : 0 < Nat.sqrt (st.regs rW + st.regs rC))
    (hWpos : 0 < c.wScale)
    (hWtM : c.wScale + Nat.sqrt (st.regs rW + st.regs rC) < M)
    (hkrFit : st.regs rKr + st.regs 43 < M)
    (hfitPos : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
      (arun idx st c.accHead).regs 169 *
        (arun idx st c.accHead).regs 167 < AddWide.B128)
    (hfitNeg : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
      (arun idx st c.accHead).regs 170 *
        (arun idx st c.accHead).regs 168 < AddWide.B128) :
    FirstBodySpec c (st.regs rW + st.regs rC)
      ((arun idx st c.accHead).regs 169)
      ((arun idx st c.accHead).regs 170)
      ((arun idx st c.accHead).regs 167)
      ((arun idx st c.accHead).regs 168) st (arun idx st c.accBody) := by
  have hh := accHead_first_run c idx st hkr hbsPos hbsM hgate hzero haddr
    hword harrword hk hkFit hkclosed htFit hdoubleFit ht2Fit hWM hsum
    htvFit hceilFit
  exact accBody_first_of_head c idx st _ _ hh rfl rfl hroot htpos hWpos hWtM
    hkrFit hfitPos hfitNeg hword harrword

end LeanCompCert.Ports.CDEMAbelBody
