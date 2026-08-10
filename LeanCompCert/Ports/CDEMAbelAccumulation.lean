import LeanCompCert.Ports.CDEMAbelBisection

namespace LeanCompCert.Ports.CDEMAbelAccumulation

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives

def mulAddS (ra rb pLo pHi accLo accHi carry
    s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List Instr :=
  Section413G1Denote.mulWideG 4294967295 4294967296
    ra rb pLo pHi s0 s1 s2 s3 s4 s5 s6 s7 ++
  addWideS accLo accHi pLo pHi carry

theorem mulAdd_run_mod (idx : Nat) (r : RegState)
    (ra rb pLo pHi accLo accHi carry s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hpLo : Section413G1Denote.NotIn8 pLo s0 s1 s2 s3 s4 s5 s6 s7)
    (hpHi : Section413G1Denote.NotIn8 pHi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : pLo ≠ pHi)
    (haccLo : accLo ≠ pLo ∧ accLo ≠ pHi ∧
      Section413G1Denote.NotIn8 accLo s0 s1 s2 s3 s4 s5 s6 s7)
    (haccHi : accHi ≠ pLo ∧ accHi ≠ pHi ∧
      Section413G1Denote.NotIn8 accHi s0 s1 s2 s3 s4 s5 s6 s7)
    (hregs : AddWidePort.WideRegs accLo accHi carry pLo pHi)
    (hword : ∀ j, r j < M) :
    let out := srun idx r
      (mulAddS ra rb pLo pHi accLo accHi carry s0 s1 s2 s3 s4 s5 s6 s7)
    AddWide.wval (out accLo, out accHi) =
      (AddWide.wval (r accLo, r accHi) + r ra * r rb) % AddWide.B128 ∧
    ∀ j, j ≠ pLo → j ≠ pHi →
      Section413G1Denote.NotIn8 j s0 s1 s2 s3 s4 s5 s6 s7 →
      j ≠ accLo → j ≠ accHi → j ≠ carry → out j = r j := by
  let q := srun idx r (Section413G1Denote.mulWideG 4294967295 4294967296
    ra rb pLo pHi s0 s1 s2 s3 s4 s5 s6 s7)
  let out := srun idx q (addWideS accLo accHi pLo pHi carry)
  have hmul := Section413G1Denote.mulWideG_hl idx r ra rb pLo pHi
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hpLo hpHi hlohi hword
  have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ r hword
  have hqframe (j : Nat) (hjLo : j ≠ pLo) (hjHi : j ≠ pHi)
      (hjs : Section413G1Denote.NotIn8 j s0 s1 s2 s3 s4 s5 s6 s7) :
      q j = r j := by
    simpa [q] using Section413G1Denote.mulWideG_frame idx r
      4294967295 4294967296 ra rb pLo pHi s0 s1 s2 s3 s4 s5 s6 s7
      j hjLo hjHi hjs
  have hqprod : AddWide.wval (q pLo, q pHi) = r ra * r rb := by
    have hs := MulWide.hl_spec (r ra) (r rb)
      (by
        have hx := hword ra
        rw [AddWidePort.M_eq_B64] at hx
        simpa using hx)
      (by
        have hx := hword rb
        rw [AddWidePort.M_eq_B64] at hx
        simpa using hx)
    rw [show q pLo = (MulWide.hl (r ra) (r rb)).1 by simpa [q] using hmul.1,
      show q pHi = (MulWide.hl (r ra) (r rb)).2 by simpa [q] using hmul.2]
    exact hs.1
  have hqprodOk : AddWide.Ok (q pLo, q pHi) := by
    constructor
    · rw [← AddWidePort.M_eq_B64]
      exact hqword pLo
    · rw [← AddWidePort.M_eq_B64]
      exact hqword pHi
  have hqaccLo : q accLo = r accLo :=
    hqframe accLo haccLo.1 haccLo.2.1 haccLo.2.2
  have hqaccHi : q accHi = r accHi :=
    hqframe accHi haccHi.1 haccHi.2.1 haccHi.2.2
  have hqaccOk : AddWide.Ok (q accLo, q accHi) := by
    constructor
    · rw [hqaccLo, ← AddWidePort.M_eq_B64]
      exact hword accLo
    · rw [hqaccHi, ← AddWidePort.M_eq_B64]
      exact hword accHi
  have hadd := addWideS_run idx q accLo accHi pLo pHi carry hregs
  dsimp only at hadd
  have houtPair : (out accLo, out accHi) =
      AddWide.addWide (q accLo, q accHi) (q pLo, q pHi) := by
    simpa [out] using hadd.1
  have houtVal : AddWide.wval (out accLo, out accHi) =
      (AddWide.wval (r accLo, r accHi) + r ra * r rb) % AddWide.B128 := by
    rw [houtPair, AddWide.addWide_spec _ _ hqaccOk hqprodOk,
      hqaccLo, hqaccHi, hqprod]
  have houtFrame (j : Nat) (hjLo : j ≠ pLo) (hjHi : j ≠ pHi)
      (hjs : Section413G1Denote.NotIn8 j s0 s1 s2 s3 s4 s5 s6 s7)
      (hjaLo : j ≠ accLo) (hjaHi : j ≠ accHi) (hjC : j ≠ carry) :
      out j = r j := by
    rw [show out j = q j by simpa [out] using hadd.2 j hjaLo hjaHi hjC,
      hqframe j hjLo hjHi hjs]
  rw [mulAddS, srun_append]
  exact ⟨houtVal, houtFrame⟩

theorem mulAdd_run_exact (idx : Nat) (r : RegState)
    (ra rb pLo pHi accLo accHi carry s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hpLo : Section413G1Denote.NotIn8 pLo s0 s1 s2 s3 s4 s5 s6 s7)
    (hpHi : Section413G1Denote.NotIn8 pHi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : pLo ≠ pHi)
    (haccLo : accLo ≠ pLo ∧ accLo ≠ pHi ∧
      Section413G1Denote.NotIn8 accLo s0 s1 s2 s3 s4 s5 s6 s7)
    (haccHi : accHi ≠ pLo ∧ accHi ≠ pHi ∧
      Section413G1Denote.NotIn8 accHi s0 s1 s2 s3 s4 s5 s6 s7)
    (hregs : AddWidePort.WideRegs accLo accHi carry pLo pHi)
    (hword : ∀ j, r j < M)
    (hfit : AddWide.wval (r accLo, r accHi) + r ra * r rb < AddWide.B128) :
    let out := srun idx r
      (mulAddS ra rb pLo pHi accLo accHi carry s0 s1 s2 s3 s4 s5 s6 s7)
    AddWide.wval (out accLo, out accHi) =
      AddWide.wval (r accLo, r accHi) + r ra * r rb := by
  have h := mulAdd_run_mod idx r ra rb pLo pHi accLo accHi carry
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hpLo hpHi hlohi haccLo haccHi
    hregs hword
  dsimp only at h ⊢
  rw [h.1, Nat.mod_eq_of_lt hfit]

/-! ## The production `accProd` block -/

def posS : List Instr :=
  mulAddS 169 167 171 172 rUpLo rUpHi 188
    180 181 182 183 184 185 186 187

def negS : List Instr :=
  mulAddS 170 168 173 174 rUnLo rUnHi 188
    180 181 182 183 184 185 186 187

def accProdS : List Instr := posS ++ negS

theorem accProd_decomp (c : Cfg) :
    c.accProd = ArrayScalarBlock.lift accProdS := by
  simp [Cfg.accProd, accProdS, posS, negS, mulAddS,
    Section413G1Denote.mulWideBody_lift,
    CDEMAbelPrimitives.addWideBody_lift, ArrayScalarBlock.lift_append]

theorem accProdS_run_mod (idx : Nat) (r : RegState)
    (hword : ∀ j, r j < M) :
    let out := srun idx r accProdS
    AddWide.wval (out rUpLo, out rUpHi) =
        (AddWide.wval (r rUpLo, r rUpHi) + r 169 * r 167) %
          AddWide.B128 ∧
      AddWide.wval (out rUnLo, out rUnHi) =
        (AddWide.wval (r rUnLo, r rUnHi) + r 170 * r 168) %
          AddWide.B128 ∧
      ∀ j, j ≠ 171 → j ≠ 172 → j ≠ 173 → j ≠ 174 →
        Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 →
        j ≠ rUpLo → j ≠ rUpHi → j ≠ rUnLo → j ≠ rUnHi →
        j ≠ 188 → out j = r j := by
  let q := srun idx r posS
  let out := srun idx q negS
  have hpos := mulAdd_run_mod idx r 169 167 171 172 rUpLo rUpHi 188
    180 181 182 183 184 185 186 187
    (by simp [Section413G1Denote.Distinct8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by decide)
    (by simp [rUpLo, Section413G1Denote.NotIn8])
    (by simp [rUpHi, Section413G1Denote.NotIn8])
    (⟨by simp [rUpLo, rUpHi], by simp [rUpLo], by simp [rUpHi],
      by simp [rUpLo], by simp [rUpHi], by decide,
      by simp [rUpLo], by simp [rUpHi], by decide⟩)
    hword
  dsimp only at hpos
  have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ r hword
  have hqframe (j : Nat) (hjLo : j ≠ 171) (hjHi : j ≠ 172)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hjuLo : j ≠ rUpLo) (hjuHi : j ≠ rUpHi) (hjC : j ≠ 188) :
      q j = r j := by
    simpa [q, posS] using hpos.2 j hjLo hjHi hjs hjuLo hjuHi hjC
  have hneg := mulAdd_run_mod idx q 170 168 173 174 rUnLo rUnHi 188
    180 181 182 183 184 185 186 187
    (by simp [Section413G1Denote.Distinct8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by decide)
    (by simp [rUnLo, Section413G1Denote.NotIn8])
    (by simp [rUnHi, Section413G1Denote.NotIn8])
    (⟨by simp [rUnLo, rUnHi], by simp [rUnLo], by simp [rUnHi],
      by simp [rUnLo], by simp [rUnHi], by decide,
      by simp [rUnLo], by simp [rUnHi], by decide⟩)
    hqword
  dsimp only at hneg
  have hq170 : q 170 = r 170 := hqframe 170 (by decide) (by decide)
    (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
    (by simp [rUpHi]) (by decide)
  have hq168 : q 168 = r 168 := hqframe 168 (by decide) (by decide)
    (by simp [Section413G1Denote.NotIn8]) (by simp [rUpLo])
    (by simp [rUpHi]) (by decide)
  have hqunLo : q rUnLo = r rUnLo := hqframe rUnLo
    (by simp [rUnLo]) (by simp [rUnLo])
    (by simp [rUnLo, Section413G1Denote.NotIn8])
    (by simp [rUnLo, rUpLo]) (by simp [rUnLo, rUpHi]) (by simp [rUnLo])
  have hqunHi : q rUnHi = r rUnHi := hqframe rUnHi
    (by simp [rUnHi]) (by simp [rUnHi])
    (by simp [rUnHi, Section413G1Denote.NotIn8])
    (by simp [rUnHi, rUpLo]) (by simp [rUnHi, rUpHi]) (by simp [rUnHi])
  have houtUpLo : out rUpLo = q rUpLo := by
    simpa [out, negS] using hneg.2 rUpLo
      (by simp [rUpLo]) (by simp [rUpLo])
      (by simp [rUpLo, Section413G1Denote.NotIn8])
      (by simp [rUpLo, rUnLo]) (by simp [rUpLo, rUnHi]) (by simp [rUpLo])
  have houtUpHi : out rUpHi = q rUpHi := by
    simpa [out, negS] using hneg.2 rUpHi
      (by simp [rUpHi]) (by simp [rUpHi])
      (by simp [rUpHi, Section413G1Denote.NotIn8])
      (by simp [rUpHi, rUnLo]) (by simp [rUpHi, rUnHi]) (by simp [rUpHi])
  have hup : AddWide.wval (out rUpLo, out rUpHi) =
      (AddWide.wval (r rUpLo, r rUpHi) + r 169 * r 167) %
        AddWide.B128 := by
    rw [houtUpLo, houtUpHi]
    simpa [q, posS] using hpos.1
  have hun : AddWide.wval (out rUnLo, out rUnHi) =
      (AddWide.wval (r rUnLo, r rUnHi) + r 170 * r 168) %
        AddWide.B128 := by
    change AddWide.wval
      (srun idx q
          (mulAddS 170 168 173 174 rUnLo rUnHi 188
            180 181 182 183 184 185 186 187) rUnLo,
        srun idx q
          (mulAddS 170 168 173 174 rUnLo rUnHi 188
            180 181 182 183 184 185 186 187) rUnHi) = _
    simpa [hq170, hq168, hqunLo, hqunHi] using hneg.1
  have houtFrame (j : Nat) (hj171 : j ≠ 171) (hj172 : j ≠ 172)
      (hj173 : j ≠ 173) (hj174 : j ≠ 174)
      (hjs : Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187)
      (hjuLo : j ≠ rUpLo) (hjuHi : j ≠ rUpHi)
      (hjnLo : j ≠ rUnLo) (hjnHi : j ≠ rUnHi) (hjC : j ≠ 188) :
      out j = r j := by
    have hjq : out j = q j := by
      simpa [out, negS] using
        hneg.2 j hj173 hj174 hjs hjnLo hjnHi hjC
    rw [hjq, hqframe j hj171 hj172 hjs hjuLo hjuHi hjC]
  simpa [accProdS, srun_append, q, out] using ⟨hup, hun, houtFrame⟩

theorem accProd_run_mod (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M) :
    let out := arun idx st c.accProd
    AddWide.wval (out.regs rUpLo, out.regs rUpHi) =
        (AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
          st.regs 169 * st.regs 167) % AddWide.B128 ∧
      AddWide.wval (out.regs rUnLo, out.regs rUnHi) =
        (AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
          st.regs 170 * st.regs 168) % AddWide.B128 ∧
      out.arr = st.arr ∧
      ∀ j, j ≠ 171 → j ≠ 172 → j ≠ 173 → j ≠ 174 →
        Section413G1Denote.NotIn8 j 180 181 182 183 184 185 186 187 →
        j ≠ rUpLo → j ≠ rUpHi → j ≠ rUnLo → j ≠ rUnHi →
        j ≠ 188 → out.regs j = st.regs j := by
  rw [accProd_decomp, ArrayScalarBlock.arun_lift]
  have h := accProdS_run_mod idx st.regs hword
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1, rfl, h.2.2⟩

theorem accProd_run_exact (c : Cfg) (idx : Nat) (st : AState)
    (hword : ∀ j, st.regs j < M)
    (hfitPos : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
      st.regs 169 * st.regs 167 < AddWide.B128)
    (hfitNeg : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
      st.regs 170 * st.regs 168 < AddWide.B128) :
    let out := arun idx st c.accProd
    AddWide.wval (out.regs rUpLo, out.regs rUpHi) =
        AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
          st.regs 169 * st.regs 167 ∧
      AddWide.wval (out.regs rUnLo, out.regs rUnHi) =
        AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
          st.regs 170 * st.regs 168 ∧
      out.arr = st.arr := by
  have h := accProd_run_mod c idx st hword
  dsimp only at h ⊢
  rw [h.1, h.2.1, Nat.mod_eq_of_lt hfitPos, Nat.mod_eq_of_lt hfitNeg]
  exact ⟨rfl, rfl, h.2.2.1⟩

end LeanCompCert.Ports.CDEMAbelAccumulation
