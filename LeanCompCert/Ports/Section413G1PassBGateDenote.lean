import LeanCompCert.Ports.Section413G1WeightCompose

/-!
# Section 4.1.3 G2 pass-B gate denotation

This module proves the pass-B gate/partner prefix, its dynamic-divisor
definedness, and the high-register frame used to compose the two certified
`touchBody` calls without unfolding either emitted multiplier body.
-/

namespace LeanCompCert.Ports.Section413G1Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.InstrBlock (srun srun_lt_of_lt)
open LeanCompCert.Ports.Section413G1Program

def passBGateS : List Instr := passBGateBody.map scalarOf

theorem passBGateBody_lift : passBGateBody = lift passBGateS := by
  simp [passBGateBody, passBGateS, scalarOf, lift]

theorem passBGateS_spec (k : Nat) (s : RegState) (z : TSel)
    (hs : ∀ j, s j < M) (h31 : s 31 = z.X) (h34 : s 34 = z.inB)
    (h38 : s 38 = z.rB) (hB : z.inB ≤ 1) (hrB : z.rB ≠ 0) :
    let f := srun k s passBGateS
    let g1 := bnat (z.X % z.rB = 0) *
      bnat (z.rB * z.rB % M ≤ z.X) * z.inB
    let q2 := z.X / z.rB
    let g2 := g1 * (1 - bnat (q2 = z.rB))
    f 214 = g1 ∧ f 215 = q2 ∧ f 218 = g2 := by
  have hXM : z.X < M := by rw [← h31]; exact hs 31
  have hrM : z.rB < M := by rw [← h38]; exact hs 38
  have hrpos : 0 < z.rB := Nat.pos_of_ne_zero hrB
  have hremM : z.X % z.rB < M := Nat.lt_trans (Nat.mod_lt _ hrpos) hrM
  have hqM : z.X / z.rB < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hXM
  let a := bnat (z.X % z.rB = 0)
  let b := bnat (z.rB * z.rB % M ≤ z.X)
  let g1 := a * b * z.inB
  have ha : a ≤ 1 := bnat_le_one _
  have hb : b ≤ 1 := bnat_le_one _
  have hab : a * b ≤ 1 := by simpa using Nat.mul_le_mul ha hb
  have hg1 : g1 ≤ 1 := by simpa [g1] using Nat.mul_le_mul hab hB
  have hg1M : g1 < M := Nat.lt_of_le_of_lt hg1 (by decide)
  have hg2M : g1 * (1 - bnat (z.X / z.rB = z.rB)) < M := by
    have hc : 1 - bnat (z.X / z.rB = z.rB) ≤ 1 := by
      have := bnat_le_one (z.X / z.rB = z.rB)
      omega
    exact Nat.lt_of_le_of_lt (by simpa using Nat.mul_le_mul hg1 hc) (by decide)
  have hsub1 : (1 + (M - 1)) % M = 0 := by decide
  simp only [passBGateS, passBGateBody, scalarOf, List.map_cons, List.map_nil, srun,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, if_true, if_false, Nat.reduceEqDiff, h31, h34, h38,
    hrB, Nat.mod_eq_of_lt hremM, Nat.mod_eq_of_lt hqM]
  rcases (by omega : z.inB = 0 ∨ z.inB = 1) with hIn | hIn <;>
    by_cases hp : z.X % z.rB = 0 <;>
    by_cases hb' : z.rB * z.rB % M ≤ z.X <;>
    by_cases he : z.X / z.rB = z.rB <;>
    simp [bnat, hIn, hp, hb', he, one_mod_M, hsub1]

theorem passBGateS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 210 ∨ 218 < j) : srun k s passBGateS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [passBGateS, passBGateBody, scalarOf, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp only [InstrBlock.sdest] <;> omega

theorem passBGateS_defined (k : Nat) (s : RegState) (h38 : s 38 ≠ 0) :
    InstrBlock.SAllDefined k s passBGateS := by
  simp [passBGateS, passBGateBody, scalarOf, InstrBlock.SAllDefined,
    InstrBlock.SDefined, InstrBlock.sdest, InstrBlock.sval, denoteOperand,
    denoteOp, RegState.set, h38]

theorem passBGateBody_defined (len k : Nat) (st : AState)
    (h38 : st.regs 38 ≠ 0) : AllDefined len k st passBGateBody := by
  rw [passBGateBody_lift, allDefined_lift]
  exact passBGateS_defined k st.regs h38

set_option maxRecDepth 4000 in
theorem touchBody_high_frame (c : Cfg) (k g dSlot j : Nat) (st : AState)
    (hj : (20 ≤ j ∧ j < 40) ∨ 209 < j)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2) :
    (arun k st (c.touchBody g dSlot)).regs j = st.regs j := by
  let L := touchLoadState c g dSlot st
  let P : AState := ⟨srun k L.regs (touchProductS g), L.arr⟩
  let T0 : AState := ⟨srun k P.regs (touchTermS g), P.arr⟩
  let T := T0.writeReg 186 (T0.arr (T0.regs 194))
  let D : AState := ⟨srun k T.regs (touchDeltaS g), T.arr⟩
  have hL : arun k st (c.touchLoadBody g dSlot) = L :=
    touchLoadBody_run c k g dSlot st hP1 hP2
  have hbody : arun k st (c.touchBody g dSlot) =
      arun k D (c.touchStoreBody g) := by
    simp only [Cfg.touchBody, arun_append, hL, Cfg.touchTermBody]
    rw [touchProductBody_lift, arun_lift, touchTermScalarBody_lift, arun_lift,
      touchMuLoadBody_run, touchDeltaBody_lift, arun_lift]
  have hLj : L.regs j = st.regs j := by
    simp [L, touchLoadState, AState.writeReg, show j ≠ 180 by omega,
      show j ≠ 181 by omega, show j ≠ 191 by omega,
      show j ≠ 192 by omega, show j ≠ 194 by omega]
  have hPj : P.regs j = L.regs j :=
    touchProductS_external_frame k L.regs g j
      (by simp [CmulExternal, rViol]; omega) (by omega) (by omega) (by omega)
  have hT0j : T0.regs j = P.regs j :=
    touchTermS_frame k P.regs g j (by omega) (by omega) (by omega)
      (by simp [rViol]; omega)
  have hTj : T.regs j = T0.regs j := by simp [T, AState.writeReg]; omega
  have hDj : D.regs j = T.regs j :=
    touchDeltaS_frame k T.regs g j (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by simp [rViol]; omega)
  rw [hbody, touchStoreBody_regs_frame c k g j D (by omega) (by omega)
    (by omega) (by omega), hDj, hTj, hT0j, hPj, hLj]

theorem passBGateBody_obs (k : Nat) (st : AState) :
    obsT (arun k st passBGateBody) = obsT st := by
  rw [passBGateBody_lift, arun_lift]
  change
    ({ viol := srun k st.regs passBGateS rViol,
       res := srun k st.regs passBGateS 2,
       sq := srun k st.regs passBGateS 3,
       par := srun k st.regs passBGateS 4,
       sigma := srun k st.regs passBGateS 5,
       wLo := srun k st.regs passBGateS 6,
       wHi := srun k st.regs passBGateS 7,
       wwLo := srun k st.regs passBGateS 8,
       wwHi := srun k st.regs passBGateS 9,
       dLo := srun k st.regs passBGateS 10,
       dHi := srun k st.regs passBGateS 11,
       gLo := srun k st.regs passBGateS 12,
       gHi := srun k st.regs passBGateS 13, arr := st.arr } : TState) = obsT st
  rw [TState.mk.injEq]
  simp only [obsT]
  exact ⟨passBGateS_frame k st.regs rViol (by simp [rViol]),
    passBGateS_frame k st.regs 2 (by omega),
    passBGateS_frame k st.regs 3 (by omega),
    passBGateS_frame k st.regs 4 (by omega),
    passBGateS_frame k st.regs 5 (by omega),
    passBGateS_frame k st.regs 6 (by omega),
    passBGateS_frame k st.regs 7 (by omega),
    passBGateS_frame k st.regs 8 (by omega),
    passBGateS_frame k st.regs 9 (by omega),
    passBGateS_frame k st.regs 10 (by omega),
    passBGateS_frame k st.regs 11 (by omega),
    passBGateS_frame k st.regs 12 (by omega),
    passBGateS_frame k st.regs 13 (by omega), trivial⟩

theorem passBBody_run (c : Cfg) (k : Nat) (st : AState) :
    arun k st c.passBBody =
      arun k (arun k (arun k st passBGateBody) (c.touchBody 214 38))
        (c.touchBody 218 215) := by
  simp only [Cfg.passBBody, arun_append]

theorem passBBody_selector_frame (c : Cfg) (k : Nat) (st : AState) (j : Nat)
    (hj : 20 ≤ j ∧ j < 40) (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2) :
    (arun k st c.passBBody).regs j = st.regs j := by
  rw [passBBody_run,
    touchBody_high_frame c k 218 215 j _ (Or.inl hj) hP1 hP2,
    touchBody_high_frame c k 214 38 j _ (Or.inl hj) hP1 hP2,
    passBGateBody_lift, arun_lift]
  change srun k st.regs passBGateS j = st.regs j
  exact passBGateS_frame k st.regs j (Or.inl (by omega))

theorem tpassB_eq (c : Cfg) (z : TSel) (t : TState) :
    c.tpassB z t =
      let g1 := bnat (z.X % z.rB = 0) *
        bnat (z.rB * z.rB % M ≤ z.X) * z.inB
      let q2 := z.X / z.rB
      let g2 := g1 * (1 - bnat (q2 = z.rB))
      c.ttouch g2 q2 (c.ttouch g1 z.rB t) := rfl

theorem tsel_rB_ne_zero (c : Cfg) (idx : Nat) : (c.tsel idx).rB ≠ 0 := by
  let rBr := tsub ((tsub idx c.phase1) % c.p) c.s
  have hrM : rBr < M := by
    dsimp only [rBr, tsub]
    exact Nat.mod_lt _ (by decide)
  change (bnat (rBr = 0) + rBr) % M ≠ 0
  by_cases hr : rBr = 0
  · simp [hr, bnat, one_mod_M]
  · rw [show bnat (rBr = 0) = 0 by simp [bnat, hr], Nat.zero_add,
      Nat.mod_eq_of_lt hrM]
    exact hr

theorem tsel_inB_le_one (c : Cfg) (idx : Nat) : (c.tsel idx).inB ≤ 1 := by
  simp only [Cfg.tsel]
  have h1 := bnat_le_one (c.s + 1 ≤ (tsub idx c.phase1) % c.p)
  have h2 := bnat_le_one ((tsub idx c.phase1) % c.p ≤ 2 * c.s)
  have h3 := bnat_le_one (idx < c.phase1)
  have hP2 : 1 - bnat (idx < c.phase1) ≤ 1 := by omega
  have h12 : bnat (c.s + 1 ≤ (tsub idx c.phase1) % c.p) *
      bnat ((tsub idx c.phase1) % c.p ≤ 2 * c.s) ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul h1 h2
  simpa only [Nat.one_mul] using Nat.mul_le_mul h12 hP2

theorem tsel_isF_le_one (c : Cfg) (idx : Nat) : (c.tsel idx).isF ≤ 1 := by
  simp only [Cfg.tsel]
  have h1 := bnat_le_one ((tsub idx c.phase1) % c.p = 2 * c.s + 1)
  have h2 := bnat_le_one (idx < c.phase1)
  have hP2 : 1 - bnat (idx < c.phase1) ≤ 1 := by omega
  simpa only [Nat.one_mul] using Nat.mul_le_mul h1 hP2

theorem Admissible.passBProducts (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) :
    let z := c.tsel idx
    let g1 := bnat (z.X % z.rB = 0) *
      bnat (z.rB * z.rB % M ≤ z.X) * z.inB
    let q2 := z.X / z.rB
    let g2 := g1 * (1 - bnat (q2 = z.rB))
    g1 * z.rB ≤ c.cap ∧ g2 * q2 ≤ c.cap := by
  let z := c.tsel idx
  let g1 := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q2 := z.X / z.rB
  let g2 := g1 * (1 - bnat (q2 = z.rB))
  change g1 * z.rB ≤ c.cap ∧ g2 * q2 ≤ c.cap
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  by_cases hphase : idx < c.phase1
  · have hzinB : z.inB = 0 := by simp [z, Cfg.tsel, hphase, bnat]
    have hg1 : g1 = 0 := by simp [g1, hzinB]
    have hg2 : g2 = 0 := by simp [g2, hg1]
    simp [hg1, hg2]
  · have hphasele : c.phase1 ≤ idx := Nat.le_of_not_gt hphase
    have hsubM : idx - c.phase1 < M := by omega
    have hsub : tsub idx c.phase1 = idx - c.phase1 := by
      rw [tsub]
      have heq : idx + (M - c.phase1) = (idx - c.phase1) + M := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsubM]
    let pX := (idx - c.phase1) % c.p
    have hpXlt : pX < c.p := Nat.mod_lt _ (p_pos c)
    have hpXM : pX < M := Nat.lt_trans hpXlt hPM
    by_cases hlo : c.s + 1 ≤ pX
    · by_cases hhi : pX ≤ 2 * c.s
      · have hsM : c.s < M := by omega
        have hsle : c.s ≤ pX := by omega
        have hdiffM : pX - c.s < M := by omega
        have htsub : tsub pX c.s = pX - c.s := by
          rw [tsub]
          have heq : pX + (M - c.s) = (pX - c.s) + M := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hdiffM]
        have hdiff0 : pX - c.s ≠ 0 := by omega
        have hzrB : z.rB = pX - c.s := by
          simp [z, Cfg.tsel, hsub, pX, htsub, hdiff0, bnat,
            Nat.mod_eq_of_lt hdiffM]
        have hzinB : z.inB = 1 := by
          simp [z, Cfg.tsel, hsub, pX, hlo, hhi, hphase, bnat]
        have hx0 : (idx - c.phase1) / c.p < c.cap := by
          apply (Nat.div_lt_iff_lt_mul (p_pos c)).mpr
          simp only [Cfg.loopCount] at hidx
          omega
        have hcapM : c.cap + 1 < M := by
          have hcapArr : c.cap + 1 < c.arrayLen := by
            simp [Cfg.arrayLen]
          exact Nat.lt_trans hcapArr hc.arrayLt
        have hzX : z.X = (idx - c.phase1) / c.p + 1 := by
          simp [z, Cfg.tsel, hsub, Nat.mod_eq_of_lt (by omega :
            (idx - c.phase1) / c.p + 1 < M)]
        have hg1le : g1 ≤ 1 := by
          have ha := bnat_le_one (z.X % z.rB = 0)
          have hb := bnat_le_one (z.rB * z.rB % M ≤ z.X)
          have hab : bnat (z.X % z.rB = 0) *
              bnat (z.rB * z.rB % M ≤ z.X) ≤ 1 := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul ha hb
          simpa [g1, hzinB] using hab
        have hrBcap : z.rB ≤ c.cap := by
          have hsCap := sqrt_le_self c.cap
          have hdiffle : pX - c.s ≤ c.s := by omega
          calc
            z.rB = pX - c.s := hzrB
            _ ≤ c.s := hdiffle
            _ ≤ c.cap := hsCap
        have hg1r : g1 * z.rB ≤ c.cap := by
          have := Nat.mul_le_mul hg1le hrBcap
          simpa only [Nat.one_mul] using this
        have hqcap : q2 ≤ c.cap := by
          calc
            q2 = z.X / z.rB := rfl
            _ ≤ z.X := Nat.div_le_self _ _
            _ = (idx - c.phase1) / c.p + 1 := hzX
            _ ≤ c.cap := by omega
        have hg2le : g2 ≤ 1 := by
          have hc2 : 1 - bnat (q2 = z.rB) ≤ 1 := by
            have := bnat_le_one (q2 = z.rB)
            omega
          have := Nat.mul_le_mul hg1le hc2
          simpa [g2] using this
        have hg2q : g2 * q2 ≤ c.cap := by
          have := Nat.mul_le_mul hg2le hqcap
          simpa only [Nat.one_mul] using this
        exact ⟨hg1r, hg2q⟩
      · have hzinB : z.inB = 0 := by
          simp [z, Cfg.tsel, hsub, pX, hhi, bnat]
        have hg1 : g1 = 0 := by simp [g1, hzinB]
        have hg2 : g2 = 0 := by simp [g2, hg1]
        simp [hg1, hg2]
    · have hzinB : z.inB = 0 := by
        simp [z, Cfg.tsel, hsub, pX, hlo, bnat]
      have hg1 : g1 = 0 := by simp [g1, hzinB]
      have hg2 : g2 = 0 := by simp [g2, hg1]
      simp [hg1, hg2]

/-! Keep the two large `ttouch` terms behind the observation theorem while
composing them.  Re-simplifying their transparent definitions here makes Lean
normalize two copies of the complete interval multiplier and is needlessly
expensive. -/

set_option maxHeartbeats 500000 in
theorem passBBody_obs (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (h31 : st.regs 31 = z.X) (h34 : st.regs 34 = z.inB)
    (h38 : st.regs 38 = z.rB) (hB : z.inB ≤ 1) (hrB : z.rB ≠ 0)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2) :
    obsT (arun k st c.passBBody) = c.tpassB z (obsT st) := by
  let G := arun k st passBGateBody
  let U := arun k G (c.touchBody 214 38)
  let g1 := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q2 := z.X / z.rB
  let g2 := g1 * (1 - bnat (q2 = z.rB))
  have hgate := passBGateS_spec k st.regs z hs h31 h34 h38 hB hrB
  dsimp only at hgate
  have hG214 : G.regs 214 = g1 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.1
  have hG215 : G.regs 215 = q2 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.2.1
  have hG218 : G.regs 218 = g2 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.2.2
  have hG38 : G.regs 38 = z.rB := by
    simpa only [G, passBGateBody_lift, arun_lift,
      passBGateS_frame k st.regs 38 (by omega)] using h38
  have hGobs : obsT G = obsT st := passBGateBody_obs k st
  have hGlt : ∀ j, G.regs j < M := arun_regs_lt k _ st hs harr
  have hGarr : ∀ i, G.arr i < M := arun_arr_lt k _ st hs harr
  have hUobs0 := touchBody_obs c k 214 38 G (by omega) hP1 hP2 hGlt hGarr
  have hUobs : obsT U = c.ttouch g1 z.rB (obsT st) := by
    calc
      obsT U = c.ttouch (G.regs 214) (G.regs 38) (obsT G) := hUobs0
      _ = c.ttouch g1 z.rB (obsT st) := by rw [hG214, hG38, hGobs]
  have hUdef : U = arun k G (c.touchBody 214 38) := rfl
  have hU215 : U.regs 215 = q2 := by
    calc
      U.regs 215 = (arun k G (c.touchBody 214 38)).regs 215 :=
        congrArg (fun x : AState => x.regs 215) hUdef
      _ = G.regs 215 := touchBody_high_frame c k 214 38 215 G (by omega) hP1 hP2
      _ = q2 := hG215
  have hU218 : U.regs 218 = g2 := by
    calc
      U.regs 218 = (arun k G (c.touchBody 214 38)).regs 218 :=
        congrArg (fun x : AState => x.regs 218) hUdef
      _ = G.regs 218 := touchBody_high_frame c k 214 38 218 G (by omega) hP1 hP2
      _ = g2 := hG218
  have hUlt : ∀ j, U.regs j < M := arun_regs_lt k _ G hGlt hGarr
  have hUarr : ∀ i, U.arr i < M := arun_arr_lt k _ G hGlt hGarr
  have hVobs0 := touchBody_obs c k 218 215 U (by omega) hP1 hP2 hUlt hUarr
  rw [passBBody_run]
  change obsT (arun k U (c.touchBody 218 215)) = _
  calc
    obsT (arun k U (c.touchBody 218 215)) =
        c.ttouch (U.regs 218) (U.regs 215) (obsT U) := hVobs0
    _ = c.ttouch g2 q2 (c.ttouch g1 z.rB (obsT st)) := by
      rw [hU218, hU215, hUobs]
    _ = c.tpassB z (obsT st) := (tpassB_eq c z (obsT st)).symm

/-- All three touch addresses are in the three-plane array as soon as the
gated base product is a candidate index.  This deliberately uses only
`Nat.mod_le`; it does not smuggle in a no-wrap assumption. -/
theorem touchAddrBounds (c : Cfg) (g d : Nat) (hgd : g * d ≤ c.cap) :
    c.touchBase g d < c.arrayLen ∧
      c.touchA1 g d < c.arrayLen ∧ c.touchA2 g d < c.arrayLen := by
  have hb : c.touchBase g d ≤ g * d := by
    simpa only [Cfg.touchBase] using Nat.mod_le (g * d) M
  have ha1 : c.touchA1 g d ≤ c.touchBase g d + c.plane1 := by
    simpa only [Cfg.touchA1] using
      Nat.mod_le (c.touchBase g d + c.plane1) M
  have ha2 : c.touchA2 g d ≤ c.touchBase g d + c.plane2 := by
    simpa only [Cfg.touchA2] using
      Nat.mod_le (c.touchBase g d + c.plane2) M
  simp only [Cfg.arrayLen, Cfg.plane1, Cfg.plane2] at *
  omega

theorem passBBody_defined (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M)
    (h31 : st.regs 31 = z.X) (h34 : st.regs 34 = z.inB)
    (h38 : st.regs 38 = z.rB) (hB : z.inB ≤ 1) (hrB : z.rB ≠ 0)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2)
    (hA11 : c.touchA1
      (bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB)
      z.rB < c.arrayLen)
    (hA12 : c.touchA2
      (bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB)
      z.rB < c.arrayLen)
    (hBase1 : c.touchBase
      (bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB)
      z.rB < c.arrayLen)
    (hA21 : c.touchA1
      ((bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB) *
        (1 - bnat (z.X / z.rB = z.rB))) (z.X / z.rB) < c.arrayLen)
    (hA22 : c.touchA2
      ((bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB) *
        (1 - bnat (z.X / z.rB = z.rB))) (z.X / z.rB) < c.arrayLen)
    (hBase2 : c.touchBase
      ((bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB) *
        (1 - bnat (z.X / z.rB = z.rB))) (z.X / z.rB) < c.arrayLen) :
    AllDefined c.arrayLen k st c.passBBody := by
  let G := arun k st passBGateBody
  let U := arun k G (c.touchBody 214 38)
  let g1 := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q2 := z.X / z.rB
  let g2 := g1 * (1 - bnat (q2 = z.rB))
  have hgate := passBGateS_spec k st.regs z hs h31 h34 h38 hB hrB
  dsimp only at hgate
  have hG214 : G.regs 214 = g1 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.1
  have hG215 : G.regs 215 = q2 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.2.1
  have hG218 : G.regs 218 = g2 := by
    simpa only [G, passBGateBody_lift, arun_lift] using hgate.2.2
  have hG38 : G.regs 38 = z.rB := by
    simpa only [G, passBGateBody_lift, arun_lift,
      passBGateS_frame k st.regs 38 (by omega)] using h38
  have hUdef : U = arun k G (c.touchBody 214 38) := rfl
  have hU215 : U.regs 215 = q2 := by
    calc
      U.regs 215 = (arun k G (c.touchBody 214 38)).regs 215 :=
        congrArg (fun x : AState => x.regs 215) hUdef
      _ = G.regs 215 := touchBody_high_frame c k 214 38 215 G (by omega) hP1 hP2
      _ = q2 := hG215
  have hU218 : U.regs 218 = g2 := by
    calc
      U.regs 218 = (arun k G (c.touchBody 214 38)).regs 218 :=
        congrArg (fun x : AState => x.regs 218) hUdef
      _ = G.regs 218 := touchBody_high_frame c k 214 38 218 G (by omega) hP1 hP2
      _ = g2 := hG218
  rw [show c.passBBody = passBGateBody ++
      (c.touchBody 214 38 ++ c.touchBody 218 215) by
        simp [Cfg.passBBody, List.append_assoc], AllDefined_append]
  refine ⟨passBGateBody_defined c.arrayLen k st (by rw [h38]; exact hrB), ?_⟩
  rw [AllDefined_append]
  refine ⟨touchBody_defined c k 214 38 G hP1 hP2 ?_ ?_ ?_, ?_⟩
  · simpa only [hG214, hG38] using hA11
  · simpa only [hG214, hG38] using hA12
  · simpa only [hG214, hG38] using hBase1
  · apply touchBody_defined c k 218 215 U hP1 hP2
    · simpa only [hU218, hU215] using hA21
    · simpa only [hU218, hU215] using hA22
    · simpa only [hU218, hU215] using hBase2

theorem selTrialPassAWeight_regs (c : Cfg) (idx : Nat) (st : AState) (j : Nat)
    (hj : 20 ≤ j ∧ j < 40) :
    (arun idx st ((((c.selBody ++ trialBody) ++ passABody) ++
      c.weightBody))).regs j = srun idx st.regs (selS c) j := by
  rw [arun_append, weightBody_decode_frame c idx _ j hj,
    selTrialPassA_regs c idx st j (by omega)]

theorem selTrialPassAWeightPassB_regs (c : Cfg) (idx : Nat) (st : AState)
    (j : Nat) (hj : 20 ≤ j ∧ j < 40)
    (hP1 : c.plane1 % M = c.plane1) (hP2 : c.plane2 % M = c.plane2) :
    (arun idx st (((((c.selBody ++ trialBody) ++ passABody) ++
      c.weightBody)) ++ c.passBBody)).regs j = srun idx st.regs (selS c) j := by
  rw [arun_append, passBBody_selector_frame c idx _ j hj hP1 hP2,
    selTrialPassAWeight_regs c idx st j hj]

theorem selTrialPassAWeightPassB_selector (c : Cfg) (hc : Admissible c)
    (idx : Nat) (hidx : idx < c.loopCount) (st : AState) :
    let P := arun idx st (((((c.selBody ++ trialBody) ++ passABody) ++
      c.weightBody)) ++ c.passBBody)
    P.regs 31 = (c.tsel idx).X ∧ P.regs 35 = (c.tsel idx).isF := by
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  have hP1lt : c.plane1 < M := by
    exact Nat.lt_trans (by simp [Cfg.plane1, Cfg.arrayLen]) hc.arrayLt
  have hP2lt : c.plane2 < M := by
    exact Nat.lt_trans (by simp [Cfg.plane2, Cfg.arrayLen]) hc.arrayLt
  change srun idx st.regs (selS c) 31 = (c.tsel idx).X at hz31
  change srun idx st.regs (selS c) 35 = (c.tsel idx).isF at hz35
  exact ⟨(selTrialPassAWeightPassB_regs c idx st 31 (by omega)
      (Nat.mod_eq_of_lt hP1lt) (Nat.mod_eq_of_lt hP2lt)).trans hz31,
    (selTrialPassAWeightPassB_regs c idx st 35 (by omega)
      (Nat.mod_eq_of_lt hP1lt) (Nat.mod_eq_of_lt hP2lt)).trans hz35⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 700000 in
theorem selTrialPassAWeightPassB_obs (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (h1 : st.regs 1 = 0) (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) :
    obsT (arun idx st (((((c.selBody ++ trialBody) ++ passABody) ++
      c.weightBody)) ++ c.passBBody)) =
      c.tpassB (c.tsel idx)
        (tweight (c.tsel idx)
          (tpassA (c.tsel idx) (ttrial (c.tsel idx) (obsT st)))) := by
  let W := arun idx st (((c.selBody ++ trialBody) ++ passABody) ++ c.weightBody)
  let z := c.tsel idx
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 31 = z.X at hz31
  change srun idx st.regs (selS c) 34 = z.inB at hz34
  change srun idx st.regs (selS c) 38 = z.rB at hz38
  have hW31 : W.regs 31 = z.X :=
    (selTrialPassAWeight_regs c idx st 31 (by omega)).trans hz31
  have hW34 : W.regs 34 = z.inB :=
    (selTrialPassAWeight_regs c idx st 34 (by omega)).trans hz34
  have hW38 : W.regs 38 = z.rB :=
    (selTrialPassAWeight_regs c idx st 38 (by omega)).trans hz38
  have hWlt : ∀ j, W.regs j < M := arun_regs_lt idx _ st hs harr
  have hWarr : ∀ i, W.arr i < M := arun_arr_lt idx _ st hs harr
  have hP1lt : c.plane1 < M := by
    have : c.plane1 < c.arrayLen := by simp [Cfg.plane1, Cfg.arrayLen]
    exact Nat.lt_trans this hc.arrayLt
  have hP2lt : c.plane2 < M := by
    have : c.plane2 < c.arrayLen := by simp [Cfg.plane2, Cfg.arrayLen]
    exact Nat.lt_trans this hc.arrayLt
  have hpb := passBBody_obs c idx W z hWlt hWarr hW31 hW34 hW38
    (tsel_inB_le_one c idx) (tsel_rB_ne_zero c idx)
    (Nat.mod_eq_of_lt hP1lt) (Nat.mod_eq_of_lt hP2lt)
  have hp := selTrialPassAWeight_obs c hc idx hidx st hs harr h1 hSq hPar
  change obsT W = tweight z (tpassA z (ttrial z (obsT st))) at hp
  rw [arun_append]
  rw [hp] at hpb
  exact hpb

set_option maxRecDepth 4000 in
theorem selTrialPassAWeightPassB_defined (c : Cfg) (hc : Admissible c)
    (idx : Nat) (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M) :
    AllDefined c.arrayLen idx st (((((c.selBody ++ trialBody) ++ passABody) ++
      c.weightBody)) ++ c.passBBody) := by
  let W := arun idx st (((c.selBody ++ trialBody) ++ passABody) ++ c.weightBody)
  let z := c.tsel idx
  let g1 := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q2 := z.X / z.rB
  let g2 := g1 * (1 - bnat (q2 = z.rB))
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 31 = z.X at hz31
  change srun idx st.regs (selS c) 34 = z.inB at hz34
  change srun idx st.regs (selS c) 38 = z.rB at hz38
  have hW31 : W.regs 31 = z.X :=
    (selTrialPassAWeight_regs c idx st 31 (by omega)).trans hz31
  have hW34 : W.regs 34 = z.inB :=
    (selTrialPassAWeight_regs c idx st 34 (by omega)).trans hz34
  have hW38 : W.regs 38 = z.rB :=
    (selTrialPassAWeight_regs c idx st 38 (by omega)).trans hz38
  have hWlt : ∀ j, W.regs j < M := arun_regs_lt idx _ st hs harr
  have hP1lt : c.plane1 < M := by
    have : c.plane1 < c.arrayLen := by simp [Cfg.plane1, Cfg.arrayLen]
    exact Nat.lt_trans this hc.arrayLt
  have hP2lt : c.plane2 < M := by
    have : c.plane2 < c.arrayLen := by simp [Cfg.plane2, Cfg.arrayLen]
    exact Nat.lt_trans this hc.arrayLt
  have hprod := Admissible.passBProducts c hc idx hidx
  dsimp only at hprod
  change g1 * z.rB ≤ c.cap ∧ g2 * q2 ≤ c.cap at hprod
  have ha1 := touchAddrBounds c g1 z.rB hprod.1
  have ha2 := touchAddrBounds c g2 q2 hprod.2
  rw [AllDefined_append]
  refine ⟨selTrialPassAWeight_defined c hc idx hidx st hs harr, ?_⟩
  apply passBBody_defined c idx W z hWlt hW31 hW34 hW38
    (tsel_inB_le_one c idx) (tsel_rB_ne_zero c idx)
    (Nat.mod_eq_of_lt hP1lt) (Nat.mod_eq_of_lt hP2lt)
  · exact ha1.2.1
  · exact ha1.2.2
  · exact ha1.1
  · exact ha2.2.1
  · exact ha2.2.2
  · exact ha2.1

end LeanCompCert.Ports.Section413G1Denote
