import LeanCompCert.Ports.Section413G2Denote

/-!
# Section 4.1.3 G2 weight-stage denotation

This module proves the scalar certificate program implementing `tweight`.
The arithmetic is split into small blocks so Lean checks the denotation
quickly; the long finite sweep remains an external CompCert computation.
-/

namespace LeanCompCert.Ports.Section413G2Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.InstrBlock (sdest sval srun srun_append srun_lt_of_lt
  SDefined SAllDefined)
open LeanCompCert.Ports.Section413G2Program
open LeanCompCert.Ports.CDEMAbelScan (muxBody)

def weightAddrS : List Instr := weightAddrBody.map scalarOf
def weightCalcS : List Instr := weightCalcBody.map scalarOf

theorem weightAddrBody_lift : weightAddrBody = lift weightAddrS := by
  simp [weightAddrBody, weightAddrS, scalarOf, lift]

theorem weightCalcBody_lift : weightCalcBody = lift weightCalcS := by
  simp [weightCalcBody, weightCalcS, scalarOf, lift]

theorem weightAddrS_spec (k : Nat) (s : RegState) :
    srun k s weightAddrS 71 = s 33 * s 31 % M := by
  simp [weightAddrS, weightAddrBody, scalarOf, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set]

theorem weightAddrS_frame (k : Nat) (s : RegState) (j : Nat) (h71 : j ≠ 71) :
    srun k s weightAddrS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [weightAddrS, weightAddrBody, scalarOf, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl
  simp only [sdest]
  omega

theorem weightSig1_ne_zero (sigma : Nat) (hsigma : sigma < M) :
    (sigma + bnat (sigma = 0)) % M ≠ 0 := by
  by_cases h : sigma = 0
  · simp [h, bnat, show M ≠ 1 by decide]
  · have hpos : 0 < sigma := Nat.pos_of_ne_zero h
    simp [bnat, h, Nat.mod_eq_of_lt hsigma]

def weightFlagsS : List Instr :=
  [ .binop 73 .eq (.reg 72) (.lit 1)
  , .binop 74 .eq (.reg 72) (.lit 2)
  , .binop 75 .urem (.reg 31) (.lit 2)
  , .binop 76 .eq (.reg 75) (.lit 1)
  , .binop 77 .add (.reg 73) (.reg 74)
  , .binop 77 .mul (.reg 77) (.reg 76)
  , .binop 77 .mul (.reg 77) (.reg 33)
  , .binop 78 .eq (.reg 5) (.lit 0)
  , .binop 79 .add (.reg 5) (.reg 78) ]

def weightQuotG (scale scale1 : Nat) : List Instr :=
  [ .binop 80 .udiv (.lit scale) (.reg 79)
  , .binop 81 .add (.reg 79) (.lit scale1)
  , .binop 81 .udiv (.reg 81) (.reg 79)
  , .binop 82 .sub (.lit 0) (.reg 81)
  , .binop 83 .sub (.lit 0) (.reg 80) ]

def weightQuotS : List Instr := weightQuotG SCALE (SCALE - 1)

def weightRawS : List Instr :=
  [ .binop 84 .mul (.reg 73) (.reg 80)
  , .binop 85 .mul (.reg 74) (.reg 82)
  , .binop 86 .add (.reg 84) (.reg 85)
  , .binop 86 .mul (.reg 86) (.reg 77)
  , .binop 87 .mul (.reg 73) (.reg 81)
  , .binop 88 .mul (.reg 74) (.reg 83)
  , .binop 89 .add (.reg 87) (.reg 88)
  , .binop 89 .mul (.reg 89) (.reg 77) ]

theorem weightCalcS_decomp :
    weightCalcS = weightFlagsS ++ weightQuotS ++ weightRawS := by
  simp [weightCalcS, weightCalcBody, weightFlagsS, weightQuotS, weightRawS,
    weightQuotG, scalarOf]

theorem weightFlagsS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M) (h5 : s 5 = t.sigma) (h31 : s 31 = z.X)
    (h33 : s 33 = z.isW) (h72 : s 72 = t.arr (z.isW * z.X % M))
    (hW : z.isW ≤ 1) :
    let f := srun k s weightFlagsS
    let muX := t.arr (z.isW * z.X % M)
    f 73 = bnat (muX = 1) ∧ f 74 = bnat (muX = 2) ∧
      f 77 = (bnat (muX = 1) + bnat (muX = 2)) *
        bnat (z.X % 2 = 1) * z.isW ∧
      f 79 = (t.sigma + bnat (t.sigma = 0)) % M := by
  have hsig : t.sigma < M := by rw [← h5]; exact hs 5
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let odd := bnat (z.X % 2 = 1)
  have hPN : isP + isM ≤ 1 := by
    dsimp only [isP, isM, muX]
    by_cases hp : t.arr (z.isW * z.X % M) = 1 <;>
      by_cases hm : t.arr (z.isW * z.X % M) = 2 <;>
      simp [bnat, hp, hm] at * <;> omega
  have hOdd : odd ≤ 1 := bnat_le_one _
  have hM1 : (1 : Nat) < M := by decide
  have hPNM : isP + isM < M := Nat.lt_of_le_of_lt hPN hM1
  have hPO : (isP + isM) * odd < M := by
    have h := Nat.mul_le_mul hPN hOdd
    exact Nat.lt_of_le_of_lt (by simpa using h) hM1
  have hLive : (isP + isM) * odd * z.isW < M := by
    have hPO1 : (isP + isM) * odd ≤ 1 := by
      simpa using Nat.mul_le_mul hPN hOdd
    have h := Nat.mul_le_mul hPO1 hW
    exact Nat.lt_of_le_of_lt (by simpa using h) hM1
  have hrem : z.X % 2 % M = z.X % 2 := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans (Nat.mod_lt z.X (by decide)) (by decide)
  simp only [weightFlagsS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff,
    h5, h31, h33, h72, one_mod_M, zero_mod_M,
    show 2 % M = 2 by decide, hrem]
  change
    _ = isP ∧ _ = isM ∧ _ = (isP + isM) * odd * z.isW ∧ _ = _
  dsimp only [isP, isM, odd, muX]
  have hWM : z.isW % M = z.isW :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hW hM1)
  by_cases hp : t.arr (z.isW * z.X % M) = 1 <;>
    by_cases hm : t.arr (z.isW * z.X % M) = 2 <;>
    by_cases ho : z.X % 2 = 1 <;>
    simp [bnat, hp, hm, ho, hWM] at * <;> omega

theorem weightQuotG_spec (k : Nat) (s : RegState) (sig1 scale scale1 : Nat)
    (hsig : s 79 = sig1) (h0 : sig1 ≠ 0)
    (hScale : scale % M = scale) (hScaleM : scale < M)
    (hScale1 : scale1 % M = scale1) :
    let f := srun k s (weightQuotG scale scale1)
    f 80 = scale / sig1 ∧
      f 81 = ((sig1 + scale1) % M) / sig1 ∧
      f 82 = tsub 0 (((sig1 + scale1) % M) / sig1) ∧
      f 83 = tsub 0 (scale / sig1) := by
  have hF : scale / sig1 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hScaleM
  have hC : ((sig1 + scale1) % M) / sig1 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ M_pos)
  simp only [weightQuotG, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff,
    hsig, h0, hScale, hScale1, zero_mod_M, tsub]
  simp only [Nat.mod_eq_of_lt hF, Nat.mod_eq_of_lt hC]
  simp only [true_and]

theorem weightQuotS_spec (k : Nat) (s : RegState) (sig1 : Nat)
    (hsig : s 79 = sig1) (h0 : sig1 ≠ 0) :
    let f := srun k s weightQuotS
    f 80 = SCALE / sig1 ∧
      f 81 = ((sig1 + (SCALE - 1)) % M) / sig1 ∧
      f 82 = tsub 0 (((sig1 + (SCALE - 1)) % M) / sig1) ∧
      f 83 = tsub 0 (SCALE / sig1) := by
  exact weightQuotG_spec k s sig1 SCALE (SCALE - 1) hsig h0
    (by decide) (by decide) (by decide)

theorem weightRawS_spec (k : Nat) (s : RegState)
    (isP isM live magF magC negC negF : Nat)
    (h73 : s 73 = isP) (h74 : s 74 = isM) (h77 : s 77 = live)
    (h80 : s 80 = magF) (h81 : s 81 = magC)
    (h82 : s 82 = negC) (h83 : s 83 = negF)
    (hP : isP ≤ 1) (hN : isM ≤ 1) (_hLive : live < M)
    (hF : magF < M) (hC : magC < M) (hNC : negC < M) (hNF : negF < M) :
    let f := srun k s weightRawS
    f 86 = (isP * magF + isM * negC) % M * live % M ∧
      f 89 = (isP * magC + isM * negF) % M * live % M := by
  have hPF : isP * magF < M := by
    rcases (by omega : isP = 0 ∨ isP = 1) with rfl | rfl <;> simp [hF, M_pos]
  have hPC : isP * magC < M := by
    rcases (by omega : isP = 0 ∨ isP = 1) with rfl | rfl <;> simp [hC, M_pos]
  have hNNC : isM * negC < M := by
    rcases (by omega : isM = 0 ∨ isM = 1) with rfl | rfl <;> simp [hNC, M_pos]
  have hNNF : isM * negF < M := by
    rcases (by omega : isM = 0 ∨ isM = 1) with rfl | rfl <;> simp [hNF, M_pos]
  simp only [weightRawS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff,
    h73, h74, h77, h80, h81, h82, h83, Nat.mod_eq_of_lt hPF,
    Nat.mod_eq_of_lt hPC, Nat.mod_eq_of_lt hNNC, Nat.mod_eq_of_lt hNNF]
  simp only [true_and]

theorem weightFlagsS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 73 ∨ 79 < j) : srun k s weightFlagsS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [weightFlagsS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem weightQuotS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 80 ∨ 83 < j) : srun k s weightQuotS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [weightQuotS, weightQuotG, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem weightRawS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 84 ∨ 89 < j) : srun k s weightRawS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [weightRawS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem weightCalcS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 73 ∨ 89 < j) : srun k s weightCalcS j = s j := by
  rw [weightCalcS_decomp, srun_append, srun_append,
    weightRawS_frame k _ j (by omega), weightQuotS_frame k _ j (by omega),
    weightFlagsS_frame k s j (by omega)]

theorem weightCalcS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M) (h5 : s 5 = t.sigma) (h31 : s 31 = z.X)
    (h33 : s 33 = z.isW) (h72 : s 72 = t.arr (z.isW * z.X % M))
    (hW : z.isW ≤ 1) :
    let f := srun k s weightCalcS
    let muX := t.arr (z.isW * z.X % M)
    let isP := bnat (muX = 1)
    let isM := bnat (muX = 2)
    let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
    let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
    let magF := SCALE / sig1
    let magC := ((sig1 + (SCALE - 1)) % M) / sig1
    f 86 = (isP * magF + isM * tsub 0 magC) % M * live % M ∧
      f 89 = (isP * magC + isM * tsub 0 magF) % M * live % M := by
  let a := srun k s weightFlagsS
  let b := srun k a weightQuotS
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
  let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  have ha := weightFlagsS_spec k s z t hs h5 h31 h33 h72 hW
  dsimp only at ha
  rcases ha with ⟨ha73, ha74, ha77, ha79⟩
  change a 73 = isP at ha73
  change a 74 = isM at ha74
  change a 77 = live at ha77
  change a 79 = sig1 at ha79
  have hsigM : t.sigma < M := by rw [← h5]; exact hs 5
  have hsig0 : sig1 ≠ 0 := weightSig1_ne_zero t.sigma hsigM
  have hbq := weightQuotS_spec k a sig1 ha79 hsig0
  dsimp only at hbq
  rcases hbq with ⟨hb80, hb81, hb82, hb83⟩
  change b 80 = magF at hb80
  change b 81 = magC at hb81
  change b 82 = tsub 0 magC at hb82
  change b 83 = tsub 0 magF at hb83
  have hab (j : Nat) (hj : j < 80) : b j = a j :=
    weightQuotS_frame k a j (by omega)
  have hb73 : b 73 = isP := (hab 73 (by omega)).trans ha73
  have hb74 : b 74 = isM := (hab 74 (by omega)).trans ha74
  have hb77 : b 77 = live := (hab 77 (by omega)).trans ha77
  have hblt : ∀ j, b j < M :=
    srun_lt_of_lt k _ a (srun_lt_of_lt k _ s hs)
  have hLive : live < M := by rw [← hb77]; exact hblt 77
  have hF : magF < M := by rw [← hb80]; exact hblt 80
  have hC : magC < M := by rw [← hb81]; exact hblt 81
  have hNC : tsub 0 magC < M := by rw [← hb82]; exact hblt 82
  have hNF : tsub 0 magF < M := by rw [← hb83]; exact hblt 83
  have hr := weightRawS_spec k b isP isM live magF magC (tsub 0 magC)
    (tsub 0 magF) hb73 hb74 hb77 hb80 hb81 hb82 hb83
    (bnat_le_one _) (bnat_le_one _) hLive hF hC hNC hNF
  rw [weightCalcS_decomp, srun_append, srun_append]
  exact hr

def weightFinishS : List Instr :=
  muxS 6 33 86 6 90 ++ muxS 7 33 89 7 90 ++
    cmulS 33 6 7 6 7 98 99 ++ muxS 8 33 98 8 90 ++ muxS 9 33 99 9 90

theorem weightFinishBody_lift : weightFinishBody = lift weightFinishS := by
  simp only [weightFinishBody, weightFinishS, muxBody_lift, cmulBody_lift,
    lift, List.map_append]

theorem weightFinishS_decomp :
    weightFinishS = muxS 6 33 86 6 90 ++ muxS 7 33 89 7 90 ++
      cmulS 33 6 7 6 7 98 99 ++ muxS 8 33 98 8 90 ++
      muxS 9 33 99 9 90 := rfl

theorem weightFinishS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : CmulExternal j) (h6 : j ≠ 6) (h7 : j ≠ 7) (h8 : j ≠ 8)
    (h9 : j ≠ 9) (h90 : j ≠ 90) (h98 : j ≠ 98) (h99 : j ≠ 99) :
    srun k s weightFinishS j = s j := by
  rw [weightFinishS_decomp, srun_append, srun_append, srun_append, srun_append,
    muxS_frame k _ 9 33 99 9 90 j h9 h90,
    muxS_frame k _ 8 33 98 8 90 j h8 h90,
    cmulS_external_frame k _ 33 6 7 6 7 98 99 j hj h98 h99,
    muxS_frame k _ 7 33 89 7 90 j h7 h90,
    muxS_frame k s 6 33 86 6 90 j h6 h90]

set_option maxRecDepth 2000 in
theorem weightFinishS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M) (hV : s rViol = t.viol)
    (h6 : s 6 = t.wLo) (h7 : s 7 = t.wHi)
    (h8 : s 8 = t.wwLo) (h9 : s 9 = t.wwHi)
    (h33 : s 33 = z.isW) (h86 : s 86 =
      let muX := t.arr (z.isW * z.X % M)
      let isP := bnat (muX = 1)
      let isM := bnat (muX = 2)
      let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
      let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
      let magF := SCALE / sig1
      let magC := ((sig1 + (SCALE - 1)) % M) / sig1
      (isP * magF + isM * tsub 0 magC) % M * live % M)
    (h89 : s 89 =
      let muX := t.arr (z.isW * z.X % M)
      let isP := bnat (muX = 1)
      let isM := bnat (muX = 2)
      let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
      let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
      let magF := SCALE / sig1
      let magC := ((sig1 + (SCALE - 1)) % M) / sig1
      (isP * magC + isM * tsub 0 magF) % M * live % M)
    (hW : z.isW ≤ 1) :
    let f := srun k s weightFinishS
    f rViol = (tweight z t).viol ∧ f 6 = (tweight z t).wLo ∧
      f 7 = (tweight z t).wHi ∧ f 8 = (tweight z t).wwLo ∧
      f 9 = (tweight z t).wwHi := by
  let a := srun k s (muxS 6 33 86 6 90)
  let b := srun k a (muxS 7 33 89 7 90)
  let p := srun k b (cmulS 33 6 7 6 7 98 99)
  let d := srun k p (muxS 8 33 98 8 90)
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
  let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  let rawLo := (isP * magF + isM * tsub 0 magC) % M * live % M
  let rawHi := (isP * magC + isM * tsub 0 magF) % M * live % M
  let wLo := if z.isW = 1 then rawLo else t.wLo
  let wHi := if z.isW = 1 then rawHi else t.wHi
  let ww := tcmul z.isW wLo wHi wLo wHi t.viol
  change s 86 = rawLo at h86
  change s 89 = rawHi at h89
  have ha6 := muxS_spec k s 6 33 86 6 90 (by omega) (by omega) (by omega)
    (by omega) (by simpa [h33] using hW) hs
  have ha6' : a 6 = wLo := by
    change a 6 = (if s 33 = 1 then s 86 else s 6) at ha6
    rw [h33, h86, h6] at ha6
    exact ha6
  have haf (j : Nat) (h6j : j ≠ 6) (h90j : j ≠ 90) : a j = s j :=
    muxS_frame k s 6 33 86 6 90 j h6j h90j
  have halt : ∀ j, a j < M := srun_lt_of_lt k _ s hs
  have hb7 := muxS_spec k a 7 33 89 7 90 (by omega) (by omega) (by omega)
    (by omega) (by rw [haf 33 (by omega) (by omega), h33]; exact hW) halt
  have hb7' : b 7 = wHi := by
    change b 7 = (if a 33 = 1 then a 89 else a 7) at hb7
    rw [haf 33 (by omega) (by omega), h33,
      haf 89 (by omega) (by omega), h89,
      haf 7 (by omega) (by omega), h7] at hb7
    exact hb7
  have hbf (j : Nat) (h7j : j ≠ 7) (h90j : j ≠ 90) : b j = a j :=
    muxS_frame k a 7 33 89 7 90 j h7j h90j
  have hb6 : b 6 = wLo := (hbf 6 (by omega) (by omega)).trans ha6'
  have hb33 : b 33 = z.isW :=
    (hbf 33 (by omega) (by omega)).trans ((haf 33 (by omega) (by omega)).trans h33)
  have hbV : b rViol = t.viol :=
    (hbf rViol (by simp [rViol]) (by simp [rViol])).trans
      ((haf rViol (by simp [rViol]) (by simp [rViol])).trans hV)
  have hblt : ∀ j, b j < M := srun_lt_of_lt k _ a halt
  have hp := cmulS_spec k b 33 6 7 6 7 98 99
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CmulExternal, rViol])
    (by omega) hblt
  have hp98 : p 98 = ww.1 := by
    simpa [p, ww, hb33, hb6, hb7', hbV] using hp.1
  have hp99 : p 99 = ww.2.1 := by
    simpa [p, ww, hb33, hb6, hb7', hbV] using hp.2.1
  have hpV : p rViol = ww.2.2 := by
    simpa [p, ww, hb33, hb6, hb7', hbV] using hp.2.2
  have hpf (j : Nat) (hj : CmulExternal j) (h98j : j ≠ 98)
      (h99j : j ≠ 99) : p j = b j :=
    cmulS_external_frame k b 33 6 7 6 7 98 99 j hj h98j h99j
  have hplt : ∀ j, p j < M := srun_lt_of_lt k _ b hblt
  have hd8 := muxS_spec k p 8 33 98 8 90 (by omega) (by omega) (by omega)
    (by omega)
    (by rw [hpf 33 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb33]; exact hW)
    hplt
  have hp8 : p 8 = t.wwLo := by
    rw [hpf 8 (by simp [CmulExternal, rViol]) (by omega) (by omega),
      hbf 8 (by omega) (by omega), haf 8 (by omega) (by omega), h8]
  change d 8 = (if p 33 = 1 then p 98 else p 8) at hd8
  rw [hpf 33 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb33,
    hp98, hp8] at hd8
  have hd8' : d 8 = (if z.isW = 1 then ww.1 else t.wwLo) := hd8
  have hdf (j : Nat) (h8j : j ≠ 8) (h90j : j ≠ 90) : d j = p j :=
    muxS_frame k p 8 33 98 8 90 j h8j h90j
  have hdlt : ∀ j, d j < M := srun_lt_of_lt k _ p hplt
  have hf9 := muxS_spec k d 9 33 99 9 90 (by omega) (by omega) (by omega)
    (by omega)
    (by rw [hdf 33 (by omega) (by omega),
      hpf 33 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb33]; exact hW)
    hdlt
  have hp9 : p 9 = t.wwHi := by
    rw [hpf 9 (by simp [CmulExternal, rViol]) (by omega) (by omega),
      hbf 9 (by omega) (by omega), haf 9 (by omega) (by omega), h9]
  change srun k d (muxS 9 33 99 9 90) 9 =
    (if d 33 = 1 then d 99 else d 9) at hf9
  rw [hdf 33 (by omega) (by omega),
    hpf 33 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb33,
    hdf 99 (by omega) (by omega), hp99, hdf 9 (by omega) (by omega), hp9] at hf9
  rw [weightFinishS_decomp, srun_append, srun_append, srun_append, srun_append]
  change let f := srun k d (muxS 9 33 99 9 90); _
  dsimp only
  have hfV : srun k d (muxS 9 33 99 9 90) rViol = ww.2.2 := by
    rw [muxS_frame k d 9 33 99 9 90 rViol (by simp [rViol]) (by simp [rViol]),
      hdf rViol (by simp [rViol]) (by simp [rViol]), hpV]
  have hf6 : srun k d (muxS 9 33 99 9 90) 6 = wLo := by
    rw [muxS_frame k d 9 33 99 9 90 6 (by omega) (by omega),
      hdf 6 (by omega) (by omega),
      hpf 6 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb6]
  have hf7 : srun k d (muxS 9 33 99 9 90) 7 = wHi := by
    rw [muxS_frame k d 9 33 99 9 90 7 (by omega) (by omega),
      hdf 7 (by omega) (by omega),
      hpf 7 (by simp [CmulExternal, rViol]) (by omega) (by omega), hb7']
  have hf8 : srun k d (muxS 9 33 99 9 90) 8 =
      (if z.isW = 1 then ww.1 else t.wwLo) := by
    rw [muxS_frame k d 9 33 99 9 90 8 (by omega) (by omega), hd8']
  have hf9v : srun k d (muxS 9 33 99 9 90) 9 =
      (if z.isW = 1 then ww.2.1 else t.wwHi) := hf9
  change _ = ww.2.2 ∧ _ = wLo ∧ _ = wHi ∧
    _ = (if z.isW = 1 then ww.1 else t.wwLo) ∧
    _ = (if z.isW = 1 then ww.2.1 else t.wwHi)
  exact ⟨hfV, hf6, hf7, hf8, hf9v⟩

end LeanCompCert.Ports.Section413G2Denote
