import LeanCompCert.Ports.Section413G1WeightDenote

/-!
# Section 4.1.3 G2 complete weight-body denotation

This module crosses the weight stage's sole array-load boundary, proves all
dynamic divisors nonzero, and identifies the emitted machine state with the
transparent `tweight` transition.
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

theorem weightFlagsS_sig1 (k : Nat) (s : RegState) :
    srun k s weightFlagsS 79 = (s 5 + bnat (s 5 = 0)) % M := by
  simp [weightFlagsS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, bnat]

theorem weightQuotG_defined (k : Nat) (s : RegState) (scale scale1 : Nat)
    (h79 : s 79 ≠ 0) :
    InstrBlock.SAllDefined k s (weightQuotG scale scale1) := by
  simp [weightQuotG, InstrBlock.SAllDefined, InstrBlock.SDefined,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
    RegState.set, h79]

theorem weightFlagsS_defined (k : Nat) (s : RegState) :
    InstrBlock.SAllDefined k s weightFlagsS := by
  have h2 : 2 % M ≠ 0 := by decide
  simp [weightFlagsS, InstrBlock.SAllDefined, InstrBlock.SDefined,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp, RegState.set, h2]

theorem weightCalcS_defined (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    InstrBlock.SAllDefined k s weightCalcS := by
  let a := srun k s weightFlagsS
  let b := srun k a weightQuotS
  have ha79 : a 79 = (s 5 + bnat (s 5 = 0)) % M := weightFlagsS_sig1 k s
  have h0 : a 79 ≠ 0 := by
    rw [ha79]
    exact weightSig1_ne_zero (s 5) (hs 5)
  rw [weightCalcS_decomp, InstrBlock.SAllDefined_append,
    InstrBlock.SAllDefined_append]
  exact ⟨⟨weightFlagsS_defined k s,
    weightQuotG_defined k a SCALE (SCALE - 1) h0⟩,
    sAllDefined_of_noDiv k weightRawS b (by decide)⟩

set_option maxRecDepth 4000 in
theorem weightFinishBody_alwaysDef :
    weightFinishBody.all alwaysDef = true := by
  simp [weightFinishBody, LeanCompCert.Ports.CDEMAbelScan.muxBody,
    cmulBody_alwaysDef, alwaysDef]

theorem weightBody_defined (c : Cfg) (len k : Nat) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (hAddr : st.regs 33 * st.regs 31 % M < len) :
    AllDefined len k st c.weightBody := by
  let A : AState := ⟨srun k st.regs weightAddrS, st.arr⟩
  let L := A.writeReg 72 (A.arr (A.regs 71))
  have hArun : arun k st weightAddrBody = A := by
    rw [weightAddrBody_lift, arun_lift]
  have hA71 : A.regs 71 = st.regs 33 * st.regs 31 % M := by
    exact weightAddrS_spec k st.regs
  have hLrun : arun k A [.load 72 71] = L := by rfl
  have hAlt : ∀ j, A.regs j < M := by
    intro j
    exact srun_lt_of_lt k _ st.regs hs j
  have hLlt : ∀ j, L.regs j < M := by
    intro j
    simp only [L, AState.writeReg]
    split
    · exact harr _
    · exact hAlt j
  rw [show c.weightBody = weightAddrBody ++
      ([.load 72 71] ++ (weightCalcBody ++ weightFinishBody)) from by
        simp [Cfg.weightBody, List.append_assoc], AllDefined_append]
  constructor
  · exact allDefined_lift_of_noDiv len k weightAddrS st (by decide)
  · rw [hArun, AllDefined_append]
    constructor
    · simp [AllDefined, ADefined, hA71, hAddr]
    · rw [hLrun, AllDefined_append]
      constructor
      · rw [weightCalcBody_lift, allDefined_lift]
        exact weightCalcS_defined k L.regs hLlt
      · apply allDefined_of_alwaysDef
        exact weightFinishBody_alwaysDef

/- The weight stage leaves selector/decode registers `20`--`39` untouched.
Keeping this as a small exported frame theorem avoids reopening the complete
`cmul` body when the following pass-B stage reads registers 31, 34, and 38. -/
set_option maxRecDepth 4000 in
theorem weightBody_decode_frame (c : Cfg) (k : Nat) (st : AState) (j : Nat)
    (hj : 20 ≤ j ∧ j < 40) :
    (arun k st c.weightBody).regs j = st.regs j := by
  let A : AState := ⟨srun k st.regs weightAddrS, st.arr⟩
  let L := A.writeReg 72 (A.arr (A.regs 71))
  let C : AState := ⟨srun k L.regs weightCalcS, L.arr⟩
  let F : AState := ⟨srun k C.regs weightFinishS, C.arr⟩
  have hrun : arun k st c.weightBody = F := by
    simp only [Cfg.weightBody, arun_append, weightAddrBody_lift, arun_lift,
      weightCalcBody_lift, weightFinishBody_lift]
    rfl
  have hFC : F.regs j = C.regs j :=
    weightFinishS_frame k C.regs j
      (by simp [CmulExternal, rViol]; omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hCL : C.regs j = L.regs j := weightCalcS_frame k L.regs j (by omega)
  have hLA : L.regs j = A.regs j := by simp [L, AState.writeReg]; omega
  have hAst : A.regs j = st.regs j :=
    weightAddrS_frame k st.regs j (by omega)
  rw [hrun, hFC, hCL, hLA, hAst]

set_option maxRecDepth 10000 in
theorem weightBody_obs (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (h31 : st.regs 31 = z.X) (h33 : st.regs 33 = z.isW)
    (hW : z.isW ≤ 1) :
    obsT (arun k st c.weightBody) = tweight z (obsT st) := by
  let A : AState := ⟨srun k st.regs weightAddrS, st.arr⟩
  let L := A.writeReg 72 (A.arr (A.regs 71))
  let C : AState := ⟨srun k L.regs weightCalcS, L.arr⟩
  let F : AState := ⟨srun k C.regs weightFinishS, C.arr⟩
  have hrun : arun k st c.weightBody = F := by
    simp only [Cfg.weightBody, arun_append, weightAddrBody_lift, arun_lift,
      weightCalcBody_lift, weightFinishBody_lift]
    rfl
  have hA31 : A.regs 31 = z.X := by
    rw [show A.regs 31 = st.regs 31 from weightAddrS_frame k st.regs 31 (by omega), h31]
  have hA33 : A.regs 33 = z.isW := by
    rw [show A.regs 33 = st.regs 33 from weightAddrS_frame k st.regs 33 (by omega), h33]
  have hA71 : A.regs 71 = z.isW * z.X % M := by
    change srun k st.regs weightAddrS 71 = _
    rw [weightAddrS_spec, h33, h31]
  have hL31 : L.regs 31 = z.X := by simp [L, AState.writeReg, hA31]
  have hL33 : L.regs 33 = z.isW := by simp [L, AState.writeReg, hA33]
  have hLframe (j : Nat) (hj : j ≠ 72) : L.regs j = A.regs j := by
    simp [L, AState.writeReg, hj]
  have hL72 : L.regs 72 = (obsT st).arr (z.isW * z.X % M) := by
    change A.arr (A.regs 71) = st.arr (z.isW * z.X % M)
    rw [hA71]
  have hL5 : L.regs 5 = (obsT st).sigma := by
    simp [L, AState.writeReg, A]
    rw [weightAddrS_frame k st.regs 5 (by omega)]
    rfl
  have hAlt : ∀ j, A.regs j < M := by
    intro j
    exact srun_lt_of_lt k _ st.regs hs j
  have hLlt : ∀ j, L.regs j < M := by
    intro j
    simp only [L, AState.writeReg]
    split
    · exact harr _
    · exact hAlt j
  have hcalc := weightCalcS_spec k L.regs z (obsT st) hLlt hL5 hL31 hL33 hL72 hW
  dsimp only at hcalc
  rcases hcalc with ⟨hC86, hC89⟩
  have hCframe (j : Nat) (hj : j < 73 ∨ 89 < j) : C.regs j = L.regs j :=
    weightCalcS_frame k L.regs j hj
  have hClt : ∀ j, C.regs j < M := by
    intro j
    exact srun_lt_of_lt k _ L.regs hLlt j
  have hfinish := weightFinishS_spec k C.regs z (obsT st) hClt
    (by rw [hCframe rViol (by simp [rViol]), hLframe rViol (by simp [rViol])]
        exact weightAddrS_frame k st.regs rViol (by simp [rViol]))
    (by rw [hCframe 6 (by omega), hLframe 6 (by omega)]
        exact weightAddrS_frame k st.regs 6 (by omega))
    (by rw [hCframe 7 (by omega), hLframe 7 (by omega)]
        exact weightAddrS_frame k st.regs 7 (by omega))
    (by rw [hCframe 8 (by omega), hLframe 8 (by omega)]
        exact weightAddrS_frame k st.regs 8 (by omega))
    (by rw [hCframe 9 (by omega), hLframe 9 (by omega)]
        exact weightAddrS_frame k st.regs 9 (by omega))
    (by rw [hCframe 33 (by omega)]; exact hL33)
    hC86 hC89 hW
  dsimp only at hfinish
  rcases hfinish with ⟨hFV, hF6, hF7, hF8, hF9⟩
  have hFV' : F.regs rViol = (tweight z (obsT st)).viol := hFV
  have hF6' : F.regs 6 = (tweight z (obsT st)).wLo := hF6
  have hF7' : F.regs 7 = (tweight z (obsT st)).wHi := hF7
  have hF8' : F.regs 8 = (tweight z (obsT st)).wwLo := hF8
  have hF9' : F.regs 9 = (tweight z (obsT st)).wwHi := hF9
  rw [hrun]
  change
    ({ viol := F.regs rViol, res := F.regs 2, sq := F.regs 3,
       par := F.regs 4, sigma := F.regs 5, wLo := F.regs 6,
       wHi := F.regs 7, wwLo := F.regs 8, wwHi := F.regs 9,
       dLo := F.regs 10, dHi := F.regs 11, gLo := F.regs 12,
       gHi := F.regs 13, arr := F.arr } : TState) = _
  rw [TState.mk.injEq]
  simp only [hFV', hF6', hF7', hF8', hF9', true_and, tweight, obsT]
  have hFframe (j : Nat) (hj : CmulExternal j) (h6j : j ≠ 6)
      (h7j : j ≠ 7) (h8j : j ≠ 8) (h9j : j ≠ 9)
      (h90j : j ≠ 90) (h98j : j ≠ 98) (h99j : j ≠ 99) :
      F.regs j = C.regs j :=
    weightFinishS_frame k C.regs j hj h6j h7j h8j h9j h90j h98j h99j
  have persistent (j : Nat) (hj : CmulExternal j) (h6j : j ≠ 6)
      (h7j : j ≠ 7) (h8j : j ≠ 8) (h9j : j ≠ 9)
      (h71j : j ≠ 71) (h72j : j ≠ 72) (h90j : j ≠ 90)
      (h98j : j ≠ 98) (h99j : j ≠ 99) (hcj : j < 73) :
      F.regs j = st.regs j := by
    rw [hFframe j hj h6j h7j h8j h9j h90j h98j h99j,
      hCframe j (by omega)]
    rw [hLframe j h72j]
    change srun k st.regs weightAddrS j = st.regs j
    exact weightAddrS_frame k st.regs j h71j
  exact ⟨persistent 2 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 3 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 4 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 5 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 10 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 11 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 12 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    persistent 13 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), rfl⟩

end LeanCompCert.Ports.Section413G1Denote
