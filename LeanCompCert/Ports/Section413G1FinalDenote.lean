import LeanCompCert.Ports.Section413G1PassBGateDenote

/-!
# Section 4.1.3 G2 finalization denotation

The emitted finalization block is split into accumulator, width-guard, lower
endpoint, and upper endpoint stages.  This module starts the corresponding
scalar denotation without changing the emitted instruction list.
-/

namespace LeanCompCert.Ports.Section413G1Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.InstrBlock (srun srun_append srun_lt_of_lt)
open LeanCompCert.Ports.Section413G1Program

def finAccumS : List Instr :=
  [ .binop 220 .mul (.reg 35) (.reg 10)
  , .binop 12 .add (.reg 12) (.reg 220)
  , .binop 221 .mul (.reg 35) (.reg 11)
  , .binop 13 .add (.reg 13) (.reg 221)
  , .binop 222 .sub (.lit 1) (.reg 35)
  , .binop 10 .mul (.reg 10) (.reg 222)
  , .binop 11 .mul (.reg 11) (.reg 222) ]

theorem finAccumBody_lift : finAccumBody = lift finAccumS := rfl

theorem finAccumS_spec (k : Nat) (s : RegState) (isF : Nat)
    (h35 : s 35 = isF) (hF : isF ≤ 1) :
    let f := srun k s finAccumS
    f 12 = (s 12 + isF * s 10 % M) % M ∧
      f 13 = (s 13 + isF * s 11 % M) % M ∧
      f 10 = s 10 * (1 - isF) % M ∧
      f 11 = s 11 * (1 - isF) % M := by
  have hsub : (1 + (M - isF)) % M = 1 - isF := msub_bit hF
  simp only [finAccumS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, h35, hsub,
    one_mod_M, if_true, if_false, Nat.reduceEqDiff]
  simp

theorem finAccumS_frame (k : Nat) (s : RegState) (j : Nat)
    (h10 : j ≠ 10) (h11 : j ≠ 11) (h12 : j ≠ 12) (h13 : j ≠ 13)
    (h220 : j ≠ 220) (h221 : j ≠ 221) (h222 : j ≠ 222) :
    srun k s finAccumS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [finAccumS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [InstrBlock.sdest] <;> omega

def finGuardS : List Instr :=
  guardG CAP 35 12 223 ++ guardG CAP 35 13 223

theorem finGuardBody_lift : finGuardBody = lift finGuardS := by
  simp [finGuardBody, finGuardS, guardBody_lift, lift]

theorem finGuardS_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun k s finGuardS rViol =
      tguard (s 35) (s 13) (tguard (s 35) (s 12) (s rViol)) := by
  let u := srun k s (guardG CAP 35 12 223)
  have huV : u rViol = tguard (s 35) (s 12) (s rViol) :=
    guardG_tguard k s 35 12 223 (by simp [rViol]) (by omega) hs
  have hu35 : u 35 = s 35 :=
    guardG_frame k s CAP 35 12 223 35 (by omega) (by simp [rViol])
  have hu13 : u 13 = s 13 :=
    guardG_frame k s CAP 35 12 223 13 (by omega) (by simp [rViol])
  have hult : ∀ j, u j < M := srun_lt_of_lt k _ s hs
  rw [finGuardS, srun_append,
    guardG_tguard k u 35 13 223 (by simp [rViol]) (by omega) hult,
    hu35, hu13, huV]

theorem finGuardS_frame (k : Nat) (s : RegState) (j : Nat)
    (h223 : j ≠ 223) (hV : j ≠ rViol) :
    srun k s finGuardS j = s j := by
  rw [finGuardS, srun_append,
    guardG_frame k _ CAP 35 13 223 j h223 hV,
    guardG_frame k s CAP 35 12 223 j h223 hV]

theorem finAccumGuardS_spec (k : Nat) (s : RegState) (isF : Nat)
    (hs : ∀ j, s j < M) (h35 : s 35 = isF) (hF : isF ≤ 1) :
    let a := srun k s finAccumS
    let f := srun k a finGuardS
    f rViol = tguard isF ((s 13 + isF * s 11 % M) % M)
      (tguard isF ((s 12 + isF * s 10 % M) % M) (s rViol)) := by
  let a := srun k s finAccumS
  have ha := finAccumS_spec k s isF h35 hF
  dsimp only at ha
  have haV : a rViol = s rViol :=
    finAccumS_frame k s rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol])
  have ha35 : a 35 = isF :=
    (finAccumS_frame k s 35 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h35
  have ha12 : a 12 = (s 12 + isF * s 10 % M) % M := ha.1
  have ha13 : a 13 = (s 13 + isF * s 11 % M) % M := ha.2.1
  have halt : ∀ j, a j < M := srun_lt_of_lt k _ s hs
  dsimp only
  rw [finGuardS_spec k a halt, ha35, ha13, ha12, haV]

theorem finAccumGuardBody_lift :
    finAccumBody ++ finGuardBody = lift (finAccumS ++ finGuardS) := by
  rw [finAccumBody_lift, finGuardBody_lift, lift_append]

def finLowPreS (c : Cfg) : List Instr :=
  [ .binop 224 .ge (.reg 31) (.lit c.checkLo)
  , .binop 225 .mul (.reg 35) (.reg 224)
  , .binop 226 .mul (.reg 31) (.lit 10)
  , .binop 227 .ge (.reg 12) (.lit H63)
  , .binop 228 .sub (.lit 0) (.reg 12) ]

theorem finLowPreBody_lift (c : Cfg) : c.finLowPreBody = lift (finLowPreS c) := rfl

theorem finLowPreS_spec (c : Cfg) (k : Nat) (s : RegState)
    (hcl : c.checkLo % M = c.checkLo) :
    let f := srun k s (finLowPreS c)
    f 224 = bnat (c.checkLo ≤ s 31) ∧
      f 225 = s 35 * bnat (c.checkLo ≤ s 31) % M ∧
      f 226 = s 31 * 10 % M ∧
      f 227 = bnat (H63 ≤ s 12) ∧
      f 228 = tsub 0 (s 12) := by
  simp only [finLowPreS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, hcl, H63_mod,
    show (10 : Nat) % M = 10 by decide, zero_mod_M, if_true, if_false,
    Nat.reduceEqDiff, ge_iff_le, tsub, bnat]
  simp

theorem finLowPreS_frame (c : Cfg) (k : Nat) (s : RegState) (j : Nat)
    (h224 : j ≠ 224) (h225 : j ≠ 225) (h226 : j ≠ 226)
    (h227 : j ≠ 227) (h228 : j ≠ 228) :
    srun k s (finLowPreS c) j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [finLowPreS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [InstrBlock.sdest] <;> omega

def finLowPostS : List Instr :=
  [ .binop 241 .gt (.reg 232) (.lit 1)
  , .binop 242 .eq (.reg 232) (.lit 1)
  , .binop 243 .gt (.reg 231) (.lit KLO)
  , .binop 244 .mul (.reg 242) (.reg 243)
  , .binop 245 .add (.reg 241) (.reg 244)
  , .binop 246 .mul (.reg 227) (.reg 245)
  , .binop 246 .mul (.reg 246) (.reg 225)
  , .binop rViol .bor (.reg rViol) (.reg 246) ]

theorem finLowPostBody_lift : finLowPostBody = lift finLowPostS := rfl

theorem KLO_mod : KLO % M = KLO := by decide

theorem bor_mod_M {a b : Nat} (ha : a < M) (hb : b < M) :
    (a ||| b) % M = a ||| b := by
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

theorem finLowPostS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hsg : s 227 ≤ 1) (hchk : s 225 ≤ 1) :
    srun k s finLowPostS rViol =
      s rViol ||| (s 227 *
        (bnat (1 < s 232) + bnat (s 232 = 1) * bnat (KLO < s 231)) *
          s 225) := by
  let a := bnat (1 < s 232)
  let b := bnat (s 232 = 1)
  let d := bnat (KLO < s 231)
  have ha : a ≤ 1 := bnat_le_one _
  have hb : b ≤ 1 := bnat_le_one _
  have hd : d ≤ 1 := bnat_le_one _
  have hbdle : b * d ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hb hd
  have hbd : b * d < M := by
    exact Nat.lt_of_le_of_lt hbdle (by decide)
  have habdle : a + b * d ≤ 2 := by omega
  have habd : a + b * d < M := by
    exact Nat.lt_of_le_of_lt habdle (by decide)
  have hsgmle : s 227 * (a + b * d) ≤ 2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hsg habdle
  have hsgm : s 227 * (a + b * d) < M := by
    exact Nat.lt_of_le_of_lt hsgmle (by decide)
  have hbadle : s 227 * (a + b * d) * s 225 ≤ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hsgmle hchk
  have hbad : s 227 * (a + b * d) * s 225 < M := by
    exact Nat.lt_of_le_of_lt hbadle (by decide)
  have hor := bor_mod_M (hs rViol) hbad
  dsimp only [a, b, d] at hbd habd hsgm hbad hor
  simp only [finLowPostS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, one_mod_M,
    KLO_mod, rViol, if_true, if_false, Nat.reduceEqDiff, gt_iff_lt]
  simp only [bnat] at hbd habd hsgm hbad hor ⊢
  simp only [rViol] at hor
  rw [Nat.mod_eq_of_lt hbd, Nat.mod_eq_of_lt habd,
    Nat.mod_eq_of_lt hsgm, Nat.mod_eq_of_lt hbad, hor]

theorem finLowPostS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 241) (hV : j ≠ rViol) :
    srun k s finLowPostS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [finLowPostS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [InstrBlock.sdest] <;> omega

def finLowS (c : Cfg) : List Instr :=
  finLowPreS c ++ muxS 229 227 228 12 230 ++
    mulWideG 4294967295 4294967296 229 226 231 232
      233 234 235 236 237 238 239 240 ++ finLowPostS

theorem finLowBody_lift (c : Cfg) : c.finLowBody = lift (finLowS c) := by
  rw [Cfg.finLowBody, finLowS, finLowPreBody_lift, muxBody_lift,
    mulWideBody_lift, finLowPostBody_lift]
  simp only [lift_append]

theorem finLowS_frame (c : Cfg) (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 224) (hV : j ≠ rViol) :
    srun k s (finLowS c) j = s j := by
  rw [finLowS, srun_append,
    finLowPostS_frame k _ j (by omega) hV, srun_append,
    mulWideG_frame k _ 4294967295 4294967296 229 226 231 232
      233 234 235 236 237 238 239 240 j (by omega) (by omega)
        (by simp [NotIn8]; omega),
    srun_append, muxS_frame k _ 229 227 228 12 230 j (by omega) (by omega),
    finLowPreS_frame c k s j (by omega) (by omega) (by omega) (by omega)
      (by omega)]

theorem finLowS_spec (c : Cfg) (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h35 : s 35 ≤ 1)
    (hcl : c.checkLo % M = c.checkLo) :
    let chk := s 35 * bnat (c.checkLo ≤ s 31)
    let tenX := s 31 * 10 % M
    let sLo := bnat (H63 ≤ s 12)
    let mLo := if sLo = 1 then tsub 0 (s 12) else s 12
    srun k s (finLowS c) rViol = s rViol |||
      (sLo * tfinBadCore mLo tenX * chk) := by
  let P := srun k s (finLowPreS c)
  let U := srun k P (muxS 229 227 228 12 230)
  let V := srun k U (mulWideG 4294967295 4294967296 229 226 231 232
    233 234 235 236 237 238 239 240)
  let sLo := bnat (H63 ≤ s 12)
  let chk := s 35 * bnat (c.checkLo ≤ s 31)
  let tenX := s 31 * 10 % M
  let mLo := if sLo = 1 then tsub 0 (s 12) else s 12
  let pl := Verified.MulWide.hl mLo tenX
  have hp := finLowPreS_spec c k s hcl
  dsimp only at hp
  have hsLo : sLo ≤ 1 := bnat_le_one _
  have hcheck : bnat (c.checkLo ≤ s 31) ≤ 1 := bnat_le_one _
  have hchk : chk ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul h35 hcheck
  have hchkM : chk < M := Nat.lt_of_le_of_lt hchk (by decide)
  have hP225 : P 225 = chk := by
    rw [show P 225 = s 35 * bnat (c.checkLo ≤ s 31) % M from hp.2.1,
      Nat.mod_eq_of_lt hchkM]
  have hP226 : P 226 = tenX := hp.2.2.1
  have hP227 : P 227 = sLo := hp.2.2.2.1
  have hP228 : P 228 = tsub 0 (s 12) := hp.2.2.2.2
  have hP12 : P 12 = s 12 :=
    finLowPreS_frame c k s 12 (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hPlt : ∀ j, P j < M := srun_lt_of_lt k _ s hs
  have hU229 : U 229 = mLo := by
    rw [show U 229 = (if P 227 = 1 then P 228 else P 12) from
      muxS_spec k P 229 227 228 12 230 (by omega) (by omega) (by omega)
        (by omega) (by rw [hP227]; exact hsLo) hPlt,
      hP227, hP228, hP12]
  have hU226 : U 226 = tenX := by
    rw [show U 226 = P 226 from muxS_frame k P 229 227 228 12 230 226
      (by omega) (by omega), hP226]
  have hU225 : U 225 = chk := by
    rw [show U 225 = P 225 from muxS_frame k P 229 227 228 12 230 225
      (by omega) (by omega), hP225]
  have hU227 : U 227 = sLo := by
    rw [show U 227 = P 227 from muxS_frame k P 229 227 228 12 230 227
      (by omega) (by omega), hP227]
  have hUlt : ∀ j, U j < M := srun_lt_of_lt k _ P hPlt
  have hwide := mulWideG_hl k U 229 226 231 232 233 234 235 236 237 238
    239 240 (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8])
    (by omega) hUlt
  have hV231 : V 231 = pl.1 := by simpa only [V, hU229, hU226, pl] using hwide.1
  have hV232 : V 232 = pl.2 := by simpa only [V, hU229, hU226, pl] using hwide.2
  have hV225 : V 225 = chk := by
    rw [show V 225 = U 225 from mulWideG_frame k U 4294967295 4294967296
      229 226 231 232 233 234 235 236 237 238 239 240 225
      (by omega) (by omega) (by simp [NotIn8]), hU225]
  have hV227 : V 227 = sLo := by
    rw [show V 227 = U 227 from mulWideG_frame k U 4294967295 4294967296
      229 226 231 232 233 234 235 236 237 238 239 240 227
      (by omega) (by omega) (by simp [NotIn8]), hU227]
  have hPr : P rViol = s rViol := by
    change srun k s (finLowPreS c) rViol = s rViol
    exact finLowPreS_frame c k s rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
  have hVr : V rViol = s rViol := by
    rw [show V rViol = U rViol from mulWideG_frame k U 4294967295 4294967296
      229 226 231 232 233 234 235 236 237 238 239 240 rViol
      (by simp [rViol]) (by simp [rViol]) (by simp [NotIn8, rViol]),
      show U rViol = P rViol from muxS_frame k P 229 227 228 12 230 rViol
        (by simp [rViol]) (by simp [rViol]),
      hPr]
  have hVlt : ∀ j, V j < M := srun_lt_of_lt k _ U hUlt
  have hpost := finLowPostS_spec k V hVlt (by rw [hV227]; exact hsLo)
    (by rw [hV225]; exact hchk)
  rw [finLowS, srun_append, srun_append, srun_append]
  change srun k V finLowPostS rViol = _
  rw [hpost, hVr, hV227, hV232, hV231, hV225]
  rfl

theorem finLowS_chk (c : Cfg) (k : Nat) (s : RegState)
    (hcl : c.checkLo % M = c.checkLo) (h35 : s 35 ≤ 1) :
    srun k s (finLowS c) 225 = s 35 * bnat (c.checkLo ≤ s 31) := by
  have hp := finLowPreS_spec c k s hcl
  dsimp only at hp
  have hchk : s 35 * bnat (c.checkLo ≤ s 31) < M := by
    have hb := bnat_le_one (c.checkLo ≤ s 31)
    exact Nat.lt_of_le_of_lt
      (by simpa only [Nat.one_mul] using Nat.mul_le_mul h35 hb) (by decide)
  rw [finLowS, srun_append,
    finLowPostS_frame k _ 225 (by omega) (by simp [rViol]), srun_append,
    mulWideG_frame k _ 4294967295 4294967296 229 226 231 232
      233 234 235 236 237 238 239 240 225 (by omega) (by omega)
        (by simp [NotIn8]),
    srun_append, muxS_frame k _ 229 227 228 12 230 225 (by omega) (by omega),
    hp.2.1, Nat.mod_eq_of_lt hchk]

theorem finLowS_tenX (c : Cfg) (k : Nat) (s : RegState)
    (hcl : c.checkLo % M = c.checkLo) :
    srun k s (finLowS c) 226 = s 31 * 10 % M := by
  have hp := finLowPreS_spec c k s hcl
  dsimp only at hp
  rw [finLowS, srun_append,
    finLowPostS_frame k _ 226 (by omega) (by simp [rViol]), srun_append,
    mulWideG_frame k _ 4294967295 4294967296 229 226 231 232
      233 234 235 236 237 238 239 240 226 (by omega) (by omega)
        (by simp [NotIn8]),
    srun_append, muxS_frame k _ 229 227 228 12 230 226 (by omega) (by omega),
    hp.2.2.1]

def finHighPreS : List Instr :=
  [ .binop 247 .ge (.reg 13) (.lit H63)
  , .binop 248 .sub (.lit 1) (.reg 247)
  , .binop 249 .sub (.lit 0) (.reg 13) ]

theorem finHighPreBody_lift : finHighPreBody = lift finHighPreS := rfl

theorem finHighPreS_spec (k : Nat) (s : RegState) :
    let f := srun k s finHighPreS
    let sHi := bnat (H63 ≤ s 13)
    f 247 = sHi ∧ f 248 = 1 - sHi ∧ f 249 = tsub 0 (s 13) := by
  have hb := bnat_le_one (H63 ≤ s 13)
  have hsub := msub_bit hb
  simp only [finHighPreS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, H63_mod,
    one_mod_M, zero_mod_M, if_true, if_false, Nat.reduceEqDiff, ge_iff_le,
    tsub]
  simp only [bnat] at hsub ⊢
  rw [hsub]
  simp

theorem finHighPreS_frame (k : Nat) (s : RegState) (j : Nat)
    (h247 : j ≠ 247) (h248 : j ≠ 248) (h249 : j ≠ 249) :
    srun k s finHighPreS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [finHighPreS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [InstrBlock.sdest] <;> omega

def finHighPostS : List Instr :=
  [ .binop 241 .gt (.reg 253) (.lit 1)
  , .binop 242 .eq (.reg 253) (.lit 1)
  , .binop 243 .gt (.reg 252) (.lit KLO)
  , .binop 244 .mul (.reg 242) (.reg 243)
  , .binop 245 .add (.reg 241) (.reg 244)
  , .binop 246 .mul (.reg 248) (.reg 245)
  , .binop 246 .mul (.reg 246) (.reg 225)
  , .binop rViol .bor (.reg rViol) (.reg 246) ]

theorem finHighPostBody_lift : finHighPostBody = lift finHighPostS := rfl

theorem finHighPostS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hsg : s 248 ≤ 1) (hchk : s 225 ≤ 1) :
    srun k s finHighPostS rViol =
      s rViol ||| (s 248 *
        (bnat (1 < s 253) + bnat (s 253 = 1) * bnat (KLO < s 252)) *
          s 225) := by
  let a := bnat (1 < s 253)
  let b := bnat (s 253 = 1)
  let d := bnat (KLO < s 252)
  have ha : a ≤ 1 := bnat_le_one _
  have hb : b ≤ 1 := bnat_le_one _
  have hd : d ≤ 1 := bnat_le_one _
  have hbdle : b * d ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hb hd
  have hbd : b * d < M := Nat.lt_of_le_of_lt hbdle (by decide)
  have habdle : a + b * d ≤ 2 := by omega
  have habd : a + b * d < M := Nat.lt_of_le_of_lt habdle (by decide)
  have hsgmle : s 248 * (a + b * d) ≤ 2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hsg habdle
  have hsgm : s 248 * (a + b * d) < M :=
    Nat.lt_of_le_of_lt hsgmle (by decide)
  have hbadle : s 248 * (a + b * d) * s 225 ≤ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hsgmle hchk
  have hbad : s 248 * (a + b * d) * s 225 < M :=
    Nat.lt_of_le_of_lt hbadle (by decide)
  have hor := bor_mod_M (hs rViol) hbad
  dsimp only [a, b, d] at hbd habd hsgm hbad hor
  simp only [finHighPostS, srun, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, one_mod_M,
    KLO_mod, rViol, if_true, if_false, Nat.reduceEqDiff, gt_iff_lt]
  simp only [bnat] at hbd habd hsgm hbad hor ⊢
  simp only [rViol] at hor
  rw [Nat.mod_eq_of_lt hbd, Nat.mod_eq_of_lt habd,
    Nat.mod_eq_of_lt hsgm, Nat.mod_eq_of_lt hbad, hor]

theorem finHighPostS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 241) (hV : j ≠ rViol) :
    srun k s finHighPostS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [finHighPostS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [InstrBlock.sdest] <;> omega

def finHighS : List Instr :=
  finHighPreS ++ muxS 250 247 249 13 251 ++
    mulWideG 4294967295 4294967296 250 226 252 253
      233 234 235 236 237 238 239 240 ++ finHighPostS

theorem finHighBody_lift : finHighBody = lift finHighS := by
  rw [finHighBody, finHighS, finHighPreBody_lift, muxBody_lift,
    mulWideBody_lift, finHighPostBody_lift]
  simp only [lift_append]

theorem finHighS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 225) (hV : j ≠ rViol) :
    srun k s finHighS j = s j := by
  rw [finHighS, srun_append,
    finHighPostS_frame k _ j (by omega) hV, srun_append,
    mulWideG_frame k _ 4294967295 4294967296 250 226 252 253
      233 234 235 236 237 238 239 240 j (by omega) (by omega)
        (by simp [NotIn8]; omega),
    srun_append, muxS_frame k _ 250 247 249 13 251 j (by omega) (by omega),
    finHighPreS_frame k s j (by omega) (by omega) (by omega)]

theorem finHighS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h225 : s 225 ≤ 1) :
    let tenX := s 226
    let sHi := bnat (H63 ≤ s 13)
    let mHi := if sHi = 1 then tsub 0 (s 13) else s 13
    srun k s finHighS rViol = s rViol |||
      ((1 - sHi) * tfinBadCore mHi tenX * s 225) := by
  let P := srun k s finHighPreS
  let U := srun k P (muxS 250 247 249 13 251)
  let V := srun k U (mulWideG 4294967295 4294967296 250 226 252 253
    233 234 235 236 237 238 239 240)
  let sHi := bnat (H63 ≤ s 13)
  let tenX := s 226
  let mHi := if sHi = 1 then tsub 0 (s 13) else s 13
  let ph := Verified.MulWide.hl mHi tenX
  have hp := finHighPreS_spec k s
  dsimp only at hp
  have hsHi : sHi ≤ 1 := bnat_le_one _
  have hP247 : P 247 = sHi := hp.1
  have hP248 : P 248 = 1 - sHi := hp.2.1
  have hP249 : P 249 = tsub 0 (s 13) := hp.2.2
  have hP13 : P 13 = s 13 := finHighPreS_frame k s 13 (by omega) (by omega)
    (by omega)
  have hP226 : P 226 = tenX := finHighPreS_frame k s 226 (by omega)
    (by omega) (by omega)
  have hP225 : P 225 = s 225 := finHighPreS_frame k s 225 (by omega)
    (by omega) (by omega)
  have hPlt : ∀ j, P j < M := srun_lt_of_lt k _ s hs
  have hU250 : U 250 = mHi := by
    rw [show U 250 = (if P 247 = 1 then P 249 else P 13) from
      muxS_spec k P 250 247 249 13 251 (by omega) (by omega) (by omega)
        (by omega) (by rw [hP247]; exact hsHi) hPlt,
      hP247, hP249, hP13]
  have hU226 : U 226 = tenX := by
    rw [show U 226 = P 226 from muxS_frame k P 250 247 249 13 251 226
      (by omega) (by omega), hP226]
  have hU225 : U 225 = s 225 := by
    rw [show U 225 = P 225 from muxS_frame k P 250 247 249 13 251 225
      (by omega) (by omega), hP225]
  have hU248 : U 248 = 1 - sHi := by
    rw [show U 248 = P 248 from muxS_frame k P 250 247 249 13 251 248
      (by omega) (by omega), hP248]
  have hUlt : ∀ j, U j < M := srun_lt_of_lt k _ P hPlt
  have hwide := mulWideG_hl k U 250 226 252 253 233 234 235 236 237 238
    239 240 (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8]) (by omega) hUlt
  have hV252 : V 252 = ph.1 := by simpa only [V, hU250, hU226, ph] using hwide.1
  have hV253 : V 253 = ph.2 := by simpa only [V, hU250, hU226, ph] using hwide.2
  have hV225 : V 225 = s 225 := by
    rw [show V 225 = U 225 from mulWideG_frame k U 4294967295 4294967296
      250 226 252 253 233 234 235 236 237 238 239 240 225
      (by omega) (by omega) (by simp [NotIn8]), hU225]
  have hV248 : V 248 = 1 - sHi := by
    rw [show V 248 = U 248 from mulWideG_frame k U 4294967295 4294967296
      250 226 252 253 233 234 235 236 237 238 239 240 248
      (by omega) (by omega) (by simp [NotIn8]), hU248]
  have hPr : P rViol = s rViol := by
    change srun k s finHighPreS rViol = s rViol
    exact finHighPreS_frame k s rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol])
  have hVr : V rViol = s rViol := by
    rw [show V rViol = U rViol from mulWideG_frame k U 4294967295 4294967296
      250 226 252 253 233 234 235 236 237 238 239 240 rViol
      (by simp [rViol]) (by simp [rViol]) (by simp [NotIn8, rViol]),
      show U rViol = P rViol from muxS_frame k P 250 247 249 13 251 rViol
        (by simp [rViol]) (by simp [rViol]), hPr]
  have hVlt : ∀ j, V j < M := srun_lt_of_lt k _ U hUlt
  have hsg : 1 - sHi ≤ 1 := by omega
  have hpost := finHighPostS_spec k V hVlt (by rw [hV248]; exact hsg)
    (by rw [hV225]; exact h225)
  rw [finHighS, srun_append, srun_append, srun_append]
  change srun k V finHighPostS rViol = _
  rw [hpost, hVr, hV248, hV253, hV252, hV225]
  rfl

def finAccumGuardS : List Instr := finAccumS ++ finGuardS

def finLowPrefixS (c : Cfg) : List Instr :=
  finAccumGuardS ++ finLowS c

def finS (c : Cfg) : List Instr := finLowPrefixS c ++ finHighS

theorem finBody_lift (c : Cfg) : c.finBody = lift (finS c) := by
  rw [Cfg.finBody, finS, finLowPrefixS, finAccumGuardS,
    finAccumBody_lift, finGuardBody_lift,
    finLowBody_lift, finHighBody_lift]
  simp only [lift_append]

theorem finS_frame_2_9 (c : Cfg) (k : Nat) (s : RegState) (j : Nat)
    (hj : 2 ≤ j) (hj9 : j ≤ 9) : srun k s (finS c) j = s j := by
  rw [finS, finLowPrefixS, finAccumGuardS, srun_append,
    finHighS_frame k _ j (by omega) (by simp [rViol]; omega),
    srun_append, finLowS_frame c k _ j (by omega) (by simp [rViol]; omega),
    srun_append, finGuardS_frame k _ j (by omega) (by simp [rViol]; omega),
    finAccumS_frame k s j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]

theorem finS_accum_spec (c : Cfg) (k : Nat) (s : RegState) (isF : Nat)
    (h35 : s 35 = isF) (hF : isF ≤ 1) :
    let f := srun k s (finS c)
    f 10 = s 10 * (1 - isF) % M ∧
      f 11 = s 11 * (1 - isF) % M ∧
      f 12 = (s 12 + isF * s 10 % M) % M ∧
      f 13 = (s 13 + isF * s 11 % M) % M := by
  let A := srun k s finAccumS
  have ha := finAccumS_spec k s isF h35 hF
  dsimp only at ha
  have frame (j : Nat) (hj : 10 ≤ j) (hj13 : j ≤ 13) :
      srun k s (finS c) j = A j := by
    rw [finS, finLowPrefixS, finAccumGuardS, srun_append,
      finHighS_frame k _ j (by omega) (by simp [rViol]; omega),
      srun_append, finLowS_frame c k _ j (by omega) (by simp [rViol]; omega),
      srun_append, finGuardS_frame k _ j (by omega) (by simp [rViol]; omega)]
  exact ⟨(frame 10 (by omega) (by omega)).trans ha.2.2.1,
    (frame 11 (by omega) (by omega)).trans ha.2.2.2,
    (frame 12 (by omega) (by omega)).trans ha.1,
    (frame 13 (by omega) (by omega)).trans ha.2.1⟩

theorem finAccumGuardS_violT (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (h35 : st.regs 35 = z.isF)
    (hF : z.isF ≤ 1) :
    srun k st.regs finAccumGuardS rViol =
      tguard z.isF (tfinGHi z (obsT st))
        (tguard z.isF (tfinGLo z (obsT st)) (obsT st).viol) := by
  have h := finAccumGuardS_spec k st.regs z.isF hs h35 hF
  change srun k st.regs finAccumGuardS rViol = _
  rw [finAccumGuardS, srun_append]
  exact h

theorem finAccumGuardS_low_inputs (k : Nat) (st : AState) (z : TSel)
    (h31 : st.regs 31 = z.X) (h35 : st.regs 35 = z.isF)
    (hF : z.isF ≤ 1) :
    let G := srun k st.regs finAccumGuardS
    G 12 = tfinGLo z (obsT st) ∧ G 13 = tfinGHi z (obsT st) ∧
      G 31 = z.X ∧ G 35 = z.isF := by
  let A := srun k st.regs finAccumS
  let G := srun k A finGuardS
  have ha := finAccumS_spec k st.regs z.isF h35 hF
  dsimp only at ha
  have hA31 : A 31 = z.X := by
    have h := finAccumS_frame k st.regs 31 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    change A 31 = st.regs 31 at h
    exact h.trans h31
  have hA35 : A 35 = z.isF := by
    have h := finAccumS_frame k st.regs 35 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    change A 35 = st.regs 35 at h
    exact h.trans h35
  have hG12 : G 12 = (st.regs 12 + z.isF * st.regs 10 % M) % M :=
    (finGuardS_frame k A 12 (by omega) (by simp [rViol])).trans ha.1
  have hG13 : G 13 = (st.regs 13 + z.isF * st.regs 11 % M) % M :=
    (finGuardS_frame k A 13 (by omega) (by simp [rViol])).trans ha.2.1
  have hG31 : G 31 = z.X :=
    (finGuardS_frame k A 31 (by omega) (by simp [rViol])).trans hA31
  have hG35 : G 35 = z.isF :=
    (finGuardS_frame k A 35 (by omega) (by simp [rViol])).trans hA35
  change G 12 = _ ∧ G 13 = _ ∧ G 31 = _ ∧ G 35 = _
  exact ⟨hG12, hG13, hG31, hG35⟩

theorem finLowS_badLo (c : Cfg) (k : Nat) (s : RegState) (z : TSel)
    (t : TState) (hs : ∀ j, s j < M)
    (h12 : s 12 = tfinGLo z t) (h31 : s 31 = z.X)
    (h35 : s 35 = z.isF) (hF : z.isF ≤ 1)
    (hcl : c.checkLo % M = c.checkLo) :
    srun k s (finLowS c) rViol = s rViol ||| c.tfinBadLo z t := by
  have h := finLowS_spec c k s hs (by rw [h35]; exact hF) hcl
  dsimp only at h
  rw [h12, h31, h35] at h
  rw [h]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000 in
theorem finLowPrefixS_viol (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (h31 : st.regs 31 = z.X)
    (h35 : st.regs 35 = z.isF) (hF : z.isF ≤ 1)
    (hcl : c.checkLo % M = c.checkLo) :
    srun k st.regs (finLowPrefixS c) rViol =
      tguard z.isF (tfinGHi z (obsT st))
          (tguard z.isF (tfinGLo z (obsT st)) (obsT st).viol) |||
        c.tfinBadLo z (obsT st) := by
  let G := srun k st.regs finAccumGuardS
  have hi := finAccumGuardS_low_inputs k st z h31 h35 hF
  dsimp only at hi
  have hGlt : ∀ j, G j < M := srun_lt_of_lt k _ st.regs hs
  have hlo := finLowS_badLo c k G z (obsT st) hGlt hi.1 hi.2.2.1
    hi.2.2.2 hF hcl
  have hguard := finAccumGuardS_violT k st z hs h35 hF
  change G rViol = _ at hguard
  rw [finLowPrefixS, srun_append, hlo, hguard]

theorem finLowPrefixS_high_inputs (c : Cfg) (k : Nat) (st : AState)
    (z : TSel) (h31 : st.regs 31 = z.X) (h35 : st.regs 35 = z.isF)
    (hF : z.isF ≤ 1) (hcl : c.checkLo % M = c.checkLo) :
    let L := srun k st.regs (finLowPrefixS c)
    L 13 = tfinGHi z (obsT st) ∧
      L 225 = c.tfinChk z ∧ L 226 = z.X * 10 % M := by
  let G := srun k st.regs finAccumGuardS
  let L := srun k G (finLowS c)
  have hi := finAccumGuardS_low_inputs k st z h31 h35 hF
  dsimp only at hi
  have hG13 := hi.2.1
  have hG31 := hi.2.2.1
  have hG35 := hi.2.2.2
  change G 13 = _ at hG13
  change G 31 = _ at hG31
  change G 35 = _ at hG35
  have hL13 : L 13 = G 13 := finLowS_frame c k G 13 (by omega)
    (by simp [rViol])
  have hL225 : L 225 = z.isF * bnat (c.checkLo ≤ z.X) := by
    rw [show L 225 = G 35 * bnat (c.checkLo ≤ G 31) from
      finLowS_chk c k G hcl (by rw [hG35]; exact hF), hG35, hG31]
  have hL226 : L 226 = z.X * 10 % M := by
    rw [show L 226 = G 31 * 10 % M from finLowS_tenX c k G hcl, hG31]
  rw [finLowPrefixS, srun_append]
  change L 13 = _ ∧ L 225 = _ ∧ L 226 = _
  exact ⟨hL13.trans hG13, by simpa only [Cfg.tfinChk] using hL225, hL226⟩

theorem finHighS_badHi (c : Cfg) (k : Nat) (s : RegState) (z : TSel)
    (t : TState) (hs : ∀ j, s j < M)
    (h13 : s 13 = tfinGHi z t) (h225 : s 225 = c.tfinChk z)
    (h226 : s 226 = z.X * 10 % M) (h225le : s 225 ≤ 1) :
    srun k s finHighS rViol = s rViol ||| c.tfinBadHi z t := by
  have h := finHighS_spec k s hs h225le
  dsimp only at h
  rw [h13, h225, h226] at h
  rw [h]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000 in
theorem finS_viol (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (h31 : st.regs 31 = z.X)
    (h35 : st.regs 35 = z.isF) (hF : z.isF ≤ 1)
    (hcl : c.checkLo % M = c.checkLo) :
    srun k st.regs (finS c) rViol = (c.tfin z (obsT st)).viol := by
  let L := srun k st.regs (finLowPrefixS c)
  have hi := finLowPrefixS_high_inputs c k st z h31 h35 hF hcl
  dsimp only at hi
  have hL13 := hi.1
  have hL225 := hi.2.1
  have hL226 := hi.2.2
  change L 13 = _ at hL13
  change L 225 = _ at hL225
  change L 226 = _ at hL226
  have hLlt : ∀ j, L j < M := srun_lt_of_lt k _ st.regs hs
  have hL225le : L 225 ≤ 1 := by
    rw [hL225, Cfg.tfinChk]
    have hb := bnat_le_one (c.checkLo ≤ z.X)
    simpa only [Nat.one_mul] using Nat.mul_le_mul hF hb
  have hhi := finHighS_badHi c k L z (obsT st) hLlt hL13 hL225 hL226
    hL225le
  have hlo := finLowPrefixS_viol c k st z hs h31 h35 hF hcl
  change L rViol = _ at hlo
  rw [finS, srun_append, hhi, hlo]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000 in
theorem finBody_obs (c : Cfg) (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (h31 : st.regs 31 = z.X)
    (h35 : st.regs 35 = z.isF) (hF : z.isF ≤ 1)
    (hcl : c.checkLo % M = c.checkLo) :
    obsT (arun k st c.finBody) = c.tfin z (obsT st) := by
  rw [finBody_lift, arun_lift]
  let F := srun k st.regs (finS c)
  change
    ({ viol := F rViol, res := F 2, sq := F 3, par := F 4, sigma := F 5,
       wLo := F 6, wHi := F 7, wwLo := F 8, wwHi := F 9,
       dLo := F 10, dHi := F 11, gLo := F 12, gHi := F 13,
       arr := st.arr } : TState) = c.tfin z (obsT st)
  rw [TState.mk.injEq]
  refine ⟨finS_viol c k st z hs h31 h35 hF hcl, ?_⟩
  simp only [Cfg.tfin, obsT]
  have keep (j : Nat) (hj : 2 ≤ j) (hj9 : j ≤ 9) : F j = st.regs j := by
    have h := finS_frame_2_9 c k st.regs j hj hj9
    change F j = st.regs j at h
    exact h
  have hacc := finS_accum_spec c k st.regs z.isF h35 hF
  dsimp only at hacc
  change F 10 = _ ∧ F 11 = _ ∧ F 12 = _ ∧ F 13 = _ at hacc
  constructor
  · exact keep 2 (by omega) (by omega)
  constructor
  · exact keep 3 (by omega) (by omega)
  constructor
  · exact keep 4 (by omega) (by omega)
  constructor
  · exact keep 5 (by omega) (by omega)
  constructor
  · exact keep 6 (by omega) (by omega)
  constructor
  · exact keep 7 (by omega) (by omega)
  constructor
  · exact keep 8 (by omega) (by omega)
  constructor
  · exact keep 9 (by omega) (by omega)
  constructor
  · exact hacc.1
  constructor
  · exact hacc.2.1
  constructor
  · exact hacc.2.2.1
  constructor
  · exact hacc.2.2.2
  trivial

theorem finBody_alwaysDef (c : Cfg) : (c.finBody).all alwaysDef = true := by
  simp [Cfg.finBody, finAccumBody, finGuardBody, Cfg.finLowBody, finHighBody,
    Cfg.finLowPreBody, finLowPostBody, finHighPreBody, finHighPostBody,
    guardBody, LeanCompCert.Ports.CDEMAbelScan.muxBody,
    LeanCompCert.Ports.CDEMAbelScan.mulWideBody, alwaysDef]

theorem finBody_defined (c : Cfg) (len k : Nat) (st : AState) :
    AllDefined len k st c.finBody := by
  apply allDefined_of_alwaysDef
  exact finBody_alwaysDef c

def bodyPrefix (c : Cfg) : List AInstr :=
  ((((c.selBody ++ trialBody) ++ passABody) ++ c.weightBody)) ++ c.passBBody

theorem body_eq_prefix_fin (c : Cfg) :
    c.body = bodyPrefix c ++ c.finBody := by
  simp [Cfg.body, bodyPrefix, List.append_assoc]

theorem body_defined (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M) :
    AllDefined c.arrayLen idx st c.body := by
  rw [body_eq_prefix_fin, AllDefined_append]
  refine ⟨selTrialPassAWeightPassB_defined c hc idx hidx st hs harr, ?_⟩
  exact finBody_defined c c.arrayLen idx (arun idx st (bodyPrefix c))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 100000 in
theorem body_obs (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (h1 : st.regs 1 = 0) (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) :
    obsT (arun idx st c.body) = c.tstep idx (obsT st) := by
  let P := arun idx st (bodyPrefix c)
  let z := c.tsel idx
  have hp := selTrialPassAWeightPassB_obs c hc idx hidx st hs harr h1 hSq hPar
  change obsT P = c.tpassB z
    (tweight z (tpassA z (ttrial z (obsT st)))) at hp
  have hsel := selTrialPassAWeightPassB_selector c hc idx hidx st
  dsimp only at hsel
  have hP31 : P.regs 31 = z.X := hsel.1
  have hP35 : P.regs 35 = z.isF := hsel.2
  have hPlt : ∀ j, P.regs j < M := arun_regs_lt idx _ st hs harr
  have hf := finBody_obs c idx P z hPlt hP31 hP35 (tsel_isF_le_one c idx)
    (Nat.mod_eq_of_lt hc.checkLoLt)
  rw [body_eq_prefix_fin, arun_append]
  calc
    obsT (arun idx P c.finBody) = c.tfin z (obsT P) := hf
    _ = c.tfin z (c.tpassB z
        (tweight z (tpassA z (ttrial z (obsT st))))) := by rw [hp]
    _ = c.tstep idx (obsT st) := rfl

/-! ## The loop bridge -/

theorem lor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

theorem lxor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

theorem ttrial_sq_par_le_one (z : TSel) (t : TState)
    (hP1 : z.inP1 ≤ 1) (hD0 : z.isD0 ≤ 1)
    (hSq : t.sq ≤ 1) (hPar : t.par ≤ 1) :
    (ttrial z t).sq ≤ 1 ∧ (ttrial z t).par ≤ 1 := by
  let sq0 := t.sq * (1 - z.isD0)
  let par0 := t.par * (1 - z.isD0)
  let res := if z.isD0 = 1 then z.n1 else t.res
  let hit := bnat (res % z.d1 = 0) * z.inP1
  let hit2 := bnat ((if hit = 1 then res / z.d1 else res) % z.d1 = 0) * hit
  have hsq0 : sq0 ≤ 1 := by
    rcases (by omega : t.sq = 0 ∨ t.sq = 1) with h | h <;>
      rcases (by omega : z.isD0 = 0 ∨ z.isD0 = 1) with h' | h' <;>
      simp [sq0, h, h']
  have hpar0 : par0 ≤ 1 := by
    rcases (by omega : t.par = 0 ∨ t.par = 1) with h | h <;>
      rcases (by omega : z.isD0 = 0 ∨ z.isD0 = 1) with h' | h' <;>
      simp [par0, h, h']
  have hhit : hit ≤ 1 := by
    dsimp only [hit]
    exact Nat.le_trans (Nat.mul_le_mul_right z.inP1 (bnat_le_one _)) (by omega)
  have hhit2 : hit2 ≤ 1 := by
    dsimp only [hit2]
    exact Nat.le_trans (Nat.mul_le_mul_right hit (bnat_le_one _)) (by omega)
  change sq0 ||| hit2 ≤ 1 ∧ par0 ^^^ hit ≤ 1
  exact ⟨lor_le_one hsq0 hhit2, lxor_le_one hpar0 hhit⟩

theorem tstep_sq_par_le_one (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (t : TState)
    (hSq : t.sq ≤ 1) (hPar : t.par ≤ 1) :
    (c.tstep idx t).sq ≤ 1 ∧ (c.tstep idx t).par ≤ 1 := by
  have hfacts := hc.trialFacts c idx hidx
  dsimp only at hfacts
  have ht := ttrial_sq_par_le_one (c.tsel idx) t hfacts.1 hfacts.2.1 hSq hPar
  exact ht

/-- The small machine invariant needed by the denotation proof.  Word bounds
are intrinsic to every executed instruction; register 1 is the permanent
zero operand, and the trial-division state carries two bits. -/
def MachineInv (st : AState) : Prop :=
  (∀ j, st.regs j < M) ∧ (∀ i, st.arr i < M) ∧ st.regs 1 = 0 ∧
    st.regs 3 ≤ 1 ∧ st.regs 4 ≤ 1

set_option maxRecDepth 100000 in
theorem body_reg_one_frame (c : Cfg) (idx : Nat) (st : AState) :
    (arun idx st c.body).regs 1 = st.regs 1 := by
  apply arun_regs_frame
  intro i hi
  have hb : c.body.all (fun x => decide (adest x ≠ some 1)) = true := by rfl
  exact of_decide_eq_true ((List.all_eq_true.mp hb) i hi)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem body_machineInv (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState) (hInv : MachineInv st) :
    MachineInv (arun idx st c.body) := by
  rcases hInv with ⟨hs, harr, h1, hSq, hPar⟩
  have hobs := body_obs c hc idx hidx st hs harr h1 hSq hPar
  have hbits := tstep_sq_par_le_one c hc idx hidx (obsT st) hSq hPar
  refine ⟨arun_regs_lt idx c.body st hs harr,
    arun_arr_lt idx c.body st hs harr, ?_, ?_, ?_⟩
  · exact (body_reg_one_frame c idx st).trans h1
  · have h := congrArg TState.sq hobs
    have h' : (arun idx st c.body).regs 3 = (c.tstep idx (obsT st)).sq := by
      simpa only [obsT] using h
    rw [h']
    exact hbits.1
  · have h := congrArg TState.par hobs
    have h' : (arun idx st c.body).regs 4 = (c.tstep idx (obsT st)).par := by
      simpa only [obsT] using h
    rw [h']
    exact hbits.2

def machineEntry (c : Cfg) : AState := arun 0 initialAState c.init

theorem init_denotes_machineEntry (c : Cfg) (_hc : Admissible c) :
    denoteAInstrs c.arrayLen 0 initialAState c.init = some (machineEntry c) := by
  have hi := init_reaches_tInit c (by simp [Cfg.arrayLen]; omega)
  exact denoteAInstrs_eq_arun c.arrayLen 0 c.init initialAState hi.1

theorem machineEntry_inv (c : Cfg) (_hc : Admissible c) :
    MachineInv (machineEntry c) := by
  have hi := init_reaches_tInit c (by simp [Cfg.arrayLen]; omega)
  have hs0 : ∀ j, initialAState.regs j < M := by intro j; simp [initialAState, initialState, M]
  have ha0 : ∀ i, initialAState.arr i < M := by intro i; simp [initialAState, M]
  have hobs := hi.2
  unfold machineEntry
  refine ⟨arun_regs_lt 0 c.init initialAState hs0 ha0,
    arun_arr_lt 0 c.init initialAState hs0 ha0, ?_, ?_, ?_⟩
  · change (arun 0 initialAState c.init).regs 1 = 0
    rw [arun_regs_frame]
    · rfl
    · intro i hi
      simp only [Cfg.init, LeanCompCert.Ports.CDEMAbelScan.storeLit,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
  · have h := congrArg TState.sq hobs
    change (arun 0 initialAState c.init).regs 3 = 0 at h
    omega
  · have h := congrArg TState.par hobs
    change (arun 0 initialAState c.init).regs 4 = 0 at h
    omega

def g2Loop (c : Cfg) (hc : Admissible c) :
    LeanCompCert.Verified.Algorithm.ArrayLoop TState where
  program := g1Program c
  inv := MachineInv
  step := fun idx st => arun idx st c.body
  obs := obsT
  g := c.tstep
  out := TState.viol
  entry := machineEntry c
  init_reaches := init_denotes_machineEntry c hc
  inv_entry := machineEntry_inv c hc
  body_sim := by
    intro idx st hidx hInv
    apply denoteAInstrs_eq_arun
    exact body_defined c hc idx hidx st hInv.1 hInv.2.1
  inv_step := by
    intro idx st hidx hInv
    exact body_machineInv c hc idx hidx st hInv
  obs_step := by
    intro idx st hidx hInv
    exact body_obs c hc idx hidx st hInv.1 hInv.2.1 hInv.2.2.1
      hInv.2.2.2.1 hInv.2.2.2.2
  epilogue_reads := by
    intro st hInv
    rfl

theorem g2Loop_value (c : Cfg) (hc : Admissible c) :
    (g2Loop c hc).value = c.tFlag := by
  have hi := (init_reaches_tInit c (by simp [Cfg.arrayLen]; omega)).2
  have hentry : obsT (machineEntry c) = tInit := by
    simpa only [machineEntry] using hi
  change ((List.range c.loopCount).foldl (fun t i => c.tstep i t)
    (obsT (machineEntry c))).viol = c.tRun.viol
  rw [hentry]
  rfl

/-- The emitted array program denotes exactly the transparent-model flag. -/
theorem g1Program_denote (c : Cfg) (hc : Admissible c) :
    (g1Program c).denote = some c.tFlag := by
  exact (g2Loop c hc).denote_eq (g2Loop_value c hc)

end LeanCompCert.Ports.Section413G1Denote
