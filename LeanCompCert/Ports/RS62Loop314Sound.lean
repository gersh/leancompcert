import LeanCompCert.Ports.RS62Loop314HeadSound
import LeanCompCert.Ports.CDEMAbelPrimitives
import LeanCompCert.Verified.ArrayRegFrame

/-! # Symbolic denotation of the compiled RS62 (3.14) verifier -/

namespace LeanCompCert.Ports.RS62Loop314Sound

set_option maxRecDepth 3000000
set_option maxHeartbeats 400000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62Loop314Program
open LeanCompCert.Ports.RS62Loop314GateFrame
open LeanCompCert.Ports.RS62Loop314ProductSound
open LeanCompCert.Ports.RS62Loop314HeadSound

abbrev B : Nat := MulWide.B64
def wval (x : Nat × Nat) : Nat := x.1 + B * x.2

private theorem bit_or_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) :
    x ||| y ≤ 1 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> decide

private theorem bit_or_eq_zero {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1)
    (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp_all

private theorem frame (k r : Nat) (l : List AInstr) (s : AState)
    (h : ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  ArrayRegFrame.arun_frame k r l h s

/-- Word-oriented source model consumed by the compiler proof.  It is the
paper recurrence with primality abstracted as a Boolean predicate and with
the proved word-safe forms of the two fixed-log increments. -/
def loop314 (p : Nat → Bool) : Nat → Nat → Nat → Nat → Nat →
    Option (Nat × Nat × Nat)
  | 0, n, logL, logU, acc =>
      if n * RS62.fpD ≤ acc + n * RS62.fpD * RS62.fpD / (2 * logU) then
        some (logL, logU, acc)
      else none
  | f + 1, n, logL, logU, acc =>
      if p n then
        if 2003 ≤ n then
          if n * RS62.fpD ≤ acc + n * RS62.fpD * RS62.fpD / (2 * logU) then
            loop314 p f (n + 1)
              (RS62.incLWord n + logL) (RS62.incUWord n + logU) (acc + logL)
          else none
        else
          loop314 p f (n + 1)
            (RS62.incLWord n + logL) (RS62.incUWord n + logU) (acc + logL)
      else
        loop314 p f (n + 1)
          (RS62.incLWord n + logL) (RS62.incUWord n + logU) acc

/-- Exact division-free form checked by the compiled guard. -/
theorem guard314_mul_iff (n logU acc : Nat) (hlogU : 0 < logU) :
    n * RS62.fpD ≤ acc + n * RS62.fpD * RS62.fpD / (2 * logU) ↔
      n * RS62.fpD ≤ acc ∨
        (n * RS62.fpD - acc) * (2 * logU) ≤
          n * RS62.fpD * RS62.fpD := by
  have hden : 0 < 2 * logU := Nat.mul_pos (by decide) hlogU
  by_cases hdone : n * RS62.fpD ≤ acc
  · constructor
    · exact fun _ => Or.inl hdone
    · exact fun _ => Nat.le_trans hdone (Nat.le_add_right acc _)
  · have hacc : acc < n * RS62.fpD := by omega
    constructor
    · intro hguard
      apply Or.inr
      apply (Nat.le_div_iff_mul_le hden).mp
      omega
    · intro hguard
      rcases hguard with hdone' | hmul
      · exact Nat.le_trans hdone' (Nat.le_add_right acc _)
      · have hquot : n * RS62.fpD - acc ≤
            n * RS62.fpD * RS62.fpD / (2 * logU) :=
          (Nat.le_div_iff_mul_le hden).mpr hmul
        omega

theorem nD_limbs (n : Nat) :
    (n * RS62.fpD) % B + B * (n / 65536) = n * RS62.fpD := by
  simp only [B, MulWide.B64, RS62.fpD]
  omega

theorem wide_le_iff (x y : Nat × Nat)
    (hx : x.1 < B) (hy : y.1 < B) :
    wval x ≤ wval y ↔ x.2 < y.2 ∨ x.2 = y.2 ∧ x.1 ≤ y.1 := by
  simp only [wval, B, MulWide.B64] at hx hy ⊢
  omega

/-- The suffix's limbwise comparison against `(0,rhs,0)` is exactly the
corresponding natural-number comparison. -/
theorem wide3_le_middle_iff (x : Nat × Nat × Nat) (rhs : Nat)
    (hx0 : x.1 < B) (hx1 : x.2.1 < B) (hx2 : x.2.2 < B)
    (hrhs : rhs < B) :
    MulWide3.wval3 x ≤ B * rhs ↔
      x.2.2 = 0 ∧ (x.2.1 < rhs ∨ x.2.1 = rhs ∧ x.1 = 0) := by
  simp only [MulWide3.wval3, MulWide3.B64, B, MulWide.B64] at hx0 hx1 hx2 hrhs ⊢
  omega

theorem rhs314_middle (n : Nat) :
    B * (n * 4294967296) = n * RS62.fpD * RS62.fpD := by
  simp only [B, MulWide.B64, RS62.fpD]
  omega

/-- Natural-number view of the head island. -/
theorem guardHeadBody_value (k : Nat) (s : AState)
    (hn : s.regs rN ≤ 2 ^ 40)
    (hAccLo : s.regs rAccLo < M) (hAccHi : s.regs rAccHi < M) :
    let out := arun k s guardHeadBody
    (out.regs rDeltaLo, out.regs rDeltaHi) =
        (s.regs rN * RS62.fpD % M, s.regs rN / 65536) ∧
      wval (out.regs rDeltaLo, out.regs rDeltaHi) =
        s.regs rN * RS62.fpD ∧
      out.regs rDone =
        (if s.regs rN * RS62.fpD ≤
            wval (s.regs rAccLo, s.regs rAccHi) then 1 else 0) ∧
      out.arr = s.arr := by
  have hh := guardHeadBody_spec k s hn hAccLo hAccHi
  dsimp only at hh ⊢
  have hlo : s.regs rN * RS62.fpD % M < B := by
    simpa [M, B, MulWide.B64] using
      Nat.mod_lt (s.regs rN * RS62.fpD) (by decide : 0 < M)
  have hlimbs : wval
      (s.regs rN * RS62.fpD % M, s.regs rN / 65536) =
        s.regs rN * RS62.fpD := by
    simpa [wval, M, B, MulWide.B64] using nD_limbs (s.regs rN)
  have hcmp := wide_le_iff
    (s.regs rN * RS62.fpD % M, s.regs rN / 65536)
    (s.regs rAccLo, s.regs rAccHi) hlo
    (by simpa [M, B, MulWide.B64] using hAccLo)
  rw [hlimbs] at hcmp
  have hpair :
      ((arun k s guardHeadBody).regs rDeltaLo,
        (arun k s guardHeadBody).regs rDeltaHi) =
        (s.regs rN * RS62.fpD % M, s.regs rN / 65536) := by
    exact Prod.ext hh.2.2.2.1 hh.2.2.2.2.1
  refine ⟨hpair, ?_, ?_, hh.2.2.2.2.2⟩
  · rw [hh.2.2.2.1, hh.2.2.2.2.1]
    exact hlimbs
  · rw [hh.2.2.1]
    simp only [hcmp]

/-- The subtraction island is the reusable proved two-limb subtraction. -/
theorem guardSubtractBody_spec (k : Nat) (s : AState) :
    let out := arun k s guardSubtractBody
    (out.regs rDeltaLo, out.regs rDeltaHi) =
        AddWide.subWide (s.regs rDeltaLo, s.regs rDeltaHi)
          (s.regs rAccLo, s.regs rAccHi) ∧ out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.guardSubtractBody, arun_lift]
  constructor
  · exact (AddWidePort.subWideBody_run rDeltaLo rDeltaHi rBorrow
      rAccLo rAccHi k
      ⟨by decide, by decide, by decide,
       by decide, by decide, by decide,
       by decide, by decide, by decide⟩ s.regs).1
  · exact arun_lift_arr k
      (AddWidePort.subWideBody rDeltaLo rDeltaHi rBorrow rAccLo rAccHi) s

/-- When the direct comparison failed, recombining the subtraction output is
the exact natural difference. -/
theorem guardSubtractBody_value (k : Nat) (s : AState)
    (hDeltaLo : s.regs rDeltaLo < B) (hDeltaHi : s.regs rDeltaHi < B)
    (hAccLo : s.regs rAccLo < B) (hAccHi : s.regs rAccHi < B)
    (hle : wval (s.regs rAccLo, s.regs rAccHi) ≤
      wval (s.regs rDeltaLo, s.regs rDeltaHi)) :
    let out := arun k s guardSubtractBody
    wval (out.regs rDeltaLo, out.regs rDeltaHi) =
        wval (s.regs rDeltaLo, s.regs rDeltaHi) -
          wval (s.regs rAccLo, s.regs rAccHi) ∧ out.arr = s.arr := by
  have hs := guardSubtractBody_spec k s
  dsimp only at hs ⊢
  rw [hs.1]
  constructor
  · exact AddWide.subWide_exact _ _ ⟨hDeltaLo, hDeltaHi⟩
      ⟨hAccLo, hAccHi⟩ hle
  · exact hs.2

/-- The factor island forms `2*logU`; under the loop invariant it does not
wrap and records a zero wrap bit. -/
theorem guardFactorBody_spec (k : Nat) (s : AState)
    (hFactor : s.regs rLogU + s.regs rLogU < M) :
    let out := arun k s guardFactorBody
    out.regs rFactor = s.regs rLogU + s.regs rLogU ∧
      out.regs rFactorWrap = 0 ∧ out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.guardFactorBody, arun_lift]
  have hmod : (s.regs rLogU + s.regs rLogU) % M =
      s.regs rLogU + s.regs rLogU := Nat.mod_eq_of_lt hFactor
  have hnot : ¬s.regs rLogU + s.regs rLogU < s.regs rLogU := by omega
  have hne : rLogU ≠ rFactor := by decide
  have hFactor' : s.regs 181 + s.regs 181 < 18446744073709551616 := by
    simpa [rLogU, RS62PrimeMaskLadder.rLogU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU, M] using hFactor
  have hmod' : (s.regs 181 + s.regs 181) % 18446744073709551616 =
      s.regs 181 + s.regs 181 := Nat.mod_eq_of_lt hFactor'
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rFactor, rFactorWrap, rLogU, RS62PrimeMaskLadder.rLogU,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
    M, hmod, hmod', hnot, hne, hFactor']

/-- Composed semantic contract for the guard prefix.  The subtraction value
is needed only when the direct comparison bit is zero. -/
theorem guardPrefix_spec (k : Nat) (s : AState)
    (hn : s.regs rN ≤ 2 ^ 40)
    (hAccLo : s.regs rAccLo < M) (hAccHi : s.regs rAccHi < M)
    (hFactor : s.regs rLogU + s.regs rLogU < M) :
    let out := arun k s guardPrefix
    out.regs rDone =
        (if s.regs rN * RS62.fpD ≤
            wval (s.regs rAccLo, s.regs rAccHi) then 1 else 0) ∧
      out.regs rFactor = s.regs rLogU + s.regs rLogU ∧
      out.regs rFactorWrap = 0 ∧
      (out.regs rDone = 0 →
        wval (out.regs rDeltaLo, out.regs rDeltaHi) =
          s.regs rN * RS62.fpD -
            wval (s.regs rAccLo, s.regs rAccHi)) ∧
      out.arr = s.arr := by
  let h := arun k s guardHeadBody
  let d := arun k h guardSubtractBody
  let f := arun k d guardFactorBody
  have hh := guardHeadBody_value k s hn hAccLo hAccHi
  change (h.regs rDeltaLo, h.regs rDeltaHi) =
      (s.regs rN * RS62.fpD % M, s.regs rN / 65536) ∧
    wval (h.regs rDeltaLo, h.regs rDeltaHi) = s.regs rN * RS62.fpD ∧
    h.regs rDone =
      (if s.regs rN * RS62.fpD ≤ wval (s.regs rAccLo, s.regs rAccHi)
        then 1 else 0) ∧ h.arr = s.arr at hh
  have hhAccLo : h.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo guardHeadBody s (by decide)
  have hhAccHi : h.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi guardHeadBody s (by decide)
  have hhLogU : h.regs rLogU = s.regs rLogU :=
    frame k rLogU guardHeadBody s (by decide)
  have hhDoneLo : h.regs rDone ≤ 1 := by
    rw [hh.2.2.1]
    split <;> omega
  have hhDeltaLo : h.regs rDeltaLo < B := by
    rw [show h.regs rDeltaLo = s.regs rN * RS62.fpD % M from
      congrArg Prod.fst hh.1]
    simpa [M, B, MulWide.B64] using
      Nat.mod_lt (s.regs rN * RS62.fpD) (by decide : 0 < M)
  have hhDeltaHi : h.regs rDeltaHi < B := by
    rw [show h.regs rDeltaHi = s.regs rN / 65536 from
      congrArg Prod.snd hh.1]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt hn (by decide))
  have hdDone : d.regs rDone = h.regs rDone :=
    frame k rDone guardSubtractBody h (by decide)
  have hdLogU : d.regs rLogU = h.regs rLogU :=
    frame k rLogU guardSubtractBody h (by decide)
  have hdDelta (hz : d.regs rDone = 0) :
      wval (d.regs rDeltaLo, d.regs rDeltaHi) =
        s.regs rN * RS62.fpD - wval (s.regs rAccLo, s.regs rAccHi) := by
    have hheadZero : h.regs rDone = 0 := by simpa [hdDone] using hz
    have hnot : ¬s.regs rN * RS62.fpD ≤
        wval (s.regs rAccLo, s.regs rAccHi) := by
      intro hle
      rw [hh.2.2.1] at hheadZero
      simp [hle] at hheadZero
    have hsub := guardSubtractBody_value k h hhDeltaLo hhDeltaHi
      (by simpa [hhAccLo, M, B, MulWide.B64] using hAccLo)
      (by simpa [hhAccHi, M, B, MulWide.B64] using hAccHi) (by
        rw [hh.2.1, hhAccLo, hhAccHi]
        omega)
    dsimp only at hsub
    rw [hsub.1, hh.2.1, hhAccLo, hhAccHi]
  have hf := guardFactorBody_spec k d (by
    rw [hdLogU, hhLogU]
    exact hFactor)
  change f.regs rFactor = d.regs rLogU + d.regs rLogU ∧
    f.regs rFactorWrap = 0 ∧ f.arr = d.arr at hf
  have hfDone : f.regs rDone = d.regs rDone :=
    frame k rDone guardFactorBody d (by decide)
  have hfDeltaLo : f.regs rDeltaLo = d.regs rDeltaLo :=
    frame k rDeltaLo guardFactorBody d (by decide)
  have hfDeltaHi : f.regs rDeltaHi = d.regs rDeltaHi :=
    frame k rDeltaHi guardFactorBody d (by decide)
  have hdArr := (guardSubtractBody_spec k h).2
  have hout : arun k s guardPrefix = f := by
    rw [RS62Loop314Program.guardPrefix, arun_append, arun_append]
  dsimp only
  rw [hout]
  refine ⟨?_, ?_, hf.2.1, ?_, hf.2.2.trans (hdArr.trans hh.2.2.2)⟩
  · rw [hfDone, hdDone]
    exact hh.2.2.1
  · rw [hf.1, hdLogU, hhLogU]
  · intro hz
    rw [hfDeltaLo, hfDeltaHi]
    apply hdDelta
    simpa [hfDone] using hz


/-- The first suffix island computes the exact three-limb comparison bit. -/
theorem crossCompareBody_spec (k : Nat) (s : AState)
    (hPLo : s.regs rPLo < B) (hPMid : s.regs rPMid < B)
    (hPTop : s.regs rPTop < B)
    (hRhs : s.regs rN * 4294967296 < B) :
    let out := arun k s crossCompareBody
    out.regs rCross =
      (if MulWide3.wval3 (s.regs rPLo, s.regs rPMid, s.regs rPTop) ≤
          s.regs rN * RS62.fpD * RS62.fpD then 1 else 0) ∧
      out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.crossCompareBody, arun_lift]
  have hiff := wide3_le_middle_iff
    (s.regs rPLo, s.regs rPMid, s.regs rPTop)
    (s.regs rN * 4294967296) hPLo hPMid hPTop hRhs
  rw [rhs314_middle] at hiff
  simp only [hiff]
  have hmod : s.regs rN * 4294967296 % M =
      s.regs rN * 4294967296 := by
    apply Nat.mod_eq_of_lt
    simpa [M, B, MulWide.B64] using hRhs
  have hmod' : s.regs 132 * 4294967296 % 18446744073709551616 =
      s.regs 132 * 4294967296 := by
    simpa [rN, RS62PrimeMaskLadder.rN, M] using hmod
  by_cases ht : s.regs rPTop = 0 <;>
    by_cases hm : s.regs rPMid < s.regs rN * 4294967296 <;>
    by_cases he : s.regs rPMid = s.regs rN * 4294967296 <;>
    by_cases hl : s.regs rPLo = 0 <;>
    simp only [rPTop] at ht <;>
    simp only [rPMid, rN, RS62PrimeMaskLadder.rN] at hm he <;>
    simp only [rPLo] at hl <;>
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rRhsHi, rN, rTopZero, rPTop, rMidLt, rPMid, rMidEq, rLoZero,
      rPLo, rEqLoZero, rCross0, rCross,
      RS62PrimeMaskLadder.rN, M, B, MulWide.B64, hmod, hmod',
      ht, hm, he, hl]

/-- The decision island converts the direct/cross disjunction into one
prime-gated failure bit. -/
theorem guardDecisionBody_spec (k : Nat) (s : AState)
    (hGate : s.regs rGate ≤ 1) (hDone : s.regs rDone ≤ 1)
    (hCross : s.regs rCross ≤ 1) :
    let out := arun k s guardDecisionBody
    out.regs rGateFail =
        (if s.regs rGate = 1 ∧ s.regs rDone = 0 ∧
            s.regs rCross = 0 then 1 else 0) ∧
      out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.guardDecisionBody, arun_lift]
  have hg : s.regs rGate = 0 ∨ s.regs rGate = 1 := by omega
  have hd : s.regs rDone = 0 ∨ s.regs rDone = 1 := by omega
  have hc : s.regs rCross = 0 ∨ s.regs rCross = 1 := by omega
  rcases hg with hg | hg <;> rcases hd with hd | hd <;>
    rcases hc with hc | hc <;>
    simp_all [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rGateFail, rGate, rFail, rPass, rDone, rCross,
      RS62PrimeMaskLadder.rGate, M]

/-- The last two instructions are a fail-closed latch: zero afterwards means
the old latch, the gated failure, and the factor-wrap bit were all zero. -/
theorem guardLatchBody_zero_sound (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) (hFail : s.regs rGateFail ≤ 1)
    (hWrap : s.regs rFactorWrap ≤ 1)
    (hZero : (arun k s guardLatchBody).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs rGateFail = 0 ∧
      s.regs rFactorWrap = 0 := by
  rw [RS62Loop314Program.guardLatchBody, arun_lift] at hZero
  have hb : s.regs rBad = 0 ∨ s.regs rBad = 1 := by omega
  have hf : s.regs rGateFail = 0 ∨ s.regs rGateFail = 1 := by omega
  have hw : s.regs rFactorWrap = 0 ∨ s.regs rFactorWrap = 1 := by omega
  rcases hb with hb | hb <;> rcases hf with hf | hf <;>
    rcases hw with hw | hw <;>
    simp_all [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rBad, rGateFail, rFactorWrap, M]

theorem guardLatchBody_bad_le (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) (hFail : s.regs rGateFail ≤ 1)
    (hWrap : s.regs rFactorWrap ≤ 1) :
    (arun k s guardLatchBody).regs rBad ≤ 1 := by
  rw [RS62Loop314Program.guardLatchBody, arun_lift]
  have hb : s.regs rBad = 0 ∨ s.regs rBad = 1 := by omega
  have hf : s.regs rGateFail = 0 ∨ s.regs rGateFail = 1 := by omega
  have hw : s.regs rFactorWrap = 0 ∨ s.regs rFactorWrap = 1 := by omega
  rcases hb with hb | hb <;> rcases hf with hf | hf <;>
    rcases hw with hw | hw <;>
    simp_all [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rBad, rGateFail, rFactorWrap, M]

/-- A zero suffix latch certifies the old latches and the prime-gated
division-free guard.  This is the compositional form used by the loop proof. -/
theorem guardSuffix_zero_sound (k : Nat) (s : AState)
    (hPLo : s.regs rPLo < B) (hPMid : s.regs rPMid < B)
    (hPTop : s.regs rPTop < B)
    (hRhs : s.regs rN * 4294967296 < B)
    (hGate : s.regs rGate ≤ 1) (hDone : s.regs rDone ≤ 1)
    (hBad : s.regs rBad ≤ 1) (hWrap : s.regs rFactorWrap ≤ 1)
    (hZero : (arun k s guardSuffix).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs rFactorWrap = 0 ∧
      (s.regs rGate = 0 ∨ s.regs rDone = 1 ∨
        MulWide3.wval3 (s.regs rPLo, s.regs rPMid, s.regs rPTop) ≤
          s.regs rN * RS62.fpD * RS62.fpD) := by
  let c := arun k s crossCompareBody
  let d := arun k c guardDecisionBody
  let l := arun k d guardLatchBody
  have hc := crossCompareBody_spec k s hPLo hPMid hPTop hRhs
  change c.regs rCross =
      (if MulWide3.wval3 (s.regs rPLo, s.regs rPMid, s.regs rPTop) ≤
          s.regs rN * RS62.fpD * RS62.fpD then 1 else 0) ∧
      c.arr = s.arr at hc
  have hcGate : c.regs rGate = s.regs rGate :=
    frame k rGate crossCompareBody s (by decide)
  have hcDone : c.regs rDone = s.regs rDone :=
    frame k rDone crossCompareBody s (by decide)
  have hcBad : c.regs rBad = s.regs rBad :=
    frame k rBad crossCompareBody s (by decide)
  have hcWrap : c.regs rFactorWrap = s.regs rFactorWrap :=
    frame k rFactorWrap crossCompareBody s (by decide)
  have hcCross : c.regs rCross ≤ 1 := by
    rw [hc.1]
    split <;> omega
  have hd := guardDecisionBody_spec k c
    (by simpa [hcGate] using hGate) (by simpa [hcDone] using hDone) hcCross
  change d.regs rGateFail =
      (if c.regs rGate = 1 ∧ c.regs rDone = 0 ∧
          c.regs rCross = 0 then 1 else 0) ∧ d.arr = c.arr at hd
  have hdBad : d.regs rBad = c.regs rBad :=
    frame k rBad guardDecisionBody c (by decide)
  have hdWrap : d.regs rFactorWrap = c.regs rFactorWrap :=
    frame k rFactorWrap guardDecisionBody c (by decide)
  have hdFail : d.regs rGateFail ≤ 1 := by
    rw [hd.1]
    split <;> omega
  have hout : arun k s guardSuffix = l := by
    rw [RS62Loop314Program.guardSuffix, arun_append, arun_append]
  have hlZero : l.regs rBad = 0 := by
    rw [← hout]
    exact hZero
  have hl := guardLatchBody_zero_sound k d
    (by simpa [hdBad, hcBad] using hBad) hdFail
    (by simpa [hdWrap, hcWrap] using hWrap) hlZero
  have hb0 : s.regs rBad = 0 := by
    rw [← hcBad, ← hdBad]
    exact hl.1
  have hw0 : s.regs rFactorWrap = 0 := by
    rw [← hcWrap, ← hdWrap]
    exact hl.2.2
  refine ⟨hb0, hw0, ?_⟩
  by_cases hg1 : s.regs rGate = 1
  · by_cases hd0 : s.regs rDone = 0
    · by_cases hmath :
          MulWide3.wval3 (s.regs rPLo, s.regs rPMid, s.regs rPTop) ≤
            s.regs rN * RS62.fpD * RS62.fpD
      · exact Or.inr (Or.inr hmath)
      · have hcross0 : c.regs rCross = 0 := by
          rw [hc.1]
          simp [hmath]
        have hgate1 : c.regs rGate = 1 := by simpa [hcGate] using hg1
        have hdone0 : c.regs rDone = 0 := by simpa [hcDone] using hd0
        have hfail1 : d.regs rGateFail = 1 := by
          rw [hd.1]
          simp [hgate1, hdone0, hcross0]
        omega
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)


/-- A clean sticky bit after the literal compiled guard proves the paper
guard at every gated cell. -/
theorem guardBody_zero_sound (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hn : s.regs rN ≤ 2 ^ 40)
    (hRhs : s.regs rN * 4294967296 < B)
    (hFactor : s.regs rLogU + s.regs rLogU < M)
    (hLogU : 0 < s.regs rLogU) (hGate : s.regs rGate ≤ 1)
    (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s guardBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (s.regs rGate = 0 ∨
        s.regs rN * RS62.fpD ≤
          wval (s.regs rAccLo, s.regs rAccHi) +
            s.regs rN * RS62.fpD * RS62.fpD /
              (2 * s.regs rLogU)) := by
  let p := arun k s guardPrefix
  let q := arun k p productBody
  let z := arun k q guardSuffix
  have hp := guardPrefix_spec k s hn (hword rAccLo) (hword rAccHi) hFactor
  change p.regs rDone =
      (if s.regs rN * RS62.fpD ≤ wval (s.regs rAccLo, s.regs rAccHi)
        then 1 else 0) ∧
    p.regs rFactor = s.regs rLogU + s.regs rLogU ∧
    p.regs rFactorWrap = 0 ∧
    (p.regs rDone = 0 →
      wval (p.regs rDeltaLo, p.regs rDeltaHi) =
        s.regs rN * RS62.fpD - wval (s.regs rAccLo, s.regs rAccHi)) ∧
    p.arr = s.arr at hp
  have hpword : ∀ j, p.regs j < M :=
    arun_regs_word k guardPrefix s hword harray
  have hparray : ∀ j, p.arr j < M := by simpa [hp.2.2.2.2] using harray
  have hprod := productBody_spec k p hpword
  change (q.regs rPLo, q.regs rPMid, q.regs rPTop) =
      MulWide3.mulWideByWord
        (p.regs rDeltaLo, p.regs rDeltaHi) (p.regs rFactor) ∧
    q.arr = p.arr at hprod
  have hqword : ∀ j, q.regs j < M :=
    arun_regs_word k productBody p hpword hparray
  have hpN : p.regs rN = s.regs rN :=
    frame k rN guardPrefix s (by decide)
  have hpGate : p.regs rGate = s.regs rGate :=
    frame k rGate guardPrefix s (by decide)
  have hpBad : p.regs rBad = s.regs rBad :=
    frame k rBad guardPrefix s (by decide)
  have hqN : q.regs rN = p.regs rN :=
    frame k rN productBody p (by decide)
  have hqGate : q.regs rGate = p.regs rGate :=
    productBody_preserves_gate k p
  have hqDone : q.regs rDone = p.regs rDone :=
    frame k rDone productBody p (by decide)
  have hqBad : q.regs rBad = p.regs rBad :=
    frame k rBad productBody p (by decide)
  have hqWrap : q.regs rFactorWrap = p.regs rFactorWrap :=
    frame k rFactorWrap productBody p (by decide)
  have hout : arun k s guardBody = z := by
    rw [RS62Loop314Program.guardBody, arun_append, arun_append]
  have hzZero : z.regs rBad = 0 := by
    rw [← hout]
    exact hZero
  have hzs := guardSuffix_zero_sound k q
    (by simpa [M, B, MulWide.B64] using hqword rPLo)
    (by simpa [M, B, MulWide.B64] using hqword rPMid)
    (by simpa [M, B, MulWide.B64] using hqword rPTop)
    (by simpa [hqN, hpN] using hRhs)
    (by simpa [hqGate, hpGate] using hGate)
    (by rw [hqDone, hp.1]; split <;> omega)
    (by simpa [hqBad, hpBad] using hBad)
    (by rw [hqWrap, hp.2.2.1]; omega) hzZero
  have hsBad : s.regs rBad = 0 := by
    rw [← hpBad, ← hqBad]
    exact hzs.1
  refine ⟨hsBad, ?_⟩
  rcases hzs.2.2 with hgate0 | hdone1 | hcross
  · exact Or.inl (by simpa [hqGate, hpGate] using hgate0)
  · apply Or.inr
    have hpDone1 : p.regs rDone = 1 := by simpa [hqDone] using hdone1
    rw [hp.1] at hpDone1
    have hdirect : s.regs rN * RS62.fpD ≤
        wval (s.regs rAccLo, s.regs rAccHi) := by
      by_cases h : s.regs rN * RS62.fpD ≤
          wval (s.regs rAccLo, s.regs rAccHi)
      · exact h
      · simp [h] at hpDone1
    exact Nat.le_trans hdirect (Nat.le_add_right _ _)
  · apply Or.inr
    apply (guard314_mul_iff (s.regs rN) (s.regs rLogU)
      (wval (s.regs rAccLo, s.regs rAccHi)) hLogU).mpr
    by_cases hdirect : s.regs rN * RS62.fpD ≤
        wval (s.regs rAccLo, s.regs rAccHi)
    · exact Or.inl hdirect
    · apply Or.inr
      have hpDone0 : p.regs rDone = 0 := by rw [hp.1]; simp [hdirect]
      have hdelta : AddWide.wval (p.regs rDeltaLo, p.regs rDeltaHi) =
          s.regs rN * RS62.fpD - wval (s.regs rAccLo, s.regs rAccHi) := by
        simpa only [wval, AddWide.wval, B, AddWide.B64, MulWide.B64] using
          hp.2.2.2.1 hpDone0
      have hmul := MulWide3.mulWideByWord_spec
        (p.regs rDeltaLo, p.regs rDeltaHi) (p.regs rFactor)
        ⟨by simpa [M, MulWide.B64] using hpword rDeltaLo,
         by simpa [M, MulWide.B64] using hpword rDeltaHi⟩
        (by simpa [M, MulWide.B64] using hpword rFactor)
      calc
        (s.regs rN * RS62.fpD - wval (s.regs rAccLo, s.regs rAccHi)) *
              (2 * s.regs rLogU) =
            AddWide.wval (p.regs rDeltaLo, p.regs rDeltaHi) * p.regs rFactor := by
              rw [hdelta, hp.2.1]
              rw [Nat.two_mul]
        _ = MulWide3.wval3
              (q.regs rPLo, q.regs rPMid, q.regs rPTop) := by
                rw [hprod.1, hmul]
        _ ≤ q.regs rN * RS62.fpD * RS62.fpD := hcross
        _ = s.regs rN * RS62.fpD * RS62.fpD := by rw [hqN, hpN]

/-- The accumulator prelude snapshots the high limb and forms the gated
addend exactly. -/
theorem accumulatorPrepBody_spec (k : Nat) (s : AState)
    (hGate : s.regs rGate ≤ 1) (hOldL : s.regs rOldL < M) :
    let out := arun k s accumulatorPrepBody
    out.regs rOldAccHi = s.regs rAccHi ∧
      out.regs rAccAdd = s.regs rGate * s.regs rOldL ∧
      out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.accumulatorPrepBody, arun_lift]
  have hg : s.regs rGate = 0 ∨ s.regs rGate = 1 := by omega
  rcases hg with hg | hg <;>
    simp_all [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rOldAccHi, rAccHi, rAccAdd, rGate, rOldL,
      RS62PrimeMaskLadder.rGate, M]

/-- The accumulator core is the reusable proved one-word wide addition. -/
theorem accumulatorAddBody_spec (k : Nat) (s : AState)
    (hAccHi : s.regs rAccHi < M) :
    let out := arun k s accumulatorAddBody
    (out.regs rAccLo, out.regs rAccHi) =
        AddWide.addWideLo (s.regs rAccLo, s.regs rAccHi)
          (s.regs rAccAdd) ∧ out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.accumulatorAddBody, arun_lift]
  constructor
  · exact (AddWidePort.addWideLoBody_run rAccLo rAccHi rAccCarry
      rAccAdd k (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s.regs hAccHi).1
  · exact arun_lift_arr k
      (AddWidePort.addWideLoBody rAccLo rAccHi rAccCarry rAccAdd) s

/-- A zero accumulator latch certifies that the incoming sticky bit was also
zero. -/
theorem accumulatorLatchBody_zero_sound (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s accumulatorLatchBody).regs rBad = 0) :
    s.regs rBad = 0 ∧ ¬s.regs rAccHi < s.regs rOldAccHi := by
  let wrap := if s.regs rAccHi < s.regs rOldAccHi then 1 else 0
  have hwrap : wrap ≤ 1 := by simp only [wrap]; split <;> omega
  have hout : (arun k s accumulatorLatchBody).regs rBad =
      (s.regs rBad ||| wrap) % M := by
    rw [RS62Loop314Program.accumulatorLatchBody, arun_lift]
    rfl
  have hor : s.regs rBad ||| wrap < M :=
    Nat.lt_of_le_of_lt (bit_or_le_one hBad hwrap) (by decide)
  rw [hout, Nat.mod_eq_of_lt hor] at hZero
  have hz := bit_or_eq_zero hBad hwrap hZero
  exact ⟨hz.1, by
    intro hlt
    simp [wrap, hlt] at hz⟩

theorem accumulatorLatchBody_bad_le (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s accumulatorLatchBody).regs rBad ≤ 1 := by
  let wrap := if s.regs rAccHi < s.regs rOldAccHi then 1 else 0
  have hwrap : wrap ≤ 1 := by simp only [wrap]; split <;> omega
  have hout : (arun k s accumulatorLatchBody).regs rBad =
      (s.regs rBad ||| wrap) % M := by
    rw [RS62Loop314Program.accumulatorLatchBody, arun_lift]
    rfl
  rw [hout, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (bit_or_le_one hBad hwrap) (by decide))]
  exact bit_or_le_one hBad hwrap

/-- A clean compiled accumulator step is exact natural-number addition. -/
theorem accumulatorBody_zero_sound (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (hGate : s.regs rGate ≤ 1) (hBad : s.regs rBad ≤ 1)
    (hSum : wval (s.regs rAccLo, s.regs rAccHi) +
      s.regs rGate * s.regs rOldL < AddWide.B128)
    (hZero : (arun k s accumulatorBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      wval ((arun k s accumulatorBody).regs rAccLo,
        (arun k s accumulatorBody).regs rAccHi) =
          wval (s.regs rAccLo, s.regs rAccHi) +
            s.regs rGate * s.regs rOldL ∧
      (arun k s accumulatorBody).arr = s.arr := by
  let p := arun k s accumulatorPrepBody
  let a := arun k p accumulatorAddBody
  let l := arun k a accumulatorLatchBody
  have hp := accumulatorPrepBody_spec k s hGate (hword rOldL)
  change p.regs rOldAccHi = s.regs rAccHi ∧
    p.regs rAccAdd = s.regs rGate * s.regs rOldL ∧ p.arr = s.arr at hp
  have hpLo : p.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo accumulatorPrepBody s (by decide)
  have hpHi : p.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi accumulatorPrepBody s (by decide)
  have hpBad : p.regs rBad = s.regs rBad :=
    frame k rBad accumulatorPrepBody s (by decide)
  have ha := accumulatorAddBody_spec k p (by rw [hpHi]; exact hword rAccHi)
  change (a.regs rAccLo, a.regs rAccHi) =
      AddWide.addWideLo (p.regs rAccLo, p.regs rAccHi) (p.regs rAccAdd) ∧
    a.arr = p.arr at ha
  have haBad : a.regs rBad = p.regs rBad :=
    frame k rBad accumulatorAddBody p (by decide)
  have haOldHi : a.regs rOldAccHi = p.regs rOldAccHi :=
    frame k rOldAccHi accumulatorAddBody p (by decide)
  have haddM : p.regs rAccAdd < B := by
    rw [hp.2.1]
    have : s.regs rGate = 0 ∨ s.regs rGate = 1 := by omega
    rcases this with hg | hg
    · simp [hg, B, MulWide.B64]
    · simpa [hg, M, B, MulWide.B64] using hword rOldL
  have haValue : wval (a.regs rAccLo, a.regs rAccHi) =
      wval (s.regs rAccLo, s.regs rAccHi) +
        s.regs rGate * s.regs rOldL := by
    rw [ha.1]
    have hexact := AddWide.addWideLo_exact
      (p.regs rAccLo, p.regs rAccHi) (p.regs rAccAdd)
      ⟨by simpa [hpLo, M, B, MulWide.B64] using hword rAccLo,
       by simpa [hpHi, M, B, MulWide.B64] using hword rAccHi⟩
      haddM (by simpa [wval, AddWide.wval, B, AddWide.B64,
        MulWide.B64, hpLo, hpHi, hp.2.1] using hSum)
    simpa [wval, AddWide.wval, B, AddWide.B64, MulWide.B64,
      hpLo, hpHi, hp.2.1] using hexact
  have hout : arun k s accumulatorBody = l := by
    rw [RS62Loop314Program.accumulatorBody, arun_append, arun_append]
  have hlZero : l.regs rBad = 0 := by rw [← hout]; exact hZero
  have hl := accumulatorLatchBody_zero_sound k a
    (by simpa [haBad, hpBad] using hBad) hlZero
  have hlLo : l.regs rAccLo = a.regs rAccLo :=
    frame k rAccLo accumulatorLatchBody a (by decide)
  have hlHi : l.regs rAccHi = a.regs rAccHi :=
    frame k rAccHi accumulatorLatchBody a (by decide)
  have hlArr := arun_lift_arr k
    [ .binop rAccWrap .lt (.reg rAccHi) (.reg rOldAccHi)
    , .binop rBad .bor (.reg rBad) (.reg rAccWrap) ] a
  rw [hout]
  refine ⟨?_, ?_, hlArr.trans (ha.2.trans hp.2.2)⟩
  · rw [← hpBad, ← haBad]
    exact hl.1
  · rw [hlLo, hlHi]
    exact haValue

/-- The lower fixed-log arithmetic island is already proved by the reusable
log-sweep port. -/
theorem logLowerBody_spec (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs rN) (hn40 : s.regs rN ≤ 2 ^ 40) :
    let out := arun k s logLowerBody
    out.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
        RS62.incLWord (s.regs rN) ∧
      out.regs rN = s.regs rN ∧ out.arr = s.arr := by
  simpa [RS62Loop314Program.logLowerBody, rN,
    RS62PrimeMaskLadder.rN] using
    (LeanCompCert.Ports.RamareCombined100M.LogSweep.lowerScalarBody_run
      k s hn2 hn40)

/-- The upper fixed-log arithmetic island is likewise the existing proved
log-sweep implementation. -/
theorem logUpperBody_spec (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs rN) (hn40 : s.regs rN ≤ 2 ^ 40) :
    let out := arun k s logUpperBody
    out.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU =
        RS62.incUWord (s.regs rN) ∧
      out.regs rN = s.regs rN ∧ out.arr = s.arr := by
  simpa [RS62Loop314Program.logUpperBody, rN,
    RS62PrimeMaskLadder.rN] using
    (LeanCompCert.Ports.RamareCombined100M.LogSweep.upperScalarBody_run
      k s hn2 hn40)

/-- The two endpoint commits are exact when the loop invariant gives room. -/
theorem logAddBody_spec (k : Nat) (s : AState)
    (hL : s.regs rLogL +
        s.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL < M)
    (hU : s.regs rLogU +
        s.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU < M) :
    let out := arun k s logAddBody
    out.regs rLogL = s.regs rLogL +
        s.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL ∧
      out.regs rLogU = s.regs rLogU +
        s.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU ∧
      out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.logAddBody, arun_lift]
  have hmL := Nat.mod_eq_of_lt hL
  have hmU := Nat.mod_eq_of_lt hU
  have hL' : s.regs 180 + s.regs 182 < 18446744073709551616 := by
    simpa [rLogL, RS62PrimeMaskLadder.rLogL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL, M] using hL
  have hU' : s.regs 181 + s.regs 183 < 18446744073709551616 := by
    simpa [rLogU, RS62PrimeMaskLadder.rLogU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU, M] using hU
  have hmL' : (s.regs 180 + s.regs 182) % 18446744073709551616 =
      s.regs 180 + s.regs 182 := Nat.mod_eq_of_lt hL'
  have hmU' : (s.regs 181 + s.regs 183) % 18446744073709551616 =
      s.regs 181 + s.regs 183 := Nat.mod_eq_of_lt hU'
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rLogL, rLogU, RS62PrimeMaskLadder.rLogL,
    RS62PrimeMaskLadder.rLogU,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU,
    M, hmL, hmU, hmL', hmU', hL', hU']

/-- With nondecreasing endpoints, a zero wrap latch certifies the incoming
sticky bit was zero while preserving both endpoints. -/
theorem logWrapBody_zero_sound (k : Nat) (s : AState)
    (hOldL : s.regs rOldL ≤ s.regs rLogL)
    (hOldU : s.regs rOldU ≤ s.regs rLogU)
    (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s logWrapBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (arun k s logWrapBody).regs rLogL = s.regs rLogL ∧
      (arun k s logWrapBody).regs rLogU = s.regs rLogU ∧
      (arun k s logWrapBody).arr = s.arr := by
  let bL := if s.regs rLogL < s.regs rOldL then 1 else 0
  let bU := if s.regs rLogU < s.regs rOldU then 1 else 0
  let b := (bL ||| bU) % M
  have hbL : bL ≤ 1 := by simp only [bL]; split <;> omega
  have hbU : bU ≤ 1 := by simp only [bU]; split <;> omega
  have hbor : bL ||| bU < M :=
    Nat.lt_of_le_of_lt (bit_or_le_one hbL hbU) (by decide)
  have hb : b ≤ 1 := by
    simp only [b]
    rw [Nat.mod_eq_of_lt hbor]
    exact bit_or_le_one hbL hbU
  have hnL : ¬s.regs rLogL < s.regs rOldL := by omega
  have hnU : ¬s.regs rLogU < s.regs rOldU := by omega
  have bz : b = 0 := by simp [b, bL, bU, hnL, hnU]
  have hout : (arun k s logWrapBody).regs rBad =
      (s.regs rBad ||| b) % M := by
    rw [RS62Loop314Program.logWrapBody, arun_lift]
    rfl
  have hor : s.regs rBad ||| b < M :=
    Nat.lt_of_le_of_lt (bit_or_le_one hBad hb) (by decide)
  rw [hout, Nat.mod_eq_of_lt hor] at hZero
  have hz := bit_or_eq_zero hBad hb hZero
  exact ⟨hz.1,
    frame k rLogL logWrapBody s (by decide),
    frame k rLogU logWrapBody s (by decide),
    arun_lift_arr k
      [ .binop rWrapL .lt (.reg rLogL) (.reg rOldL)
      , .binop rWrapU .lt (.reg rLogU) (.reg rOldU)
      , .binop rLogWrap .bor (.reg rWrapL) (.reg rWrapU)
      , .binop rBad .bor (.reg rBad) (.reg rLogWrap) ] s⟩

theorem logWrapBody_bad_le (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s logWrapBody).regs rBad ≤ 1 := by
  let bL := if s.regs rLogL < s.regs rOldL then 1 else 0
  let bU := if s.regs rLogU < s.regs rOldU then 1 else 0
  let b := (bL ||| bU) % M
  have hbL : bL ≤ 1 := by simp only [bL]; split <;> omega
  have hbU : bU ≤ 1 := by simp only [bU]; split <;> omega
  have hbor : bL ||| bU < M :=
    Nat.lt_of_le_of_lt (bit_or_le_one hbL hbU) (by decide)
  have hb : b ≤ 1 := by
    simp only [b]
    rw [Nat.mod_eq_of_lt hbor]
    exact bit_or_le_one hbL hbU
  have hout : (arun k s logWrapBody).regs rBad =
      (s.regs rBad ||| b) % M := by
    rw [RS62Loop314Program.logWrapBody, arun_lift]
    rfl
  rw [hout, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (bit_or_le_one hBad hb) (by decide))]
  exact bit_or_le_one hBad hb

/-- A clean compiled log step advances both endpoint sums by the exact fixed
increments computed by compiled scalar code. -/
theorem logBody_zero_sound (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs rN) (hn40 : s.regs rN ≤ 2 ^ 40)
    (hOldL : s.regs rOldL = s.regs rLogL)
    (hOldU : s.regs rOldU = s.regs rLogU)
    (hBad : s.regs rBad ≤ 1)
    (hL : s.regs rLogL + RS62.incLWord (s.regs rN) < M)
    (hU : s.regs rLogU + RS62.incUWord (s.regs rN) < M)
    (hZero : (arun k s logBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (arun k s logBody).regs rLogL =
        s.regs rLogL + RS62.incLWord (s.regs rN) ∧
      (arun k s logBody).regs rLogU =
        s.regs rLogU + RS62.incUWord (s.regs rN) ∧
      (arun k s logBody).arr = s.arr := by
  let l := arun k s logLowerBody
  let u := arun k l logUpperBody
  let a := arun k u logAddBody
  let w := arun k a logWrapBody
  have hl := logLowerBody_spec k s hn2 hn40
  change l.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
      RS62.incLWord (s.regs rN) ∧ l.regs rN = s.regs rN ∧
    l.arr = s.arr at hl
  have hu := logUpperBody_spec k l (by rw [hl.2.1]; exact hn2)
    (by rw [hl.2.1]; exact hn40)
  change u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU =
      RS62.incUWord (l.regs rN) ∧ u.regs rN = l.regs rN ∧
    u.arr = l.arr at hu
  have hlLogL : l.regs rLogL = s.regs rLogL :=
    frame k rLogL logLowerBody s (by decide)
  have hlLogU : l.regs rLogU = s.regs rLogU :=
    frame k rLogU logLowerBody s (by decide)
  have hlOldL : l.regs rOldL = s.regs rOldL :=
    frame k rOldL logLowerBody s (by decide)
  have hlOldU : l.regs rOldU = s.regs rOldU :=
    frame k rOldU logLowerBody s (by decide)
  have hlBad : l.regs rBad = s.regs rBad :=
    frame k rBad logLowerBody s (by decide)
  have huIL : u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
      l.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL :=
    frame k LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL
      logUpperBody l (by decide)
  have huLogL : u.regs rLogL = l.regs rLogL :=
    frame k rLogL logUpperBody l (by decide)
  have huLogU : u.regs rLogU = l.regs rLogU :=
    frame k rLogU logUpperBody l (by decide)
  have huOldL : u.regs rOldL = l.regs rOldL :=
    frame k rOldL logUpperBody l (by decide)
  have huOldU : u.regs rOldU = l.regs rOldU :=
    frame k rOldU logUpperBody l (by decide)
  have huBad : u.regs rBad = l.regs rBad :=
    frame k rBad logUpperBody l (by decide)
  have ha := logAddBody_spec k u (by
    rw [huLogL, hlLogL, huIL, hl.1]
    exact hL) (by
    rw [huLogU, hlLogU, hu.1, hl.2.1]
    exact hU)
  change a.regs rLogL = u.regs rLogL +
      u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL ∧
    a.regs rLogU = u.regs rLogU +
      u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU ∧
    a.arr = u.arr at ha
  have haOldL : a.regs rOldL = u.regs rOldL :=
    frame k rOldL logAddBody u (by decide)
  have haOldU : a.regs rOldU = u.regs rOldU :=
    frame k rOldU logAddBody u (by decide)
  have haBad : a.regs rBad = u.regs rBad :=
    frame k rBad logAddBody u (by decide)
  have hout : arun k s logBody = w := by
    rw [RS62Loop314Program.logBody, arun_append, arun_append,
      RS62Loop314Program.logCommitBody, arun_append]
  have hwZero : w.regs rBad = 0 := by rw [← hout]; exact hZero
  have hw := logWrapBody_zero_sound k a (by
    rw [haOldL, huOldL, hlOldL, hOldL, ha.1]
    omega) (by
    rw [haOldU, huOldU, hlOldU, hOldU, ha.2.1]
    omega) (by simpa [haBad, huBad, hlBad] using hBad) hwZero
  rw [hout]
  refine ⟨?_, ?_, ?_, hw.2.2.2.trans (ha.2.2.trans (hu.2.2.trans hl.2.2))⟩
  · rw [← hlBad, ← huBad, ← haBad]
    exact hw.1
  · rw [hw.2.1, ha.1, huLogL, hlLogL, huIL, hl.1]
  · rw [hw.2.2.1, ha.2.1, huLogU, hlLogU, hu.1, hl.2.1]

/-- Exact semantics of the loop's mask load and candidate decoder. -/
theorem maskPrefix_spec (n0 k : Nat) (s : AState)
    (hkM : k < M) (hnM : n0 + k < M) :
    let out := arun k s (maskPrefix n0)
    out.regs rGate = s.arr k ∧ out.regs rN = n0 + k ∧
      out.arr = s.arr := by
  simp [RS62Loop314Program.maskPrefix, arun, astep,
    RS62PrimeMaskLadder.rAddr, rGate, rN,
    RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hnM]

/-- The two old-log snapshots are literal register moves. -/
theorem snapshotBody_spec (k : Nat) (s : AState) :
    let out := arun k s snapshotBody
    out.regs rOldL = s.regs rLogL ∧ out.regs rOldU = s.regs rLogU ∧
      out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.snapshotBody, arun_lift]
  simp [srun, sdest, sval, denoteOperand, RegState.set,
    rOldL, rOldU, rLogL, rLogU, RS62PrimeMaskLadder.rLogL,
    RS62PrimeMaskLadder.rLogU,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU]

theorem guardBody_bad_le (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hn : s.regs rN ≤ 2 ^ 40)
    (hRhs : s.regs rN * 4294967296 < B)
    (hFactor : s.regs rLogU + s.regs rLogU < M)
    (hGate : s.regs rGate ≤ 1) (hBad : s.regs rBad ≤ 1) :
    (arun k s guardBody).regs rBad ≤ 1 := by
  let p := arun k s guardPrefix
  let q := arun k p productBody
  let c := arun k q crossCompareBody
  let d := arun k c guardDecisionBody
  let l := arun k d guardLatchBody
  have hp := guardPrefix_spec k s hn (hword rAccLo) (hword rAccHi) hFactor
  change p.regs rDone =
      (if s.regs rN * RS62.fpD ≤ wval (s.regs rAccLo, s.regs rAccHi)
        then 1 else 0) ∧
    p.regs rFactor = s.regs rLogU + s.regs rLogU ∧
    p.regs rFactorWrap = 0 ∧
    (p.regs rDone = 0 →
      wval (p.regs rDeltaLo, p.regs rDeltaHi) =
        s.regs rN * RS62.fpD - wval (s.regs rAccLo, s.regs rAccHi)) ∧
    p.arr = s.arr at hp
  have hpword : ∀ j, p.regs j < M :=
    arun_regs_word k guardPrefix s hword harray
  have hparray : ∀ j, p.arr j < M := by simpa [hp.2.2.2.2] using harray
  have hqword : ∀ j, q.regs j < M :=
    arun_regs_word k productBody p hpword hparray
  have hpN : p.regs rN = s.regs rN := frame k rN guardPrefix s (by decide)
  have hqN : q.regs rN = p.regs rN := frame k rN productBody p (by decide)
  have hc := crossCompareBody_spec k q
    (by simpa [M, B, MulWide.B64] using hqword rPLo)
    (by simpa [M, B, MulWide.B64] using hqword rPMid)
    (by simpa [M, B, MulWide.B64] using hqword rPTop)
    (by simpa [hqN, hpN] using hRhs)
  change c.regs rCross =
      (if MulWide3.wval3 (q.regs rPLo, q.regs rPMid, q.regs rPTop) ≤
          q.regs rN * RS62.fpD * RS62.fpD then 1 else 0) ∧
    c.arr = q.arr at hc
  have hcCross : c.regs rCross ≤ 1 := by rw [hc.1]; split <;> omega
  have hpDoneLe : p.regs rDone ≤ 1 := by rw [hp.1]; split <;> omega
  have hqDone : q.regs rDone = p.regs rDone :=
    frame k rDone productBody p (by decide)
  have hcDone : c.regs rDone = q.regs rDone :=
    frame k rDone crossCompareBody q (by decide)
  have hpGate : p.regs rGate = s.regs rGate :=
    frame k rGate guardPrefix s (by decide)
  have hqGate : q.regs rGate = p.regs rGate :=
    productBody_preserves_gate k p
  have hcGate : c.regs rGate = q.regs rGate :=
    frame k rGate crossCompareBody q (by decide)
  have hd := guardDecisionBody_spec k c
    (by simpa [hcGate, hqGate, hpGate] using hGate)
    (by simpa [hcDone, hqDone] using hpDoneLe) hcCross
  change d.regs rGateFail =
      (if c.regs rGate = 1 ∧ c.regs rDone = 0 ∧ c.regs rCross = 0
        then 1 else 0) ∧ d.arr = c.arr at hd
  have hdFail : d.regs rGateFail ≤ 1 := by rw [hd.1]; split <;> omega
  have hpBad : p.regs rBad = s.regs rBad :=
    frame k rBad guardPrefix s (by decide)
  have hqBad : q.regs rBad = p.regs rBad :=
    frame k rBad productBody p (by decide)
  have hcBad : c.regs rBad = q.regs rBad :=
    frame k rBad crossCompareBody q (by decide)
  have hdBad : d.regs rBad = c.regs rBad :=
    frame k rBad guardDecisionBody c (by decide)
  have hpWrap := hp.2.2.1
  have hqWrap : q.regs rFactorWrap = p.regs rFactorWrap :=
    frame k rFactorWrap productBody p (by decide)
  have hcWrap : c.regs rFactorWrap = q.regs rFactorWrap :=
    frame k rFactorWrap crossCompareBody q (by decide)
  have hdWrap : d.regs rFactorWrap = c.regs rFactorWrap :=
    frame k rFactorWrap guardDecisionBody c (by decide)
  have hl := guardLatchBody_bad_le k d
    (by simpa [hdBad, hcBad, hqBad, hpBad] using hBad) hdFail
    (by rw [hdWrap, hcWrap, hqWrap, hpWrap]; omega)
  have hout : arun k s guardBody = l := by
    simp only [RS62Loop314Program.guardBody, arun_append,
      RS62Loop314Program.guardSuffix, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  rw [hout]
  exact hl

theorem accumulatorBody_bad_le (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s accumulatorBody).regs rBad ≤ 1 := by
  let p := arun k s accumulatorPrepBody
  let a := arun k p accumulatorAddBody
  let l := arun k a accumulatorLatchBody
  have hpBad : p.regs rBad = s.regs rBad :=
    frame k rBad accumulatorPrepBody s (by decide)
  have haBad : a.regs rBad = p.regs rBad :=
    frame k rBad accumulatorAddBody p (by decide)
  have hl := accumulatorLatchBody_bad_le k a
    (by simpa [haBad, hpBad] using hBad)
  have hout : arun k s accumulatorBody = l := by
    rw [RS62Loop314Program.accumulatorBody, arun_append, arun_append]
  rw [hout]
  exact hl

theorem logBody_bad_le (k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s logBody).regs rBad ≤ 1 := by
  let l := arun k s logLowerBody
  let u := arun k l logUpperBody
  let a := arun k u logAddBody
  let w := arun k a logWrapBody
  have hlBad : l.regs rBad = s.regs rBad :=
    frame k rBad logLowerBody s (by decide)
  have huBad : u.regs rBad = l.regs rBad :=
    frame k rBad logUpperBody l (by decide)
  have haBad : a.regs rBad = u.regs rBad :=
    frame k rBad logAddBody u (by decide)
  have hw := logWrapBody_bad_le k a
    (by simpa [haBad, huBad, hlBad] using hBad)
  have hout : arun k s logBody = w := by
    rw [RS62Loop314Program.logBody, arun_append, arun_append,
      RS62Loop314Program.logCommitBody, arun_append]
  rw [hout]
  exact hw

/-- One clean compiled loop cell implements the source recurrence step. -/
theorem body_zero_sound (n0 k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hkM : k < M) (hnM : n0 + k < M)
    (hn2 : 2 ≤ n0 + k) (hn40 : n0 + k ≤ 2 ^ 40)
    (hRhs : (n0 + k) * 4294967296 < B)
    (hCell : s.arr k ≤ 1)
    (hFactor : s.regs rLogU + s.regs rLogU < M)
    (hLogU : 0 < s.regs rLogU)
    (hAccSum : wval (s.regs rAccLo, s.regs rAccHi) +
      s.arr k * s.regs rLogL < AddWide.B128)
    (hL : s.regs rLogL + RS62.incLWord (n0 + k) < M)
    (hU : s.regs rLogU + RS62.incUWord (n0 + k) < M)
    (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s (body n0)).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (s.arr k = 0 ∨
        (n0 + k) * RS62.fpD ≤
          wval (s.regs rAccLo, s.regs rAccHi) +
            (n0 + k) * RS62.fpD * RS62.fpD /
              (2 * s.regs rLogU)) ∧
      (arun k s (body n0)).regs rLogL =
        s.regs rLogL + RS62.incLWord (n0 + k) ∧
      (arun k s (body n0)).regs rLogU =
        s.regs rLogU + RS62.incUWord (n0 + k) ∧
      wval ((arun k s (body n0)).regs rAccLo,
        (arun k s (body n0)).regs rAccHi) =
          wval (s.regs rAccLo, s.regs rAccHi) +
            s.arr k * s.regs rLogL ∧
      (arun k s (body n0)).arr = s.arr := by
  let m := arun k s (maskPrefix n0)
  let x := arun k m snapshotBody
  let g := arun k x guardBody
  let a := arun k g accumulatorBody
  let l := arun k a logBody
  have hm := maskPrefix_spec n0 k s hkM hnM
  change m.regs rGate = s.arr k ∧ m.regs rN = n0 + k ∧
    m.arr = s.arr at hm
  have hmword : ∀ j, m.regs j < M :=
    arun_regs_word k (maskPrefix n0) s hword harray
  have hmarray : ∀ j, m.arr j < M := by simpa [hm.2.2] using harray
  have hmLogL : m.regs rLogL = s.regs rLogL :=
    frame k rLogL (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rLogL, RS62PrimeMaskLadder.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL] <;> decide)
  have hmLogU : m.regs rLogU = s.regs rLogU :=
    frame k rLogU (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rLogU, RS62PrimeMaskLadder.rLogU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] <;> decide)
  have hmAccLo : m.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rAccLo] <;> decide)
  have hmAccHi : m.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rAccHi] <;> decide)
  have hmBad : m.regs rBad = s.regs rBad :=
    frame k rBad (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rBad] <;> decide)
  have hx := snapshotBody_spec k m
  change x.regs rOldL = m.regs rLogL ∧ x.regs rOldU = m.regs rLogU ∧
    x.arr = m.arr at hx
  have hxword : ∀ j, x.regs j < M :=
    arun_regs_word k snapshotBody m hmword hmarray
  have hxarray : ∀ j, x.arr j < M := by simpa [hx.2.2] using hmarray
  have hxN : x.regs rN = m.regs rN :=
    frame k rN snapshotBody m (by decide)
  have hxGate : x.regs rGate = m.regs rGate :=
    frame k rGate snapshotBody m (by decide)
  have hxLogL : x.regs rLogL = m.regs rLogL :=
    frame k rLogL snapshotBody m (by decide)
  have hxLogU : x.regs rLogU = m.regs rLogU :=
    frame k rLogU snapshotBody m (by decide)
  have hxAccLo : x.regs rAccLo = m.regs rAccLo :=
    frame k rAccLo snapshotBody m (by decide)
  have hxAccHi : x.regs rAccHi = m.regs rAccHi :=
    frame k rAccHi snapshotBody m (by decide)
  have hxBad : x.regs rBad = m.regs rBad :=
    frame k rBad snapshotBody m (by decide)
  have hgword : ∀ j, g.regs j < M :=
    arun_regs_word k guardBody x hxword hxarray
  have hgArr : g.arr = x.arr :=
    arun_scalarOnly_arr k guardBody x (by trivial)
  have hgarray : ∀ j, g.arr j < M := by simpa [hgArr] using hxarray
  have hgN : g.regs rN = x.regs rN :=
    frame k rN guardBody x (by decide)
  have hgGate : g.regs rGate = x.regs rGate :=
    guardBody_preserves_gate k x
  have hgLogL : g.regs rLogL = x.regs rLogL :=
    frame k rLogL guardBody x (by decide)
  have hgLogU : g.regs rLogU = x.regs rLogU :=
    frame k rLogU guardBody x (by decide)
  have hgOldL : g.regs rOldL = x.regs rOldL :=
    frame k rOldL guardBody x (by decide)
  have hgOldU : g.regs rOldU = x.regs rOldU :=
    frame k rOldU guardBody x (by decide)
  have hgAccLo : g.regs rAccLo = x.regs rAccLo :=
    frame k rAccLo guardBody x (by decide)
  have hgAccHi : g.regs rAccHi = x.regs rAccHi :=
    frame k rAccHi guardBody x (by decide)
  have hgBad := guardBody_bad_le k x hxword hxarray
    (by rw [hxN, hm.2.1]; exact hn40)
    (by rw [hxN, hm.2.1]; exact hRhs)
    (by rw [hxLogU, hmLogU]; exact hFactor)
    (by rw [hxGate, hm.1]; exact hCell)
    (by rw [hxBad, hmBad]; exact hBad)
  have haBad := accumulatorBody_bad_le k g hgBad
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k accumulatorBody g hgword hgarray
  have haArr : a.arr = g.arr :=
    arun_scalarOnly_arr k accumulatorBody g (by trivial)
  have haarray : ∀ j, a.arr j < M := by simpa [haArr] using hgarray
  have haN : a.regs rN = g.regs rN :=
    frame k rN accumulatorBody g (by decide)
  have haLogL : a.regs rLogL = g.regs rLogL :=
    frame k rLogL accumulatorBody g (by decide)
  have haLogU : a.regs rLogU = g.regs rLogU :=
    frame k rLogU accumulatorBody g (by decide)
  have haOldL : a.regs rOldL = g.regs rOldL :=
    frame k rOldL accumulatorBody g (by decide)
  have haOldU : a.regs rOldU = g.regs rOldU :=
    frame k rOldU accumulatorBody g (by decide)
  have hout : arun k s (body n0) = l := by
    simp only [RS62Loop314Program.body, arun_append]
    rfl
  have hlZero : l.regs rBad = 0 := by rw [← hout]; exact hZero
  have hl := logBody_zero_sound k a
    (by rw [haN, hgN, hxN, hm.2.1]; exact hn2)
    (by rw [haN, hgN, hxN, hm.2.1]; exact hn40)
    (by rw [haOldL, hgOldL, hx.1, haLogL, hgLogL, hxLogL])
    (by rw [haOldU, hgOldU, hx.2.1, haLogU, hgLogU, hxLogU])
    haBad
    (by rw [haLogL, hgLogL, hxLogL, hmLogL, haN, hgN, hxN, hm.2.1]; exact hL)
    (by rw [haLogU, hgLogU, hxLogU, hmLogU, haN, hgN, hxN, hm.2.1]; exact hU)
    hlZero
  have haSound := accumulatorBody_zero_sound k g hgword
    (by rw [hgGate, hxGate, hm.1]; exact hCell)
    hgBad (by
      rw [hgAccLo, hgAccHi, hxAccLo, hxAccHi, hmAccLo, hmAccHi,
        hgGate, hxGate, hm.1, hgOldL, hx.1, hmLogL]
      exact hAccSum) hl.1
  have hgSound := guardBody_zero_sound k x hxword hxarray
    (by rw [hxN, hm.2.1]; exact hn40)
    (by rw [hxN, hm.2.1]; exact hRhs)
    (by rw [hxLogU, hmLogU]; exact hFactor)
    (by rw [hxLogU, hmLogU]; exact hLogU)
    (by rw [hxGate, hm.1]; exact hCell)
    (by rw [hxBad, hmBad]; exact hBad) haSound.1
  have hlAccLo : l.regs rAccLo = a.regs rAccLo :=
    frame k rAccLo logBody a (by decide)
  have hlAccHi : l.regs rAccHi = a.regs rAccHi :=
    frame k rAccHi logBody a (by decide)
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmBad, ← hxBad]
    exact hgSound.1
  · rcases hgSound.2 with hgate0 | hguard
    · exact Or.inl (by simpa [hxGate, hm.1] using hgate0)
    · exact Or.inr (by simpa [hxN, hm.2.1, hxLogU, hmLogU,
        hxAccLo, hxAccHi, hmAccLo, hmAccHi] using hguard)
  · rw [hl.2.1, haLogL, hgLogL, hxLogL, hmLogL,
      haN, hgN, hxN, hm.2.1]
  · rw [hl.2.2.1, haLogU, hgLogU, hxLogU, hmLogU,
      haN, hgN, hxN, hm.2.1]
  · rw [hlAccLo, hlAccHi, haSound.2.1, hgAccLo, hgAccHi,
      hxAccLo, hxAccHi, hmAccLo, hmAccHi, hgGate, hxGate, hm.1,
      hgOldL, hx.1, hmLogL]
  · exact hl.2.2.2.trans (haArr.trans (hgArr.trans (hx.2.2.trans hm.2.2)))

/-- The final prelude installs the forced endpoint guard. -/
theorem finalPrepBody_spec (k nEnd : Nat) (s : AState)
    (hnM : nEnd < M) :
    let out := arun k s (finalPrepBody nEnd)
    out.regs rGate = 1 ∧ out.regs rN = nEnd ∧ out.arr = s.arr := by
  dsimp only
  rw [RS62Loop314Program.finalPrepBody, arun_lift]
  have hnM' : nEnd < 18446744073709551616 := by simpa [M] using hnM
  simp [srun, sdest, sval, denoteOperand, RegState.set,
    rGate, rN, RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
    M, Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hnM']

/-- A clean compiled epilogue proves the source fuel-zero endpoint guard. -/
theorem finalBody_zero_sound (k nEnd : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hnM : nEnd < M) (hn40 : nEnd ≤ 2 ^ 40)
    (hRhs : nEnd * 4294967296 < B)
    (hFactor : s.regs rLogU + s.regs rLogU < M)
    (hLogU : 0 < s.regs rLogU) (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s (finalBody nEnd)).regs rBad = 0) :
    s.regs rBad = 0 ∧
      nEnd * RS62.fpD ≤
        wval (s.regs rAccLo, s.regs rAccHi) +
          nEnd * RS62.fpD * RS62.fpD / (2 * s.regs rLogU) := by
  let p := arun k s (finalPrepBody nEnd)
  let g := arun k p guardBody
  have hp := finalPrepBody_spec k nEnd s hnM
  change p.regs rGate = 1 ∧ p.regs rN = nEnd ∧ p.arr = s.arr at hp
  have hpword : ∀ j, p.regs j < M :=
    arun_regs_word k (finalPrepBody nEnd) s hword harray
  have hparray : ∀ j, p.arr j < M := by simpa [hp.2.2] using harray
  have hpLogU : p.regs rLogU = s.regs rLogU :=
    frame k rLogU (finalPrepBody nEnd) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        rLogU, RS62PrimeMaskLadder.rLogU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] <;>
        decide)
  have hpAccLo : p.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo (finalPrepBody nEnd) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        rAccLo] <;> decide)
  have hpAccHi : p.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi (finalPrepBody nEnd) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        rAccHi] <;> decide)
  have hpBad : p.regs rBad = s.regs rBad :=
    frame k rBad (finalPrepBody nEnd) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        rBad] <;> decide)
  have hout : arun k s (finalBody nEnd) = g := by
    rw [RS62Loop314Program.finalBody, arun_append]
  have hgZero : g.regs rBad = 0 := by rw [← hout]; exact hZero
  have hg := guardBody_zero_sound k p hpword hparray
    (by rw [hp.2.1]; exact hn40)
    (by rw [hp.2.1]; exact hRhs)
    (by rw [hpLogU]; exact hFactor)
    (by rw [hpLogU]; exact hLogU)
    (by rw [hp.1]; omega) (by rw [hpBad]; exact hBad) hgZero
  refine ⟨?_, ?_⟩
  · rw [← hpBad]
    exact hg.1
  · rcases hg.2 with hgate | hguard
    · rw [hp.1] at hgate
      omega
    · simpa [hp.2.1, hpLogU, hpAccLo, hpAccHi] using hguard

/-! ## Symbolic segment fold -/

structure State314 where
  logL : Nat
  logU : Nat
  acc : Nat
deriving Repr, DecidableEq

def sourceStep (arr : Nat → Nat) (n0 : Nat)
    (st : State314) (k : Nat) : State314 := {
  logL := st.logL + RS62.incLWord (n0 + k)
  logU := st.logU + RS62.incUWord (n0 + k)
  acc := st.acc + arr k * st.logL
}

def sourceFold (arr : Nat → Nat) (n0 f : Nat) (initial : State314) :
    State314 :=
  (List.range f).foldl (sourceStep arr n0) initial

theorem sourceFold_succ (arr : Nat → Nat) (n0 f : Nat)
    (initial : State314) :
    sourceFold arr n0 (f + 1) initial =
      sourceStep arr n0 (sourceFold arr n0 f initial) f := by
  unfold sourceFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sourceFold_cons (arr : Nat → Nat) (n0 f : Nat)
    (initial : State314) :
    sourceFold arr n0 (f + 1) initial =
      sourceFold (fun k => arr (k + 1)) (n0 + 1) f
        (sourceStep arr n0 initial 0) := by
  induction f with
  | zero =>
      rw [sourceFold_succ]
      rfl
  | succ f ih =>
      rw [sourceFold_succ]
      rw [ih]
      rw [sourceFold_succ]
      simp [sourceStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Per-prefix arithmetic room.  Production campaigns establish these cheap
word bounds; the finite prime/log scan itself remains compiled C. -/
def Room (arr : Nat → Nat) (n0 f : Nat) (initial : State314) : Prop :=
  ∀ k, k < f →
    let st := sourceFold arr n0 k initial
    arr k ≤ 1 ∧ 0 < st.logU ∧ st.logU + st.logU < M ∧
      st.acc + arr k * st.logL < AddWide.B128 ∧
      st.logL + RS62.incLWord (n0 + k) < M ∧
      st.logU + RS62.incUWord (n0 + k) < M

private theorem room_mono (arr : Nat → Nat) (n0 : Nat) (initial : State314)
    {f g : Nat} (hfg : f ≤ g) (h : Room arr n0 g initial) :
    Room arr n0 f initial := by
  intro k hk
  exact h k (Nat.lt_of_lt_of_le hk hfg)

private theorem rhs_bound_mono {a b : Nat} (hab : a ≤ b)
    (h : b * 4294967296 < B) : a * 4294967296 < B :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 4294967296 hab) h

def machineFoldState (arr : Nat → Nat) (n0 f SL SU accLo accHi : Nat) :
    AState :=
  (List.range f).foldl (fun st k => arun k st (body n0))
    (arun 0 (initialAStateWithArray arr) (init SL SU accLo accHi))

theorem machineFoldState_succ (arr : Nat → Nat)
    (n0 f SL SU accLo accHi : Nat) :
    machineFoldState arr n0 (f + 1) SL SU accLo accHi =
      arun f (machineFoldState arr n0 f SL SU accLo accHi) (body n0) := by
  unfold machineFoldState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem init_spec (arr : Nat → Nat) (SL SU accLo accHi : Nat)
    (hSL : SL < M) (hSU : SU < M)
    (hLo : accLo < M) (hHi : accHi < M) :
    let out := arun 0 (initialAStateWithArray arr) (init SL SU accLo accHi)
    out.regs rLogL = SL ∧ out.regs rLogU = SU ∧
      out.regs rAccLo = accLo ∧ out.regs rAccHi = accHi ∧
      out.regs rBad = 0 ∧ out.arr = arr := by
  simp [RS62Loop314Program.init, RS62PrimeMaskLadder.init,
    arun, astep, initialAStateWithArray, AState.writeReg,
    sdest, sval, denoteOperand, rLogL, rLogU, rAccLo, rAccHi, rBad,
    RS62PrimeMaskLadder.rLogL, RS62PrimeMaskLadder.rLogU,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
    Nat.mod_eq_of_lt hSL, Nat.mod_eq_of_lt hSU,
    Nat.mod_eq_of_lt hLo, Nat.mod_eq_of_lt hHi]

theorem machineFold_word (arr : Nat → Nat) (n0 f SL SU accLo accHi : Nat)
    (harray : ∀ j, arr j < M) :
    (∀ j, (machineFoldState arr n0 f SL SU accLo accHi).regs j < M) ∧
      ∀ j, (machineFoldState arr n0 f SL SU accLo accHi).arr j < M := by
  induction f with
  | zero =>
      unfold machineFoldState
      simp only [List.range_zero, List.foldl_nil]
      exact arun_word 0 (init SL SU accLo accHi)
        (initialAStateWithArray arr) (by
          intro j
          simp [initialAStateWithArray,
            LeanCompCert.Verified.Reflect.initialState, M]) (by
          simpa [initialAStateWithArray] using harray)
  | succ f ih =>
      rw [machineFoldState_succ]
      exact arun_word f (body n0)
        (machineFoldState arr n0 f SL SU accLo accHi) ih.1 ih.2



theorem body_bad_le (n0 k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hkM : k < M) (hnM : n0 + k < M)
    (hn40 : n0 + k ≤ 2 ^ 40)
    (hRhs : (n0 + k) * 4294967296 < B)
    (hCell : s.arr k ≤ 1)
    (hFactor : s.regs rLogU + s.regs rLogU < M)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s (body n0)).regs rBad ≤ 1 := by
  let m := arun k s (maskPrefix n0)
  let x := arun k m snapshotBody
  let g := arun k x guardBody
  let a := arun k g accumulatorBody
  let l := arun k a logBody
  have hm := maskPrefix_spec n0 k s hkM hnM
  change m.regs rGate = s.arr k ∧ m.regs rN = n0 + k ∧ m.arr = s.arr at hm
  have hmword : ∀ j, m.regs j < M :=
    arun_regs_word k (maskPrefix n0) s hword harray
  have hmarray : ∀ j, m.arr j < M := by simpa [hm.2.2] using harray
  have hmLogU : m.regs rLogU = s.regs rLogU :=
    frame k rLogU (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rLogU, RS62PrimeMaskLadder.rLogU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] <;> decide)
  have hmBad : m.regs rBad = s.regs rBad :=
    frame k rBad (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rBad] <;> decide)
  have hxword : ∀ j, x.regs j < M :=
    arun_regs_word k snapshotBody m hmword hmarray
  have hxarray : ∀ j, x.arr j < M :=
    arun_arr_word k snapshotBody m hmword hmarray
  have hxN : x.regs rN = m.regs rN := frame k rN snapshotBody m (by decide)
  have hxGate : x.regs rGate = m.regs rGate :=
    frame k rGate snapshotBody m (by decide)
  have hxLogU : x.regs rLogU = m.regs rLogU :=
    frame k rLogU snapshotBody m (by decide)
  have hxBad : x.regs rBad = m.regs rBad :=
    frame k rBad snapshotBody m (by decide)
  have hg := guardBody_bad_le k x hxword hxarray
    (by rw [hxN, hm.2.1]; exact hn40)
    (by rw [hxN, hm.2.1]; exact hRhs)
    (by rw [hxLogU, hmLogU]; exact hFactor)
    (by rw [hxGate, hm.1]; exact hCell)
    (by rw [hxBad, hmBad]; exact hBad)
  have hgword : ∀ j, g.regs j < M :=
    arun_regs_word k guardBody x hxword hxarray
  have hgarray : ∀ j, g.arr j < M :=
    arun_arr_word k guardBody x hxword hxarray
  have ha := accumulatorBody_bad_le k g hg
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k accumulatorBody g hgword hgarray
  have haarray : ∀ j, a.arr j < M :=
    arun_arr_word k accumulatorBody g hgword hgarray
  have hl := logBody_bad_le k a ha
  have hout : arun k s (body n0) = l := by
    simp only [RS62Loop314Program.body, arun_append]
    rfl
  rw [hout]
  exact hl

theorem accumulatorBody_value (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (hGate : s.regs rGate ≤ 1)
    (hSum : wval (s.regs rAccLo, s.regs rAccHi) +
      s.regs rGate * s.regs rOldL < AddWide.B128) :
    wval ((arun k s accumulatorBody).regs rAccLo,
      (arun k s accumulatorBody).regs rAccHi) =
        wval (s.regs rAccLo, s.regs rAccHi) +
          s.regs rGate * s.regs rOldL ∧
      (arun k s accumulatorBody).arr = s.arr := by
  let p := arun k s accumulatorPrepBody
  let a := arun k p accumulatorAddBody
  let l := arun k a accumulatorLatchBody
  have hp := accumulatorPrepBody_spec k s hGate (hword rOldL)
  change p.regs rOldAccHi = s.regs rAccHi ∧
    p.regs rAccAdd = s.regs rGate * s.regs rOldL ∧ p.arr = s.arr at hp
  have hpLo : p.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo accumulatorPrepBody s (by decide)
  have hpHi : p.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi accumulatorPrepBody s (by decide)
  have ha := accumulatorAddBody_spec k p (by rw [hpHi]; exact hword rAccHi)
  change (a.regs rAccLo, a.regs rAccHi) =
      AddWide.addWideLo (p.regs rAccLo, p.regs rAccHi) (p.regs rAccAdd) ∧
    a.arr = p.arr at ha
  have haddM : p.regs rAccAdd < B := by
    rw [hp.2.1]
    have hg : s.regs rGate = 0 ∨ s.regs rGate = 1 := by omega
    rcases hg with hg | hg
    · simp [hg, B, MulWide.B64]
    · simpa [hg, M, B, MulWide.B64] using hword rOldL
  have haValue : wval (a.regs rAccLo, a.regs rAccHi) =
      wval (s.regs rAccLo, s.regs rAccHi) +
        s.regs rGate * s.regs rOldL := by
    rw [ha.1]
    have hexact := AddWide.addWideLo_exact
      (p.regs rAccLo, p.regs rAccHi) (p.regs rAccAdd)
      ⟨by simpa [hpLo, M, B, MulWide.B64] using hword rAccLo,
       by simpa [hpHi, M, B, MulWide.B64] using hword rAccHi⟩
      haddM (by simpa [wval, AddWide.wval, B, AddWide.B64,
        MulWide.B64, hpLo, hpHi, hp.2.1] using hSum)
    simpa [wval, AddWide.wval, B, AddWide.B64, MulWide.B64,
      hpLo, hpHi, hp.2.1] using hexact
  have hlLo : l.regs rAccLo = a.regs rAccLo :=
    frame k rAccLo accumulatorLatchBody a (by decide)
  have hlHi : l.regs rAccHi = a.regs rAccHi :=
    frame k rAccHi accumulatorLatchBody a (by decide)
  have hlArr := arun_lift_arr k
    [ .binop rAccWrap .lt (.reg rAccHi) (.reg rOldAccHi)
    , .binop rBad .bor (.reg rBad) (.reg rAccWrap) ] a
  have hout : arun k s accumulatorBody = l := by
    rw [RS62Loop314Program.accumulatorBody, arun_append, arun_append]
  rw [hout, hlLo, hlHi]
  exact ⟨haValue, hlArr.trans (ha.2.trans hp.2.2)⟩

theorem logBody_value (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs rN) (hn40 : s.regs rN ≤ 2 ^ 40)
    (hL : s.regs rLogL + RS62.incLWord (s.regs rN) < M)
    (hU : s.regs rLogU + RS62.incUWord (s.regs rN) < M) :
    (arun k s logBody).regs rLogL =
        s.regs rLogL + RS62.incLWord (s.regs rN) ∧
      (arun k s logBody).regs rLogU =
        s.regs rLogU + RS62.incUWord (s.regs rN) ∧
      (arun k s logBody).arr = s.arr := by
  let l := arun k s logLowerBody
  let u := arun k l logUpperBody
  let a := arun k u logAddBody
  let w := arun k a logWrapBody
  have hl := logLowerBody_spec k s hn2 hn40
  change l.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
      RS62.incLWord (s.regs rN) ∧ l.regs rN = s.regs rN ∧ l.arr = s.arr at hl
  have hu := logUpperBody_spec k l (by rw [hl.2.1]; exact hn2)
    (by rw [hl.2.1]; exact hn40)
  change u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU =
      RS62.incUWord (l.regs rN) ∧ u.regs rN = l.regs rN ∧ u.arr = l.arr at hu
  have huIL : u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
      l.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL :=
    frame k LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL
      logUpperBody l (by decide)
  have hlLogL : l.regs rLogL = s.regs rLogL :=
    frame k rLogL logLowerBody s (by decide)
  have hlLogU : l.regs rLogU = s.regs rLogU :=
    frame k rLogU logLowerBody s (by decide)
  have huLogL : u.regs rLogL = l.regs rLogL :=
    frame k rLogL logUpperBody l (by decide)
  have huLogU : u.regs rLogU = l.regs rLogU :=
    frame k rLogU logUpperBody l (by decide)
  have ha := logAddBody_spec k u (by
    rw [huLogL, hlLogL, huIL, hl.1]; exact hL) (by
    rw [huLogU, hlLogU, hu.1, hl.2.1]; exact hU)
  change a.regs rLogL = u.regs rLogL +
      u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL ∧
    a.regs rLogU = u.regs rLogU +
      u.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU ∧
    a.arr = u.arr at ha
  have hwL : w.regs rLogL = a.regs rLogL :=
    frame k rLogL logWrapBody a (by decide)
  have hwU : w.regs rLogU = a.regs rLogU :=
    frame k rLogU logWrapBody a (by decide)
  have hwArr := arun_lift_arr k
    [ .binop rWrapL .lt (.reg rLogL) (.reg rOldL)
    , .binop rWrapU .lt (.reg rLogU) (.reg rOldU)
    , .binop rLogWrap .bor (.reg rWrapL) (.reg rWrapU)
    , .binop rBad .bor (.reg rBad) (.reg rLogWrap) ] a
  have hout : arun k s logBody = w := by
    rw [RS62Loop314Program.logBody, arun_append, arun_append,
      RS62Loop314Program.logCommitBody, arun_append]
  rw [hout, hwL, hwU]
  exact ⟨by rw [ha.1, huLogL, hlLogL, huIL, hl.1],
    by rw [ha.2.1, huLogU, hlLogU, hu.1, hl.2.1],
    hwArr.trans (ha.2.2.trans (hu.2.2.trans hl.2.2))⟩

theorem body_value (n0 k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hkM : k < M) (hnM : n0 + k < M)
    (hn2 : 2 ≤ n0 + k) (hn40 : n0 + k ≤ 2 ^ 40)
    (hCell : s.arr k ≤ 1)
    (hAccSum : wval (s.regs rAccLo, s.regs rAccHi) +
      s.arr k * s.regs rLogL < AddWide.B128)
    (hL : s.regs rLogL + RS62.incLWord (n0 + k) < M)
    (hU : s.regs rLogU + RS62.incUWord (n0 + k) < M) :
    (arun k s (body n0)).regs rLogL =
        s.regs rLogL + RS62.incLWord (n0 + k) ∧
      (arun k s (body n0)).regs rLogU =
        s.regs rLogU + RS62.incUWord (n0 + k) ∧
      wval ((arun k s (body n0)).regs rAccLo,
        (arun k s (body n0)).regs rAccHi) =
          wval (s.regs rAccLo, s.regs rAccHi) +
            s.arr k * s.regs rLogL ∧
      (arun k s (body n0)).arr = s.arr := by
  let m := arun k s (maskPrefix n0)
  let x := arun k m snapshotBody
  let g := arun k x guardBody
  let a := arun k g accumulatorBody
  let l := arun k a logBody
  have hm := maskPrefix_spec n0 k s hkM hnM
  change m.regs rGate = s.arr k ∧ m.regs rN = n0 + k ∧ m.arr = s.arr at hm
  have hmword : ∀ j, m.regs j < M :=
    arun_regs_word k (maskPrefix n0) s hword harray
  have hmarray : ∀ j, m.arr j < M := by simpa [hm.2.2] using harray
  have hmLogL : m.regs rLogL = s.regs rLogL :=
    frame k rLogL (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rLogL, RS62PrimeMaskLadder.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL] <;> decide)
  have hmLogU : m.regs rLogU = s.regs rLogU :=
    frame k rLogU (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rLogU, RS62PrimeMaskLadder.rLogU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] <;> decide)
  have hmAccLo : m.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rAccLo] <;> decide)
  have hmAccHi : m.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi (maskPrefix n0) s (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, maskPrefix,
        rAccHi] <;> decide)
  have hx := snapshotBody_spec k m
  change x.regs rOldL = m.regs rLogL ∧ x.regs rOldU = m.regs rLogU ∧
    x.arr = m.arr at hx
  have hxword : ∀ j, x.regs j < M :=
    arun_regs_word k snapshotBody m hmword hmarray
  have hxarray : ∀ j, x.arr j < M := by simpa [hx.2.2] using hmarray
  have hxGate : x.regs rGate = m.regs rGate :=
    frame k rGate snapshotBody m (by decide)
  have hxLogL : x.regs rLogL = m.regs rLogL :=
    frame k rLogL snapshotBody m (by decide)
  have hxLogU : x.regs rLogU = m.regs rLogU :=
    frame k rLogU snapshotBody m (by decide)
  have hxAccLo : x.regs rAccLo = m.regs rAccLo :=
    frame k rAccLo snapshotBody m (by decide)
  have hxAccHi : x.regs rAccHi = m.regs rAccHi :=
    frame k rAccHi snapshotBody m (by decide)
  have hgword : ∀ j, g.regs j < M :=
    arun_regs_word k guardBody x hxword hxarray
  have hgArr : g.arr = x.arr :=
    arun_scalarOnly_arr k guardBody x (by trivial)
  have hgarray : ∀ j, g.arr j < M := by simpa [hgArr] using hxarray
  have hgGate : g.regs rGate = x.regs rGate :=
    guardBody_preserves_gate k x
  have hgLogL : g.regs rLogL = x.regs rLogL :=
    frame k rLogL guardBody x (by decide)
  have hgLogU : g.regs rLogU = x.regs rLogU :=
    frame k rLogU guardBody x (by decide)
  have hgOldL : g.regs rOldL = x.regs rOldL :=
    frame k rOldL guardBody x (by decide)
  have hgAccLo : g.regs rAccLo = x.regs rAccLo :=
    frame k rAccLo guardBody x (by decide)
  have hgAccHi : g.regs rAccHi = x.regs rAccHi :=
    frame k rAccHi guardBody x (by decide)
  have ha := accumulatorBody_value k g hgword
    (by rw [hgGate, hxGate, hm.1]; exact hCell) (by
      rw [hgAccLo, hgAccHi, hxAccLo, hxAccHi, hmAccLo, hmAccHi,
        hgGate, hxGate, hm.1, hgOldL, hx.1, hmLogL]
      exact hAccSum)
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k accumulatorBody g hgword hgarray
  have haArr : a.arr = g.arr := ha.2
  have haN : a.regs rN = n0 + k := by
    rw [frame k rN accumulatorBody g (by decide),
      frame k rN guardBody x (by decide),
      frame k rN snapshotBody m (by decide), hm.2.1]
  have haLogL : a.regs rLogL = s.regs rLogL := by
    rw [frame k rLogL accumulatorBody g (by decide), hgLogL,
      hxLogL, hmLogL]
  have haLogU : a.regs rLogU = s.regs rLogU := by
    rw [frame k rLogU accumulatorBody g (by decide), hgLogU,
      hxLogU, hmLogU]
  have hl := logBody_value k a (by rw [haN]; exact hn2)
    (by rw [haN]; exact hn40)
    (by rw [haLogL, haN]; exact hL)
    (by rw [haLogU, haN]; exact hU)
  have hlAccLo : l.regs rAccLo = a.regs rAccLo :=
    frame k rAccLo logBody a (by decide)
  have hlAccHi : l.regs rAccHi = a.regs rAccHi :=
    frame k rAccHi logBody a (by decide)
  have hout : arun k s (body n0) = l := by
    simp only [RS62Loop314Program.body, arun_append]
    rfl
  rw [hout]
  refine ⟨?_, ?_, ?_, hl.2.2.trans (haArr.trans (hgArr.trans
    (hx.2.2.trans hm.2.2)))⟩
  · rw [hl.1, haLogL, haN]
  · rw [hl.2.1, haLogU, haN]
  · rw [hlAccLo, hlAccHi, ha.1, hgAccLo, hgAccHi,
      hxAccLo, hxAccHi, hmAccLo, hmAccHi, hgGate, hxGate, hm.1,
      hgOldL, hx.1, hmLogL]

theorem machineFold_observe (arr : Nat → Nat)
    (n0 f SL SU accLo accHi : Nat)
    (harray : ∀ j, arr j < M) (hn0 : 2 ≤ n0)
    (hfM : f < M) (hEnd : n0 + f ≤ 2 ^ 40)
    (hRhsEnd : (n0 + f) * 4294967296 < B)
    (hSL : SL < M) (hSU : SU < M)
    (hLo : accLo < M) (hHi : accHi < M)
    (hRoom : Room arr n0 f
      ⟨SL, SU, wval (accLo, accHi)⟩) :
    let out := machineFoldState arr n0 f SL SU accLo accHi
    let src := sourceFold arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩
    out.regs rLogL = src.logL ∧ out.regs rLogU = src.logU ∧
      wval (out.regs rAccLo, out.regs rAccHi) = src.acc ∧
      out.arr = arr ∧ out.regs rBad ≤ 1 := by
  induction f with
  | zero =>
      have hi := init_spec arr SL SU accLo accHi hSL hSU hLo hHi
      simp only [machineFoldState, List.range_zero, List.foldl_nil,
        sourceFold, State314.logL, State314.logU, State314.acc]
      exact ⟨hi.1, hi.2.1, by rw [hi.2.2.1, hi.2.2.2.1],
        hi.2.2.2.2.2, by rw [hi.2.2.2.2.1]; omega⟩
  | succ f ih =>
      let mid := machineFoldState arr n0 f SL SU accLo accHi
      let src := sourceFold arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩
      have hfM' : f < M := by omega
      have hEnd' : n0 + f ≤ 2 ^ 40 := by omega
      have hnM' : n0 + f < M :=
        Nat.lt_of_le_of_lt hEnd' (by decide)
      have hRhs' : (n0 + f) * 4294967296 < B :=
        rhs_bound_mono (by omega) hRhsEnd
      have hRoom' : Room arr n0 f
          ⟨SL, SU, wval (accLo, accHi)⟩ :=
        room_mono arr n0 _ (Nat.le_succ f) hRoom
      have hmid := ih hfM' hEnd' hRhs' hRoom'
      change mid.regs rLogL = src.logL ∧ mid.regs rLogU = src.logU ∧
        wval (mid.regs rAccLo, mid.regs rAccHi) = src.acc ∧
        mid.arr = arr ∧ mid.regs rBad ≤ 1 at hmid
      have hr := hRoom f (Nat.lt_succ_self f)
      dsimp only at hr
      have hmw := machineFold_word arr n0 f SL SU accLo accHi harray
      change (∀ j, mid.regs j < M) ∧ ∀ j, mid.arr j < M at hmw
      have hv := body_value n0 f mid hmw.1 hmw.2 hfM' hnM'
        (by omega) hEnd' (by rw [hmid.2.2.2.1]; exact hr.1)
        (by rw [hmid.2.2.1, hmid.2.2.2.1, hmid.1]; exact hr.2.2.2.1)
        (by rw [hmid.1]; exact hr.2.2.2.2.1)
        (by rw [hmid.2.1]; exact hr.2.2.2.2.2)
      have hb := body_bad_le n0 f mid hmw.1 hmw.2 hfM' hnM'
        hEnd' hRhs' (by rw [hmid.2.2.2.1]; exact hr.1)
        (by rw [hmid.2.1]; exact hr.2.2.1) hmid.2.2.2.2
      rw [machineFoldState_succ, sourceFold_succ]
      dsimp only [sourceStep]
      exact ⟨hv.1.trans (by rw [hmid.1]),
        hv.2.1.trans (by rw [hmid.2.1]),
        hv.2.2.1.trans (by rw [hmid.2.2.1, hmid.2.2.2.1, hmid.1]),
        hv.2.2.2.trans hmid.2.2.2.1, hb⟩

def GuardAt (n : Nat) (st : State314) : Prop :=
  n * RS62.fpD ≤ st.acc +
    n * RS62.fpD * RS62.fpD / (2 * st.logU)

def CellGuards (arr : Nat → Nat) (n0 f : Nat)
    (initial : State314) : Prop :=
  ∀ k, k < f → arr k = 0 ∨
    GuardAt (n0 + k) (sourceFold arr n0 k initial)

theorem machineFold_clean_guards (arr : Nat → Nat)
    (n0 f SL SU accLo accHi : Nat)
    (harray : ∀ j, arr j < M) (hn0 : 2 ≤ n0)
    (hfM : f < M) (hEnd : n0 + f ≤ 2 ^ 40)
    (hRhsEnd : (n0 + f) * 4294967296 < B)
    (hSL : SL < M) (hSU : SU < M)
    (hLo : accLo < M) (hHi : accHi < M)
    (hRoom : Room arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩)
    (hClean : (machineFoldState arr n0 f SL SU accLo accHi).regs rBad = 0) :
    CellGuards arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩ := by
  induction f with
  | zero =>
      intro k hk
      omega
  | succ f ih =>
      let mid := machineFoldState arr n0 f SL SU accLo accHi
      let src := sourceFold arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩
      have hfM' : f < M := by omega
      have hEnd' : n0 + f ≤ 2 ^ 40 := by omega
      have hnM' : n0 + f < M :=
        Nat.lt_of_le_of_lt hEnd' (by decide)
      have hRhs' : (n0 + f) * 4294967296 < B :=
        rhs_bound_mono (by omega) hRhsEnd
      have hRoom' : Room arr n0 f
          ⟨SL, SU, wval (accLo, accHi)⟩ :=
        room_mono arr n0 _ (Nat.le_succ f) hRoom
      have hmid := machineFold_observe arr n0 f SL SU accLo accHi
        harray hn0 hfM' hEnd' hRhs' hSL hSU hLo hHi hRoom'
      change mid.regs rLogL = src.logL ∧ mid.regs rLogU = src.logU ∧
        wval (mid.regs rAccLo, mid.regs rAccHi) = src.acc ∧
        mid.arr = arr ∧ mid.regs rBad ≤ 1 at hmid
      have hr := hRoom f (Nat.lt_succ_self f)
      dsimp only at hr
      have hmw := machineFold_word arr n0 f SL SU accLo accHi harray
      change (∀ j, mid.regs j < M) ∧ ∀ j, mid.arr j < M at hmw
      have hlastClean : (arun f mid (body n0)).regs rBad = 0 := by
        rw [← machineFoldState_succ]
        exact hClean
      have hlast := body_zero_sound n0 f mid hmw.1 hmw.2
        hfM' hnM' (by omega) hEnd' hRhs'
        (by rw [hmid.2.2.2.1]; exact hr.1)
        (by rw [hmid.2.1]; exact hr.2.2.1)
        (by rw [hmid.2.1]; exact hr.2.1)
        (by rw [hmid.2.2.1, hmid.2.2.2.1, hmid.1]; exact hr.2.2.2.1)
        (by rw [hmid.1]; exact hr.2.2.2.2.1)
        (by rw [hmid.2.1]; exact hr.2.2.2.2.2)
        hmid.2.2.2.2 hlastClean
      have hprev := ih hfM' hEnd' hRhs' hRoom' hlast.1
      intro k hk
      by_cases hkf : k < f
      · exact hprev k hkf
      · have hkEq : k = f := by omega
        subst k
        rcases hlast.2.1 with hzero | hguard
        · exact Or.inl (by simpa [hmid.2.2.2.1] using hzero)
        · exact Or.inr (by simpa [GuardAt, hmid.1, hmid.2.1,
            hmid.2.2.1] using hguard)

theorem loop314_eq_some_of_guards (p : Nat → Bool) :
    ∀ (f n0 : Nat) (arr : Nat → Nat) (initial : State314),
    2003 ≤ n0 →
    RS62PrimeMaskLadder.MaskCorrect p arr n0 f →
    CellGuards arr n0 f initial →
    GuardAt (n0 + f) (sourceFold arr n0 f initial) →
    loop314 p f n0 initial.logL initial.logU initial.acc =
      some ((sourceFold arr n0 f initial).logL,
        (sourceFold arr n0 f initial).logU,
        (sourceFold arr n0 f initial).acc) := by
  intro f
  induction f with
  | zero =>
      intro n0 arr initial hn0 hmask hcells hend
      have hg : n0 * RS62.fpD ≤ initial.acc +
          n0 * RS62.fpD * RS62.fpD / (2 * initial.logU) := by
        simpa [GuardAt, sourceFold] using hend
      simp [loop314, sourceFold, hg]
  | succ f ih =>
      intro n0 arr initial hn0 hmask hcells hend
      let arr' : Nat → Nat := fun k => arr (k + 1)
      let initial' := sourceStep arr n0 initial 0
      have hmask0 := hmask 0 (Nat.zero_lt_succ f)
      have hcell0 := hcells 0 (Nat.zero_lt_succ f)
      have hmask' : RS62PrimeMaskLadder.MaskCorrect p arr' (n0 + 1) f := by
        intro k hk
        have h := hmask (k + 1) (by omega)
        simpa [arr', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hcells' : CellGuards arr' (n0 + 1) f initial' := by
        intro k hk
        have h := hcells (k + 1) (by omega)
        rw [sourceFold_cons arr n0 k initial] at h
        simpa [arr', initial', GuardAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hend' : GuardAt ((n0 + 1) + f)
          (sourceFold arr' (n0 + 1) f initial') := by
        rw [← sourceFold_cons arr n0 f initial]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
      have htail := ih (n0 + 1) arr' initial' (by omega)
        hmask' hcells' hend'
      rw [← sourceFold_cons arr n0 f initial] at htail
      cases hp : p n0 with
      | false =>
          have harr0 : arr 0 = 0 := by simpa [hp] using hmask0
          simpa [loop314, hp, initial', arr', sourceStep, harr0,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      | true =>
          have harr0 : arr 0 = 1 := by simpa [hp] using hmask0
          have hg : GuardAt n0 initial := by
            rcases hcell0 with hz | hg
            · rw [harr0] at hz
              omega
            · simpa [GuardAt, sourceFold] using hg
          have hg' : n0 * RS62.fpD ≤ initial.acc +
              n0 * RS62.fpD * RS62.fpD / (2 * initial.logU) := by
            simpa [GuardAt] using hg
          simpa [loop314, hp, hn0, hg', initial', arr', sourceStep, harr0,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Receipt-facing bridge: one successful compiled segment with `bad = 0`
proves the exact source `loop314` result. -/
theorem source_loop314_of_runFromArray (p : Nat → Bool)
    (arr : Nat → Nat) (n0 f SL SU accLo accHi outReg : Nat)
    (out : AState)
    (harray : ∀ j, arr j < M) (hn0 : 2003 ≤ n0)
    (hfM : f < M) (hnM : n0 + f < M)
    (hEnd : n0 + f ≤ 2 ^ 40)
    (hRhsEnd : (n0 + f) * 4294967296 < B)
    (hSL : SL < M) (hSU : SU < M)
    (hLo : accLo < M) (hHi : accHi < M)
    (hRoom : Room arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩)
    (hEndLog :
      let src := sourceFold arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩
      0 < src.logU ∧ src.logU + src.logU < M)
    (hmask : RS62PrimeMaskLadder.MaskCorrect p arr n0 f)
    (hRun : (program n0 f SL SU accLo accHi outReg).runFromArray arr =
      some out)
    (hClean : out.regs rBad = 0) :
    loop314 p f n0 SL SU (wval (accLo, accHi)) =
      some (out.regs rLogL, out.regs rLogU,
        wval (out.regs rAccLo, out.regs rAccHi)) := by
  let mid := machineFoldState arr n0 f SL SU accLo accHi
  let fin := arun 0 mid (finalBody (n0 + f))
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (program n0 f SL SU accLo accHi outReg) arr out hRun
  have houtEq : out = fin := by
    simpa [RS62Loop314Program.program, machineFoldState, fin, mid, arun]
      using hout
  have hobs := machineFold_observe arr n0 f SL SU accLo accHi
    harray (by omega) hfM hEnd hRhsEnd hSL hSU hLo hHi hRoom
  let src := sourceFold arr n0 f ⟨SL, SU, wval (accLo, accHi)⟩
  change mid.regs rLogL = src.logL ∧ mid.regs rLogU = src.logU ∧
    wval (mid.regs rAccLo, mid.regs rAccHi) = src.acc ∧
    mid.arr = arr ∧ mid.regs rBad ≤ 1 at hobs
  have hmw := machineFold_word arr n0 f SL SU accLo accHi harray
  change (∀ j, mid.regs j < M) ∧ ∀ j, mid.arr j < M at hmw
  have hfinClean : fin.regs rBad = 0 := by
    rw [← houtEq]
    exact hClean
  have hfinal := finalBody_zero_sound 0 (n0 + f) mid hmw.1 hmw.2
    hnM hEnd hRhsEnd (by
      rw [hobs.2.1]
      exact hEndLog.2) (by
      rw [hobs.2.1]
      exact hEndLog.1) hobs.2.2.2.2 hfinClean
  have hcells := machineFold_clean_guards arr n0 f SL SU accLo accHi
    harray (by omega) hfM hEnd hRhsEnd hSL hSU hLo hHi hRoom hfinal.1
  have hendGuard : GuardAt (n0 + f) src := by
    simpa [GuardAt, hobs.1, hobs.2.1, hobs.2.2.1] using hfinal.2
  have hsource := loop314_eq_some_of_guards p f n0 arr
    ⟨SL, SU, wval (accLo, accHi)⟩ hn0 hmask hcells hendGuard
  have finalFrame (r : Nat)
      (hPrep : ArrayRegFrame.writes r (finalPrepBody (n0 + f)) = false)
      (hGuard : ArrayRegFrame.writes r guardBody = false) :
      fin.regs r = mid.regs r := by
    dsimp only [fin]
    rw [finalBody, arun_append, frame 0 r guardBody _ hGuard,
      frame 0 r (finalPrepBody (n0 + f)) mid hPrep]
  have hfinLogL : fin.regs rLogL = mid.regs rLogL :=
    finalFrame rLogL (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        lift, rLogL, rGate, rN, RS62PrimeMaskLadder.rLogL,
        RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL]) (by decide)
  have hfinLogU : fin.regs rLogU = mid.regs rLogU :=
    finalFrame rLogU (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        lift, rLogU, rGate, rN, RS62PrimeMaskLadder.rLogU,
        RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU]) (by decide)
  have hfinAccLo : fin.regs rAccLo = mid.regs rAccLo :=
    finalFrame rAccLo (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        lift, rAccLo, rGate, rN, RS62PrimeMaskLadder.rGate,
        RS62PrimeMaskLadder.rN]) (by decide)
  have hfinAccHi : fin.regs rAccHi = mid.regs rAccHi :=
    finalFrame rAccHi (by
      simp [ArrayRegFrame.writes, ArrayRegFrame.instrWrites, finalPrepBody,
        lift, rAccHi, rGate, rN, RS62PrimeMaskLadder.rGate,
        RS62PrimeMaskLadder.rN]) (by decide)
  rw [houtEq, hfinLogL, hfinLogU, hfinAccLo, hfinAccHi,
    hobs.1, hobs.2.1, hobs.2.2.1]
  exact hsource

end LeanCompCert.Ports.RS62Loop314Sound
