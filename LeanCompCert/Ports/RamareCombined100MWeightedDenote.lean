import LeanCompCert.Ports.RamareCombined100MWideEndpoint

/-!
# Denotation of the per-candidate weighted-absolute update

This is kept separate from the endpoint and sweep proofs so elaborating it
never unfolds either exact product implementation or the production loop.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WeightedDenote

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.SeamBlock

theorem absIlo_run (k : Nat) (s : AState) (hsrc : s.regs rIlo < M) :
    (arun k s (absOf rWmag rIlo)).regs rWmag =
      (if Section413Cells.H63 ≤ s.regs rIlo then M - s.regs rIlo
       else s.regs rIlo) := by
  simp only [Section413Cells.H63]
  simp only [rIlo] at hsrc
  rcases Nat.lt_or_ge (s.regs 321) 9223372036854775808 with h | h
  · have h' : ¬ 9223372036854775808 ≤ s.regs 321 := Nat.not_le.mpr h
    simp [absOf, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rWmag, rIlo, h, h',
      Nat.mod_eq_of_lt hsrc,
      Nat.mod_eq_of_lt (show 9223372036854775808 < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  · have h' : ¬ s.regs 321 < 9223372036854775808 := Nat.not_lt.mpr h
    have hpos : M - s.regs 321 < M := by
      have : (0 : Nat) < s.regs 321 := by
        have : 0 < 9223372036854775808 := by decide
        omega
      omega
    simp [absOf, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rWmag, rIlo, h, h',
      Nat.mod_eq_of_lt hpos,
      Nat.mod_eq_of_lt (show 9223372036854775808 < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]

theorem absIhi_run (k : Nat) (s : AState) (hsrc : s.regs rIhi < M) :
    (arun k s (absOf rWq rIhi)).regs rWq =
      (if Section413Cells.H63 ≤ s.regs rIhi then M - s.regs rIhi
       else s.regs rIhi) := by
  simp only [Section413Cells.H63]
  simp only [rIhi] at hsrc
  rcases Nat.lt_or_ge (s.regs 322) 9223372036854775808 with h | h
  · have h' : ¬ 9223372036854775808 ≤ s.regs 322 := Nat.not_le.mpr h
    simp [absOf, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rWq, rIhi, h, h',
      Nat.mod_eq_of_lt hsrc,
      Nat.mod_eq_of_lt (show 9223372036854775808 < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  · have h' : ¬ s.regs 322 < 9223372036854775808 := Nat.not_lt.mpr h
    have hpos : M - s.regs 322 < M := by
      have : (0 : Nat) < s.regs 322 := by
        have : 0 < 9223372036854775808 := by decide
        omega
      omega
    simp [absOf, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rWq, rIhi, h, h',
      Nat.mod_eq_of_lt hpos,
      Nat.mod_eq_of_lt (show 9223372036854775808 < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]

theorem absIlo_encode (k : Nat) (s : AState) (z : Int)
    (hz : s.regs rIlo = Section413Cells.encodeZ z)
    (hlo : -(Section413Cells.H63 : Int) ≤ z)
    (hhi : z < (Section413Cells.H63 : Int)) :
    (arun k s (absOf rWmag rIlo)).regs rWmag = z.natAbs := by
  rw [absIlo_run k s (by rw [hz]; exact Section413Cells.encodeZ_lt z), hz]
  have hs := Section413Cells.encodeZ_sign z hlo hhi
  by_cases h : z < 0
  · rw [if_pos (hs.mpr h)]
    exact Section413Cells.encodeZ_mag_neg z hlo h
  · rw [if_neg (fun hh => h (hs.mp hh))]
    exact Section413Cells.encodeZ_mag_nonneg z (Int.le_of_not_gt h) hhi

theorem absIhi_encode (k : Nat) (s : AState) (z : Int)
    (hz : s.regs rIhi = Section413Cells.encodeZ z)
    (hlo : -(Section413Cells.H63 : Int) ≤ z)
    (hhi : z < (Section413Cells.H63 : Int)) :
    (arun k s (absOf rWq rIhi)).regs rWq = z.natAbs := by
  rw [absIhi_run k s (by rw [hz]; exact Section413Cells.encodeZ_lt z), hz]
  have hs := Section413Cells.encodeZ_sign z hlo hhi
  by_cases h : z < 0
  · rw [if_pos (hs.mpr h)]
    exact Section413Cells.encodeZ_mag_neg z hlo h
  · rw [if_neg (fun hh => h (hs.mp hh))]
    exact Section413Cells.encodeZ_mag_nonneg z (Int.le_of_not_gt h) hhi

/-- The scalar suffix of `weightedStep`, after the two endpoint magnitudes
have been materialized in `rWmag` and `rWq`. -/
def weightedFinish : List AInstr :=
  [ .scalar (.binop rT4 .ge (.reg rWmag) (.reg rWq))
  , .scalar (.binop rT5 .lt (.reg rWmag) (.reg rWq))
  , .scalar (.binop rA .mul (.reg rT4) (.reg rWmag))
  , .scalar (.binop rB .mul (.reg rT5) (.reg rWq))
  , .scalar (.binop rWmag .add (.reg rA) (.reg rB))
  , .scalar (.binop rB .eq (.reg sCand) (.lit 0))
  , .scalar (.binop rB .add (.reg rB) (.reg sCand))
  , .scalar (.binop rA .udiv (.reg rWmag) (.reg rB))
  , .scalar (.binop rT4 .urem (.reg rWmag) (.reg rB))
  , .scalar (.binop rT5 .ne (.reg rT4) (.lit 0))
  , .scalar (.binop rA .add (.reg rA) (.reg rT5))
  , .scalar (.binop rAccW .add (.reg rAccW) (.reg rA)) ]

theorem weightedStep_eq :
    weightedStep = absOf rWmag rIlo ++ absOf rWq rIhi ++ weightedFinish := by
  rfl

private theorem weightedFinish_run_raw (k : Nat) (s : AState)
    (hn : 0 < s.regs 132) (hnM : s.regs 132 < M)
    (hlo : s.regs 323 < M) (hhi : s.regs 324 < M)
    (hacc : s.regs 261 < M)
    (hsum : s.regs 261 + ceilDiv (max (s.regs 323) (s.regs 324))
      (s.regs 132) < M) :
    (arun k s weightedFinish).regs 261 =
      s.regs 261 + ceilDiv (max (s.regs 323) (s.regs 324)) (s.regs 132) := by
  rw [ceilDiv_eq_div_add_modBit _ _ hn] at hsum ⊢
  have hden : ((if s.regs 132 = 0 then 1 else 0) + s.regs 132) % M =
      s.regs 132 := by
    rw [if_neg (Nat.ne_of_gt hn), Nat.zero_add, Nat.mod_eq_of_lt hnM]
  by_cases h : s.regs 323 < s.regs 324
  · have hnot : ¬ s.regs 324 ≤ s.regs 323 := by omega
    rw [Nat.max_eq_right (by omega)] at hsum ⊢
    have hsel :
        ((if s.regs 324 ≤ s.regs 323 then 1 else 0) * s.regs 323 +
          (if s.regs 323 < s.regs 324 then 1 else 0) * s.regs 324) % M =
            s.regs 324 := by
      simp [h, hnot, Nat.mod_eq_of_lt hhi]
    by_cases hr : s.regs 324 % s.regs 132 = 0
    · simp only [hr, if_pos, if_true] at hsum ⊢
      have hdiv : s.regs 324 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi
      have hsum' : s.regs 261 + s.regs 324 / s.regs 132 < M := by omega
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hnot, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hsum']
    · simp only [hr, if_neg, if_false] at hsum ⊢
      have hceil : s.regs 324 / s.regs 132 + 1 < M := by omega
      have hdiv : s.regs 324 / s.regs 132 < M := by omega
      have hrem : s.regs 324 % s.regs 132 < M :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hn) (Nat.le_of_lt hnM)
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hnot, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hrem,
        Nat.mod_eq_of_lt hceil, Nat.mod_eq_of_lt hsum]
  · have hge : s.regs 324 ≤ s.regs 323 := Nat.le_of_not_gt h
    rw [Nat.max_eq_left hge] at hsum ⊢
    have hsel :
        ((if s.regs 324 ≤ s.regs 323 then 1 else 0) * s.regs 323 +
          (if s.regs 323 < s.regs 324 then 1 else 0) * s.regs 324) % M =
            s.regs 323 := by
      simp [h, hge, Nat.mod_eq_of_lt hlo]
    by_cases hr : s.regs 323 % s.regs 132 = 0
    · simp only [hr, if_pos, if_true] at hsum ⊢
      have hdiv : s.regs 323 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
      have hsum' : s.regs 261 + s.regs 323 / s.regs 132 < M := by omega
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hge, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hsum']
    · simp only [hr, if_neg, if_false] at hsum ⊢
      have hceil : s.regs 323 / s.regs 132 + 1 < M := by omega
      have hdiv : s.regs 323 / s.regs 132 < M := by omega
      have hrem : s.regs 323 % s.regs 132 < M :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hn) (Nat.le_of_lt hnM)
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hge, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hrem,
        Nat.mod_eq_of_lt hceil, Nat.mod_eq_of_lt hsum]

theorem weightedFinish_run (k : Nat) (s : AState)
    (hn : 0 < s.regs sCand) (hnM : s.regs sCand < M)
    (hlo : s.regs rWmag < M) (hhi : s.regs rWq < M)
    (hacc : s.regs rAccW < M)
    (hsum : s.regs rAccW +
      ceilDiv (max (s.regs rWmag) (s.regs rWq)) (s.regs sCand) < M) :
    (arun k s weightedFinish).regs rAccW =
      s.regs rAccW +
        ceilDiv (max (s.regs rWmag) (s.regs rWq)) (s.regs sCand) := by
  exact weightedFinish_run_raw k s hn hnM hlo hhi hacc hsum

/-- Exact modular form of the weighted update.  Unlike `weightedFinish_run`,
this theorem does not assume that the final accumulator addition fits; the V3
program checks the resulting carry explicitly. -/
theorem weightedFinish_run_mod (k : Nat) (s : AState)
    (hn : 0 < s.regs sCand) (hnM : s.regs sCand < M)
    (hlo : s.regs rWmag < M) (hhi : s.regs rWq < M)
    (hacc : s.regs rAccW < M) :
    (arun k s weightedFinish).regs rAccW =
      (s.regs rAccW +
        ceilDiv (max (s.regs rWmag) (s.regs rWq)) (s.regs sCand)) % M := by
  change (arun k s weightedFinish).regs 261 =
    (s.regs 261 + ceilDiv (max (s.regs 323) (s.regs 324)) (s.regs 132)) % M
  simp only [rAccW, rWmag, rWq, sCand] at hn hnM hlo hhi hacc
  rw [ceilDiv_eq_div_add_modBit _ _ hn]
  have hden : ((if s.regs 132 = 0 then 1 else 0) + s.regs 132) % M =
      s.regs 132 := by
    rw [if_neg (Nat.ne_of_gt hn), Nat.zero_add, Nat.mod_eq_of_lt hnM]
  by_cases h : s.regs 323 < s.regs 324
  · have hnot : ¬ s.regs 324 ≤ s.regs 323 := by omega
    rw [Nat.max_eq_right (by omega)]
    have hsel :
        ((if s.regs 324 ≤ s.regs 323 then 1 else 0) * s.regs 323 +
          (if s.regs 323 < s.regs 324 then 1 else 0) * s.regs 324) % M =
            s.regs 324 := by
      simp [h, hnot, Nat.mod_eq_of_lt hhi]
    by_cases hr : s.regs 324 % s.regs 132 = 0
    · have hdiv : s.regs 324 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hnot, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv]
    · have hdiv : s.regs 324 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi
      have hrem : s.regs 324 % s.regs 132 < M :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hn) (Nat.le_of_lt hnM)
      have hxpos : 0 < s.regs 324 :=
        Nat.pos_of_ne_zero (fun hx => hr (by simp [hx]))
      have hdne : s.regs 132 ≠ 1 := by
        intro hd
        apply hr
        rw [hd]
        exact Nat.mod_one _
      have hdivlt := Nat.div_lt_self hxpos (by omega : 1 < s.regs 132)
      have hceil : s.regs 324 / s.regs 132 + 1 < M := by omega
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hnot, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hrem,
        Nat.mod_eq_of_lt hceil]
  · have hge : s.regs 324 ≤ s.regs 323 := Nat.le_of_not_gt h
    rw [Nat.max_eq_left hge]
    have hsel :
        ((if s.regs 324 ≤ s.regs 323 then 1 else 0) * s.regs 323 +
          (if s.regs 323 < s.regs 324 then 1 else 0) * s.regs 324) % M =
            s.regs 323 := by
      simp [h, hge, Nat.mod_eq_of_lt hlo]
    by_cases hr : s.regs 323 % s.regs 132 = 0
    · have hdiv : s.regs 323 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hge, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv]
    · have hdiv : s.regs 323 / s.regs 132 < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
      have hrem : s.regs 323 % s.regs 132 < M :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hn) (Nat.le_of_lt hnM)
      have hxpos : 0 < s.regs 323 :=
        Nat.pos_of_ne_zero (fun hx => hr (by simp [hx]))
      have hdne : s.regs 132 ≠ 1 := by
        intro hd
        apply hr
        rw [hd]
        exact Nat.mod_one _
      have hdivlt := Nat.div_lt_self hxpos (by omega : 1 < s.regs 132)
      have hceil : s.regs 323 / s.regs 132 + 1 < M := by omega
      simp [weightedFinish, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg,
        rA, rB, rT4, rT5, rWmag, rWq, rAccW, sCand,
        h, hge, hden, hsel, hr, Nat.ne_of_gt hn,
        Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hacc,
        Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hrem,
        Nat.mod_eq_of_lt hceil]

theorem weightedStep_run (k : Nat) (s : AState) (lo hi : Int)
    (hloWord : s.regs rIlo = Section413Cells.encodeZ lo)
    (hhiWord : s.regs rIhi = Section413Cells.encodeZ hi)
    (hloMin : -(Section413Cells.H63 : Int) ≤ lo)
    (hloMax : lo < (Section413Cells.H63 : Int))
    (hhiMin : -(Section413Cells.H63 : Int) ≤ hi)
    (hhiMax : hi < (Section413Cells.H63 : Int))
    (hloAbs : lo.natAbs < M) (hhiAbs : hi.natAbs < M)
    (hn : 0 < s.regs sCand) (hnM : s.regs sCand < M)
    (hacc : s.regs rAccW < M)
    (hsum : s.regs rAccW + divUpper32 (intervalAbsUpper lo hi)
      (s.regs sCand) < M) :
    (arun k s weightedStep).regs rAccW =
      s.regs rAccW + divUpper32 (intervalAbsUpper lo hi) (s.regs sCand) := by
  let s1 := arun k s (absOf rWmag rIlo)
  let s2 := arun k s1 (absOf rWq rIhi)
  have hmag1 : s1.regs rWmag = lo.natAbs :=
    absIlo_encode k s lo hloWord hloMin hloMax
  have hIhi1 : s1.regs rIhi = Section413Cells.encodeZ hi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hhiWord]
  have hmag2hi : s2.regs rWq = hi.natAbs :=
    absIhi_encode k s1 hi hIhi1 hhiMin hhiMax
  have hmag2lo : s2.regs rWmag = lo.natAbs := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hmag1]
  have hn2 : s2.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hacc2 : s2.regs rAccW = s.regs rAccW := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hfinish := weightedFinish_run k s2
    (by rw [hn2]; exact hn) (by rw [hn2]; exact hnM)
    (by rw [hmag2lo]; exact hloAbs) (by rw [hmag2hi]; exact hhiAbs)
    (by rw [hacc2]; exact hacc) (by
      rw [hacc2, hmag2lo, hmag2hi, hn2]
      simpa only [divUpper32, intervalAbsUpper] using hsum)
  rw [weightedStep_eq, arun_append, arun_append]
  change (arun k s2 weightedFinish).regs rAccW = _
  rw [hfinish, hacc2, hmag2lo, hmag2hi, hn2]
  rfl

/-- Modular counterpart of `weightedStep_run`, used with the emitted V3
overflow check to derive the non-modular source transition. -/
theorem weightedStep_run_mod (k : Nat) (s : AState) (lo hi : Int)
    (hloWord : s.regs rIlo = Section413Cells.encodeZ lo)
    (hhiWord : s.regs rIhi = Section413Cells.encodeZ hi)
    (hloMin : -(Section413Cells.H63 : Int) ≤ lo)
    (hloMax : lo < (Section413Cells.H63 : Int))
    (hhiMin : -(Section413Cells.H63 : Int) ≤ hi)
    (hhiMax : hi < (Section413Cells.H63 : Int))
    (hloAbs : lo.natAbs < M) (hhiAbs : hi.natAbs < M)
    (hn : 0 < s.regs sCand) (hnM : s.regs sCand < M)
    (hacc : s.regs rAccW < M) :
    (arun k s weightedStep).regs rAccW =
      (s.regs rAccW + divUpper32 (intervalAbsUpper lo hi)
        (s.regs sCand)) % M := by
  let s1 := arun k s (absOf rWmag rIlo)
  let s2 := arun k s1 (absOf rWq rIhi)
  have hmag1 : s1.regs rWmag = lo.natAbs :=
    absIlo_encode k s lo hloWord hloMin hloMax
  have hIhi1 : s1.regs rIhi = Section413Cells.encodeZ hi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hhiWord]
  have hmag2hi : s2.regs rWq = hi.natAbs :=
    absIhi_encode k s1 hi hIhi1 hhiMin hhiMax
  have hmag2lo : s2.regs rWmag = lo.natAbs := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hmag1]
  have hn2 : s2.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hacc2 : s2.regs rAccW = s.regs rAccW := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hfinish := weightedFinish_run_mod k s2
    (by rw [hn2]; exact hn) (by rw [hn2]; exact hnM)
    (by rw [hmag2lo]; exact hloAbs) (by rw [hmag2hi]; exact hhiAbs)
    (by rw [hacc2]; exact hacc)
  rw [weightedStep_eq, arun_append, arun_append]
  change (arun k s2 weightedFinish).regs rAccW = _
  rw [hfinish, hacc2, hmag2lo, hmag2hi, hn2]
  rfl

end LeanCompCert.Ports.RamareCombined100M.WeightedDenote
