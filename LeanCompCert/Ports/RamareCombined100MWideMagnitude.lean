import LeanCompCert.Ports.RamareCombined100MWeightedDenote

/-!
# Absolute value and maximum for signed two-limb endpoint sums

The row checkpoints consume `max |rLo| |rHi|`.  The endpoint sums are signed
two-limb values, so this block performs a two-limb negation selected by the
high-limb sign bit.  It does not run the sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WideMagnitude

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.SeamBlock
open LeanCompCert.Ports.RamareCombined100M.WideEndpoint

def rMagLoLo : Nat := 332
def rMagLoHi : Nat := 333
def rMagHiLo : Nat := 334
def rMagHiHi : Nat := 335
def rAbsSign : Nat := 336
def rAbsInv : Nat := 337
def rAbsBorrow : Nat := 338
def rAbsNegLo : Nat := 339
def rAbsNegHi : Nat := 340
def rAbsTmp : Nat := 341
def rCmpHiGt : Nat := 342
def rCmpHiEq : Nat := 343
def rCmpLoGe : Nat := 344
def rCmpTmp : Nat := 345
def rMaxLo : Nat := 346
def rMaxHi : Nat := 347

/-- Compute the two-limb modular negation into dedicated scratch. -/
def negWide (srcLo srcHi : Nat) : List AInstr :=
  movLit rAbsNegLo 0 ++ movLit rAbsNegHi 0 ++
    LeanCompCert.Ports.AddWidePort.subWideABody
      rAbsNegLo rAbsNegHi rAbsBorrow srcLo srcHi

/-- Select one limb from the original or negated pair.  Keeping this as a
small block is important: its denotation can be proved independently of the
two-limb subtraction, so elaboration never expands both at once. -/
def selectLimb (src neg dst : Nat) : List AInstr :=
  movReg rC rAbsSign ++ movReg rX neg ++ movReg rY src ++
    selectBlock ++ movReg dst rSel

def signWide (srcHi : Nat) : List AInstr :=
  [ .scalar (.binop rAbsSign .ge (.reg srcHi) (.lit Section413Cells.H63)) ]

/-- Branch-free absolute value of one signed two-limb pair.  This staged form
reuses the small proved subtraction and select blocks, avoiding a single
large `simp` expansion. -/
def absWide (srcLo srcHi dstLo dstHi : Nat) : List AInstr :=
  negWide srcLo srcHi ++
    signWide srcHi ++
    selectLimb srcLo rAbsNegLo dstLo ++
    selectLimb srcHi rAbsNegHi dstHi

/-- Set `rAbsSign` when the first unsigned two-limb value is at least the
second, using the usual lexicographic comparison of high then low limbs. -/
def wideGe : List AInstr :=
  [ .scalar (.binop rCmpHiGt .gt (.reg rMagLoHi) (.reg rMagHiHi))
  , .scalar (.binop rCmpHiEq .eq (.reg rMagLoHi) (.reg rMagHiHi))
  , .scalar (.binop rCmpLoGe .ge (.reg rMagLoLo) (.reg rMagHiLo))
  , .scalar (.binop rCmpTmp .band (.reg rCmpHiEq) (.reg rCmpLoGe))
  , .scalar (.binop rAbsSign .bor (.reg rCmpHiGt) (.reg rCmpTmp)) ]

def maxWide : List AInstr :=
  wideGe ++ selectLimb rMagHiLo rMagLoLo rMaxLo ++
    selectLimb rMagHiHi rMagLoHi rMaxHi

def intervalMagnitudeWide : List AInstr :=
  absWide rAccLo rAccLoHi rMagLoLo rMagLoHi ++
    absWide rAccHi rAccHiHi rMagHiLo rMagHiHi ++ maxWide

def negLo (lo : Nat) : Nat := (M - lo) % M
def negHi (lo hi : Nat) : Nat := ((M - hi) % M +
  (M - (if lo = 0 then 0 else 1))) % M

theorem signWide_run (k : Nat) (s : AState) (srcHi : Nat) :
    (arun k s (signWide srcHi)).regs rAbsSign =
      if Section413Cells.H63 ≤ s.regs srcHi then 1 else 0 := by
  simp [signWide, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rAbsSign,
    Nat.mod_eq_of_lt (show Section413Cells.H63 < M by decide),
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

theorem wideGe_run (k : Nat) (s : AState) :
    (arun k s wideGe).regs rAbsSign =
      if s.regs rMagHiHi < s.regs rMagLoHi ∨
          (s.regs rMagLoHi = s.regs rMagHiHi ∧
            s.regs rMagHiLo ≤ s.regs rMagLoLo) then 1 else 0 := by
  by_cases hgt : s.regs rMagHiHi < s.regs rMagLoHi <;>
    by_cases heq : s.regs rMagLoHi = s.regs rMagHiHi <;>
      by_cases hlo : s.regs rMagHiLo ≤ s.regs rMagLoLo <;>
        simp only [rMagLoLo, rMagLoHi, rMagHiLo, rMagHiHi] at hgt heq hlo ⊢ <;>
        simp [wideGe, arun, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
          AState.writeReg, rCmpHiGt, rCmpHiEq, rCmpLoGe, rCmpTmp,
          rAbsSign, rMagLoLo, rMagLoHi, rMagHiLo, rMagHiHi,
          hgt, heq, hlo,
          Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)] <;> omega

theorem wval_le_iff_lex {alo ahi blo bhi : Nat}
    (halo : alo < WideSigned.B64) (ha : ahi < WideSigned.B64)
    (hblo : blo < WideSigned.B64) (hb : bhi < WideSigned.B64) :
    LeanCompCert.Verified.AddWide.wval (blo, bhi) ≤
        LeanCompCert.Verified.AddWide.wval (alo, ahi) ↔
      bhi < ahi ∨ (ahi = bhi ∧ blo ≤ alo) := by
  simp only [LeanCompCert.Verified.AddWide.wval, WideSigned.B64,
    LeanCompCert.Verified.AddWide.B64,
    LeanCompCert.Verified.MulWide.B64] at *
  omega

theorem hiOf_sign (z : Int)
    (hlo : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ z)
    (hhi : z < ((WideSigned.B128 : Nat) / 2 : Nat)) :
    Section413Cells.H63 ≤ WideSigned.hiOf z ↔ z < 0 := by
  simp only [WideSigned.hiOf, WideSigned.encodeZ128, WideSigned.B128,
    WideSigned.B64, LeanCompCert.Verified.AddWide.B128,
    LeanCompCert.Verified.AddWide.B64, LeanCompCert.Verified.MulWide.B64,
    Section413Cells.H63] at *
  omega

private theorem subWide_zero_split (x : Nat) (hx0 : 0 < x)
    (hx : x < WideSigned.B128) :
    LeanCompCert.Verified.AddWide.wval
        (LeanCompCert.Verified.AddWide.subWide (0, 0)
          (x % WideSigned.B64, x / WideSigned.B64)) = WideSigned.B128 - x := by
  have hB : 0 < WideSigned.B64 := LeanCompCert.Verified.AddWide.B64_pos
  have hm := Nat.mod_lt x hB
  have hd : x / WideSigned.B64 < WideSigned.B64 := by
    simp only [WideSigned.B128, WideSigned.B64,
      LeanCompCert.Verified.AddWide.B128,
      LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Verified.MulWide.B64] at hx ⊢
    omega
  have hsplit := Nat.mod_add_div x WideSigned.B64
  let lo := x % WideSigned.B64
  let hi := x / WideSigned.B64
  have hlo : lo < M := by
    simpa only [lo, WideSigned.B64,
      LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Ports.AddWidePort.M_eq_B64] using hm
  have hhi : hi < M := by
    simpa only [hi, WideSigned.B64,
      LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Ports.AddWidePort.M_eq_B64] using hd
  have hsplit' : lo + M * hi = x := by
    simpa only [lo, hi, WideSigned.B64,
      LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Ports.AddWidePort.M_eq_B64, Nat.mul_comm] using hsplit
  have hzeroLo : (0 + (M - lo)) % M = if lo = 0 then 0 else M - lo := by
    by_cases h : lo = 0
    · simp [h]
    · rw [if_neg h]
      exact sub_mod_lt (by omega) hlo
  have hzeroHi : (0 + (M - hi)) % M = if hi = 0 then 0 else M - hi := by
    by_cases h : hi = 0
    · simp [h]
    · rw [if_neg h]
      exact sub_mod_lt (Nat.pos_of_ne_zero h) hhi
  have hpair : LeanCompCert.Verified.AddWide.subWide (0, 0) (lo, hi) =
      if lo = 0 then (0, M - hi) else (M - lo, M - hi - 1) := by
    apply Prod.ext
    · simp only [LeanCompCert.Verified.AddWide.subWide, Prod.fst]
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      rw [hzeroLo]
      split <;> rfl
    · simp only [LeanCompCert.Verified.AddWide.subWide, Prod.snd]
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      rw [hzeroHi]
      by_cases hlo0 : lo = 0
      · rw [if_pos hlo0]
        have hhi0 : hi ≠ 0 := by
          intro h
          rw [hlo0, h] at hsplit'
          simp at hsplit'
          omega
        rw [if_neg hhi0]
        have hhipos : 0 < hi := Nat.pos_of_ne_zero hhi0
        have hdiff : M - hi < M := by omega
        simp [hlo0, Nat.mod_eq_of_lt hdiff]
      · rw [if_neg hlo0]
        have hlopos : 0 < lo := Nat.pos_of_ne_zero hlo0
        by_cases hhi0 : hi = 0
        · rw [if_pos hhi0]
          simp [hlopos, Nat.mod_eq_of_lt (show M - 1 < M by decide)]
          omega
        · rw [if_neg hhi0]
          have hhipos : 0 < hi := Nat.pos_of_ne_zero hhi0
          have hsub := sub_mod_ge (a := M - hi) (b := 1)
            (by omega) (by omega)
          simpa [hlopos] using hsub
  change LeanCompCert.Verified.AddWide.wval
      (LeanCompCert.Verified.AddWide.subWide (0, 0) (lo, hi)) = _
  rw [hpair]
  by_cases hlo0 : lo = 0
  · rw [if_pos hlo0]
    simp only [LeanCompCert.Verified.AddWide.wval, Prod.fst, Prod.snd,
      Nat.zero_add, WideSigned.B64]
    rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
    simp only [WideSigned.B128, LeanCompCert.Verified.AddWide.B128,
      LeanCompCert.Verified.Reflect.M] at hx hsplit' ⊢
    omega
  · rw [if_neg hlo0]
    simp only [LeanCompCert.Verified.AddWide.wval, Prod.fst, Prod.snd,
      WideSigned.B64]
    rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
    simp only [WideSigned.B128, LeanCompCert.Verified.AddWide.B128,
      LeanCompCert.Verified.Reflect.M] at hx hsplit' hlo hhi ⊢
    omega

theorem negCanonical_wval (z : Int)
    (hlo : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ z) (hz : z < 0) :
    LeanCompCert.Verified.AddWide.wval
        (LeanCompCert.Verified.AddWide.subWide (0, 0)
          (WideSigned.loOf z, WideSigned.hiOf z)) = z.natAbs := by
  have henc : WideSigned.encodeZ128 z = WideSigned.B128 - z.natAbs := by
    simp only [WideSigned.encodeZ128, WideSigned.B128,
      LeanCompCert.Verified.AddWide.B128] at *
    omega
  have hpos : 0 < WideSigned.encodeZ128 z := by
    rw [henc]
    simp only [WideSigned.B128, LeanCompCert.Verified.AddWide.B128] at hlo ⊢
    omega
  have hlt := WideSigned.encodeZ128_lt z
  unfold WideSigned.loOf WideSigned.hiOf
  rw [subWide_zero_split (WideSigned.encodeZ128 z) hpos hlt, henc]
  simp only [WideSigned.B128, LeanCompCert.Verified.AddWide.B128] at hlo ⊢
  omega

theorem canonical_wval_natAbs_of_nonneg (z : Int) (hz : 0 ≤ z)
    (hhi : z < ((WideSigned.B128 : Nat) / 2 : Nat)) :
    LeanCompCert.Verified.AddWide.wval
        (WideSigned.loOf z, WideSigned.hiOf z) = z.natAbs := by
  have hrep := WideSigned.loOf_hiOf_rep z
  unfold WideSigned.rep at hrep
  rw [hrep]
  simp only [WideSigned.encodeZ128, WideSigned.B128,
    LeanCompCert.Verified.AddWide.B128] at *
  omega

private theorem selectAccLoLow_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (hn : s.regs rAbsNegLo < M) (hx : s.regs rAccLo < M) :
    (arun k s (selectLimb rAccLo rAbsNegLo rMagLoLo)).regs rMagLoLo =
      (if s.regs rAbsSign = 1 then s.regs rAbsNegLo else s.regs rAccLo) := by
  simp only [rAbsSign] at hc
  simp only [rAbsNegLo] at hn
  simp only [rAccLo] at hx
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegLo, rMagLoLo, rAccLo,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegLo, rMagLoLo, rAccLo,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

private theorem selectAccLoHigh_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (hn : s.regs rAbsNegHi < M) (hx : s.regs rAccLoHi < M) :
    (arun k s (selectLimb rAccLoHi rAbsNegHi rMagLoHi)).regs rMagLoHi =
      (if s.regs rAbsSign = 1 then s.regs rAbsNegHi else s.regs rAccLoHi) := by
  simp only [rAbsSign] at hc
  simp only [rAbsNegHi] at hn
  simp only [rAccLoHi] at hx
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegHi, rMagLoHi, rAccLoHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegHi, rMagLoHi, rAccLoHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

private theorem selectAccHiLow_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (hn : s.regs rAbsNegLo < M) (hx : s.regs rAccHi < M) :
    (arun k s (selectLimb rAccHi rAbsNegLo rMagHiLo)).regs rMagHiLo =
      (if s.regs rAbsSign = 1 then s.regs rAbsNegLo else s.regs rAccHi) := by
  simp only [rAbsSign] at hc
  simp only [rAbsNegLo] at hn
  simp only [rAccHi] at hx
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegLo, rMagHiLo, rAccHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegLo, rMagHiLo, rAccHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

private theorem selectAccHiHigh_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (hn : s.regs rAbsNegHi < M) (hx : s.regs rAccHiHi < M) :
    (arun k s (selectLimb rAccHiHi rAbsNegHi rMagHiHi)).regs rMagHiHi =
      (if s.regs rAbsSign = 1 then s.regs rAbsNegHi else s.regs rAccHiHi) := by
  simp only [rAbsSign] at hc
  simp only [rAbsNegHi] at hn
  simp only [rAccHiHi] at hx
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegHi, rMagHiHi, rAccHiHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rAbsNegHi, rMagHiHi, rAccHiHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

private theorem selectMaxLow_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (ha : s.regs rMagLoLo < M) (hb : s.regs rMagHiLo < M) :
    (arun k s (selectLimb rMagHiLo rMagLoLo rMaxLo)).regs rMaxLo =
      (if s.regs rAbsSign = 1 then s.regs rMagLoLo else s.regs rMagHiLo) := by
  simp only [rAbsSign] at hc
  simp only [rMagLoLo] at ha
  simp only [rMagHiLo] at hb
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rMagLoLo, rMagHiLo, rMaxLo,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rMagLoLo, rMagHiLo, rMaxLo,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

private theorem selectMaxHigh_run (k : Nat) (s : AState)
    (hc : s.regs rAbsSign = 0 ∨ s.regs rAbsSign = 1)
    (ha : s.regs rMagLoHi < M) (hb : s.regs rMagHiHi < M) :
    (arun k s (selectLimb rMagHiHi rMagLoHi rMaxHi)).regs rMaxHi =
      (if s.regs rAbsSign = 1 then s.regs rMagLoHi else s.regs rMagHiHi) := by
  simp only [rAbsSign] at hc
  simp only [rMagLoHi] at ha
  simp only [rMagHiHi] at hb
  rcases hc with h0 | h1
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rMagLoHi, rMagHiHi, rMaxHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectLimb, movReg, selectBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rAbsSign, rMagLoHi, rMagHiHi, rMaxHi,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem negWideLo_run (k : Nat) (s : AState) :
    let out := arun k s (negWide rAccLo rAccLoHi)
    (out.regs rAbsNegLo, out.regs rAbsNegHi) =
      LeanCompCert.Verified.AddWide.subWide (0, 0)
        (s.regs rAccLo, s.regs rAccLoHi) := by
  dsimp only
  rw [negWide, arun_append, arun_append]
  let s0 := arun k s (movLit rAbsNegLo 0)
  let s1 := arun k s0 (movLit rAbsNegHi 0)
  have hzlo : s1.regs rAbsNegLo = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      movLit_run _ _ _ _ (by decide)]
  have hzhi : s1.regs rAbsNegHi = 0 :=
    movLit_run _ _ _ _ (by decide)
  have hslo : s1.regs rAccLo = s.regs rAccLo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hshi : s1.regs rAccLoHi = s.regs rAccLoHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  rw [WideSigned.subWideABody_run k s1 rAbsNegLo rAbsNegHi rAbsBorrow
    rAccLo rAccLoHi (by
      exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩), hzlo, hzhi, hslo, hshi]

theorem negWideHi_run (k : Nat) (s : AState) :
    let out := arun k s (negWide rAccHi rAccHiHi)
    (out.regs rAbsNegLo, out.regs rAbsNegHi) =
      LeanCompCert.Verified.AddWide.subWide (0, 0)
        (s.regs rAccHi, s.regs rAccHiHi) := by
  dsimp only
  rw [negWide, arun_append, arun_append]
  let s0 := arun k s (movLit rAbsNegLo 0)
  let s1 := arun k s0 (movLit rAbsNegHi 0)
  have hzlo : s1.regs rAbsNegLo = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      movLit_run _ _ _ _ (by decide)]
  have hzhi : s1.regs rAbsNegHi = 0 := movLit_run _ _ _ _ (by decide)
  have hslo : s1.regs rAccHi = s.regs rAccHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hshi : s1.regs rAccHiHi = s.regs rAccHiHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  rw [WideSigned.subWideABody_run k s1 rAbsNegLo rAbsNegHi rAbsBorrow
    rAccHi rAccHiHi (by
      exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩), hzlo, hzhi, hslo, hshi]

theorem absAccLoWide_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := arun k s (absWide rAccLo rAccLoHi rMagLoLo rMagLoHi)
    (out.regs rMagLoLo, out.regs rMagLoHi) =
      if Section413Cells.H63 ≤ s.regs rAccLoHi then
        LeanCompCert.Verified.AddWide.subWide (0, 0)
          (s.regs rAccLo, s.regs rAccLoHi)
      else (s.regs rAccLo, s.regs rAccLoHi) := by
  dsimp only
  let sN := arun k s (negWide rAccLo rAccLoHi)
  let sS := arun k sN (signWide rAccLoHi)
  let sL := arun k sS (selectLimb rAccLo rAbsNegLo rMagLoLo)
  let sH := arun k sL (selectLimb rAccLoHi rAbsNegHi rMagLoHi)
  have hneg : (sN.regs rAbsNegLo, sN.regs rAbsNegHi) =
      LeanCompCert.Verified.AddWide.subWide (0, 0)
        (s.regs rAccLo, s.regs rAccLoHi) := negWideLo_run k s
  have hloN : sN.regs rAccLo = s.regs rAccLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhiN : sN.regs rAccLoHi = s.regs rAccLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hsign : sS.regs rAbsSign =
      if Section413Cells.H63 ≤ s.regs rAccLoHi then 1 else 0 := by
    rw [signWide_run, hhiN]
  have hloS : sS.regs rAccLo = s.regs rAccLo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hloN]
  have hhiS : sS.regs rAccLoHi = s.regs rAccLoHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hhiN]
  have hnloS : sS.regs rAbsNegLo = sN.regs rAbsNegLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hnhiS : sS.regs rAbsNegHi = sN.regs rAbsNegHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwN : ∀ j, sN.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (negWide rAccLo rAccLoHi) s hw haW).1
  have haN : ∀ j, sN.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (negWide rAccLo rAccLoHi) s hw haW).2
  have hwS : ∀ j, sS.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (signWide rAccLoHi) sN hwN haN).1
  have hbit : sS.regs rAbsSign = 0 ∨ sS.regs rAbsSign = 1 := by
    rw [hsign]
    split <;> simp
  have hlow : sL.regs rMagLoLo =
      if sS.regs rAbsSign = 1 then sS.regs rAbsNegLo else sS.regs rAccLo :=
    selectAccLoLow_run k sS hbit (hwS _) (hwS _)
  have hsignL : sL.regs rAbsSign = sS.regs rAbsSign :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhiL : sL.regs rAccLoHi = sS.regs rAccLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hnhiL : sL.regs rAbsNegHi = sS.regs rAbsNegHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwL : ∀ j, sL.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (selectLimb rAccLo rAbsNegLo rMagLoLo) sS hwS
      ((LeanCompCert.Ports.Section413G1Denote.arun_lt k
        (signWide rAccLoHi) sN hwN haN).2)).1
  have hhigh : sH.regs rMagLoHi =
      if sL.regs rAbsSign = 1 then sL.regs rAbsNegHi else sL.regs rAccLoHi :=
    selectAccLoHigh_run k sL
      (by rw [hsignL]; exact hbit) (hwL _) (hwL _)
  have hlowH : sH.regs rMagLoLo = sL.regs rMagLoLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  change (sH.regs rMagLoLo, sH.regs rMagLoHi) = _
  by_cases h : Section413Cells.H63 ≤ s.regs rAccLoHi
  · rw [if_pos h]
    have hs1 : sS.regs rAbsSign = 1 := by simp [hsign, h]
    rw [hlowH, hlow, hhigh, hs1, if_pos rfl, hsignL, hs1, if_pos rfl,
      hnloS, hnhiL, hnhiS]
    exact hneg
  · rw [if_neg h]
    have hs0 : sS.regs rAbsSign = 0 := by simp [hsign, h]
    rw [hlowH, hlow, hhigh, hs0, if_neg (by decide), hsignL, hs0,
      if_neg (by decide), hloS, hhiL, hhiS]

theorem absAccHiWide_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := arun k s (absWide rAccHi rAccHiHi rMagHiLo rMagHiHi)
    (out.regs rMagHiLo, out.regs rMagHiHi) =
      if Section413Cells.H63 ≤ s.regs rAccHiHi then
        LeanCompCert.Verified.AddWide.subWide (0, 0)
          (s.regs rAccHi, s.regs rAccHiHi)
      else (s.regs rAccHi, s.regs rAccHiHi) := by
  dsimp only
  let sN := arun k s (negWide rAccHi rAccHiHi)
  let sS := arun k sN (signWide rAccHiHi)
  let sL := arun k sS (selectLimb rAccHi rAbsNegLo rMagHiLo)
  let sH := arun k sL (selectLimb rAccHiHi rAbsNegHi rMagHiHi)
  have hneg : (sN.regs rAbsNegLo, sN.regs rAbsNegHi) =
      LeanCompCert.Verified.AddWide.subWide (0, 0)
        (s.regs rAccHi, s.regs rAccHiHi) := negWideHi_run k s
  have hloN : sN.regs rAccHi = s.regs rAccHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhiN : sN.regs rAccHiHi = s.regs rAccHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hsign : sS.regs rAbsSign =
      if Section413Cells.H63 ≤ s.regs rAccHiHi then 1 else 0 := by
    rw [signWide_run, hhiN]
  have hloS : sS.regs rAccHi = s.regs rAccHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hloN]
  have hhiS : sS.regs rAccHiHi = s.regs rAccHiHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hhiN]
  have hnloS : sS.regs rAbsNegLo = sN.regs rAbsNegLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hnhiS : sS.regs rAbsNegHi = sN.regs rAbsNegHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwN : ∀ j, sN.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (negWide rAccHi rAccHiHi) s hw haW).1
  have haN : ∀ j, sN.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (negWide rAccHi rAccHiHi) s hw haW).2
  have hwS : ∀ j, sS.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (signWide rAccHiHi) sN hwN haN).1
  have hbit : sS.regs rAbsSign = 0 ∨ sS.regs rAbsSign = 1 := by
    rw [hsign]
    split <;> simp
  have hlow : sL.regs rMagHiLo =
      if sS.regs rAbsSign = 1 then sS.regs rAbsNegLo else sS.regs rAccHi :=
    selectAccHiLow_run k sS hbit (hwS _) (hwS _)
  have hsignL : sL.regs rAbsSign = sS.regs rAbsSign :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhiL : sL.regs rAccHiHi = sS.regs rAccHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hnhiL : sL.regs rAbsNegHi = sS.regs rAbsNegHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwL : ∀ j, sL.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (selectLimb rAccHi rAbsNegLo rMagHiLo) sS hwS
      ((LeanCompCert.Ports.Section413G1Denote.arun_lt k
        (signWide rAccHiHi) sN hwN haN).2)).1
  have hhigh : sH.regs rMagHiHi =
      if sL.regs rAbsSign = 1 then sL.regs rAbsNegHi else sL.regs rAccHiHi :=
    selectAccHiHigh_run k sL
      (by rw [hsignL]; exact hbit) (hwL _) (hwL _)
  have hlowH : sH.regs rMagHiLo = sL.regs rMagHiLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  change (sH.regs rMagHiLo, sH.regs rMagHiHi) = _
  by_cases h : Section413Cells.H63 ≤ s.regs rAccHiHi
  · rw [if_pos h]
    have hs1 : sS.regs rAbsSign = 1 := by simp [hsign, h]
    rw [hlowH, hlow, hhigh, hs1, if_pos rfl, hsignL, hs1, if_pos rfl,
      hnloS, hnhiL, hnhiS]
    exact hneg
  · rw [if_neg h]
    have hs0 : sS.regs rAbsSign = 0 := by simp [hsign, h]
    rw [hlowH, hlow, hhigh, hs0, if_neg (by decide), hsignL, hs0,
      if_neg (by decide), hloS, hhiL, hhiS]

theorem absAccLoWide_wval (k : Nat) (s : AState) (z : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccLo) (s.regs rAccLoHi) z)
    (hlo : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ z)
    (hhi : z < ((WideSigned.B128 : Nat) / 2 : Nat)) :
    let out := arun k s (absWide rAccLo rAccLoHi rMagLoLo rMagLoHi)
    LeanCompCert.Verified.AddWide.wval
      (out.regs rMagLoLo, out.regs rMagLoHi) = z.natAbs := by
  dsimp only
  have hcanon := WideSigned.rep_eq_canonical z
    (by
      change s.regs rAccLo < LeanCompCert.Verified.AddWide.B64
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      exact hw rAccLo) hrep
  rw [absAccLoWide_run k s hw haW, hcanon.1, hcanon.2]
  have hsign := hiOf_sign z hlo hhi
  by_cases hz : z < 0
  · rw [if_pos (hsign.mpr hz)]
    exact negCanonical_wval z hlo hz
  · rw [if_neg (fun h => hz (hsign.mp h))]
    exact canonical_wval_natAbs_of_nonneg z (Int.le_of_not_gt hz) hhi

theorem absAccHiWide_wval (k : Nat) (s : AState) (z : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccHi) (s.regs rAccHiHi) z)
    (hlo : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ z)
    (hhi : z < ((WideSigned.B128 : Nat) / 2 : Nat)) :
    let out := arun k s (absWide rAccHi rAccHiHi rMagHiLo rMagHiHi)
    LeanCompCert.Verified.AddWide.wval
      (out.regs rMagHiLo, out.regs rMagHiHi) = z.natAbs := by
  dsimp only
  have hcanon := WideSigned.rep_eq_canonical z
    (by
      change s.regs rAccHi < LeanCompCert.Verified.AddWide.B64
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      exact hw rAccHi) hrep
  rw [absAccHiWide_run k s hw haW, hcanon.1, hcanon.2]
  have hsign := hiOf_sign z hlo hhi
  by_cases hz : z < 0
  · rw [if_pos (hsign.mpr hz)]
    exact negCanonical_wval z hlo hz
  · rw [if_neg (fun h => hz (hsign.mp h))]
    exact canonical_wval_natAbs_of_nonneg z (Int.le_of_not_gt hz) hhi

theorem maxWide_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := arun k s maxWide
    (out.regs rMaxLo, out.regs rMaxHi) =
      if LeanCompCert.Verified.AddWide.wval
            (s.regs rMagHiLo, s.regs rMagHiHi) ≤
          LeanCompCert.Verified.AddWide.wval
            (s.regs rMagLoLo, s.regs rMagLoHi) then
        (s.regs rMagLoLo, s.regs rMagLoHi)
      else (s.regs rMagHiLo, s.regs rMagHiHi) := by
  dsimp only
  let sG := arun k s wideGe
  let sL := arun k sG (selectLimb rMagHiLo rMagLoLo rMaxLo)
  let sH := arun k sL (selectLimb rMagHiHi rMagLoHi rMaxHi)
  have hchoose : sG.regs rAbsSign =
      if s.regs rMagHiHi < s.regs rMagLoHi ∨
          (s.regs rMagLoHi = s.regs rMagHiHi ∧
            s.regs rMagHiLo ≤ s.regs rMagLoLo) then 1 else 0 := wideGe_run k s
  have hbit : sG.regs rAbsSign = 0 ∨ sG.regs rAbsSign = 1 := by
    rw [hchoose]
    split <;> simp
  have hframeG (r : Nat)
      (hr : r = rMagLoLo ∨ r = rMagLoHi ∨ r = rMagHiLo ∨ r = rMagHiHi) :
      sG.regs r = s.regs r := by
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwG : ∀ j, sG.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k wideGe s hw haW).1
  have haG : ∀ j, sG.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k wideGe s hw haW).2
  have hlo : sL.regs rMaxLo =
      if sG.regs rAbsSign = 1 then sG.regs rMagLoLo else sG.regs rMagHiLo :=
    selectMaxLow_run k sG hbit (hwG _) (hwG _)
  have hsignL : sL.regs rAbsSign = sG.regs rAbsSign :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hmagLoHiL : sL.regs rMagLoHi = sG.regs rMagLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hmagHiHiL : sL.regs rMagHiHi = sG.regs rMagHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwL : ∀ j, sL.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (selectLimb rMagHiLo rMagLoLo rMaxLo) sG hwG haG).1
  have hhigh : sH.regs rMaxHi =
      if sL.regs rAbsSign = 1 then sL.regs rMagLoHi else sL.regs rMagHiHi :=
    selectMaxHigh_run k sL (by rw [hsignL]; exact hbit) (hwL _) (hwL _)
  have hloH : sH.regs rMaxLo = sL.regs rMaxLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hlex := wval_le_iff_lex
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMagLoLo)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMagLoHi)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMagHiLo)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMagHiHi)
  change (sH.regs rMaxLo, sH.regs rMaxHi) = _
  by_cases h : LeanCompCert.Verified.AddWide.wval
      (s.regs rMagHiLo, s.regs rMagHiHi) ≤
      LeanCompCert.Verified.AddWide.wval
        (s.regs rMagLoLo, s.regs rMagLoHi)
  · rw [if_pos h]
    have hs1 : sG.regs rAbsSign = 1 := by
      rw [hchoose, if_pos (hlex.mp h)]
    rw [hloH, hlo, hhigh, hs1, if_pos rfl, hsignL, hs1, if_pos rfl,
      hframeG _ (Or.inl rfl), hmagLoHiL, hframeG _ (Or.inr (Or.inl rfl))]
  · rw [if_neg h]
    have hs0 : sG.regs rAbsSign = 0 := by
      rw [hchoose, if_neg (fun hh => h (hlex.mpr hh))]
    rw [hloH, hlo, hhigh, hs0, if_neg (by decide), hsignL, hs0,
      if_neg (by decide), hframeG _ (Or.inr (Or.inr (Or.inl rfl))),
      hmagHiHiL, hframeG _ (Or.inr (Or.inr (Or.inr rfl)))]

theorem maxWide_wval (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := arun k s maxWide
    LeanCompCert.Verified.AddWide.wval (out.regs rMaxLo, out.regs rMaxHi) =
      max (LeanCompCert.Verified.AddWide.wval
        (s.regs rMagLoLo, s.regs rMagLoHi))
        (LeanCompCert.Verified.AddWide.wval
          (s.regs rMagHiLo, s.regs rMagHiHi)) := by
  dsimp only
  rw [maxWide_run k s hw haW]
  by_cases h : LeanCompCert.Verified.AddWide.wval
      (s.regs rMagHiLo, s.regs rMagHiHi) ≤
      LeanCompCert.Verified.AddWide.wval
        (s.regs rMagLoLo, s.regs rMagLoHi)
  · rw [if_pos h, Nat.max_eq_left h]
  · rw [if_neg h, Nat.max_eq_right (Nat.le_of_not_ge h)]

theorem intervalMagnitudeWide_run (k : Nat) (s : AState) (lo hi : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hloRep : WideSigned.rep (s.regs rAccLo) (s.regs rAccLoHi) lo)
    (hhiRep : WideSigned.rep (s.regs rAccHi) (s.regs rAccHiHi) hi)
    (hloMin : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ lo)
    (hloMax : lo < ((WideSigned.B128 : Nat) / 2 : Nat))
    (hhiMin : -((WideSigned.B128 : Nat) / 2 : Nat) ≤ hi)
    (hhiMax : hi < ((WideSigned.B128 : Nat) / 2 : Nat)) :
    let out := arun k s intervalMagnitudeWide
    LeanCompCert.Verified.AddWide.wval (out.regs rMaxLo, out.regs rMaxHi) =
      intervalAbsUpper lo hi := by
  dsimp only
  let sL := arun k s (absWide rAccLo rAccLoHi rMagLoLo rMagLoHi)
  let sH := arun k sL (absWide rAccHi rAccHiHi rMagHiLo rMagHiHi)
  have hloMag : LeanCompCert.Verified.AddWide.wval
      (sL.regs rMagLoLo, sL.regs rMagLoHi) = lo.natAbs :=
    absAccLoWide_wval k s lo hw haW hloRep hloMin hloMax
  have hHiLo : sL.regs rAccHi = s.regs rAccHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hHiHi : sL.regs rAccHiHi = s.regs rAccHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwL : ∀ j, sL.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (absWide rAccLo rAccLoHi rMagLoLo rMagLoHi) s hw haW).1
  have haL : ∀ j, sL.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (absWide rAccLo rAccLoHi rMagLoLo rMagLoHi) s hw haW).2
  have hhiMag : LeanCompCert.Verified.AddWide.wval
      (sH.regs rMagHiLo, sH.regs rMagHiHi) = hi.natAbs :=
    absAccHiWide_wval k sL hi hwL haL
      (by rw [hHiLo, hHiHi]; exact hhiRep) hhiMin hhiMax
  have hLoLo : sH.regs rMagLoLo = sL.regs rMagLoLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hLoHi : sH.regs rMagLoHi = sL.regs rMagLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwH : ∀ j, sH.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (absWide rAccHi rAccHiHi rMagHiLo rMagHiHi) sL hwL haL).1
  have haH : ∀ j, sH.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (absWide rAccHi rAccHiHi rMagHiLo rMagHiHi) sL hwL haL).2
  have hmax := maxWide_wval k sH hwH haH
  simp only [intervalMagnitudeWide, arun_append]
  change LeanCompCert.Verified.AddWide.wval
      ((arun k sH maxWide).regs rMaxLo, (arun k sH maxWide).regs rMaxHi) = _
  rw [hmax, hLoLo, hLoHi, hloMag, hhiMag]
  rfl

theorem absWide_wf (srcLo srcHi dstLo dstHi : Nat)
    (hsrcLo : srcLo < 384) (hsrcHi : srcHi < 384)
    (hdstLo : dstLo < 384) (hdstHi : dstHi < 384) :
    (absWide srcLo srcHi dstLo dstHi).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  simp [absWide, negWide, signWide, selectLimb, movLit, movReg, selectBlock,
    WideSigned.subWideABody_run,
    LeanCompCert.Ports.AddWidePort.subWideABody,
    LeanCompCert.Ports.AddWidePort.subWideBody,
    LeanCompCert.Ports.ArraySegSieve.ainstrWFB,
    LeanCompCert.Ports.ArraySegSieve.instrWFB,
    LeanCompCert.Ports.ArraySegSieve.operandWFB,
    hsrcLo, hsrcHi, hdstLo, hdstHi] <;> decide

theorem maxWide_wf :
    maxWide.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rfl

theorem intervalMagnitudeWide_wf :
    intervalMagnitudeWide.all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [intervalMagnitudeWide, List.all_append, List.all_append,
    absWide_wf rAccLo rAccLoHi rMagLoLo rMagLoHi (by decide) (by decide)
      (by decide) (by decide),
    absWide_wf rAccHi rAccHiHi rMagHiLo rMagHiHi (by decide) (by decide)
      (by decide) (by decide), maxWide_wf]
  rfl

end LeanCompCert.Ports.RamareCombined100M.WideMagnitude
