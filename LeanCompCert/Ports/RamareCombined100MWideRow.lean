import LeanCompCert.Ports.RamareCombined100MWideMagnitude

/-!
# Word-safe checkpoint test for a two-limb interval magnitude

The historical row block divided a one-word magnitude.  The exact cumulative
endpoint is wider than one word, so this replacement checks a slightly
stronger, division-free condition:

`magnitude ≤ n * (bound - (weightedAbs + 1))`.

Together with `weightedAbs + 1 ≤ bound`, this implies the source row's
strengthened quotient condition.  The product and comparison are both exact
two-limb operations.  Compilation proves only this symbolic implication; it
does not evaluate a checkpoint or the production sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WideRow

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.SeamBlock
open LeanCompCert.Ports.RamareCombined100M.WideEndpoint
open LeanCompCert.Ports.RamareCombined100M.WideMagnitude

def rRowW1 : Nat := 348
def rRowOver : Nat := 349
def rRowHiGt : Nat := 350
def rRowHiEq : Nat := 351
def rRowLoGe : Nat := 352
def rRowTmp : Nat := 353
def rRowOK : Nat := 354
def rRowMagBad : Nat := 355

/-- Prepare the two multiplicands.  `ExactProduct.rA/rB` are the established
inputs of the verified 64x64-to-128 circuit. -/
def rowProductStage (bound : Nat) : List AInstr :=
  [ .scalar (.binop rRowW1 .add (.reg rAccW) (.lit 1))
  , .scalar (.binop rRowOver .gt (.reg rRowW1) (.lit bound))
  , .scalar (.mov ExactProduct.rA (.reg sCand))
  , .scalar (.binop ExactProduct.rB .sub (.lit bound) (.reg rRowW1)) ]

/-- Compare the exact product against `rMaxHi:rMaxLo`; set `rBad` on either
an underflowed threshold or a magnitude failure. -/
def rowProductCompare : List AInstr :=
  [ .scalar (.binop rRowHiGt .gt (.reg ExactProduct.rHi) (.reg rMaxHi))
  , .scalar (.binop rRowHiEq .eq (.reg ExactProduct.rHi) (.reg rMaxHi))
  , .scalar (.binop rRowLoGe .ge (.reg ExactProduct.rLo) (.reg rMaxLo))
  , .scalar (.binop rRowTmp .band (.reg rRowHiEq) (.reg rRowLoGe))
  , .scalar (.binop rRowOK .bor (.reg rRowHiGt) (.reg rRowTmp))
  , .scalar (.binop rRowMagBad .eq (.reg rRowOK) (.lit 0))
  , .scalar (.binop rBad .bor (.reg rRowOver) (.reg rRowMagBad)) ]

def rowWideCheck (bound : Nat) : List AInstr :=
  rowProductStage bound ++ ExactProduct.floorBlock ++ rowProductCompare

/-- The division-free condition checked by `rowWideCheck` implies the
quotient-form condition used by the source row reduction. -/
theorem wideCondition_strengthened {n weighted magnitude bound : Nat}
    (hw : weighted + 1 ≤ bound)
    (hm : magnitude ≤ n * (bound - (weighted + 1))) :
    weighted + magnitude / n + 1 ≤ bound := by
  have hq : magnitude / n ≤ bound - (weighted + 1) :=
    Nat.div_le_of_le_mul hm
  omega

theorem rowProductStage_over (k : Nat) (s : AState) (bound : Nat)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M) :
    (arun k s (rowProductStage bound)).regs rRowOver =
      if bound < s.regs rAccW + 1 then 1 else 0 := by
  simp only [rAccW] at hsum
  simp [rowProductStage, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rRowW1, rRowOver, rAccW,
    ExactProduct.rA, ExactProduct.rB, sCand,
    Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hbound,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

theorem rowProductStage_inputs (k : Nat) (s : AState) (bound : Nat)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M)
    (hpass : s.regs rAccW + 1 ≤ bound) :
    let out := arun k s (rowProductStage bound)
    out.regs ExactProduct.rA = s.regs sCand ∧
      out.regs ExactProduct.rB = bound - (s.regs rAccW + 1) := by
  dsimp only
  have hsub := sub_mod_ge (a := bound) (b := s.regs rAccW + 1)
    hpass hbound
  simp only [rAccW] at hsum hpass hsub
  simp [rowProductStage, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rRowW1, rRowOver, rAccW,
    ExactProduct.rA, ExactProduct.rB, sCand,
    Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hbound,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide), hsub]

theorem rowProductCompare_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hover : s.regs rRowOver = 0 ∨ s.regs rRowOver = 1) :
    (arun k s rowProductCompare).regs rBad =
      if s.regs rRowOver = 1 ∨
          ¬ (LeanCompCert.Verified.AddWide.wval
              (s.regs rMaxLo, s.regs rMaxHi) ≤
            LeanCompCert.Verified.AddWide.wval
              (s.regs ExactProduct.rLo, s.regs ExactProduct.rHi))
      then 1 else 0 := by
  have hlex := wval_le_iff_lex
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw ExactProduct.rLo)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw ExactProduct.rHi)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMaxLo)
    (by simpa only [WideSigned.B64,
        ← LeanCompCert.Ports.AddWidePort.M_eq_B64] using hw rMaxHi)
  have hraw : (arun k s rowProductCompare).regs rBad =
      if s.regs rRowOver = 1 ∨
          ¬ (s.regs ExactProduct.rHi > s.regs rMaxHi ∨
            (s.regs ExactProduct.rHi = s.regs rMaxHi ∧
              s.regs ExactProduct.rLo ≥ s.regs rMaxLo))
      then 1 else 0 := by
    simp only [rRowOver] at hover
    rcases hover with hover | hover <;>
      by_cases hgt : s.regs ExactProduct.rHi > s.regs rMaxHi <;>
        by_cases heq : s.regs ExactProduct.rHi = s.regs rMaxHi <;>
          by_cases hlo : s.regs ExactProduct.rLo ≥ s.regs rMaxLo <;>
            simp only [ExactProduct.rLo, ExactProduct.rHi, rMaxLo, rMaxHi]
              at hgt heq hlo ⊢ <;>
            simp [rowProductCompare, arun, astep,
              LeanCompCert.Verified.InstrBlock.sdest,
              LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
              AState.writeReg, rRowHiGt, rRowHiEq, rRowLoGe, rRowTmp,
              rRowOK, rRowMagBad, rRowOver, rBad, rMaxLo, rMaxHi,
              ExactProduct.rLo, ExactProduct.rHi, hover, hgt, heq, hlo,
              Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)] <;> omega
  rw [hraw]
  by_cases h : LeanCompCert.Verified.AddWide.wval
      (s.regs rMaxLo, s.regs rMaxHi) ≤
      LeanCompCert.Verified.AddWide.wval
        (s.regs ExactProduct.rLo, s.regs ExactProduct.rHi)
  · have hl := hlex.mp h
    simp [h, hl]
  · have hl : ¬ (s.regs ExactProduct.rHi > s.regs rMaxHi ∨
        (s.regs ExactProduct.rHi = s.regs rMaxHi ∧
          s.regs ExactProduct.rLo ≥ s.regs rMaxLo)) :=
      fun hh => h (hlex.mpr hh)
    simp [h, hl]

theorem rowWideCheck_sound (k : Nat) (s : AState) (bound : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M)
    (hzero : (arun k s (rowWideCheck bound)).regs rBad = 0) :
    s.regs rAccW + 1 ≤ bound ∧
      LeanCompCert.Verified.AddWide.wval (s.regs rMaxLo, s.regs rMaxHi) ≤
        s.regs sCand * (bound - (s.regs rAccW + 1)) := by
  let staged := arun k s (rowProductStage bound)
  let product := arun k staged ExactProduct.floorBlock
  have hover := rowProductStage_over k s bound hsum hbound
  have hoverFrame : product.regs rRowOver = staged.regs rRowOver :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwStaged : ∀ j, staged.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (rowProductStage bound) s hw haW).1
  have haStaged : ∀ j, staged.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (rowProductStage bound) s hw haW).2
  have hwProduct : ∀ j, product.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      ExactProduct.floorBlock staged hwStaged haStaged).1
  have hcmp := rowProductCompare_run k product hwProduct (by
    rw [hoverFrame, hover]
    split <;> simp)
  have hcmpZero : (arun k product rowProductCompare).regs rBad = 0 := by
    simpa only [rowWideCheck, arun_append] using hzero
  rw [hcmp] at hcmpZero
  have hnot : ¬ (product.regs rRowOver = 1 ∨
      ¬ (LeanCompCert.Verified.AddWide.wval
          (product.regs rMaxLo, product.regs rMaxHi) ≤
        LeanCompCert.Verified.AddWide.wval
          (product.regs ExactProduct.rLo, product.regs ExactProduct.rHi))) := by
    intro h
    rw [if_pos h] at hcmpZero
    contradiction
  have hpass : s.regs rAccW + 1 ≤ bound := by
    apply Nat.le_of_not_gt
    intro h
    apply (not_or.mp hnot).1
    rw [hoverFrame, hover, if_pos h]
  have hinputs := rowProductStage_inputs k s bound hsum hbound hpass
  have hlow := ExactProduct.floorBlock_low k staged hwStaged
  have hhigh := ExactProduct.floorBlock_high k staged hwStaged
  have hmaxLo : product.regs rMaxLo = s.regs rMaxLo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hmaxHi : product.regs rMaxHi = s.regs rMaxHi := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  refine ⟨hpass, ?_⟩
  have hle := Classical.not_not.mp (not_or.mp hnot).2
  rw [hmaxLo, hmaxHi, hlow, hhigh, hinputs.1, hinputs.2] at hle
  have hspec := (LeanCompCert.Verified.MulWide.hl_spec
    (s.regs sCand) (bound - (s.regs rAccW + 1))
    (by
      change s.regs sCand < LeanCompCert.Verified.AddWide.B64
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      exact hw _)
    (by
      change bound - (s.regs rAccW + 1) < LeanCompCert.Verified.AddWide.B64
      rw [← LeanCompCert.Ports.AddWidePort.M_eq_B64]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound)).1
  calc
    LeanCompCert.Verified.AddWide.wval (s.regs rMaxLo, s.regs rMaxHi) ≤
        LeanCompCert.Verified.AddWide.wval
          (LeanCompCert.Verified.MulWide.hl (s.regs sCand)
            (bound - (s.regs rAccW + 1))) := hle
    _ = s.regs sCand * (bound - (s.regs rAccW + 1)) := hspec

/-- The checkpoint block always leaves a Boolean failure result.  This small
composition lemma is useful to callers which append a guarded sticky-flag
commit: they need the bit fact independently of whether the check passed. -/
theorem rowWideCheck_bad_bit (k : Nat) (s : AState) (bound : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M) :
    let out := arun k s (rowWideCheck bound)
    out.regs rBad = 0 ∨ out.regs rBad = 1 := by
  dsimp only
  let staged := arun k s (rowProductStage bound)
  let product := arun k staged ExactProduct.floorBlock
  have hover := rowProductStage_over k s bound hsum hbound
  have hoverFrame : product.regs rRowOver = staged.regs rRowOver :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hwStaged : ∀ j, staged.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (rowProductStage bound) s hw haW).1
  have haStaged : ∀ j, staged.arr j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      (rowProductStage bound) s hw haW).2
  have hwProduct : ∀ j, product.regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      ExactProduct.floorBlock staged hwStaged haStaged).1
  have hcmp := rowProductCompare_run k product hwProduct (by
    rw [hoverFrame, hover]
    split <;> simp)
  simpa only [rowWideCheck, arun_append] using
    (show (arun k product rowProductCompare).regs rBad = 0 ∨
        (arun k product rowProductCompare).regs rBad = 1 by
      rw [hcmp]
      split <;> simp)

theorem rowWideCheck_wf (bound : Nat) :
    (rowWideCheck bound).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [rowWideCheck, List.all_append, List.all_append,
    all_ainstrWFB_mono (show 327 ≤ 384 by decide) ExactProduct.blocks_wf.1]
  rfl

end LeanCompCert.Ports.RamareCombined100M.WideRow
