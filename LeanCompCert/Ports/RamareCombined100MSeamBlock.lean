import LeanCompCert.Ports.RamareCombined100MQuotient
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Ports.RamareCombined100MBodyRefinement
import LeanCompCert.Ports.RamareCombined100MExactProduct

/-!
# The Ramaré seam test as an emitted instruction block

`suffixStep`'s seam conjoins `psiU' ≤ 2 * n * scale` onto the carried flag.
Written against the psi VALUE that is unimplementable: the value is ~2.8e22, so
it does not fit a machine word -- which is exactly why the sweep carries a
`PsiQR` pair rather than a number.

Against the pair the test needs no arithmetic beyond comparisons:

    q * n + r ≤ 2 * n * B   ↔   q < 2 * B  ∨  (q = 2 * B ∧ r = 0)

(`psi_seam_iff_qr`, proved on the certificates side).  This module is that
equivalence as instructions of the verified fragment, with its denotation, so
the sweep body can adopt it.

The block is standalone: nothing here modifies the existing sweep, and the
integration is a separate step.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge

/-- Carried psi upper quotient (`rPsiUQ` in the sweep). -/
def rQ : Nat := 204
/-- Carried psi upper remainder (`rPsiUR`). -/
def rR : Nat := 205
/-- The constant `2 * scale`, seeded once.

⚠ **Must live above the sweep's scratch range.**  This was 212, which is
`LambdaPsiBase.rT0` -- a register `candidateBody` overwrites on every
iteration.  The block is correct in isolation either way, so the proof below
did not notice; wired into the sweep it would have had its "constant"
destroyed on the first candidate.  The sweep occupies 200-212 (`rSumL` through
`rT0`) and the abs/max blocks 217-223, so the seam takes 229-233.  (224 is `rMx`, below in this same file -- scan the
FILE, not just the host module, before allocating.) -/
def rTwoB : Nat := 275
def rT1 : Nat := 276
def rT2 : Nat := 277
def rT3 : Nat := 278
/-- The sticky violation flag; also above the sweep's scratch range. -/
def rViol : Nat := 279

/-- `q < 2B ∨ (q = 2B ∧ r = 0)`, negated and accumulated into `rViol`. -/
def seamPsiBlockAt (q r twoB : Nat) : List AInstr :=
  [ .scalar (.binop rT1 .lt (.reg q) (.reg twoB))
  , .scalar (.binop rT2 .eq (.reg q) (.reg twoB))
  , .scalar (.binop rT3 .eq (.reg r) (.lit 0))
  , .scalar (.binop rT2 .band (.reg rT2) (.reg rT3))
  , .scalar (.binop rT1 .bor (.reg rT1) (.reg rT2))
  , .scalar (.binop rT2 .eq (.reg rT1) (.lit 0))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rT2)) ]

def seamPsiBlock : List AInstr := seamPsiBlockAt rQ rR rTwoB

/-- **The parameterized block computes the seam test.**  The input-register
parameters let a program check a quotient/remainder pair reconstructed for the
current source denominator, rather than accidentally checking a host pair
which has already been rebased for the next iteration. -/
theorem seamPsiBlockAt_run (k : Nat) (s : AState) (q r twoB : Nat)
    (hqT1 : q ≠ rT1) (hqT2 : q ≠ rT2) (hqT3 : q ≠ rT3)
    (hrT1 : r ≠ rT1) (hrT2 : r ≠ rT2) (hrT3 : r ≠ rT3)
    (htT1 : twoB ≠ rT1) (htT2 : twoB ≠ rT2) (htT3 : twoB ≠ rT3)
    (hvT1 : rViol ≠ rT1) (hvT2 : rViol ≠ rT2)
    (hvT3 : rViol ≠ rT3) :
    (arun k s (seamPsiBlockAt q r twoB)).regs rViol =
      (s.regs rViol |||
        (if s.regs q < s.regs twoB ∨
            (s.regs q = s.regs twoB ∧ s.regs r = 0) then 0 else 1)) % M := by
  simp only [rT1, rT2, rT3, rViol] at hqT1 hqT2 hqT3 hrT1 hrT2 hrT3
  simp only [rT1, rT2, rT3, rViol] at htT1 htT2 htT3 hvT1 hvT2 hvT3
  have hM : M ≠ 1 := by decide
  by_cases h1 : s.regs q < s.regs twoB <;>
    by_cases h2 : s.regs q = s.regs twoB <;>
      by_cases h3 : s.regs r = 0 <;>
        simp [seamPsiBlockAt, arun, astep, denoteAInstr, denoteInstr,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval,
          denoteOperand, denoteOp, AState.writeReg, RegState.set,
          rT1, rT2, rT3, rViol, hqT1, hqT2, hqT3, hrT1, hrT2, hrT3,
          htT1, htT2, htT3, hvT1, hvT2, hvT3, h1, h2, h3, hM]

/-- **The block computes the seam test.**  Comparisons denote to exactly `0`/`1`
(`denoteOp`), so `band`/`bor` act as logical operations, and the seven
instructions leave `rViol` OR-ed with the negation of

    q < 2B  ∨  (q = 2B ∧ r = 0)

which `psi_seam_iff_qr` identifies with `psiU ≤ 2 * n * scale`. -/
theorem seamPsiBlock_run (k : Nat) (s : AState) :
    (arun k s seamPsiBlock).regs rViol =
      (s.regs rViol |||
        (if s.regs rQ < s.regs rTwoB ∨
            (s.regs rQ = s.regs rTwoB ∧ s.regs rR = 0) then 0 else 1)) % M := by
  simpa [seamPsiBlock] using seamPsiBlockAt_run k s rQ rR rTwoB
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Absolute difference, branch-free

Both `correctedIntegerOK` and `remainderAnchorOK` compare `|A - B|` against a
threshold, where `A` and `B` are naturals whose difference genuinely goes
either way.  The machine's `.sub` is MODULAR, not truncated, so `A - B` wraps
to `M - (B - A)` when `A < B` -- the truncated-subtraction identity
`|A-B| = (A -. B) + (B -. A)` does not transfer.

Selecting instead costs one comparison and two multiplications: the wrong
difference is multiplied by zero, so its wrapped value never reaches the sum. -/

/-- `(a + (M - b)) % M` is ordinary subtraction when `b ≤ a`. -/
theorem sub_mod_ge {a b : Nat} (hb : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hbM : b < M := Nat.lt_of_le_of_lt hb ha
  have hrw : a + (M - b) = M + (a - b) := by omega
  rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- And wraps when `a < b`. -/
theorem sub_mod_lt {a b : Nat} (h : a < b) (hbM : b < M) :
    (a + (M - b)) % M = M - (b - a) := by
  have hrw : a + (M - b) = M - (b - a) := by omega
  rw [hrw, Nat.mod_eq_of_lt (by omega)]

def rA : Nat := 263
def rB : Nat := 264
def rF : Nat := 265
def rG : Nat := 266
def rD1 : Nat := 267
def rD2 : Nat := 268
def rOut : Nat := 269

def absDiffBlock : List AInstr :=
  [ .scalar (.binop rF .ge (.reg rA) (.reg rB))
  , .scalar (.binop rD1 .sub (.reg rA) (.reg rB))
  , .scalar (.binop rD2 .sub (.reg rB) (.reg rA))
  , .scalar (.binop rG .sub (.lit 1) (.reg rF))
  , .scalar (.binop rD1 .mul (.reg rF) (.reg rD1))
  , .scalar (.binop rD2 .mul (.reg rG) (.reg rD2))
  , .scalar (.binop rOut .add (.reg rD1) (.reg rD2)) ]

/-- The block leaves `|A - B|` in `rOut`, for register contents below `M`. -/
theorem absDiffBlock_run (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M) :
    (arun k s absDiffBlock).regs rOut =
      (if s.regs rA ≥ s.regs rB then s.regs rA - s.regs rB
       else s.regs rB - s.regs rA) := by
  have hM : (0 : Nat) < M := by decide
  simp only [rA, rB] at hA hB
  simp only [absDiffBlock, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rF, rG, rD1, rD2, rOut]
  by_cases h : s.regs 264 ≤ s.regs 263
  · -- the selector is 1, so only the first difference survives; the other
    -- term is multiplied by `1 + (M-1) = M` and vanishes mod `M`
    have hg : 1 + (M - 1) = M := by omega
    simp [h, sub_mod_ge h hA, Nat.mod_self]
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · -- the selector is 0; the wrapped difference is multiplied away
    have h' : s.regs 263 < s.regs 264 := by omega
    have hg : 1 + (M - 0) = M + 1 := by omega
    simp [Nat.not_le.mpr h', sub_mod_ge (Nat.le_of_lt h') hB, hg,
      Nat.mod_eq_of_lt (show (1:Nat) < M by decide)]
    exact Nat.mod_eq_of_lt (by omega)

/-! ## Max, and the scaled threshold

`correctedIntegerOK` and `rowOK` both compare a scaled interval magnitude
against a bound.  Two things make the naive form unemittable, and both are
fixed here.

The magnitude is `max |I.1| |I.2|`, which `absDiffBlock` and `maxBlock` supply.
The comparison is `c * x ≤ B`, and computing `c * x` is exactly wrong: on a
FAILING round that product can exceed a machine word, so the artifact would
compare a wrapped value and could report success.  `mul_le_iff_le_div` turns it
into `x ≤ B / c`, where `B / c` is a compile-time constant and no
multiplication is emitted at all. -/

def rMx : Nat := 270

/-- `max a b`, by the same select the absolute difference uses. -/
def maxBlock : List AInstr :=
  [ .scalar (.binop rF .ge (.reg rA) (.reg rB))
  , .scalar (.binop rG .sub (.lit 1) (.reg rF))
  , .scalar (.binop rD1 .mul (.reg rF) (.reg rA))
  , .scalar (.binop rD2 .mul (.reg rG) (.reg rB))
  , .scalar (.binop rMx .add (.reg rD1) (.reg rD2)) ]

theorem maxBlock_run (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M) :
    (arun k s maxBlock).regs rMx =
      (if s.regs rA ≥ s.regs rB then s.regs rA else s.regs rB) := by
  have hM : (0 : Nat) < M := by decide
  simp only [rA, rB] at hA hB
  simp only [maxBlock, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rF, rG, rD1, rD2, rMx]
  by_cases h : s.regs 264 ≤ s.regs 263
  · have hg : 1 + (M - 1) = M := by omega
    simp [h]
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have h' : s.regs 263 < s.regs 264 := by omega
    simp [Nat.not_le.mpr h', Nat.mod_eq_of_lt (show (1:Nat) < M by decide)]
    exact Nat.mod_eq_of_lt (by omega)

/-- A scaled threshold test needs no multiplication: `c * x ≤ B` is exactly
`x ≤ B / c`, and `B / c` is a constant.  Emitting `c * x` instead would compare
a wrapped product on a failing round. -/
theorem mul_le_iff_le_div {c x B : Nat} (hc : 0 < c) :
    c * x ≤ B ↔ x ≤ B / c := by
  rw [Nat.le_div_iff_mul_le hc, Nat.mul_comm]

/-! ## The threshold, and the violation it records

The tail of every check: compare the magnitude against a constant and record
failure.  The constant is `B / c`, folded at emission by `mul_le_iff_le_div`,
so the emitted code contains no multiplication -- which is what keeps a
FAILING round from comparing a wrapped product. -/

def rBad : Nat := 271

/-- `viol |= (x > bound)`. -/
def thresholdBlock (bound : Nat) : List AInstr :=
  [ .scalar (.binop rBad .gt (.reg rMx) (.lit bound))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

theorem thresholdBlock_run (k : Nat) (s : AState) (bound : Nat)
    (hb : bound < M) :
    (arun k s (thresholdBlock bound)).regs rViol =
      (s.regs rViol ||| (if s.regs rMx > bound then 1 else 0)) % M := by
  simp [thresholdBlock, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rMx, rBad, rViol, Nat.mod_eq_of_lt hb]

/-! ## Composing the blocks

`arun_append` chains them, and `Verified.ArrayRegFrame.arun_frame` supplies the
frame conditions -- it discharges "this block does not write register `j`" by
`decide` for a CONCRETE `j`, which is the form assembly actually needs, since
the emitter knows exactly which registers each block reads.  An earlier attempt
here stated the frames for an abstract `j` with disequality hypotheses; that
shape does not match the available lemma and is not what the assembly wants. -/

/-! ## Row 4: the anchor check

`remainderAnchorOK_iff` (claude_math, `Combined100MHeadroom`) reduces
`anchorOK` to a statement entirely in `Nat`:

    max (absNat (sumL + gammaLower) logU) (absNat (sumU + gammaUpper) logL)
      <= 4 * scale / 10000

which is exactly `absDiffBlock` twice, `maxBlock`, `thresholdBlock`.  The
threshold is a compile-time constant, so — per `mul_le_iff_le_div` — no
multiplication is emitted and no product can wrap.

The four inputs are **pre-staged by the caller** into block-local registers.
That is deliberate: it keeps every register in the run lemma concrete, so the
frame conditions discharge by `decide`, which is the form
`ArrayRegFrame.arun_frame` actually provides.  Taking the source registers as
parameters instead would need frames for an abstract index, which is the shape
that failed here before. -/

/-- Staged `sumDivL`. -/
def rIL : Nat := 280
/-- Staged `sumDivU`. -/
def rIU : Nat := 281
/-- Staged carried `logL`. -/
def rGL : Nat := 282
/-- Staged carried `logU`. -/
def rGU : Nat := 283
/-- Holds the first absolute difference across the second `absDiffBlock`,
which rewrites `rF`..`rOut`. -/
def rSave : Nat := 284

/-- Move the sweep's live values into the block's staging registers.
`sumL`/`sumU` are `rSumL`/`rSumU` (200/201) and the carried logs are
`LogSweep.rLogL`/`rLogU` (180/181); all four are below 206, so none is written
by any block in this file. -/
def anchorStage (rSumLo rSumHi rLogLo rLogHi : Nat) : List AInstr :=
  [ .scalar (.mov rIL (.reg rSumLo))
  , .scalar (.mov rIU (.reg rSumHi))
  , .scalar (.mov rGL (.reg rLogLo))
  , .scalar (.mov rGU (.reg rLogHi)) ]

/-- Load the first pair. -/
def anchorLoad1 (gammaLo : Nat) : List AInstr :=
  [ .scalar (.binop rA .add (.reg rIL) (.lit gammaLo))
  , .scalar (.mov rB (.reg rGU)) ]

/-- Save the first difference, then load the second pair. -/
def anchorLoad2 (gammaHi : Nat) : List AInstr :=
  [ .scalar (.mov rSave (.reg rOut))
  , .scalar (.binop rA .add (.reg rIU) (.lit gammaHi))
  , .scalar (.mov rB (.reg rGL)) ]

/-- Feed both differences to `maxBlock`. -/
def anchorLoad3 : List AInstr :=
  [ .scalar (.mov rA (.reg rSave))
  , .scalar (.mov rB (.reg rOut)) ]

/-- `|sumL + gammaLo - logU|`, `|sumU + gammaHi - logL|`, their max, and the
threshold test OR-ed into `rViol`.

Named stages, not one flat list: `simp only [arun_append]` on a flat
concatenation rewrites the wrong match. -/
def anchorHead (gammaLo : Nat) : List AInstr :=
  anchorLoad1 gammaLo ++ absDiffBlock

/-- The tail up to and including the max, with the threshold left off.
Split out so a *guarded* check (row 3's `c.lower ≤ n`, row 4's `n = c.limit`)
can insert its condition between the magnitude and the flag. -/
def anchorTailMax (gammaHi : Nat) : List AInstr :=
  anchorLoad2 gammaHi ++ absDiffBlock ++ anchorLoad3 ++ maxBlock

def anchorTail (gammaHi bound : Nat) : List AInstr :=
  anchorTailMax gammaHi ++ thresholdBlock bound

def anchorBlock (gammaLo gammaHi bound : Nat) : List AInstr :=
  anchorHead gammaLo ++ anchorTail gammaHi bound

/-- The magnitude the block computes, as a plain `Nat` function. -/
def absN (a b : Nat) : Nat := if a ≥ b then a - b else b - a

theorem anchorLoad1_rA (k : Nat) (s : AState) (gammaLo : Nat) :
    (arun k s (anchorLoad1 gammaLo)).regs rA = (s.regs rIL + gammaLo) % M := by
  simp [anchorLoad1, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rIL, rGU]

theorem anchorLoad1_rB (k : Nat) (s : AState) (gammaLo : Nat) :
    (arun k s (anchorLoad1 gammaLo)).regs rB = s.regs rGU := by
  simp [anchorLoad1, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rIL, rGU]

theorem anchorLoad2_rSave (k : Nat) (s : AState) (gammaHi : Nat) :
    (arun k s (anchorLoad2 gammaHi)).regs rSave = s.regs rOut := by
  simp [anchorLoad2, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rIU, rGL, rOut, rSave]

theorem anchorLoad2_rA (k : Nat) (s : AState) (gammaHi : Nat) :
    (arun k s (anchorLoad2 gammaHi)).regs rA = (s.regs rIU + gammaHi) % M := by
  simp [anchorLoad2, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rIU, rGL, rOut, rSave]

theorem anchorLoad2_rB (k : Nat) (s : AState) (gammaHi : Nat) :
    (arun k s (anchorLoad2 gammaHi)).regs rB = s.regs rGL := by
  simp [anchorLoad2, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rIU, rGL, rOut, rSave]

theorem anchorLoad3_rA (k : Nat) (s : AState) :
    (arun k s anchorLoad3).regs rA = s.regs rSave := by
  simp [anchorLoad3, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rOut, rSave]

theorem anchorLoad3_rB (k : Nat) (s : AState) :
    (arun k s anchorLoad3).regs rB = s.regs rOut := by
  simp [anchorLoad3, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rOut, rSave]

theorem if_ge_eq_max (a b : Nat) : (if a ≥ b then a else b) = max a b := by
  by_cases h : a ≥ b <;> simp [h, Nat.max_def] <;> omega

/-- The head leaves `|sumL + gammaLo - logU|` in `rOut`. -/
theorem anchorHead_run (k : Nat) (s : AState) (gammaLo : Nat)
    (hA1 : s.regs rIL + gammaLo < M) (hB1 : s.regs rGU < M) :
    (arun k s (anchorHead gammaLo)).regs rOut =
      absN (s.regs rIL + gammaLo) (s.regs rGU) := by
  have h1A : (arun k s (anchorLoad1 gammaLo)).regs rA = s.regs rIL + gammaLo := by
    rw [anchorLoad1_rA, Nat.mod_eq_of_lt hA1]
  have h1B : (arun k s (anchorLoad1 gammaLo)).regs rB = s.regs rGU :=
    anchorLoad1_rB k s gammaLo
  rw [anchorHead, arun_append,
    absDiffBlock_run _ _ (by rw [h1A]; exact hA1) (by rw [h1B]; exact hB1),
    h1A, h1B, absN]

/-- The head touches none of the second pair's inputs, nor the flag. -/
theorem anchorHead_frame (k : Nat) (s : AState) (gammaLo r : Nat)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r (anchorHead gammaLo) = false) :
    (arun k s (anchorHead gammaLo)).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ h _

theorem anchorHead_rIU (k : Nat) (s : AState) (gammaLo : Nat) :
    (arun k s (anchorHead gammaLo)).regs rIU = s.regs rIU :=
  anchorHead_frame k s gammaLo rIU (by rfl)

theorem anchorHead_rGL (k : Nat) (s : AState) (gammaLo : Nat) :
    (arun k s (anchorHead gammaLo)).regs rGL = s.regs rGL :=
  anchorHead_frame k s gammaLo rGL (by rfl)

theorem anchorHead_rViol (k : Nat) (s : AState) (gammaLo : Nat) :
    (arun k s (anchorHead gammaLo)).regs rViol = s.regs rViol :=
  anchorHead_frame k s gammaLo rViol (by rfl)

/-- The tail consumes the first difference from `rOut`, computes the second,
takes the max and ORs the threshold test into `rViol`. -/
theorem anchorTailMax_run (k : Nat) (u : AState) (gammaHi : Nat)
    (hA2 : u.regs rIU + gammaHi < M) (hB2 : u.regs rGL < M)
    (hOut : u.regs rOut < M) :
    (arun k u (anchorTailMax gammaHi)).regs rMx =
        max (u.regs rOut) (absN (u.regs rIU + gammaHi) (u.regs rGL)) ∧
      (arun k u (anchorTailMax gammaHi)).regs rViol = u.regs rViol := by
  rw [anchorTailMax, arun_append, arun_append, arun_append]
  have hA : (arun k u (anchorLoad2 gammaHi)).regs rA = u.regs rIU + gammaHi := by
    rw [anchorLoad2_rA, Nat.mod_eq_of_lt hA2]
  have hB : (arun k u (anchorLoad2 gammaHi)).regs rB = u.regs rGL :=
    anchorLoad2_rB k u gammaHi
  have hS : (arun k u (anchorLoad2 gammaHi)).regs rSave = u.regs rOut :=
    anchorLoad2_rSave k u gammaHi
  have hV : (arun k u (anchorLoad2 gammaHi)).regs rViol = u.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hOut2 : (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock).regs rOut =
      absN (u.regs rIU + gammaHi) (u.regs rGL) := by
    rw [absDiffBlock_run _ _ (by rw [hA]; exact hA2) (by rw [hB]; exact hB2),
      hA, hB, absN]
  have hS2 : (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock).regs rSave =
      u.regs rOut := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hS]
  have hV2 : (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock).regs rViol =
      u.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hV]
  have hA3 : (arun k (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock)
      anchorLoad3).regs rA = u.regs rOut := by
    rw [anchorLoad3_rA, hS2]
  have hB3 : (arun k (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock)
      anchorLoad3).regs rB = absN (u.regs rIU + gammaHi) (u.regs rGL) := by
    rw [anchorLoad3_rB, hOut2]
  have hV3 : (arun k (arun k (arun k u (anchorLoad2 gammaHi)) absDiffBlock)
      anchorLoad3).regs rViol = u.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hV2]
  have hd2M : absN (u.regs rIU + gammaHi) (u.regs rGL) < M := by
    rw [absN]; split <;> omega
  refine ⟨?_, ?_⟩
  · rw [maxBlock_run _ _ (by rw [hA3]; exact hOut) (by rw [hB3]; exact hd2M),
      hA3, hB3, if_ge_eq_max]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hV3]

theorem anchorTail_run (k : Nat) (u : AState) (gammaHi bound : Nat)
    (hA2 : u.regs rIU + gammaHi < M) (hB2 : u.regs rGL < M)
    (hOut : u.regs rOut < M) (hb : bound < M) :
    (arun k u (anchorTail gammaHi bound)).regs rViol =
      (u.regs rViol |||
        (if max (u.regs rOut) (absN (u.regs rIU + gammaHi) (u.regs rGL)) > bound
         then 1 else 0)) % M := by
  obtain ⟨hMx, hV⟩ := anchorTailMax_run k u gammaHi hA2 hB2 hOut
  rw [anchorTail, arun_append, thresholdBlock_run _ _ _ hb, hMx, hV]

/-- **Row 4, end to end.** -/
theorem anchorBlock_run (k : Nat) (s : AState) (gammaLo gammaHi bound : Nat)
    (hA1 : s.regs rIL + gammaLo < M) (hB1 : s.regs rGU < M)
    (hA2 : s.regs rIU + gammaHi < M) (hB2 : s.regs rGL < M)
    (hb : bound < M) :
    (arun k s (anchorBlock gammaLo gammaHi bound)).regs rViol =
      (s.regs rViol |||
        (if max (absN (s.regs rIL + gammaLo) (s.regs rGU))
                (absN (s.regs rIU + gammaHi) (s.regs rGL)) > bound
         then 1 else 0)) % M := by
  have hd1M : absN (s.regs rIL + gammaLo) (s.regs rGU) < M := by
    rw [absN]; split <;> omega
  rw [anchorBlock, arun_append,
    anchorTail_run _ _ _ _
      (by rw [anchorHead_rIU]; exact hA2)
      (by rw [anchorHead_rGL]; exact hB2)
      (by rw [anchorHead_run _ _ _ hA1 hB1]; exact hd1M) hb,
    anchorHead_run _ _ _ hA1 hB1, anchorHead_rIU, anchorHead_rGL,
    anchorHead_rViol]

/-! ## Row 3(b): the corrected-psi interval, by reusing the anchor block

`correctedOK` and `anchorOK` are the same shape — two magnitudes, their max,
one threshold — differing only in what is compared and by which constant:

    anchor    | sumL + gammaLower           - logU                      |
    corrected | sumL + gammaLower + scale   - logU - divUpper psiU n     |

So `anchorBlock` is already the generic two-magnitude block; row 3(b) needs
only different *staging*.  `divLower_of_qr` and `divUpper_of_qr_zero/_pos`
(claude_math, `Combined100MHeadroom`) turn the two divisions into the carried
quotient/remainder pair, which the sweep holds in `rPsiLQ`/`rPsiLR` and
`rPsiUQ`/`rPsiUR`:

    divLower psiL n = qL
    divUpper psiU n = qU + (if rU > 0 then 1 else 0)

both emittable with no division at all. -/

/-- Scratch for the `rU > 0` ceiling adjustment. -/
def rT4 : Nat := 285

/-! The sweep's live source registers, read in place — the same convention
`rQ`/`rR` already follow.  They are deliberately NOT in the allocation guard
below: they belong to the host sweep, and this file only reads them. -/

/-- `LambdaPsiBase.rSumL`. -/
def sSumL : Nat := 200
/-- `LambdaPsiBase.rSumU`. -/
def sSumU : Nat := 201
/-- `LambdaPsiBase.rPsiLQ`; `divLower psiL n` is exactly this quotient. -/
def sPsiLQ : Nat := 202
/-- ⚠ SNAPSHOT, not the host register.  The model's `step` evaluates every
check against `st.logL`/`st.logU` -- the log state BEFORE this candidate's
update -- and only then sets `logL := st.logL + incLWord n`.  The host body
performs that update, so by the time the checks run, registers 180/181 hold
the NEXT candidate's logs.  Reading them directly makes `qSubOK` compare
`pExp * lp` against a `logU` that is one increment too large.

`candidateGatePre` copies 180/181 here before the body runs, so every block
below reads the value the model reads. -/
def rLogLPre : Nat := 316
/-- Snapshot of `LogSweep.rLogU`; see `rLogLPre`. -/
def rLogUPre : Nat := 317

/-- The host's live log registers, read only by `candidateGatePre`. -/
def sLogL : Nat := 180
def sLogU : Nat := 181

/-- Stage `correctedOK`'s four operands into the two-magnitude block's inputs:
`rIL := sumL`, `rIU := sumU`, `rGL := logL + qL`,
`rGU := logU + qU + (rU > 0)`.  `rQ`/`rR` are the carried `psiU` pair. -/
def correctedStageAt (qL qU rU : Nat) : List AInstr :=
  [ .scalar (.mov rIL (.reg sSumL))
  , .scalar (.mov rIU (.reg sSumU))
  , .scalar (.binop rGL .add (.reg rLogLPre) (.reg qL))
  , .scalar (.binop rT4 .gt (.reg rU) (.lit 0))
  , .scalar (.binop rGU .add (.reg rLogUPre) (.reg qU))
  , .scalar (.binop rGU .add (.reg rGU) (.reg rT4)) ]

def correctedStage : List AInstr :=
  [ .scalar (.mov rIL (.reg sSumL))
  , .scalar (.mov rIU (.reg sSumU))
  , .scalar (.binop rGL .add (.reg rLogLPre) (.reg sPsiLQ))
  , .scalar (.binop rT4 .gt (.reg rR) (.lit 0))
  , .scalar (.binop rGU .add (.reg rLogUPre) (.reg rQ))
  , .scalar (.binop rGU .add (.reg rGU) (.reg rT4)) ]

theorem correctedStage_rIL (k : Nat) (s : AState) :
    (arun k s correctedStage).regs rIL = s.regs sSumL := by
  simp [correctedStage, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rIL, rIU, rGL, rGU, rT4, rQ, rR, sSumL, sSumU, sPsiLQ, rLogLPre, rLogUPre]

theorem correctedStage_rIU (k : Nat) (s : AState) :
    (arun k s correctedStage).regs rIU = s.regs sSumU := by
  simp [correctedStage, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rIL, rIU, rGL, rGU, rT4, rQ, rR, sSumL, sSumU, sPsiLQ, rLogLPre, rLogUPre]

theorem correctedStage_rGL (k : Nat) (s : AState) :
    (arun k s correctedStage).regs rGL =
      (s.regs rLogLPre + s.regs sPsiLQ) % M := by
  simp [correctedStage, arun, astep, denoteAInstr, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rIL, rIU, rGL, rGU, rT4, rQ, rR, sSumL, sSumU, sPsiLQ, rLogLPre, rLogUPre]

/-- The ceiling adjustment: `rGU = logU + qU + (1 if rU > 0 else 0)`, which by
`divUpper_of_qr_zero`/`divUpper_of_qr_pos` is `logU + divUpper psiU n`. -/
theorem correctedStage_rGU (k : Nat) (s : AState)
    (h : s.regs rLogUPre + s.regs rQ + (if s.regs rR > 0 then 1 else 0) < M) :
    (arun k s correctedStage).regs rGU =
      s.regs rLogUPre + s.regs rQ + (if s.regs rR > 0 then 1 else 0) := by
  have hlt : s.regs rLogUPre + s.regs rQ < M := by split at h <;> omega
  simp only [rLogUPre, rQ, rR] at h hlt
  by_cases hr : 0 < s.regs 205
  · simp only [hr, if_true, gt_iff_lt] at h
    simp [correctedStage, arun, astep, denoteAInstr, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rIL, rIU, rGL, rGU, rT4, rQ, rR, sSumL, sSumU, sPsiLQ, rLogLPre, rLogUPre,
      hr, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h]
  · have hr' : s.regs 205 = 0 := by omega
    simp only [hr', Nat.lt_irrefl, if_false, gt_iff_lt] at h
    simp [correctedStage, arun, astep, denoteAInstr, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rIL, rIU, rGL, rGU, rT4, rQ, rR, sSumL, sSumU, sPsiLQ, rLogLPre, rLogUPre,
      hr', Nat.mod_eq_of_lt hlt]

theorem correctedStage_rGL_exact (k : Nat) (s : AState)
    (h : s.regs rLogLPre + s.regs sPsiLQ < M) :
    (arun k s correctedStage).regs rGL = s.regs rLogLPre + s.regs sPsiLQ := by
  rw [correctedStage_rGL, Nat.mod_eq_of_lt h]

theorem correctedStage_rViol (k : Nat) (s : AState) :
    (arun k s correctedStage).regs rViol = s.regs rViol :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _

/-- **Row 3(b): the corrected-psi interval test**, staged then run through the
generic two-magnitude block.  With `gammaLo := gammaLower + scale`,
`gammaHi := gammaUpper + scale` and `bound := 4 * scale / 1000`, the guarded
value is exactly `correctedOK`'s, by `correctedInterval_of_qr_*` and
`mul_le_iff_le_div`. -/
def correctedBlock (gammaLo gammaHi bound : Nat) : List AInstr :=
  correctedStage ++ anchorBlock gammaLo gammaHi bound

theorem correctedBlock_run (k : Nat) (s : AState) (gammaLo gammaHi bound : Nat)
    (hGU : s.regs rLogUPre + s.regs rQ + (if s.regs rR > 0 then 1 else 0) < M)
    (hGL : s.regs rLogLPre + s.regs sPsiLQ < M)
    (hA1 : s.regs sSumL + gammaLo < M)
    (hA2 : s.regs sSumU + gammaHi < M)
    (hb : bound < M) :
    (arun k s (correctedBlock gammaLo gammaHi bound)).regs rViol =
      (s.regs rViol |||
        (if max
            (absN (s.regs sSumL + gammaLo)
              (s.regs rLogUPre + s.regs rQ + (if s.regs rR > 0 then 1 else 0)))
            (absN (s.regs sSumU + gammaHi) (s.regs rLogLPre + s.regs sPsiLQ))
              > bound
         then 1 else 0)) % M := by
  rw [correctedBlock, arun_append,
    anchorBlock_run _ _ _ _ _
      (by rw [correctedStage_rIL]; exact hA1)
      (by rw [correctedStage_rGU _ _ hGU]; omega)
      (by rw [correctedStage_rIU]; exact hA2)
      (by rw [correctedStage_rGL_exact _ _ hGL]; omega) hb,
    correctedStage_rIL, correctedStage_rIU,
    correctedStage_rGU _ _ hGU, correctedStage_rGL_exact _ _ hGL,
    correctedStage_rViol]

/-! ## Guarded commit

Both `seam` and `anchor` are conditional in the model — `if c.lower ≤ n then …
else true`, `if n = c.limit then … else true`.  A guarded check therefore has to
put its condition between the magnitude test and the flag, which is why
`anchorTailMax` leaves the threshold off.  The candidate `n` is register 132,
the one `classifiedArithmeticBody_run` exposes. -/

/-- The candidate `n`, as the classifier leaves it. -/
def sCand : Nat := 132
/-- Scratch for the guard bit. -/
def rT5 : Nat := 286

/-- The threshold test, WITHOUT committing it to the flag. -/
def thresholdBit (bound : Nat) : List AInstr :=
  [ .scalar (.binop rBad .gt (.reg rMx) (.lit bound)) ]

/-- `rViol |||= (n ≥ lower) && (rMx > bound)`. -/
def guardedCommit (lower : Nat) : List AInstr :=
  [ .scalar (.binop rT5 .ge (.reg sCand) (.lit lower))
  , .scalar (.binop rBad .band (.reg rBad) (.reg rT5))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

/-- A violation is recorded exactly when the guard holds AND the magnitude
exceeds the bound — the emitted form of `if lower ≤ n then test else true`. -/
theorem guardedThreshold_run (k : Nat) (s : AState) (bound lower : Nat)
    (hb : bound < M) (hl : lower < M) :
    (arun k s (thresholdBit bound ++ guardedCommit lower)).regs rViol =
      (s.regs rViol |||
        (if lower ≤ s.regs sCand ∧ bound < s.regs rMx then 1 else 0)) % M := by
  have hM : M ≠ 1 := by decide
  rw [arun_append]
  by_cases hg : lower ≤ s.regs sCand <;> by_cases ht : bound < s.regs rMx <;>
    simp only [rMx, sCand] at hg ht <;>
    simp [thresholdBit, guardedCommit, arun, astep, denoteAInstr, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rMx, rBad, rViol, rT5, sCand, hg, ht, hM,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- `rViol |||= (n = at) && (rMx > bound)`.

The equality form of `guardedCommit`, for the checks the model fires at a
single candidate: `anchor` at `n = c.limit`, and each of `rowAt`'s four sites
(`462848`, `10^6`, `10^7`, `10^8`), where the row's `K` and numerator are
compile-time constants. -/
def eqGuardedCommit (at_ : Nat) : List AInstr :=
  [ .scalar (.binop rT5 .eq (.reg sCand) (.lit at_))
  , .scalar (.binop rBad .band (.reg rBad) (.reg rT5))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

theorem eqGuardedThreshold_run (k : Nat) (s : AState) (bound at_ : Nat)
    (hb : bound < M) (ha : at_ < M) :
    (arun k s (thresholdBit bound ++ eqGuardedCommit at_)).regs rViol =
      (s.regs rViol |||
        (if s.regs sCand = at_ ∧ bound < s.regs rMx then 1 else 0)) % M := by
  have hM : M ≠ 1 := by decide
  rw [arun_append]
  by_cases hg : s.regs sCand = at_ <;> by_cases ht : bound < s.regs rMx <;>
    simp only [rMx, sCand] at hg ht <;>
    simp [thresholdBit, eqGuardedCommit, arun, astep, denoteAInstr, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rMx, rBad, rViol, rT5, sCand, hg, ht, hM,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-! ## Rows 1 and 2: shift before multiplying

`coeffInterval`'s branches are `mulUpper x y = ceil (x*y / 2^32)` and
`mulLower x y = x*y / 2^32` on log values `x, y ~ log n * 2^32 ~ 2^36`.  The
intermediate `x*y ~ 2^72` overflows a machine word by ~339x, so emitting the
product as written would compare a WRAPPED value — and on a failing round a
wrapped comparison can report success.

Shifting each factor by `2^16 = logShift` first keeps every intermediate inside
a word (`(x >> 16)^2 ~ 2^40`) and lands on the same scale, because
`2^16 * 2^16 = 2^32 = coeffScale`.  The two lemmas below are what make it sound:
rounding each factor OUTWARD gives a product that brackets the model's, so a
check passed on the emitted value implies the model's check.

Both are generic in the shift `s`; instantiate at `s = 65536`. -/

theorem le_ceilDiv_mul {a d : Nat} (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h := Nat.div_add_mod (a + (d - 1)) d
  have hm : (a + (d - 1)) % d < d := Nat.mod_lt _ hd
  have hc : (a + (d - 1)) / d * d = d * ((a + (d - 1)) / d) := Nat.mul_comm _ _
  omega

/-- Ceil-shifting both factors over-approximates `mulUpper`. -/
theorem ceilShift_mul_ge (x y s : Nat) (hs : 0 < s) :
    (x * y + (s * s - 1)) / (s * s) ≤ (x + (s - 1)) / s * ((y + (s - 1)) / s) := by
  have hss : 0 < s * s := Nat.mul_pos hs hs
  have hx : x ≤ (x + (s - 1)) / s * s := le_ceilDiv_mul hs
  have hy : y ≤ (y + (s - 1)) / s * s := le_ceilDiv_mul hs
  have hprod : x * y ≤ (x + (s - 1)) / s * ((y + (s - 1)) / s) * (s * s) := by
    have h1 : x * y ≤ ((x + (s - 1)) / s * s) * ((y + (s - 1)) / s * s) :=
      Nat.mul_le_mul hx hy
    have h2 : ((x + (s - 1)) / s * s) * ((y + (s - 1)) / s * s)
        = (x + (s - 1)) / s * ((y + (s - 1)) / s) * (s * s) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hss).mpr ?_)
  have hexp : ((x + (s - 1)) / s * ((y + (s - 1)) / s)).succ * (s * s)
      = (x + (s - 1)) / s * ((y + (s - 1)) / s) * (s * s) + s * s := by
    simp [Nat.succ_mul]
  omega

/-- Floor-shifting both factors under-approximates `mulLower`. -/
theorem floorShift_mul_le (x y s : Nat) (hs : 0 < s) :
    x / s * (y / s) ≤ x * y / (s * s) := by
  have hss : 0 < s * s := Nat.mul_pos hs hs
  refine (Nat.le_div_iff_mul_le hss).mpr ?_
  have hx : x / s * s ≤ x := Nat.div_mul_le_self x s
  have hy : y / s * s ≤ y := Nat.div_mul_le_self y s
  have h2 : x / s * (y / s) * (s * s) = (x / s * s) * (y / s * s) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [h2]
  exact Nat.mul_le_mul hx hy

/-! The model's own constants: `coeffScale = 2^32 = 65536 * 65536` and
`logShift = 65536`, so the shift the emitter needs is the model's own
`2^48 -> 2^32` step and introduces no new constant. -/

theorem coeffScale_eq : coeffScale = 65536 * 65536 := by rfl

/-- **What the emitter may compute instead of `mulUpper`.**  Ceil-shift each
factor, then multiply: every intermediate stays inside a word, and the result
is `>=` the model's, so a check passed on it implies the model's check. -/
theorem mulUpper_le_ceilShifted (x y : Nat) :
    mulUpper x y ≤ (x + 65535) / 65536 * ((y + 65535) / 65536) := by
  have h := ceilShift_mul_ge x y 65536 (by decide)
  have hce : mulUpper x y = (x * y + (65536 * 65536 - 1)) / (65536 * 65536) := by
    rw [mulUpper, ceilDiv, coeffScale_eq]
  rw [hce]
  exact h

/-- And the matching under-approximation for `mulLower`. -/
theorem floorShifted_le_mulLower (x y : Nat) :
    x / 65536 * (y / 65536) ≤ mulLower x y := by
  have h := floorShift_mul_le x y 65536 (by decide)
  have hce : mulLower x y = x * y / (65536 * 65536) := by
    rw [mulLower, coeffScale_eq]
  rw [hce]
  exact h

/-! ### The emitted shifted product

`rA`, `rB` hold the two log factors; the block leaves the ceil-shifted product
in `rProd`.  Five instructions, no division and no wide intermediate. -/

def rSh1 : Nat := 287
def rSh2 : Nat := 288
def rProd : Nat := 289

/-- `rProd := ceil(rA / 2^16) * ceil(rB / 2^16)`. -/
def ceilShiftedProduct : List AInstr :=
  [ .scalar (.binop rSh1 .add (.reg rA) (.lit 65535))
  , .scalar (.binop rSh1 .lshr (.reg rSh1) (.lit 16))
  , .scalar (.binop rSh2 .add (.reg rB) (.lit 65535))
  , .scalar (.binop rSh2 .lshr (.reg rSh2) (.lit 16))
  , .scalar (.binop rProd .mul (.reg rSh1) (.reg rSh2)) ]

/-- `rProd := (rA >> 16) * (rB >> 16)`. -/
def floorShiftedProduct : List AInstr :=
  [ .scalar (.binop rSh1 .lshr (.reg rA) (.lit 16))
  , .scalar (.binop rSh2 .lshr (.reg rB) (.lit 16))
  , .scalar (.binop rProd .mul (.reg rSh1) (.reg rSh2)) ]

theorem ceilShiftedProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA + 65535 < M) (hB : s.regs rB + 65535 < M)
    (hp : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) < M) :
    (arun k s ceilShiftedProduct).regs rProd =
      (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) := by
  simp only [rA, rB] at hA hB hp
  simp [ceilShiftedProduct, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rSh1, rSh2, rProd, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (show (65535 : Nat) < M by decide),
    Nat.mod_eq_of_lt (show (16 : Nat) < M by decide)]

theorem floorShiftedProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M)
    (hp : s.regs rA / 65536 * (s.regs rB / 65536) < M) :
    (arun k s floorShiftedProduct).regs rProd =
      s.regs rA / 65536 * (s.regs rB / 65536) := by
  simp only [rA, rB] at hA hB hp
  simp [floorShiftedProduct, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rSh1, rSh2, rProd, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (show (16 : Nat) < M by decide)]

/-- **The emitted block brackets the model, upward.**  This is the statement
rows 1 and 2 consume: whatever `ceilShiftedProduct` leaves in `rProd` is at
least the model's `mulUpper`, so an interval built from it contains the
model's. -/
theorem ceilShiftedProduct_ge_mulUpper (k : Nat) (s : AState)
    (hA : s.regs rA + 65535 < M) (hB : s.regs rB + 65535 < M)
    (hp : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) < M) :
    mulUpper (s.regs rA) (s.regs rB) ≤
      (arun k s ceilShiftedProduct).regs rProd := by
  rw [ceilShiftedProduct_run k s hA hB hp]
  exact mulUpper_le_ceilShifted _ _

/-- And downward, for the lower endpoint. -/
theorem floorShiftedProduct_le_mulLower (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M)
    (hp : s.regs rA / 65536 * (s.regs rB / 65536) < M) :
    (arun k s floorShiftedProduct).regs rProd ≤
      mulLower (s.regs rA) (s.regs rB) := by
  rw [floorShiftedProduct_run k s hA hB hp]
  exact floorShifted_le_mulLower _ _

/-! ### Exact products used by production

The shifted-factor blocks above remain useful for one-sided estimates, but the
production endpoint pipeline needs equality with the model.  These aliases
instantiate the separately compiled widening-multiply proof. -/

/-- A conservative operand cap for every exact fixed-point product.  Two
operands below `2^48` have product below `2^96`, so shifting right by 32 bits
cannot overflow a 64-bit result (including the ceiling carry). -/
def exactOperandCap : Nat := 281474976710656

/-- A common cap on every projected product.  Twice this value plus either
production gamma constant is strictly below `2^63`, so the subsequent signed
endpoint encoding cannot wrap. -/
def exactProjectedCap : Nat := 4000000000000000000

/-- Fail closed when either exact-product operand is outside the range in
which its 32-bit fixed-point projection is a machine word, or when the
projected result is outside the range used by the signed endpoint proof. -/
def exactOperandCapCheck : List AInstr :=
  [ .scalar (.binop rBad .ge (.reg rA) (.lit exactOperandCap))
  , .scalar (.binop rT4 .ge (.reg rB) (.lit exactOperandCap))
  , .scalar (.binop rBad .bor (.reg rBad) (.reg rT4))
  , .scalar (.binop rT5 .ge (.reg rProd) (.lit exactProjectedCap))
  , .scalar (.binop rBad .bor (.reg rBad) (.reg rT5))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

def exactFloorProduct : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.ExactProduct.floorBlock ++
    exactOperandCapCheck

def exactCeilProduct : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.ExactProduct.ceilBlock ++
    exactOperandCapCheck

theorem exactFloorProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32) :
    (arun k s exactFloorProduct).regs rProd = mulLower (s.regs rA) (s.regs rB) := by
  rw [exactFloorProduct, arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rProd
      exactOperandCapCheck (by rfl)]
  simpa [
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rA,
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rB,
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rProd,
    rA, rB, rProd] using
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.floorBlock_run k s hw hfit

theorem exactCeilProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rA) (s.regs rB) < M) :
    (arun k s exactCeilProduct).regs rProd = mulUpper (s.regs rA) (s.regs rB) := by
  rw [exactCeilProduct, arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rProd
      exactOperandCapCheck (by rfl)]
  simpa [
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rA,
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rB,
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.rProd,
    rA, rB, rProd] using
    LeanCompCert.Ports.RamareCombined100M.ExactProduct.ceilBlock_run k s hw hfit hout

theorem exactProduct_wf :
    exactFloorProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true ∧
    exactCeilProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rcases LeanCompCert.Ports.RamareCombined100M.ExactProduct.blocks_wf with
    ⟨hf, hc⟩
  constructor <;>
    simp only [exactFloorProduct, exactCeilProduct, List.all_append,
      hf, hc, Bool.true_and, exactOperandCapCheck] <;> rfl

/-! ### Row 2: the signed accumulators

`rLo`/`rHi` accumulate `coeffInterval`'s endpoints, which are genuinely signed
(its first branch is negated).  Two's complement handles this with **no extra
instructions at all**: `Section413Cells.encodeZ_add` says

    (encodeZ a + encodeZ b) % B64 = encodeZ (a + b)

and `B64 = 2^64 = M`, so the machine's ordinary `.add` — which computes
`(x + y) % M` — already performs signed addition on encoded operands.

Magnitude, sieved 2026-08-24: the dominant term is
`Σ_{p<=1e8} (log p)^2 * 2^32 = 7.481e18` against `2^63 = 9.223e18`, i.e. 81%,
and the per-candidate `+2*gammaLower32` offsets it to ~6.99e18 (76%).  One
signed word suffices; the ~20% margin is why `decodeZ_encodeZ`'s range
hypotheses have to be discharged rather than assumed. -/

theorem M_eq_B64 : M = LeanCompCert.Verified.MulWide.B64 := by rfl

/-- Signed accumulate. One instruction. -/
def signedAccumulate (acc inc : Nat) : List AInstr :=
  [ .scalar (.binop acc .add (.reg acc) (.reg inc)) ]

theorem signedAccumulate_run (k : Nat) (s : AState) (acc inc : Nat) (a b : Int)
    (hacc : s.regs acc = Section413Cells.encodeZ a)
    (hinc : s.regs inc = Section413Cells.encodeZ b) :
    (arun k s (signedAccumulate acc inc)).regs acc =
      Section413Cells.encodeZ (a + b) := by
  simp only [signedAccumulate, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl]
  rw [hacc, hinc, M_eq_B64]
  exact Section413Cells.encodeZ_add a b

/-- `dst := -src`, two's complement: one modular subtract from zero.

`denoteOp .sub a b` is `(a + (M - b)) % M`, so with `a = 0` this is exactly
`(B64 - encodeZ z) % B64`, which `encodeZ_neg` identifies with `encodeZ (-z)`.
This is what `coeffInterval`'s first branch needs — the branch whose endpoints
are negated. -/
def negateBlock (dst src : Nat) : List AInstr :=
  [ .scalar (.binop dst .sub (.lit 0) (.reg src)) ]

theorem negateBlock_run (k : Nat) (s : AState) (dst src : Nat) (a : Int)
    (h : s.regs src = Section413Cells.encodeZ a) :
    (arun k s (negateBlock dst src)).regs dst =
      Section413Cells.encodeZ (-a) := by
  simp only [negateBlock, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl,
    Nat.mod_eq_of_lt (show (0 : Nat) < M by decide), Nat.zero_add]
  rw [h, M_eq_B64]
  exact Section413Cells.encodeZ_neg a

/-- `dst := 2 * src`, the model's `csmul 2` — `coeffInterval`'s second branch. -/
def doubleBlock (dst src : Nat) : List AInstr :=
  [ .scalar (.binop dst .mul (.lit 2) (.reg src)) ]

theorem doubleBlock_run (k : Nat) (s : AState) (dst src : Nat) (a : Int)
    (h : s.regs src = Section413Cells.encodeZ a) :
    (arun k s (doubleBlock dst src)).regs dst =
      Section413Cells.encodeZ (2 * a) := by
  simp only [doubleBlock, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl,
    Nat.mod_eq_of_lt (show (2 : Nat) < M by decide)]
  rw [h, M_eq_B64]
  exact Section413Cells.encodeZ_double a

/-! ### Branch-free select

`coeffInterval` is a three-way branch (`s.rest = 1` / `s.tail = 1` / else), and
the machine has no branches inside a rolled body.  The same select
`absDiffBlock` uses works here: multiply each candidate by a 0/1 flag and add,
so the unchosen term is multiplied away.  Two nested selects give the three-way
choice. -/

def rC : Nat := 290
def rX : Nat := 291
def rY : Nat := 292
def rSelT1 : Nat := 293
def rSelT2 : Nat := 294
def rSel : Nat := 295

/-- `rSel := if rC = 1 then rX else rY`, for `rC ∈ {0,1}`. -/
def selectBlock : List AInstr :=
  [ .scalar (.binop rSelT1 .mul (.reg rC) (.reg rX))
  , .scalar (.binop rSelT2 .sub (.lit 1) (.reg rC))
  , .scalar (.binop rSelT2 .mul (.reg rSelT2) (.reg rY))
  , .scalar (.binop rSel .add (.reg rSelT1) (.reg rSelT2)) ]

theorem selectBlock_run (k : Nat) (s : AState)
    (hc : s.regs rC = 0 ∨ s.regs rC = 1)
    (hx : s.regs rX < M) (hy : s.regs rY < M) :
    (arun k s selectBlock).regs rSel =
      (if s.regs rC = 1 then s.regs rX else s.regs rY) := by
  simp only [rC, rX, rY] at hc hx hy
  rcases hc with h0 | h1
  · simp [selectBlock, arun, astep, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rC, rX, rY, rSelT1, rSelT2, rSel, h0,
      Nat.mod_eq_of_lt hy,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp [selectBlock, arun, astep, denoteInstr,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rC, rX, rY, rSelT1, rSelT2, rSel, h1,
      Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hg : 1 + (M - 1) = M := by omega
    rw [hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-! ### Commit under an arbitrary guard

`guardedCommit`/`eqGuardedCommit` compute their condition from the candidate.
`qSubOK` and `shapeOK` are guarded by conditions on the SHAPE instead
(`s.rest = 1`, `s.q = s.rest`, ...), so the general primitive takes the guard
bit from a register and leaves computing it to the caller. -/

def rGuard : Nat := 296

/-- `rViol |||= rBad && rGuard`. -/
def commitWithGuard : List AInstr :=
  [ .scalar (.binop rBad .band (.reg rBad) (.reg rGuard))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

theorem commitWithGuard_run (k : Nat) (s : AState)
    (hb : s.regs rBad = 0 ∨ s.regs rBad = 1)
    (hg : s.regs rGuard = 0 ∨ s.regs rGuard = 1) :
    (arun k s commitWithGuard).regs rViol =
      (s.regs rViol |||
        (if s.regs rBad = 1 ∧ s.regs rGuard = 1 then 1 else 0)) % M := by
  have hM : M ≠ 1 := by decide
  simp only [rBad, rGuard] at hb hg
  rcases hb with hb | hb <;> rcases hg with hg | hg <;>
    simp [commitWithGuard, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rBad, rViol, rGuard, hb, hg, hM,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-! ### Row 6: `qSubOK`

    qSubOK c n s logL logU =
      if s.rest = 1 ∨ s.q ≠ s.rest then true
      else decide (s.pExp * lp.1 ≤ carriedLogUpper32 logU)

`s.pExp <= 27` for `n <= 1e8` and `lp.1 ~ 7.9e10`, so the product is ~2.1e12 and
fits a word with room — this is the one product in the sweep that does NOT need
shifting.  `carriedLogUpper32 x = ceil (x / 65536)` is the same `+65535` then
`>> 16` used elsewhere.  Inputs are staged, as everywhere in this file. -/

def rQsPExp : Nat := 297
def rQsLp : Nat := 298
def rQsLogU : Nat := 299
def rQsRest : Nat := 300
def rQsQ : Nat := 301

/-- `rGuard := (rest ≠ 1) && (q = rest)` — the negation of the model's
`s.rest = 1 ∨ s.q ≠ s.rest` early-out. -/
def qSubGuard : List AInstr :=
  [ .scalar (.binop rT4 .ne (.reg rQsRest) (.lit 1))
  , .scalar (.binop rT5 .eq (.reg rQsQ) (.reg rQsRest))
  , .scalar (.binop rGuard .band (.reg rT4) (.reg rT5)) ]

/-- `rBad := pExp * lp > ceil(logU / 65536)`. -/
def qSubCheck : List AInstr :=
  [ .scalar (.binop rA .mul (.reg rQsPExp) (.reg rQsLp))
  , .scalar (.binop rB .add (.reg rQsLogU) (.lit 65535))
  , .scalar (.binop rB .lshr (.reg rB) (.lit 16))
  , .scalar (.binop rBad .gt (.reg rA) (.reg rB)) ]

theorem qSubCheck_run (k : Nat) (s : AState)
    (hm : s.regs rQsPExp * s.regs rQsLp < M)
    (hl : s.regs rQsLogU + 65535 < M) :
    (arun k s qSubCheck).regs rBad =
      (if (s.regs rQsLogU + 65535) / 65536 < s.regs rQsPExp * s.regs rQsLp
       then 1 else 0) := by
  simp only [rQsPExp, rQsLp, rQsLogU] at hm hl
  have hdiv : (s.regs 299 + 65535) / 65536 < M := by
    have h := Nat.div_le_self (s.regs 299 + 65535) 65536
    omega
  simp [qSubCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rB, rBad, rQsPExp, rQsLp, rQsLogU, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hdiv,
    Nat.mod_eq_of_lt (show (65535 : Nat) < M by decide),
    Nat.mod_eq_of_lt (show (16 : Nat) < M by decide)]

theorem qSubGuard_run (k : Nat) (s : AState) :
    (arun k s qSubGuard).regs rGuard =
      (if s.regs rQsRest ≠ 1 ∧ s.regs rQsQ = s.regs rQsRest then 1 else 0) := by
  by_cases h1 : s.regs rQsRest = 1 <;> by_cases h2 : s.regs rQsQ = s.regs rQsRest <;>
    simp only [rQsRest, rQsQ] at h1 h2 <;>
    simp [qSubGuard, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, RegState.set,
      rT4, rT5, rGuard, rQsRest, rQsQ, h1, h2,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- **Row 6 end to end.**  A violation is recorded exactly when the model's
early-out does NOT fire and the inequality fails. -/
def qSubBlock : List AInstr := qSubGuard ++ qSubCheck ++ commitWithGuard

theorem qSubBlock_run (k : Nat) (s : AState)
    (hm : s.regs rQsPExp * s.regs rQsLp < M)
    (hl : s.regs rQsLogU + 65535 < M) :
    (arun k s qSubBlock).regs rViol =
      (s.regs rViol |||
        (if ((s.regs rQsLogU + 65535) / 65536 < s.regs rQsPExp * s.regs rQsLp)
            ∧ (s.regs rQsRest ≠ 1 ∧ s.regs rQsQ = s.regs rQsRest)
         then 1 else 0)) % M := by
  rw [qSubBlock, arun_append, arun_append]
  -- the guard survives `qSubCheck`, and the staged inputs survive `qSubGuard`
  have hg : (arun k (arun k s qSubGuard) qSubCheck).regs rGuard =
      (if s.regs rQsRest ≠ 1 ∧ s.regs rQsQ = s.regs rQsRest then 1 else 0) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      qSubGuard_run]
  have hpe : (arun k s qSubGuard).regs rQsPExp = s.regs rQsPExp :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hlp : (arun k s qSubGuard).regs rQsLp = s.regs rQsLp :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hlu : (arun k s qSubGuard).regs rQsLogU = s.regs rQsLogU :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hb : (arun k (arun k s qSubGuard) qSubCheck).regs rBad =
      (if (s.regs rQsLogU + 65535) / 65536 < s.regs rQsPExp * s.regs rQsLp
       then 1 else 0) := by
    rw [qSubCheck_run _ _ (by rw [hpe, hlp]; exact hm) (by rw [hlu]; exact hl),
      hpe, hlp, hlu]
  have hv : (arun k (arun k s qSubGuard) qSubCheck).regs rViol = s.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  rw [commitWithGuard_run _ _ (by rw [hb]; split <;> simp)
      (by rw [hg]; split <;> simp), hb, hg, hv]
  by_cases hA : (s.regs rQsLogU + 65535) / 65536 < s.regs rQsPExp * s.regs rQsLp <;>
    by_cases hB : s.regs rQsRest ≠ 1 ∧ s.regs rQsQ = s.regs rQsRest <;>
    simp [hA, hB]

/-! ### Row 8: the verdict is a bit

The model's `bad := st.bad || !ok` is what `rViol` already accumulates: every
commit ORs in a 0/1 comparison result.  What row 8 needs is the invariant that
makes `rViol` a verdict rather than an arbitrary word — it stays in `{0,1}`,
so seeding it to `0` in `init` and reading it out in `epilogue` gives exactly
`value c = if (run c).bad then 1 else 0`. -/

theorem or_bit {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a ||| b) % M = 0 ∨ (a ||| b) % M = 1 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;>
    simp [h, h', Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

theorem ite_bit (P : Prop) [Decidable P] :
    (if P then 1 else 0) = 0 ∨ (if P then 1 else 0) = 1 := by
  split <;> simp

/-- Every commit preserves the invariant. -/
theorem commitWithGuard_bit (k : Nat) (s : AState)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1)
    (hb : s.regs rBad = 0 ∨ s.regs rBad = 1)
    (hg : s.regs rGuard = 0 ∨ s.regs rGuard = 1) :
    (arun k s commitWithGuard).regs rViol = 0 ∨
      (arun k s commitWithGuard).regs rViol = 1 := by
  rw [commitWithGuard_run _ _ hb hg]
  exact or_bit hv (ite_bit _)

theorem thresholdBlock_bit (k : Nat) (s : AState) (bound : Nat) (hb : bound < M)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s (thresholdBlock bound)).regs rViol = 0 ∨
      (arun k s (thresholdBlock bound)).regs rViol = 1 := by
  rw [thresholdBlock_run _ _ _ hb]
  exact or_bit hv (ite_bit _)

theorem qSubBlock_bit (k : Nat) (s : AState)
    (hm : s.regs rQsPExp * s.regs rQsLp < M)
    (hl : s.regs rQsLogU + 65535 < M)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s qSubBlock).regs rViol = 0 ∨
      (arun k s qSubBlock).regs rViol = 1 := by
  rw [qSubBlock_run _ _ hm hl]
  exact or_bit hv (ite_bit _)

theorem ite_bit' (P : Prop) [Decidable P] :
    (if P then 0 else 1) = 0 ∨ (if P then 0 else 1) = 1 := by
  split <;> simp

theorem guardedThreshold_bit (k : Nat) (s : AState) (bound lower : Nat)
    (hb : bound < M) (hl : lower < M)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s (thresholdBit bound ++ guardedCommit lower)).regs rViol = 0 ∨
      (arun k s (thresholdBit bound ++ guardedCommit lower)).regs rViol = 1 := by
  rw [guardedThreshold_run _ _ _ _ hb hl]
  exact or_bit hv (ite_bit _)

theorem eqGuardedThreshold_bit (k : Nat) (s : AState) (bound at_ : Nat)
    (hb : bound < M) (ha : at_ < M)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s (thresholdBit bound ++ eqGuardedCommit at_)).regs rViol = 0 ∨
      (arun k s (thresholdBit bound ++ eqGuardedCommit at_)).regs rViol = 1 := by
  rw [eqGuardedThreshold_run _ _ _ _ hb ha]
  exact or_bit hv (ite_bit _)

theorem seamPsiBlock_bit (k : Nat) (s : AState)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s seamPsiBlock).regs rViol = 0 ∨
      (arun k s seamPsiBlock).regs rViol = 1 := by
  rw [seamPsiBlock_run]
  exact or_bit hv (ite_bit' _)

theorem anchorBlock_bit (k : Nat) (s : AState) (gammaLo gammaHi bound : Nat)
    (hA1 : s.regs rIL + gammaLo < M) (hB1 : s.regs rGU < M)
    (hA2 : s.regs rIU + gammaHi < M) (hB2 : s.regs rGL < M)
    (hb : bound < M) (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s (anchorBlock gammaLo gammaHi bound)).regs rViol = 0 ∨
      (arun k s (anchorBlock gammaLo gammaHi bound)).regs rViol = 1 := by
  rw [anchorBlock_run _ _ _ _ _ hA1 hB1 hA2 hB2 hb]
  exact or_bit hv (ite_bit _)

/-! ### Row 5: the bounded power

`shapeOK` checks `s.p ^ s.pExp * s.rest = n`, and `Shape` carries no power
field, so `p ^ pExp` has to be emitted.  It is the only construct in the sweep
that needs unrolling — but it is cheaply bounded: `p >= 2` and `p ^ pExp <= n
<= 1e8`, so `pExp <= 26`, and 27 steps suffice for every candidate.

Each step multiplies by `p` or by `1`, branch-free, via the multiplier
`m = 1 + sel * (p - 1)`: `m = p` when the step is live and `m = 1` when it is
not, so no select on the accumulator is needed and the dead steps are exact
no-ops. -/

def rPowAcc : Nat := 302
def rPowP : Nat := 303
def rPowE : Nat := 304

/-- One unrolled step: `acc := acc * (if i < e then p else 1)`.

⚠ Built with `.lt` and `.ge` rather than `1 - sel`, so the block contains **no
subtraction at all**.  That is not cosmetic: `denoteOp .sub a b` is
`(a + (M - b)) % M`, and reducing `M - b` forces the kernel to evaluate
`M = 2^64`, which deep-recurses.  The complement of a comparison is just the
opposite comparison, and it costs the same one instruction. -/
def powStep (i : Nat) : List AInstr :=
  [ .scalar (.binop rT4 .lt (.lit i) (.reg rPowE))
  , .scalar (.binop rT5 .ge (.lit i) (.reg rPowE))
  , .scalar (.binop rT4 .mul (.reg rT4) (.reg rPowP))
  , .scalar (.binop rT4 .add (.reg rT4) (.reg rT5))
  , .scalar (.binop rPowAcc .mul (.reg rPowAcc) (.reg rT4)) ]

theorem powStep_run_live (k : Nat) (s : AState) (i : Nat)
    (h : i < s.regs rPowE)
    (hi : i < M) (hp1 : 1 ≤ s.regs rPowP) (hp : s.regs rPowP < M)
    (hacc : s.regs rPowAcc * s.regs rPowP < M) :
    (arun k s (powStep i)).regs rPowAcc =
      s.regs rPowAcc * s.regs rPowP := by
  have hM1 : (1 : Nat) < M := by omega
  simp only [rPowP, rPowE, rPowAcc] at h hi hp1 hp hacc
  have h' : ¬ (s.regs 304 ≤ i) := Nat.not_le.mpr h
  simp [powStep, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rT4, rT5, rPowAcc, rPowP, rPowE, h, h',
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt hM1, Nat.mod_eq_of_lt hacc]

theorem powStep_run_dead (k : Nat) (s : AState) (i : Nat)
    (h : ¬ (i < s.regs rPowE))
    (hi : i < M) (hp1 : 1 ≤ s.regs rPowP) (hp : s.regs rPowP < M)
    (haccM : s.regs rPowAcc < M) :
    (arun k s (powStep i)).regs rPowAcc = s.regs rPowAcc := by
  have hM1 : (1 : Nat) < M := by omega
  simp only [rPowP, rPowE, rPowAcc] at h hi hp1 hp haccM
  have h' : s.regs 304 ≤ i := Nat.le_of_not_lt h
  simp [powStep, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rT4, rT5, rPowAcc, rPowP, rPowE, h, h',
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt haccM,
    Nat.mod_eq_of_lt hM1]

/-- `n` unrolled steps.  At `n = 27` this covers every candidate, since
`pExp <= 26`. -/
def powChain (n : Nat) : List AInstr := (List.range n).flatMap powStep

theorem powChain_succ (m : Nat) : powChain (m + 1) = powChain m ++ powStep m := by
  simp [powChain, List.range_succ, List.flatMap_append]

/-- The chain never writes `rPowP` — needed as a frame, and `decide` cannot do
it with `m` free. -/
theorem powChain_writes_P (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rPowP (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

theorem powChain_writes_E (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rPowE (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

theorem powChain_writes_X (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rX (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

theorem powChain_writes_B (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rB (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

theorem powChain_writes_Viol (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rViol (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

/-- After `n` steps the accumulator has been multiplied by `p` exactly
`min n e` times — the dead steps multiply by `1`, so no early exit is needed
and the unroll is uniform. -/
theorem powChain_run (k : Nat) (s : AState) (n : Nat)
    (hn : n < M) (hp1 : 1 ≤ s.regs rPowP) (hp : s.regs rPowP < M)
    (hbig : s.regs rPowAcc * s.regs rPowP ^ n < M) :
    (arun k s (powChain n)).regs rPowAcc =
      s.regs rPowAcc * s.regs rPowP ^ (min n (s.regs rPowE)) := by
  induction n with
  | zero => simp [powChain, arun]
  | succ m ih =>
      have hmM : m < M := by omega
      have hpow_mono : s.regs rPowP ^ m ≤ s.regs rPowP ^ (m + 1) :=
        Nat.pow_le_pow_right hp1 (Nat.le_succ m)
      have hbig_m : s.regs rPowAcc * s.regs rPowP ^ m < M := by
        have := Nat.mul_le_mul_left (s.regs rPowAcc) hpow_mono
        omega
      have hstep := ih hmM hbig_m
      have hP : (arun k s (powChain m)).regs rPowP = s.regs rPowP :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_P m) _
      have hE : (arun k s (powChain m)).regs rPowE = s.regs rPowE :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_E m) _
      rw [powChain_succ, arun_append]
      by_cases hlt : m < s.regs rPowE
      · rw [powStep_run_live _ _ _ (by rw [hE]; exact hlt) hmM
            (by rw [hP]; exact hp1) (by rw [hP]; exact hp)
            (by rw [hstep, hP]
                have hmin : min m (s.regs rPowE) = m := Nat.min_eq_left (by omega)
                rw [hmin, Nat.mul_assoc, ← Nat.pow_succ]
                exact hbig),
          hstep, hP]
        have hmin : min m (s.regs rPowE) = m := Nat.min_eq_left (by omega)
        have hmin' : min (m + 1) (s.regs rPowE) = m + 1 :=
          Nat.min_eq_left (by omega)
        rw [hmin, hmin', Nat.mul_assoc, ← Nat.pow_succ]
      · rw [powStep_run_dead _ _ _ (by rw [hE]; exact hlt) hmM
            (by rw [hP]; exact hp1) (by rw [hP]; exact hp)
            (by rw [hstep]
                have hmono : s.regs rPowP ^ (min m (s.regs rPowE))
                    ≤ s.regs rPowP ^ m :=
                  Nat.pow_le_pow_right hp1 (Nat.min_le_left _ _)
                have := Nat.mul_le_mul_left (s.regs rPowAcc) hmono
                omega),
          hstep]
        have hle : s.regs rPowE ≤ m := Nat.le_of_not_lt hlt
        have hmin : min m (s.regs rPowE) = s.regs rPowE := Nat.min_eq_right hle
        have hmin' : min (m + 1) (s.regs rPowE) = s.regs rPowE :=
          Nat.min_eq_right (by omega)
        rw [hmin, hmin']

/-- **Row 5's power, at production width.**  `p >= 2` and `p ^ pExp <= n <= 1e8`
force `pExp <= 26`, so 27 unrolled steps compute `p ^ pExp` exactly for every
candidate — with no loop, no early exit, and no data-dependent control flow. -/
theorem powChain_27 (k : Nat) (s : AState)
    (he : s.regs rPowE ≤ 26) (hp1 : 1 ≤ s.regs rPowP) (hp : s.regs rPowP < M)
    (hbig : s.regs rPowAcc * s.regs rPowP ^ 27 < M) :
    (arun k s (powChain 27)).regs rPowAcc =
      s.regs rPowAcc * s.regs rPowP ^ (s.regs rPowE) := by
  have h := powChain_run k s 27 (show (27 : Nat) < M by decide) hp1 hp hbig
  rwa [Nat.min_eq_right (by omega : s.regs rPowE ≤ 27)] at h

/-! ### Row 5's divisibility test, without division

`shapeOK` needs `¬ p ∣ rest`.  Emitting `rest % p` is not an option — see the
`NoDivI` note above — so the classifier supplies `q = rest / p` and
`r = rest % p`, which it has from the strip loop, and the block verifies the
witness.  `0 < r` is then exactly non-divisibility, and nothing is divided. -/

/-- **A verified quotient/remainder witness gives non-divisibility.** -/
theorem not_dvd_of_witness {p q r rest : Nat} (h : q * p + r = rest)
    (h0 : 0 < r) (hp : r < p) : ¬ p ∣ rest := by
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hpc : p * c = q * p + r := by omega
  have hqp : q * p = p * q := Nat.mul_comm q p
  have h1 : p * c < p * (q + 1) := by
    calc p * c = q * p + r := hpc
      _ < q * p + p := by omega
      _ = p * (q + 1) := by rw [hqp, Nat.mul_succ]
  have h2 : p * q ≤ p * c := by rw [hpc, ← hqp]; omega
  have hpp : 0 < p := by omega
  have hcq : c < q + 1 := Nat.lt_of_mul_lt_mul_left h1
  have hqc : q ≤ c := Nat.le_of_mul_le_mul_left h2 hpp
  have hceq : c = q := by omega
  subst hceq
  rw [← hqp] at hpc
  omega

theorem ite01_lor_one (P : Prop) [Decidable P] :
    ((if P then 0 else 1) ||| 1) = 1 := by
  split <;> simp

theorem one_lor_ite01 (P : Prop) [Decidable P] :
    (1 ||| (if P then 1 else 0)) = 1 := by
  split <;> simp

/-- **Bit-level OR of three condition flags.**

Multi-condition checks accumulate `(a ||| b) % M ||| c`, and proving them by an
eight-way `simp` split on the conditions leaves `|||` goals that `omega` cannot
touch.  Reducing at the BIT level instead — the flags are `0`/`1` by
construction — turns every such check into one rewrite. -/
theorem or3_bits {a b c : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) :
    ((a ||| b) % M ||| c) % M = (if a = 0 ∧ b = 0 ∧ c = 0 then 0 else 1) := by
  have h0 : (0 : Nat) < M := by decide
  have h1 : (1 : Nat) < M := by decide
  rcases ha with h | h <;> rcases hb with h' | h' <;> rcases hc with h'' | h'' <;>
    simp [h, h', h'', Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1]

/-- Two-flag version, for the guarded commits. -/
theorem or2_bits {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a ||| b) % M = (if a = 0 ∧ b = 0 then 0 else 1) := by
  have h0 : (0 : Nat) < M := by decide
  have h1 : (1 : Nat) < M := by decide
  rcases ha with h | h <;> rcases hb with h' | h' <;>
    simp [h, h', Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1]

/-- Supplied remainder `r = rest % p`. -/
def rShR : Nat := 305

/-- Verify the supplied witness: `q*p + r = rest`, `r ≠ 0`, `r < p`.  Seven
instructions, **no division**, and fail-closed — a bad witness sets `rBad`, so
the classifier cannot buy a pass by supplying nonsense.  With
`not_dvd_of_witness`, passing this block IS `¬ p ∣ rest`. -/
def divWitnessCheck : List AInstr :=
  [ .scalar (.binop rA .mul (.reg rY) (.reg rPowP))
  , .scalar (.binop rA .add (.reg rA) (.reg rShR))
  , .scalar (.binop rT4 .ne (.reg rA) (.reg rX))
  , .scalar (.binop rT5 .eq (.reg rShR) (.lit 0))
  , .scalar (.binop rT4 .bor (.reg rT4) (.reg rT5))
  , .scalar (.binop rT5 .ge (.reg rShR) (.reg rPowP))
  , .scalar (.binop rBad .bor (.reg rT4) (.reg rT5)) ]

theorem divWitnessCheck_run (k : Nat) (s : AState)
    (hm : s.regs rY * s.regs rPowP < M)
    (hs : s.regs rY * s.regs rPowP + s.regs rShR < M)
    (hx : s.regs rX < M) :
    (arun k s divWitnessCheck).regs rBad =
      (if s.regs rY * s.regs rPowP + s.regs rShR = s.regs rX
          ∧ s.regs rShR ≠ 0 ∧ s.regs rShR < s.regs rPowP
       then 0 else 1) := by
  simp only [rY, rPowP, rShR, rX] at hm hs hx
  simp [divWitnessCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    rA, rY, rPowP, rShR, rX, rT4, rT5, rBad,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  rw [or3_bits (ite_bit' _) (ite_bit _) (ite_bit _)]
  by_cases hA : s.regs 292 * s.regs 303 + s.regs 305 = s.regs 291 <;>
    by_cases hB : s.regs 305 = 0 <;>
      by_cases hC : s.regs 303 ≤ s.regs 305 <;>
        simp [hA, hB, hC] <;> omega

/-- `shapeOK`'s factorisation check, **generic in its target**.

`0 < e` and `base_pow * cofactor = target`, reading `base_pow` from `rPowAcc`
(supplied by `powChain_27`), the cofactor from `rX`, and the target from `rB`.

Staging the target rather than hard-wiring `sCand` is what lets ONE block serve
both of `shapeOK`'s conjuncts: the first stages `rB := n`, `rX := rest`; the
second stages `rB := rest`, `rX := tail` and re-seeds the power registers for
`(q, qExp)`.  The two conjuncts differ only in staging. -/
def shapeEqCheck : List AInstr :=
  [ .scalar (.binop rA .mul (.reg rPowAcc) (.reg rX))
  , .scalar (.binop rT4 .ne (.reg rA) (.reg rB))
  , .scalar (.binop rT5 .eq (.reg rPowE) (.lit 0))
  , .scalar (.binop rBad .bor (.reg rT4) (.reg rT5)) ]

theorem shapeEqCheck_run (k : Nat) (s : AState)
    (hm : s.regs rPowAcc * s.regs rX < M) (hn : s.regs rB < M) :
    (arun k s shapeEqCheck).regs rBad =
      (if s.regs rPowAcc * s.regs rX = s.regs rB ∧ s.regs rPowE ≠ 0
       then 0 else 1) := by
  simp only [rPowAcc, rX, rB, rPowE] at hm hn
  simp [shapeEqCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rA, rPowAcc, rX, rB, rPowE, rT4, rT5, rBad,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  rw [or2_bits (ite_bit' _) (ite_bit _)]
  by_cases hA : s.regs 302 * s.regs 291 = s.regs 264 <;>
    by_cases hB : s.regs 304 = 0 <;>
      simp [hA, hB]

/-- `shapeOK`'s `s.rest = 1` alternative: `q = 0 ∧ qExp = 0 ∧ tail = 1`.

The other side of that branch needs no new block — `powChain_27`,
`shapeEqCheck` and `divWitnessCheck` all serve it by staging
`(q, qExp, tail)` where `(p, pExp, rest)` went, with `rB := rest` as the
target.  A `selectBlock` on `rest = 1` picks between the two. -/
def shapeTrivialCheck : List AInstr :=
  [ .scalar (.binop rT4 .ne (.reg rY) (.lit 0))
  , .scalar (.binop rT5 .ne (.reg rPowE) (.lit 0))
  , .scalar (.binop rT4 .bor (.reg rT4) (.reg rT5))
  , .scalar (.binop rT5 .ne (.reg rX) (.lit 1))
  , .scalar (.binop rBad .bor (.reg rT4) (.reg rT5)) ]

theorem shapeTrivialCheck_run (k : Nat) (s : AState) :
    (arun k s shapeTrivialCheck).regs rBad =
      (if s.regs rY = 0 ∧ s.regs rPowE = 0 ∧ s.regs rX = 1 then 0 else 1) := by
  simp [shapeTrivialCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rY, rPowE, rX, rT4, rT5, rBad,
    Nat.mod_eq_of_lt (show (0 : Nat) < M by decide),
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  rw [or3_bits (ite_bit' _) (ite_bit' _) (ite_bit' _)]
  by_cases h1 : s.regs 292 = 0 <;> by_cases h2 : s.regs 304 = 0 <;>
    by_cases h3 : s.regs 291 = 1 <;> simp [h1, h2, h3]

/-! ### Row 7: `rowOK`, in strengthened form

`rowOK_of_strengthened` (claude_math, `Combined100MHeadroom`) divides `n` out of
both sides:

    10000 * (W + q + 1) <= num * 4345 * coeffScale
      ⟹ 10000 * (n*W + (q*n + rem)) <= num * 4345 * n * coeffScale

so the emitted check is a two-register sum against a **compile-time constant**
— `num` is a literal at each of `rowAt`'s four sites, and `mul_le_iff_le_div`
folds the `10000` into the bound.  No multiplication by `n`, nothing that can
wrap, three instructions.

Inputs are staged into existing scratch (`rX := weightedAbs`, `rY := q`), so
this adds **no registers** — the file is at 259 of `regCount = 260`. -/
def rowCheck (bound : Nat) : List AInstr :=
  [ .scalar (.binop rA .add (.reg rX) (.reg rY))
  , .scalar (.binop rA .add (.reg rA) (.lit 1))
  , .scalar (.binop rBad .gt (.reg rA) (.lit bound)) ]

theorem rowCheck_run (k : Nat) (s : AState) (bound : Nat)
    (hsum : s.regs rX + s.regs rY + 1 < M) (hb : bound < M) :
    (arun k s (rowCheck bound)).regs rBad =
      (if bound < s.regs rX + s.regs rY + 1 then 1 else 0) := by
  have h2 : s.regs rX + s.regs rY < M := by omega
  simp only [rX, rY] at hsum h2
  simp [rowCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rA, rX, rY, rBad,
    Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- `eqGuardedCommit` on a state where `rBad` is ALREADY set — the form row 7
needs, since `rowCheck` writes `rBad` directly rather than through `rMx`. -/
theorem eqGuardedCommit_run (k : Nat) (s : AState) (at_ : Nat)
    (hb : s.regs rBad = 0 ∨ s.regs rBad = 1) (ha : at_ < M) :
    (arun k s (eqGuardedCommit at_)).regs rViol =
      (s.regs rViol |||
        (if s.regs sCand = at_ ∧ s.regs rBad = 1 then 1 else 0)) % M := by
  have hM : M ≠ 1 := by decide
  simp only [rBad, sCand] at hb
  by_cases hg : s.regs 132 = at_ <;> rcases hb with hb | hb <;>
    simp [eqGuardedCommit, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rBad, rViol, rT5, sCand, hg, hb, hM,
      Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- **One of `rowAt`'s four sites, end to end.**  Fires only at `n = at_`, and
records a violation exactly when the strengthened bound fails there. -/
def rowSiteBlock (at_ bound : Nat) : List AInstr :=
  rowCheck bound ++ eqGuardedCommit at_

theorem rowSiteBlock_run (k : Nat) (s : AState) (at_ bound : Nat)
    (hsum : s.regs rX + s.regs rY + 1 < M) (hb : bound < M) (ha : at_ < M) :
    (arun k s (rowSiteBlock at_ bound)).regs rViol =
      (s.regs rViol |||
        (if s.regs sCand = at_ ∧ bound < s.regs rX + s.regs rY + 1
         then 1 else 0)) % M := by
  rw [rowSiteBlock, arun_append]
  have hbad : (arun k s (rowCheck bound)).regs rBad =
      (if bound < s.regs rX + s.regs rY + 1 then 1 else 0) :=
    rowCheck_run k s bound hsum hb
  have hcand : (arun k s (rowCheck bound)).regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hviol : (arun k s (rowCheck bound)).regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  rw [eqGuardedCommit_run _ _ _ (by rw [hbad]; exact ite_bit _) ha,
    hbad, hcand, hviol]
  by_cases h1 : s.regs sCand = at_ <;>
    by_cases h2 : bound < s.regs rX + s.regs rY + 1 <;> simp [h1, h2]

/-- Encoding a nonnegative in-range value is the identity. -/
theorem encodeZ_ofNat {n : Nat} (h : n < LeanCompCert.Verified.MulWide.B64) :
    Section413Cells.encodeZ (n : Int) = n := by
  unfold Section413Cells.encodeZ
  simp only [LeanCompCert.Verified.MulWide.B64] at h ⊢
  omega

/-! ### Exact endpoint product composites

These are the production replacements for the historical shifted-factor
approximations below.  Their hypotheses are ordinary word/headroom facts; the
instruction semantics itself is exactly `mulLower`/`mulUpper`. -/

def negExactCeilProduct : List AInstr :=
  exactCeilProduct ++ negateBlock rProd rProd

theorem negExactCeilProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rA) (s.regs rB) < M) :
    (arun k s negExactCeilProduct).regs rProd =
      Section413Cells.encodeZ (-((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int)) := by
  rw [negExactCeilProduct, arun_append]
  apply negateBlock_run
  rw [exactCeilProduct_run k s hw hfit hout]
  exact (encodeZ_ofNat (M_eq_B64 ▸ hout)).symm

def doubleExactFloorProduct : List AInstr :=
  exactFloorProduct ++ doubleBlock rProd rProd

theorem doubleExactFloorProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rA) (s.regs rB) < M) :
    (arun k s doubleExactFloorProduct).regs rProd =
      Section413Cells.encodeZ (2 * ((mulLower (s.regs rA) (s.regs rB) : Nat) : Int)) := by
  rw [doubleExactFloorProduct, arun_append]
  apply doubleBlock_run
  rw [exactFloorProduct_run k s hw hfit]
  exact (encodeZ_ofNat (M_eq_B64 ▸ hout)).symm

def negExactFloorProduct : List AInstr :=
  exactFloorProduct ++ negateBlock rProd rProd

theorem negExactFloorProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rA) (s.regs rB) < M) :
    (arun k s negExactFloorProduct).regs rProd =
      Section413Cells.encodeZ (-((mulLower (s.regs rA) (s.regs rB) : Nat) : Int)) := by
  rw [negExactFloorProduct, arun_append]
  apply negateBlock_run
  rw [exactFloorProduct_run k s hw hfit]
  exact (encodeZ_ofNat (M_eq_B64 ▸ hout)).symm

def doubleExactCeilProduct : List AInstr :=
  exactCeilProduct ++ doubleBlock rProd rProd

theorem doubleExactCeilProduct_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl (s.regs rA) (s.regs rB)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rA) (s.regs rB) < M) :
    (arun k s doubleExactCeilProduct).regs rProd =
      Section413Cells.encodeZ (2 * ((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int)) := by
  rw [doubleExactCeilProduct, arun_append]
  apply doubleBlock_run
  rw [exactCeilProduct_run k s hw hfit hout]
  exact (encodeZ_ofNat (M_eq_B64 ▸ hout)).symm

theorem exactEndpointProducts_wf :
    negExactCeilProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true ∧
    doubleExactFloorProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true ∧
    negExactFloorProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true ∧
    doubleExactCeilProduct.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rcases exactProduct_wf with ⟨hf, hc⟩
  simp [negExactCeilProduct, doubleExactFloorProduct, negExactFloorProduct,
    doubleExactCeilProduct, hf, hc, negateBlock, doubleBlock, rProd]
  decide

/-! ### `coeffInterval` branch A: the negated product

`coeffInterval`'s first branch is `(-(mulUpper lp.2 lp.2), -(mulLower lp.1 lp.1))`.
For the LOWER endpoint that means negating an **upper** product, and the
rounding direction has to survive the negation:

    emitted  = ceilShifted >= mulUpper        (ceilShiftedProduct_ge_mulUpper)
    negated  = -emitted    <= -mulUpper       = the model's lower endpoint

so the emitted interval still contains the model's.  Rounding the magnitude UP
is what makes the negated endpoint go DOWN — using `floorShiftedProduct` here
would silently narrow the interval and could turn a failing round into a pass. -/
def negCeilProduct : List AInstr :=
  ceilShiftedProduct ++ negateBlock rProd rProd

theorem negCeilProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA + 65535 < M) (hB : s.regs rB + 65535 < M)
    (hp : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) < M) :
    (arun k s negCeilProduct).regs rProd =
      Section413Cells.encodeZ
        (-(((s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) : Nat) : Int)) := by
  rw [negCeilProduct, arun_append]
  have hprod := ceilShiftedProduct_run k s hA hB hp
  refine negateBlock_run _ _ _ _ _ ?_
  rw [hprod]
  have hpB : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536)
      < LeanCompCert.Verified.MulWide.B64 := M_eq_B64 ▸ hp
  exact (encodeZ_ofNat hpB).symm

/-- And the bracketing survives: the negated emitted endpoint is at most the
model's, so the emitted interval contains it. -/
theorem negCeilProduct_le_neg_mulUpper (s : AState) :
    -((( (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) : Nat)) : Int)
      ≤ -((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int) := by
  have h := mulUpper_le_ceilShifted (s.regs rA) (s.regs rB)
  omega

/-! ### `coeffInterval` branch B: the doubled product

Branch B's lower endpoint is `2 * mulLower lp.1 lq.1` — **not** negated, so by
the rule above it takes the FLOOR product, which under-approximates:

    emitted = floorShifted <= mulLower  ⟹  2 * emitted <= 2 * mulLower

Same widening direction as branch A, reached the opposite way. -/
def doubleFloorProduct : List AInstr :=
  floorShiftedProduct ++ doubleBlock rProd rProd

theorem doubleFloorProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M)
    (hp : s.regs rA / 65536 * (s.regs rB / 65536) < M) :
    (arun k s doubleFloorProduct).regs rProd =
      Section413Cells.encodeZ
        (2 * ((s.regs rA / 65536 * (s.regs rB / 65536) : Nat) : Int)) := by
  rw [doubleFloorProduct, arun_append]
  have hprod := floorShiftedProduct_run k s hA hB hp
  refine doubleBlock_run _ _ _ _ _ ?_
  rw [hprod]
  have hpB : s.regs rA / 65536 * (s.regs rB / 65536)
      < LeanCompCert.Verified.MulWide.B64 := M_eq_B64 ▸ hp
  exact (encodeZ_ofNat hpB).symm

/-- The bracketing survives the doubling. -/
theorem doubleFloorProduct_le_double_mulLower (s : AState) :
    2 * ((s.regs rA / 65536 * (s.regs rB / 65536) : Nat) : Int)
      ≤ 2 * ((mulLower (s.regs rA) (s.regs rB) : Nat) : Int) := by
  have h := floorShifted_le_mulLower (s.regs rA) (s.regs rB)
  omega

/-- `dst := src + c` on an ENCODED operand, `c` a nonnegative literal.

This is `coeffInterval`'s final step — `+ 2 * gammaLower32` on the lower
endpoint, `+ 2 * gammaUpper32` on the upper.  One instruction: the machine's
modular add is two's-complement addition (`encodeZ_add`), and a nonnegative
in-range literal encodes to itself (`encodeZ_ofNat`), so no sign handling is
emitted even though `src` may be negative. -/
def addConstBlock (dst src c : Nat) : List AInstr :=
  [ .scalar (.binop dst .add (.reg src) (.lit c)) ]

theorem addConstBlock_run (k : Nat) (s : AState) (dst src c : Nat) (a : Int)
    (h : s.regs src = Section413Cells.encodeZ a)
    (hc : c < LeanCompCert.Verified.MulWide.B64) :
    (arun k s (addConstBlock dst src c)).regs dst =
      Section413Cells.encodeZ (a + (c : Int)) := by
  have hcM : c < M := M_eq_B64 ▸ hc
  have hce : Section413Cells.encodeZ ((c : Nat) : Int) = c := encodeZ_ofNat hc
  simp only [addConstBlock, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl, if_true, Option.getD_some,
    h, Nat.mod_eq_of_lt hcM, M_eq_B64, Nat.mod_eq_of_lt hc]
  rw [show Section413Cells.encodeZ a + c
        = Section413Cells.encodeZ a + Section413Cells.encodeZ ((c : Nat) : Int)
      from by rw [hce]]
  exact Section413Cells.encodeZ_add a (c : Int)

/-! ### Move primitives for the endpoint wiring

Assembling `coeffInterval` needs the two branch values held simultaneously so
`selectBlock` can choose between them.  `selectBlock` reads its candidates from
`rX` and `rY`, so the wiring is: compute branch B into `rProd`, move it to
`rX`, select against `0` on `tail = 1`; move that partial result to `rY`,
compute branch A into `rProd`, move it to `rX`, select on `rest = 1`.

Computing a branch touches `rA`, `rB`, `rSh1`, `rSh2`, `rProd` — never `rX`,
`rY`, `rC` or `rSel` — so the partial result survives, and **no register beyond
the existing scratch is needed**.  That matters: the file is at 259 of 260. -/

def movReg (dst src : Nat) : List AInstr := [ .scalar (.mov dst (.reg src)) ]

def movLit (dst c : Nat) : List AInstr := [ .scalar (.mov dst (.lit c)) ]

/-- The host's recovered pre-increment logs (`LambdaPsiBase.rOldL/rOldU`),
written once per body in `selectionBody` as `lRLogL - gate * lRIL` and read by
nothing else, so they are still live when these checks run. -/
def sOldL : Nat := 208
def sOldU : Nat := 209

/-- `pLog32`'s two components, recomputed UNGATED for branch A. -/
def rPLo : Nat := 325
def rPHi : Nat := 326
/- V3-derived q-log words, explicitly converted from the physical table's
2^48 scale to the endpoint model's 2^32 scale. -/
def rQLo : Nat := 332
def rQHi : Nat := 333

/-- Row 7's own registers: this candidate's two interval endpoints, captured
before they are accumulated away, and the per-candidate weighted magnitude. -/
def rIlo : Nat := 321
def rIhi : Nat := 322
def rWmag : Nat := 323
def rWq : Nat := 324


/-- `dst := src >> j`, the in-program rescaling from a 48-bit table cell to the
32-bit endpoint the model's `pLog32` uses. -/
def shrReg (dst src j : Nat) : List AInstr :=
  [ .scalar (.binop dst .lshr (.reg src) (.lit j)) ]

theorem shrReg_run (k : Nat) (s : AState) (dst src j : Nat)
    (hj : j < M) (hs : s.regs src < M) :
    (arun k s (shrReg dst src j)).regs dst = s.regs src / 2 ^ j := by
  have hle : s.regs src / 2 ^ j < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs
  simp [shrReg, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hle]

/-- Upward conversion of a physical `2^48` log word to the model's `2^32`
scale. -/
def ceilShift16Reg (dst src : Nat) : List AInstr :=
  [ .scalar (.binop dst .add (.reg src) (.lit 65535))
  , .scalar (.binop dst .lshr (.reg dst) (.lit 16)) ]

theorem ceilShift16Reg_run (k : Nat) (s : AState) (dst src : Nat)
    (hadd : s.regs src + 65535 < M) :
    (arun k s (ceilShift16Reg dst src)).regs dst =
      (s.regs src + 65535) / 65536 := by
  have h16 : 16 % M = 16 := by decide
  have hpow : 2 ^ (16 : Nat) = 65536 := by decide
  have hdiv : (s.regs src + 65535) / 65536 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hadd
  simp [ceilShift16Reg, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hadd,
    Nat.mod_eq_of_lt hdiv, h16, hpow]

theorem movReg_run (k : Nat) (s : AState) (dst src : Nat) :
    (arun k s (movReg dst src)).regs dst = s.regs src := by
  simp [movReg, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, AState.writeReg, RegState.set]

theorem movLit_run (k : Nat) (s : AState) (dst c : Nat) (hc : c < M) :
    (arun k s (movLit dst c)).regs dst = c := by
  simp [movLit, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, AState.writeReg, RegState.set, Nat.mod_eq_of_lt hc]

/-- Select and fold the result back into `rY`, so a second select can choose
against it.  Two applications give `coeffInterval`'s three-way branch:

    rY := 0                       -- branch C
    rX := branch B, rC := tail=1  →  rY := if tail=1 then B else 0
    rX := branch A, rC := rest=1  →  rY := if rest=1 then A else that

which is exactly the model's `if rest = 1 then _ else if tail = 1 then _ else 0`. -/
def selectIntoY : List AInstr := selectBlock ++ movReg rY rSel

theorem selectIntoY_run (k : Nat) (s : AState)
    (hc : s.regs rC = 0 ∨ s.regs rC = 1)
    (hx : s.regs rX < M) (hy : s.regs rY < M) :
    (arun k s selectIntoY).regs rY =
      (if s.regs rC = 1 then s.regs rX else s.regs rY) := by
  rw [selectIntoY, arun_append, movReg_run]
  exact selectBlock_run k s hc hx hy

/-! ### The classifier's outputs, and row 5's staging

`ShapeSieveMark` leaves the classified shape in registers 100-105 — well below
206, so they are sources this file only reads, like `rQ`/`rR`/`sCand`, and the
allocation guard deliberately excludes them. -/

/-- `ShapeSieveMark.rShapeP`. -/
def sShapeP : Nat := 100
/-- `ShapeSieveMark.rShapePE`. -/
def sShapePE : Nat := 101
/-- `ShapeSieveMark.rShapeRest`. -/
def sShapeRest : Nat := 102
/-- `ShapeSieveMark.rShapeQ`. -/
def sShapeQ : Nat := 103
/-- `ShapeSieveMark.rShapeQE`. -/
def sShapeQE : Nat := 104
/-- `ShapeSieveMark.rShapeTail`. -/
def sShapeTail : Nat := 105

/-- Stage `shapeOK`'s FIRST conjunct: base `p`, exponent `pExp`, cofactor
`rest`, target `n`, and the power accumulator seeded to `1`. -/
def shapeStageP : List AInstr :=
  movReg rPowP sShapeP ++ movReg rPowE sShapePE ++ movLit rPowAcc 1 ++
    movReg rX sShapeRest ++ movReg rB sCand

/-- Stage the SECOND conjunct: `(q, qExp, tail)` where `(p, pExp, rest)` went,
with `rest` as the target instead of `n`.  Same block shape, different sources —
which is why `shapeEqCheck` takes its target from `rB`. -/
def shapeStageQ : List AInstr :=
  movReg rPowP sShapeQ ++ movReg rPowE sShapeQE ++ movLit rPowAcc 1 ++
    movReg rX sShapeTail ++ movReg rB sShapeRest

theorem shapeStageP_run (k : Nat) (s : AState) :
    (arun k s shapeStageP).regs rPowP = s.regs sShapeP ∧
    (arun k s shapeStageP).regs rPowE = s.regs sShapePE ∧
    (arun k s shapeStageP).regs rPowAcc = 1 ∧
    (arun k s shapeStageP).regs rX = s.regs sShapeRest ∧
    (arun k s shapeStageP).regs rB = s.regs sCand := by
  rw [shapeStageP, arun_append, arun_append, arun_append, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movLit_run _ _ _ _ (by decide)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

/-- **Row 5's first conjunct, end to end.**  Stage `(p, pExp, rest)` and `n`,
raise `p` to `pExp` with the 27-step chain, then check
`0 < pExp ∧ p ^ pExp * rest = n`. -/
def shapeFirstBlock : List AInstr :=
  shapeStageP ++ powChain 27 ++ shapeEqCheck

theorem shapeFirstBlock_run (k : Nat) (s : AState)
    (he : s.regs sShapePE ≤ 26) (hp1 : 1 ≤ s.regs sShapeP)
    (hp : s.regs sShapeP < M)
    (hbig : s.regs sShapeP ^ 27 < M)
    (hprod : s.regs sShapeP ^ (s.regs sShapePE) * s.regs sShapeRest < M)
    (hn : s.regs sCand < M) :
    (arun k s shapeFirstBlock).regs rBad =
      (if s.regs sShapeP ^ (s.regs sShapePE) * s.regs sShapeRest = s.regs sCand
          ∧ s.regs sShapePE ≠ 0
       then 0 else 1) := by
  obtain ⟨hP, hE, hAcc, hX, hB⟩ := shapeStageP_run k s
  rw [shapeFirstBlock, arun_append, arun_append]
  -- the chain computes the power, and leaves the staged operands alone
  have hpow : (arun k (arun k s shapeStageP) (powChain 27)).regs rPowAcc =
      s.regs sShapeP ^ (s.regs sShapePE) := by
    rw [powChain_27 _ _ (by rw [hE]; exact he) (by rw [hP]; exact hp1)
      (by rw [hP]; exact hp) (by rw [hAcc, hP]; omega), hAcc, hP, hE, Nat.one_mul]
  have hX' : (arun k (arun k s shapeStageP) (powChain 27)).regs rX =
      s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_X 27), hX]
  have hB' : (arun k (arun k s shapeStageP) (powChain 27)).regs rB =
      s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_B 27), hB]
  have hE' : (arun k (arun k s shapeStageP) (powChain 27)).regs rPowE =
      s.regs sShapePE := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_E 27), hE]
  rw [shapeEqCheck_run _ _ (by rw [hpow, hX']; exact hprod) (by rw [hB']; exact hn),
    hpow, hX', hB', hE']

theorem shapeStageQ_run (k : Nat) (s : AState) :
    (arun k s shapeStageQ).regs rPowP = s.regs sShapeQ ∧
    (arun k s shapeStageQ).regs rPowE = s.regs sShapeQE ∧
    (arun k s shapeStageQ).regs rPowAcc = 1 ∧
    (arun k s shapeStageQ).regs rX = s.regs sShapeTail ∧
    (arun k s shapeStageQ).regs rB = s.regs sShapeRest := by
  rw [shapeStageQ, arun_append, arun_append, arun_append, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movLit_run _ _ _ _ (by decide)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

/-- **Row 5's second conjunct, end to end** — the `s.rest ≠ 1` side.  Same
three blocks as the first conjunct, staged from `(q, qExp, tail)` with `rest`
as the target. -/
def shapeSecondBlock : List AInstr :=
  shapeStageQ ++ powChain 27 ++ shapeEqCheck

theorem shapeSecondBlock_run (k : Nat) (s : AState)
    (he : s.regs sShapeQE ≤ 26) (hp1 : 1 ≤ s.regs sShapeQ)
    (hp : s.regs sShapeQ < M)
    (hbig : s.regs sShapeQ ^ 27 < M)
    (hprod : s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail < M)
    (hn : s.regs sShapeRest < M) :
    (arun k s shapeSecondBlock).regs rBad =
      (if s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail
            = s.regs sShapeRest ∧ s.regs sShapeQE ≠ 0
       then 0 else 1) := by
  obtain ⟨hP, hE, hAcc, hX, hB⟩ := shapeStageQ_run k s
  rw [shapeSecondBlock, arun_append, arun_append]
  have hpow : (arun k (arun k s shapeStageQ) (powChain 27)).regs rPowAcc =
      s.regs sShapeQ ^ (s.regs sShapeQE) := by
    rw [powChain_27 _ _ (by rw [hE]; exact he) (by rw [hP]; exact hp1)
      (by rw [hP]; exact hp) (by rw [hAcc, hP]; omega), hAcc, hP, hE, Nat.one_mul]
  have hX' : (arun k (arun k s shapeStageQ) (powChain 27)).regs rX =
      s.regs sShapeTail := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_X 27), hX]
  have hB' : (arun k (arun k s shapeStageQ) (powChain 27)).regs rB =
      s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_B 27), hB]
  have hE' : (arun k (arun k s shapeStageQ) (powChain 27)).regs rPowE =
      s.regs sShapeQE := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_E 27), hE]
  rw [shapeEqCheck_run _ _ (by rw [hpow, hX']; exact hprod) (by rw [hB']; exact hn),
    hpow, hX', hB', hE']

/-! ### Row 5's guards: `rest = 1` and its complement

`shapeOK`'s branch is `if rest = 1 then trivial else second`.  Rather than
select between two computed results, each side commits under its own guard —
the guards are complementary, both sides OR into the same `rViol`, so the
disjunction IS the model's `if`.  That removes two selects and the register
pressure they carry. -/

def restEqGuard : List AInstr :=
  [ .scalar (.binop rGuard .eq (.reg sShapeRest) (.lit 1)) ]

def restNeGuard : List AInstr :=
  [ .scalar (.binop rGuard .ne (.reg sShapeRest) (.lit 1)) ]

theorem restEqGuard_run (k : Nat) (s : AState) :
    (arun k s restEqGuard).regs rGuard =
      (if s.regs sShapeRest = 1 then 1 else 0) := by
  simp [restEqGuard, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rGuard, sShapeRest,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

theorem restNeGuard_run (k : Nat) (s : AState) :
    (arun k s restNeGuard).regs rGuard =
      (if s.regs sShapeRest = 1 then 0 else 1) := by
  simp [restNeGuard, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rGuard, sShapeRest,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- **The `rest = 1` side of `shapeOK`, end to end.** -/
def shapeTrivialBlock : List AInstr :=
  shapeTrivialCheck ++ restEqGuard ++ commitWithGuard

theorem shapeTrivialBlock_run (k : Nat) (s : AState)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1) :
    (arun k s shapeTrivialBlock).regs rViol =
      (s.regs rViol |||
        (if ¬(s.regs rY = 0 ∧ s.regs rPowE = 0 ∧ s.regs rX = 1)
            ∧ s.regs sShapeRest = 1
         then 1 else 0)) % M := by
  rw [shapeTrivialBlock, arun_append, arun_append]
  have hbad : (arun k (arun k s shapeTrivialCheck) restEqGuard).regs rBad =
      (if s.regs rY = 0 ∧ s.regs rPowE = 0 ∧ s.regs rX = 1 then 0 else 1) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      shapeTrivialCheck_run]
  have hg : (arun k (arun k s shapeTrivialCheck) restEqGuard).regs rGuard =
      (if s.regs sShapeRest = 1 then 1 else 0) := by
    rw [restEqGuard_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  have hviol : (arun k (arun k s shapeTrivialCheck) restEqGuard).regs rViol =
      s.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  rw [commitWithGuard_run _ _ (by rw [hbad]; exact ite_bit' _)
      (by rw [hg]; exact ite_bit _), hbad, hg, hviol]
  by_cases h1 : s.regs rY = 0 ∧ s.regs rPowE = 0 ∧ s.regs rX = 1 <;>
    by_cases h2 : s.regs sShapeRest = 1 <;> simp [h1, h2]

theorem powChain_writes_Rest (m : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes sShapeRest (powChain m) = false := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ]
      unfold LeanCompCert.Verified.ArrayRegFrame.writes at ih ⊢
      rw [List.any_append, ih]
      rfl

theorem shapeSecondBlock_frame_rest (k : Nat) (s : AState) :
    (arun k s shapeSecondBlock).regs sShapeRest = s.regs sShapeRest := by
  rw [shapeSecondBlock, arun_append, arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_Rest 27),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

theorem shapeSecondBlock_frame_viol (k : Nat) (s : AState) :
    (arun k s shapeSecondBlock).regs rViol = s.regs rViol := by
  rw [shapeSecondBlock, arun_append, arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (powChain_writes_Viol 27),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

/-- **The `rest ≠ 1` side of `shapeOK`, end to end** — the complement of
`shapeTrivialBlock`.  Together the two cover the model's branch with no select. -/
def shapeSecondCommitBlock : List AInstr :=
  shapeSecondBlock ++ restNeGuard ++ commitWithGuard

theorem shapeSecondCommitBlock_run (k : Nat) (s : AState)
    (he : s.regs sShapeQE ≤ 26) (hp1 : 1 ≤ s.regs sShapeQ)
    (hp : s.regs sShapeQ < M) (hbig : s.regs sShapeQ ^ 27 < M)
    (hprod : s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail < M)
    (hn : s.regs sShapeRest < M) :
    (arun k s shapeSecondCommitBlock).regs rViol =
      (s.regs rViol |||
        (if ¬(s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail
                  = s.regs sShapeRest ∧ s.regs sShapeQE ≠ 0)
            ∧ ¬(s.regs sShapeRest = 1)
         then 1 else 0)) % M := by
  rw [shapeSecondCommitBlock, arun_append, arun_append]
  have hbad : (arun k (arun k s shapeSecondBlock) restNeGuard).regs rBad =
      (if s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail
            = s.regs sShapeRest ∧ s.regs sShapeQE ≠ 0 then 0 else 1) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      shapeSecondBlock_run _ _ he hp1 hp hbig hprod hn]
  have hg : (arun k (arun k s shapeSecondBlock) restNeGuard).regs rGuard =
      (if s.regs sShapeRest = 1 then 0 else 1) := by
    rw [restNeGuard_run, shapeSecondBlock_frame_rest]
  have hviol : (arun k (arun k s shapeSecondBlock) restNeGuard).regs rViol =
      s.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      shapeSecondBlock_frame_viol]
  rw [commitWithGuard_run _ _ (by rw [hbad]; exact ite_bit' _)
      (by rw [hg]; exact ite_bit' _), hbad, hg, hviol]
  by_cases h1 : s.regs sShapeQ ^ (s.regs sShapeQE) * s.regs sShapeTail
      = s.regs sShapeRest ∧ s.regs sShapeQE ≠ 0 <;>
    by_cases h2 : s.regs sShapeRest = 1 <;> simp [h1, h2]

/-! ### Rows 1/2: branch A, staged from the sweep's existing log registers

⚠ THE NOTE THAT USED TO SIT HERE WAS WRONG, and it is worth recording what it
said because it is what the code was built on: "`LambdaPsiSelection` already
loads the log table into `rTabL`/`rTabU` and already performs `pLog32`'s
`if p = n then carried else table` selection, so `lp.1`/`lp.2` are simply
registers 210/211 — nothing to re-emit."

The selection is real, but its result goes to the LAMBDA registers; 210/211
stay the raw clamped table row.  Branch A's lower endpoint is
`-(mulUpper lp.2 lp.2)`, so it must square `sTabU`, not `rTabU`. -/

/-- ⚠ BRANCH A IS WRONG HERE, and the obvious fix does not work either.

`rTabL`/`rTabU` (210/211) are `s.arr (selectedLoIndex c p)` -- the RAW table
row, clamped to `logSink` when `p >= logLen`.  They are NOT `pLog32`, so branch
A (`rest = 1`, the only case where `p = n` can hold) reads a clamped table row
where the model reads the carried running log.  The table has 10,001 rows;
candidates run to 10^8.

⚠ `rLamL`/`rLamU` (206/207) are NOT a drop-in substitute, though they look
like one.  `LambdaPsiSelection.selectionBody` computes

    rT0   := (sRRest = 1) * (reg 11)        -- gate AND rest = 1
    rT1   := (sRP = reg 132)                -- p = n
    rLamL := rT1*rOldL + (1-rT1)*rTabL      -- this IS pLog32 ...
    rLamL := rLamL * rT0                    -- ... but then times the GATE

so `rLamL` is `pLog32` only on a GATED `rest = 1` step and 0 otherwise, while
`coeffInterval` uses `pLog32` ungated.  Substituting it was tried and reverted:
on any ungated step branch A would read 0, which is worse than the table.

The correct fix is to RECOMPUTE `pLog32` for branch A from the same inputs the
host uses -- `if sRP = reg 132 then rOldL else rTabL` -- without the gate
factor.  Note the registers: the host compares `sRP` against register 132,
NOT `sShapeP` (100), and the carried value is `rOldL`/`rOldU`, not the
`rLogLPre`/`rLogUPre` snapshot.  An earlier attempt used the wrong pair on both
counts.

Branch B needs no such fix: `tail = 1` forces `rest <> 1`, hence `p <> n`,
where `pLog32` IS the table row.  `qSubStage` likewise. -/
def sTabL : Nat := 210
/-- `LambdaPsiBase.rTabU`, the selected upper log. -/
def sTabU : Nat := 211

/-- **`pLog32`, recomputed ungated, for branch A.**

    pLog32 = if s.p = n then (carriedLogLower32 logL, carriedLogUpper32 logU)
                        else (e.lo32, e.hi32)

The host computes exactly this in `selectionBody` and then multiplies it by
`(rest = 1) * gate`, leaving it in `rLamL`/`rLamU`.  `coeffInterval` uses it
UNGATED, so the lambda registers cannot be read directly -- on an ungated step
they are 0.  This recomputes the select from the host's own inputs, without
the gate factor:

* the comparison is `sShapeP` vs `sCand`, and those ARE the host's `sRP` and
  register 132 (`ShapeSieve.rShapeP` = 100, `rN` = 132) -- same test;
* the carried side is `sOldL`/`sOldU`, the host's recovered pre-increment
  logs, NOT a snapshot taken before the body.

Both sources are 48-bit.  This block performs the explicit `>>16` conversion
(floor low, `ceilDiv` high), so the endpoint registers themselves denote the
model's 32-bit observations.

`selectBlock` reads `rC` and never writes it, so one comparison drives both. -/
def pLogRecompute : List AInstr :=
  [ .scalar (.binop rC .eq (.reg sShapeP) (.reg sCand)) ] ++
    movReg rX sOldL ++ movReg rY sTabL ++ selectBlock ++ movReg rPLo rSel ++
    shrReg rPLo rPLo 16 ++
    movReg rX sOldU ++ movReg rY sTabU ++ selectBlock ++ movReg rPHi rSel ++
    ceilShift16Reg rPHi rPHi

theorem pLogRecompute_wf :
    pLogRecompute.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- Stage `lp.2` into both product operands. -/
def branchAStage : List AInstr := movReg rA rPHi ++ movReg rB rPHi

theorem branchAStage_run (k : Nat) (s : AState) :
    (arun k s branchAStage).regs rA = s.regs rPHi ∧
    (arun k s branchAStage).regs rB = s.regs rPHi := by
  rw [branchAStage, arun_append]
  refine ⟨?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), movReg_run]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

/-- **Branch A end to end**: `rProd = encodeZ (-(ceilShift(lp.2)^2))`, which by
`negCeilProduct_le_neg_mulUpper` is at most the model's `-(mulUpper lp.2 lp.2)`. -/
def branchABlock : List AInstr := branchAStage ++ negCeilProduct

theorem branchABlock_run (k : Nat) (s : AState)
    (hA : s.regs rPHi + 65535 < M)
    (hp : (s.regs rPHi + 65535) / 65536 * ((s.regs rPHi + 65535) / 65536) < M) :
    (arun k s branchABlock).regs rProd =
      Section413Cells.encodeZ
        (-(((s.regs rPHi + 65535) / 65536
              * ((s.regs rPHi + 65535) / 65536) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchAStage_run k s
  rw [branchABlock, arun_append,
    negCeilProduct_run _ _ (by rw [ha]; exact hA) (by rw [hb]; exact hA)
      (by rw [ha, hb]; exact hp), ha, hb]

/-! ### The guarded subtraction, for `qLog32`'s `q = rest` branch

`qLog32` computes `carriedLogUpper32 logU - pExp * lp.1` in `Nat`.  The
machine's `.sub` is MODULAR, so it agrees with that truncated subtraction
exactly when no underflow occurs — which is precisely what `qSubOK` (row 6)
checks.  `sub_mod_ge` is the transfer.

⚠ Register-register `.sub` is safe here; it is `.sub` against a **literal** that
drags `M - lit` into the kernel and deep-recurses (see `powStep`).  With both
operands in registers, `M - s.regs b` stays symbolic. -/
def guardedSubBlock (dst a b : Nat) : List AInstr :=
  [ .scalar (.binop dst .sub (.reg a) (.reg b)) ]

theorem guardedSubBlock_run (k : Nat) (s : AState) (dst a b : Nat)
    (hle : s.regs b ≤ s.regs a) (ha : s.regs a < M) :
    (arun k s (guardedSubBlock dst a b)).regs dst = s.regs a - s.regs b := by
  simp only [guardedSubBlock, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl]
  exact sub_mod_ge hle ha

/-- When the guard FAILS the subtraction wraps, and this is what it wraps to —
stated so the fail-closed argument is explicit rather than implied.  The wrapped
value is harmless because `qSubOK`'s violation is already in `rViol` and
violations only ever OR in, never clear. -/
theorem guardedSubBlock_run_wrapped (k : Nat) (s : AState) (dst a b : Nat)
    (hlt : s.regs a < s.regs b) (hb : s.regs b < M) :
    (arun k s (guardedSubBlock dst a b)).regs dst = M - (s.regs b - s.regs a) := by
  simp only [guardedSubBlock, arun, astep, denoteInstr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set,
    List.foldl_cons, List.foldl_nil, if_pos rfl]
  exact sub_mod_lt hlt hb

/-! ### The `s.q`-keyed table load

`selectedLoIndex c p = if p < c.logLen then p + c.logLoBase else c.logSink`, and
`LambdaPsiSelection` emits this for `s.p` only.  Branch B needs the same for
`s.q`, so the index is recomputed branch-free — `.lt` and `.ge` for the two
complementary gates, never `1 - sel`, per the `.sub`/`M` rule above. -/

/-- `rA := if q < logLen then q + loBase else sink`. -/
def qIndexBlock (logLen loBase sink : Nat) : List AInstr :=
  [ .scalar (.binop rT4 .lt (.reg sShapeQ) (.lit logLen))
  , .scalar (.binop rT5 .ge (.reg sShapeQ) (.lit logLen))
  , .scalar (.binop rA .add (.reg sShapeQ) (.lit loBase))
  , .scalar (.binop rA .mul (.reg rA) (.reg rT4))
  , .scalar (.binop rT5 .mul (.reg rT5) (.lit sink))
  , .scalar (.binop rA .add (.reg rA) (.reg rT5)) ]

theorem qIndexBlock_run (k : Nat) (s : AState) (logLen loBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M) :
    (arun k s (qIndexBlock logLen loBase sink)).regs rA =
      (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) := by
  simp only [sShapeQ] at hsum
  rcases Nat.lt_or_ge (s.regs 103) logLen with h | h
  · have h' : ¬ (logLen ≤ s.regs 103) := Nat.not_le.mpr h
    simp [qIndexBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rT4, rT5, sShapeQ, h, h',
      Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hsink, Nat.mod_eq_of_lt hsum,
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  · have h' : ¬ (s.regs 103 < logLen) := Nat.not_lt.mpr h
    simp [qIndexBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rT4, rT5, sShapeQ, h, h',
      Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hsink, Nat.mod_eq_of_lt hsum,
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]

/-- Load the cell the index selects. -/
def loadCell (dst idx : Nat) : List AInstr := [ .load dst idx ]

theorem loadCell_run (k : Nat) (s : AState) (dst idx : Nat) :
    (arun k s (loadCell dst idx)).regs dst = s.arr (s.regs idx) := by
  simp [loadCell, arun, astep, AState.writeReg, RegState.set]

def qLogDirectLoad (logLen loBase hiBase sink : Nat) : List AInstr :=
  qIndexBlock logLen loBase sink ++ loadCell rQLo rA ++
    shrReg rQLo rQLo 16 ++
  qIndexBlock logLen hiBase sink ++ loadCell rQHi rA ++
    ceilShift16Reg rQHi rQHi

def qLogDerivedLower : List AInstr :=
  [ .scalar (.binop 334 .lshr (.reg rLogLPre) (.lit 16))
  , .scalar (.binop 336 .mul (.reg sShapePE) (.reg rPHi))
  , .scalar (.binop 340 .ge (.reg 334) (.reg 336))
  , .scalar (.binop 334 .sub (.reg 334) (.reg 336))
  , .scalar (.binop 334 .mul (.reg 334) (.reg 340)) ]

def qLogDerivedUpper : List AInstr :=
  [ .scalar (.binop 337 .add (.reg rLogUPre) (.lit 65535))
  , .scalar (.binop 337 .lshr (.reg 337) (.lit 16))
  , .scalar (.binop 339 .mul (.reg sShapePE) (.reg rPLo))
  , .scalar (.binop 341 .ge (.reg 337) (.reg 339))
  , .scalar (.binop 337 .sub (.reg 337) (.reg 339))
  , .scalar (.binop 337 .mul (.reg 337) (.reg 341)) ]

def qLogSelectGuard : List AInstr :=
  [ .scalar (.binop rT4 .ne (.reg sShapeRest) (.lit 1))
  , .scalar (.binop rT5 .eq (.reg sShapeQ) (.reg sShapeRest))
  , .scalar (.binop rC .band (.reg rT4) (.reg rT5)) ]

def selectRegs (dst yes no : Nat) : List AInstr :=
  movReg rX yes ++ movReg rY no ++ selectBlock ++
    movReg dst rSel

def qLogSelect : List AInstr :=
  qLogSelectGuard ++ selectRegs rQLo 334 rQLo ++
    selectRegs rQHi 337 rQHi

/-- Recompute the source model's q-log interval.  When `q = rest` the value
comes from `log n - pExp * log p`; otherwise it is the ordinary table cell.
The direct branch is rescaled from the physical 48-bit cells; the derived
branch is computed directly at the model's 32-bit scale.  Both natural
subtractions are implemented saturatingly, so their denotation
does not rely on modular-underflow behavior. -/
def qLogRecompute (logLen loBase hiBase sink : Nat) : List AInstr :=
  qLogDirectLoad logLen loBase hiBase sink ++ qLogDerivedLower ++
    qLogDerivedUpper ++ qLogSelect

theorem qLogRecompute_wf (logLen loBase hiBase sink : Nat) :
    (qLogRecompute logLen loBase hiBase sink).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 342) = true := by
  rfl

/-! ### Branch B, staged

`2 * mulLower lp.1 lq.1` with `lp.1 = rTabL` (already loaded by
`LambdaPsiSelection`) and `lq.1` fetched by the `s.q`-keyed load.  Order
matters: the index lands in `rA`, so the load must target `rB` BEFORE `rA` is
overwritten with `lp.1`. -/
def branchBStage (logLen loBase sink : Nat) : List AInstr :=
  qIndexBlock logLen loBase sink ++ loadCell rB rA ++ movReg rA sTabL

theorem branchBStage_run (k : Nat) (s : AState) (logLen loBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M) :
    (arun k s (branchBStage logLen loBase sink)).regs rA = s.regs sTabL ∧
    (arun k s (branchBStage logLen loBase sink)).regs rB =
      s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) := by
  rw [branchBStage, arun_append, arun_append]
  have hidx := qIndexBlock_run k s logLen loBase sink hlen hsink hsum
  refine ⟨?_, ?_⟩
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      loadCell_run, hidx]
    rfl

/-- **Branch B end to end** (the `q ≠ rest` side): `rProd = encodeZ (2 * P)`
with `P` the floor-shifted product, which by
`doubleFloorProduct_le_double_mulLower` is at most `2 * mulLower lp.1 lq.1`. -/
def branchBBlock (logLen loBase sink : Nat) : List AInstr :=
  branchBStage logLen loBase sink ++ doubleFloorProduct

theorem branchBBlock_run (k : Nat) (s : AState) (logLen loBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hA : s.regs sTabL < M)
    (hB : s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) < M)
    (hp : s.regs sTabL / 65536 *
      (s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) / 65536) < M) :
    (arun k s (branchBBlock logLen loBase sink)).regs rProd =
      Section413Cells.encodeZ
        (2 * ((s.regs sTabL / 65536 *
          (s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink)
            / 65536) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchBStage_run k s logLen loBase sink hlen hsink hsum
  rw [branchBBlock, arun_append,
    doubleFloorProduct_run _ _ (by rw [ha]; exact hA) (by rw [hb]; exact hB)
      (by rw [ha, hb]; exact hp), ha, hb]

/-! ### The endpoint's select conditions

`selectIntoY` takes its condition from `rC`.  `coeffInterval` branches on
`rest = 1` (branch A) and `tail = 1` (branch B), so those are the two
conditions, one instruction each. -/

def restEqOneToC : List AInstr :=
  [ .scalar (.binop rC .eq (.reg sShapeRest) (.lit 1)) ]

def tailEqOneToC : List AInstr :=
  [ .scalar (.binop rC .eq (.reg sShapeTail) (.lit 1)) ]

theorem restEqOneToC_run (k : Nat) (s : AState) :
    (arun k s restEqOneToC).regs rC =
      (if s.regs sShapeRest = 1 then 1 else 0) := by
  simp [restEqOneToC, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rC, sShapeRest, Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

theorem tailEqOneToC_run (k : Nat) (s : AState) :
    (arun k s tailEqOneToC).regs rC =
      (if s.regs sShapeTail = 1 then 1 else 0) := by
  simp [tailEqOneToC, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rC, sShapeTail, Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- Both conditions are bits, as `selectIntoY` requires. -/
theorem restEqOneToC_bit (k : Nat) (s : AState) :
    (arun k s restEqOneToC).regs rC = 0 ∨ (arun k s restEqOneToC).regs rC = 1 := by
  rw [restEqOneToC_run]; exact ite_bit _

theorem tailEqOneToC_bit (k : Nat) (s : AState) :
    (arun k s tailEqOneToC).regs rC = 0 ∨ (arun k s tailEqOneToC).regs rC = 1 := by
  rw [tailEqOneToC_run]; exact ite_bit _

/-! ### The lower endpoint's first fold

Seed `rY := 0` (branch C), compute branch B, move it into `rX`, set the
condition, and fold: `rY := if tail = 1 then B else 0`. -/
def lowerFoldB (logLen loBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBBlock logLen loBase sink ++ movReg rX rProd ++
    tailEqOneToC ++ selectIntoY

theorem lowerFoldB_run (k : Nat) (s : AState) (logLen loBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hA : s.regs sTabL < M)
    (hB : s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) < M)
    (hp : s.regs sTabL / 65536 *
      (s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) / 65536) < M) :
    (arun k s (lowerFoldB logLen loBase sink)).regs rY =
      (if s.regs sShapeTail = 1 then
        Section413Cells.encodeZ
          (2 * ((s.regs sTabL / 65536 *
            (s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink)
              / 65536) : Nat) : Int))
       else 0) := by
  rw [lowerFoldB, arun_append, arun_append, arun_append, arun_append]
  -- the seed
  have hy0 : (arun k s (movLit rY 0)).regs rY = 0 :=
    movLit_run _ _ _ _ (by decide)
  -- branch B's inputs survive the seed
  have e1 : (arun k s (movLit rY 0)).regs sShapeQ = s.regs sShapeQ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have e2 : (arun k s (movLit rY 0)).regs sTabL = s.regs sTabL :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have e3 : (arun k s (movLit rY 0)).arr = s.arr := by
    simp [movLit, arun, astep, AState.writeReg]
  have hbb := branchBBlock_run k (arun k s (movLit rY 0)) logLen loBase sink
    hlen hsink (by rw [e1]; exact hsum) (by rw [e2]; exact hA)
    (by rw [e3, e1]; exact hB) (by rw [e2, e3, e1]; exact hp)
  rw [e1, e2, e3] at hbb
  -- move branch B into the select's first candidate
  have hx : (arun k (arun k (arun k s (movLit rY 0))
      (branchBBlock logLen loBase sink)) (movReg rX rProd)).regs rX =
      Section413Cells.encodeZ
        (2 * ((s.regs sTabL / 65536 *
          (s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink)
            / 65536) : Nat) : Int)) := by
    rw [movReg_run, hbb]
  have hy1 : (arun k (arun k (arun k s (movLit rY 0))
      (branchBBlock logLen loBase sink)) (movReg rX rProd)).regs rY = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hy0]
  have ht : (arun k (arun k (arun k s (movLit rY 0))
      (branchBBlock logLen loBase sink)) (movReg rX rProd)).regs sShapeTail =
      s.regs sShapeTail := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  -- the condition, then the fold
  have hc := tailEqOneToC_run k (arun k (arun k (arun k s (movLit rY 0))
    (branchBBlock logLen loBase sink)) (movReg rX rProd))
  rw [ht] at hc
  have hxc : (arun k (arun k (arun k (arun k s (movLit rY 0))
      (branchBBlock logLen loBase sink)) (movReg rX rProd)) tailEqOneToC).regs rX =
      _ := LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : (arun k (arun k (arun k (arun k s (movLit rY 0))
      (branchBBlock logLen loBase sink)) (movReg rX rProd)) tailEqOneToC).regs rY =
      _ := LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy1]; exact (show (0:Nat) < M by decide)),
    hc, hxc, hyc, hx, hy1]
  by_cases h : s.regs sShapeTail = 1 <;> simp [h]

/-! ### The lower endpoint's second fold

Stated as a composable STEP over whatever the previous fold left in `rY`,
rather than inlining branch B's expression again — so the two folds chain
without the statement growing. -/
def lowerFoldAStep : List AInstr :=
  branchABlock ++ movReg rX rProd ++ restEqOneToC ++ selectIntoY

theorem lowerFoldAStep_run (k : Nat) (s : AState) (prev : Nat)
    (hprev : s.regs rY = prev) (hprevM : prev < M)
    (hA : s.regs rPHi + 65535 < M)
    (hp : (s.regs rPHi + 65535) / 65536 * ((s.regs rPHi + 65535) / 65536) < M) :
    (arun k s lowerFoldAStep).regs rY =
      (if s.regs sShapeRest = 1 then
        Section413Cells.encodeZ
          (-(((s.regs rPHi + 65535) / 65536
                * ((s.regs rPHi + 65535) / 65536) : Nat) : Int))
       else prev) := by
  rw [lowerFoldAStep, arun_append, arun_append, arun_append]
  have hbb := branchABlock_run k s hA hp
  have hx : (arun k (arun k s branchABlock) (movReg rX rProd)).regs rX =
      Section413Cells.encodeZ
        (-(((s.regs rPHi + 65535) / 65536
              * ((s.regs rPHi + 65535) / 65536) : Nat) : Int)) := by
    rw [movReg_run, hbb]
  have hy : (arun k (arun k s branchABlock) (movReg rX rProd)).regs rY = prev := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hprev]
  have hr : (arun k (arun k s branchABlock) (movReg rX rProd)).regs sShapeRest =
      s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  have hc := restEqOneToC_run k (arun k (arun k s branchABlock) (movReg rX rProd))
  rw [hr] at hc
  have hxc : (arun k (arun k (arun k s branchABlock) (movReg rX rProd))
      restEqOneToC).regs rX = _ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : (arun k (arun k (arun k s branchABlock) (movReg rX rProd))
      restEqOneToC).regs rY = _ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; exact hprevM),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeRest = 1 <;> simp [h]

/-- `coeffInterval`'s final step on the lower endpoint: `+ 2 * gammaLower32`,
in place on `rY`.  Needs no new register, so unlike the accumulate it can be
proved before the switch-over. -/
def lowerGammaStep (gammaLo : Nat) : List AInstr := addConstBlock rY rY gammaLo

theorem lowerGammaStep_run (k : Nat) (s : AState) (gammaLo : Nat) (a : Int)
    (hy : s.regs rY = Section413Cells.encodeZ a)
    (hc : gammaLo < LeanCompCert.Verified.MulWide.B64) :
    (arun k s (lowerGammaStep gammaLo)).regs rY =
      Section413Cells.encodeZ (a + (gammaLo : Int)) :=
  addConstBlock_run k s rY rY gammaLo a hy hc

/-- Chaining the two folds and the constant: the lower endpoint is
`I.1 = (branch value) + 2 * gammaLower32`, encoded, in `rY`.  Only the
`signedAccumulate` into `rLo` is left, and that needs a register the current
`regCount` does not have — see the atomicity note above. -/
theorem lowerEndpoint_shape (k : Nat) (s : AState) (gammaLo : Nat) (a : Int)
    (hy : s.regs rY = Section413Cells.encodeZ a)
    (hc : gammaLo < LeanCompCert.Verified.MulWide.B64) :
    (arun k s (lowerGammaStep gammaLo)).regs rY =
      Section413Cells.encodeZ (a + (gammaLo : Int)) :=
  lowerGammaStep_run k s gammaLo a hy hc

/-! ### The UPPER endpoint's branch composites

`coeffInterval`'s upper endpoint is `b.2 + 2 * gammaUpper32` with
`b.2 = -(mulLower lp.1 lp.1)` (branch A) or `2 * mulUpper lp.2 lq.2` (branch B).
The rounding directions are the MIRROR of the lower endpoint's, and getting
them backwards narrows the interval:

    branch A: negating a LOWER product — take FLOOR, since
              -floorShifted >= -mulLower, so the endpoint moves UP
    branch B: a positive UPPER product — take CEIL

i.e. exactly the opposite choice from the lower endpoint in both cases. -/
def negFloorProduct : List AInstr :=
  floorShiftedProduct ++ negateBlock rProd rProd

theorem negFloorProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA < M) (hB : s.regs rB < M)
    (hp : s.regs rA / 65536 * (s.regs rB / 65536) < M) :
    (arun k s negFloorProduct).regs rProd =
      Section413Cells.encodeZ
        (-((s.regs rA / 65536 * (s.regs rB / 65536) : Nat) : Int)) := by
  rw [negFloorProduct, arun_append]
  have hprod := floorShiftedProduct_run k s hA hB hp
  refine negateBlock_run _ _ _ _ _ ?_
  rw [hprod]
  have hpB : s.regs rA / 65536 * (s.regs rB / 65536)
      < LeanCompCert.Verified.MulWide.B64 := M_eq_B64 ▸ hp
  exact (encodeZ_ofNat hpB).symm

/-- Upward bracketing: the emitted upper endpoint is at least the model's. -/
theorem negFloorProduct_ge_neg_mulLower (s : AState) :
    -((mulLower (s.regs rA) (s.regs rB) : Nat) : Int)
      ≤ -((s.regs rA / 65536 * (s.regs rB / 65536) : Nat) : Int) := by
  have h := floorShifted_le_mulLower (s.regs rA) (s.regs rB)
  omega

def doubleCeilProduct : List AInstr :=
  ceilShiftedProduct ++ doubleBlock rProd rProd

theorem doubleCeilProduct_run (k : Nat) (s : AState)
    (hA : s.regs rA + 65535 < M) (hB : s.regs rB + 65535 < M)
    (hp : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536) < M) :
    (arun k s doubleCeilProduct).regs rProd =
      Section413Cells.encodeZ
        (2 * (((s.regs rA + 65535) / 65536
                * ((s.regs rB + 65535) / 65536) : Nat) : Int)) := by
  rw [doubleCeilProduct, arun_append]
  have hprod := ceilShiftedProduct_run k s hA hB hp
  refine doubleBlock_run _ _ _ _ _ ?_
  rw [hprod]
  have hpB : (s.regs rA + 65535) / 65536 * ((s.regs rB + 65535) / 65536)
      < LeanCompCert.Verified.MulWide.B64 := M_eq_B64 ▸ hp
  exact (encodeZ_ofNat hpB).symm

theorem doubleCeilProduct_ge_double_mulUpper (s : AState) :
    2 * ((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int)
      ≤ 2 * (((s.regs rA + 65535) / 65536
              * ((s.regs rB + 65535) / 65536) : Nat) : Int) := by
  have h := mulUpper_le_ceilShifted (s.regs rA) (s.regs rB)
  omega

/-! ## The whole-window lift

`placeholder_productionArithmeticProgram_denote_pendingWholeWindow` needs an
invariant carried across all 100 windows.  `bodyRun` and `windowRun` are plain
structural recursions, so the lift is two short inductions — and, crucially,
they are stated over an ARBITRARY invariant and an arbitrary body, so they hold
before and after the switch-over alike.  Proving them now means the remaining
work on the last axiom is supplying the per-candidate step, not building
induction machinery.

Companion to `SweepInduction.run_invariant` on the model side; this is the same
shape on the machine side. -/

theorem bodyRun_invariant (k : Nat) (c : LambdaPsiSweep.Cfg)
    (P : LeanCompCert.Verified.ArrayState.AState → Prop)
    (hstep : ∀ t, P t → P (arun k t (LambdaPsiSweep.body c))) :
    ∀ (fuel : Nat) (s : LeanCompCert.Verified.ArrayState.AState), P s →
      P (BodyRefinement.bodyRun k c fuel s)
  | 0, _, h => h
  | fuel + 1, s, h => hstep _ (bodyRun_invariant k c P hstep fuel s h)

theorem windowRun_invariant (k : Nat) (c : LambdaPsiSweep.Cfg)
    (P : LeanCompCert.Verified.ArrayState.AState → Prop)
    (hstep : ∀ t, P t → P (arun k t (LambdaPsiSweep.body c))) :
    ∀ (windows : Nat) (s : LeanCompCert.Verified.ArrayState.AState), P s →
      P (BodyRefinement.windowRun k c windows s)
  | 0, _, h => h
  | w + 1, s, h =>
      bodyRun_invariant k c P hstep _ _ (windowRun_invariant k c P hstep w s h)

/-- Commit `rBad` into the flag with NO guard — the form `shapeOK`'s first
conjunct needs, since that conjunct is unconditional.  One instruction. -/
def commitBad : List AInstr :=
  [ .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

theorem commitBad_run (k : Nat) (s : AState)
    (hb : s.regs rBad = 0 ∨ s.regs rBad = 1) :
    (arun k s commitBad).regs rViol =
      (s.regs rViol ||| s.regs rBad) % M := by
  simp [commitBad, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rBad, rViol]

theorem commitBad_bit (k : Nat) (s : AState)
    (hv : s.regs rViol = 0 ∨ s.regs rViol = 1)
    (hb : s.regs rBad = 0 ∨ s.regs rBad = 1) :
    (arun k s commitBad).regs rViol = 0 ∨ (arun k s commitBad).regs rViol = 1 := by
  rw [commitBad_run _ _ hb]
  exact or_bit hv hb

/-- Stage `shapeTrivialCheck`'s third operand.  `shapeStageQ` supplies `rPowE`
and `rX`; the check also reads `q` from `rY`. -/
def shapeTrivialStage : List AInstr := movReg rY sShapeQ

theorem shapeTrivialStage_run (k : Nat) (s : AState) :
    (arun k s shapeTrivialStage).regs rY = s.regs sShapeQ := movReg_run _ _ _ _

/-! ## Well-formedness of the extension

Every register this file uses is below `260`, the sweep's current `regCount`,
so all of these blocks are already well formed against it — which is what lets
them be appended to `LambdaPsiSweep.body` without weakening `program_wf`.

⚠ `powChain` needs an induction (its length depends on `m`); every other block
is a fixed list and goes by `decide`. -/

theorem powStep_wf (i : Nat) :
    (powStep i).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem powChain_wf (m : Nat) :
    (powChain m).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [powChain_succ, List.all_append, ih, powStep_wf]
      rfl

theorem seamCoreBlocks_wf :
    (absDiffBlock ++ maxBlock ++ seamPsiBlock ++ correctedStage ++
      shapeEqCheck ++ shapeTrivialCheck ++ divWitnessCheck ++ commitBad ++
      commitWithGuard ++ restEqGuard ++ restNeGuard ++ restEqOneToC ++
      tailEqOneToC ++ selectBlock).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  decide

/-- Stage row 6's operands.  ⚠ THE TABLE IS 48-BIT; `pLog32` IS 32-BIT.  `Cfg.logCells` emits only
`lo48`/`hi48`, so `sTabL` carries `lo48` -- but `qSubOK` compares against
`lp.1 = e.lo32`, and production defines `lo32 = lo48 / logShift`
(`Lemma71Engine.logLower32`).  Staging `sTabL` directly makes the left-hand
side 65536x too large, and the check fails on the FIRST candidate.

The `p = n` branch of `pLog32` needs no handling here: `p = n` forces
`rest = 1`, and `qSubOK` is `true` whenever `rest = 1`, so the guard below
already excludes it. -/
def qSubStage : List AInstr :=
  movReg rQsPExp sShapePE ++ shrReg rQsLp sTabL 16 ++
    movReg rQsLogU rLogUPre ++
    movReg rQsRest sShapeRest ++ movReg rQsQ sShapeQ

theorem qSubStage_run (k : Nat) (s : AState) (htab : s.regs sTabL < M) :
    (arun k s qSubStage).regs rQsPExp = s.regs sShapePE ∧
    (arun k s qSubStage).regs rQsLp = s.regs sTabL / 65536 ∧
    (arun k s qSubStage).regs rQsLogU = s.regs rLogUPre ∧
    (arun k s qSubStage).regs rQsRest = s.regs sShapeRest ∧
    (arun k s qSubStage).regs rQsQ = s.regs sShapeQ := by
  rw [qSubStage, arun_append, arun_append, arun_append, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
    have hframe : (arun k s (movReg rQsPExp sShapePE)).regs sTabL =
        s.regs sTabL := by
      rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
    rw [shrReg_run _ _ _ _ _ (by decide) (by rw [hframe]; exact htab), hframe]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

/-! ## The extended checks, as a block

Rows 5 and 6 assembled — the two rows that are complete end to end and need no
persistent accumulator, so they are exactly the part that can be built and
checked before any artifact change.

⚠ This is a NEW definition, deliberately not spliced into
`LambdaPsiSweep.body`: appending to the live body changes the emitted C and
would invalidate the current receipt.  It waits for the switch-over. -/
def candidateChecksV1 : List AInstr :=
  shapeFirstBlock ++ commitBad ++
    shapeStageQ ++ shapeTrivialStage ++ shapeTrivialBlock ++
    shapeSecondCommitBlock ++
    qSubStage ++ qSubBlock

theorem shapeFirstBlock_wf :
    shapeFirstBlock.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rw [shapeFirstBlock, List.all_append, List.all_append, powChain_wf]
  rfl

theorem shapeSecondBlock_wf :
    shapeSecondBlock.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rw [shapeSecondBlock, List.all_append, List.all_append, powChain_wf]
  rfl

theorem candidateChecksV1_wf :
    candidateChecksV1.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rw [candidateChecksV1, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append,
    shapeFirstBlock_wf, shapeSecondCommitBlock, List.all_append, List.all_append,
    shapeSecondBlock_wf]
  rfl

/-! ## Rows 3 and 4, assembled

Row 4 (`anchor`) is the two-magnitude block on `(sumL, sumU, logL, logU)`,
fired only at `n = c.limit`; row 3(b) (`correctedOK`) is the same block on the
staging that folds in the carried psi quotients, fired for `c.lower ≤ n`.  Both
use `thresholdBit` + a guarded commit rather than `anchorBlock`'s built-in
unguarded `thresholdBlock`, because both are conditional in the model. -/

/-- Row 4's staging at the production registers. -/
def anchorStageProd : List AInstr := anchorStage sSumL sSumU rLogLPre rLogUPre

/-- Row 4 end to end, guarded by `n = limit`. -/
def anchorRow (gammaLo gammaHi bound limit : Nat) : List AInstr :=
  anchorStageProd ++ anchorHead gammaLo ++ anchorTailMax gammaHi ++
    thresholdBit bound ++ eqGuardedCommit limit

/-- Row 3(b) end to end, guarded by `lower ≤ n`. -/
def correctedRow (gammaLo gammaHi bound lower : Nat) : List AInstr :=
  correctedStage ++ anchorHead gammaLo ++ anchorTailMax gammaHi ++
    thresholdBit bound ++ guardedCommit lower

def correctedRowAt (qL qU rU gammaLo gammaHi bound lower : Nat) : List AInstr :=
  correctedStageAt qL qU rU ++ anchorHead gammaLo ++
    anchorTailMax gammaHi ++ thresholdBit bound ++ guardedCommit lower

theorem anchorStageProd_wf :
    anchorStageProd.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem anchorRow_wf (gammaLo gammaHi bound limit : Nat) :
    (anchorRow gammaLo gammaHi bound limit).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem correctedRow_wf (gammaLo gammaHi bound lower : Nat) :
    (correctedRow gammaLo gammaHi bound lower).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- Rows 3, 4, 5 and 6 assembled — every row that is complete end to end and
needs no persistent accumulator. -/
def candidateChecksV2 (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower : Nat) : List AInstr :=
  candidateChecksV1 ++ seamPsiBlock ++
    correctedRow cgammaLo cgammaHi cbound lower ++
    anchorRow gammaLo gammaHi bound limit

theorem candidateChecksV2_wf (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower : Nat) :
    (candidateChecksV2 gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rw [candidateChecksV2, List.all_append, List.all_append, List.all_append,
    candidateChecksV1_wf, correctedRow_wf, anchorRow_wf]
  rfl

/-! ## Rows 1/2's persistent accumulators

These are the ONLY registers in the extension that must survive a candidate,
and the allocation is forced: the host sweep tops out at 214, this file's
217-259 are all per-candidate scratch, so the free persistent slots are exactly
215 and 216 — two, against three needed.  Hence `regCount` rises by one,
260 → 261, and `rAccHi` takes 260.

⚠ Blocks touching `rAccHi` are stated well formed against **261**, not 260.
Nothing else in the extension needs the bump. -/

/-- `weightedAbs`. -/
def rAccW : Nat := 261
/-- `rLo`, two's-complement encoded. -/
def rAccLo : Nat := 262
/-- `rHi`, two's-complement encoded — the register that forces `regCount` up. -/
def rAccHi : Nat := 306

/-- `rLo += I.1`: one modular add, which IS two's-complement addition. -/
def accumulateLo : List AInstr := signedAccumulate rAccLo rY

/-- `rHi += I.2`. -/
def accumulateHi : List AInstr := signedAccumulate rAccHi rY

theorem accumulateLo_run (k : Nat) (s : AState) (a acc : Int)
    (hacc : s.regs rAccLo = Section413Cells.encodeZ acc)
    (hy : s.regs rY = Section413Cells.encodeZ a) :
    (arun k s accumulateLo).regs rAccLo =
      Section413Cells.encodeZ (acc + a) :=
  signedAccumulate_run k s rAccLo rY acc a hacc hy

theorem accumulateHi_run (k : Nat) (s : AState) (a acc : Int)
    (hacc : s.regs rAccHi = Section413Cells.encodeZ acc)
    (hy : s.regs rY = Section413Cells.encodeZ a) :
    (arun k s accumulateHi).regs rAccHi =
      Section413Cells.encodeZ (acc + a) :=
  signedAccumulate_run k s rAccHi rY acc a hacc hy

theorem accumulateLo_wf :
    accumulateLo.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem accumulateHi_wf :
    accumulateHi.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- The accumulator slots are distinct from everything else this file uses, and
all sit above the host sweep's range. -/
theorem accumulatorRegs_ok :
    ([rAccW, rAccLo, rAccHi] : List Nat).Nodup ∧
    ([rAccW, rAccLo, rAccHi] : List Nat).all (fun r => decide (214 < r)) = true := by
  constructor <;> decide

/-! ## Rows 1/2: the lower endpoint pipeline, assembled

Seed and fold branch B, fold branch A over it, add `2 * gammaLower32`, and
accumulate into `rLo`.  Every stage is a proved block:
`lowerFoldB_run`, `lowerFoldAStep_run`, `lowerGammaStep_run`,
`accumulateLo_run`. -/
def lowerEndpointBlock (logLen loBase sink gammaLo : Nat) : List AInstr :=
  lowerFoldB logLen loBase sink ++ lowerFoldAStep ++ lowerGammaStep gammaLo ++
    movReg rIlo rY ++ accumulateLo

theorem lowerEndpointBlock_wf (logLen loBase sink gammaLo : Nat) :
    (lowerEndpointBlock logLen loBase sink gammaLo).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- The upper endpoint is the same pipeline with the rounding directions
swapped (`negFloorProduct` / `doubleCeilProduct`) and `accumulateHi` in place of
`accumulateLo` — the one block that needs `regCount = 261`. -/
def upperEndpointTail (gammaHi : Nat) : List AInstr :=
  lowerGammaStep gammaHi ++ movReg rIhi rY ++ accumulateHi

theorem upperEndpointTail_wf (gammaHi : Nat) :
    (upperEndpointTail gammaHi).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem upperEndpointTail_run (k : Nat) (s : AState) (gammaHi : Nat)
    (a acc : Int)
    (hy : s.regs rY = Section413Cells.encodeZ a)
    (hacc : s.regs rAccHi = Section413Cells.encodeZ acc)
    (hc : gammaHi < LeanCompCert.Verified.MulWide.B64) :
    (arun k s (upperEndpointTail gammaHi)).regs rAccHi =
      Section413Cells.encodeZ (acc + (a + (gammaHi : Int))) := by
  rw [upperEndpointTail, arun_append, arun_append]
  refine accumulateHi_run _ _ _ _ ?_ ?_
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl), hacc]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      lowerGammaStep_run _ _ _ _ hy hc]

/-! ## Row 7's four sites, instantiated

`rowAt` fires only at `n ∈ {462848, 10^6, 10^7, 10^8}`, with `num` a literal at
each.  `rowOK_of_strengthened` divides `n` out of both sides, so each site's
test is `W + q + 1 > num * 4345 * coeffScale / 10000` — a compile-time constant:

    n = 462848    num = 374   bound =   697,945,070,501   (~2^39)
    n = 1000000   num = 422   bound =   787,520,908,427   (~2^39)
    n = 10000000  num = 579   bound = 1,080,508,544,974   (~2^40)
    n = 100000000 num = 762   bound = 1,422,016,427,065   (~2^40)

All four sit far inside a word, so no product and nothing that can wrap. -/
def rowChecks : List AInstr :=
  rowSiteBlock 462848 697945070501 ++
    rowSiteBlock 1000000 787520908427 ++
    rowSiteBlock 10000000 1080508544974 ++
    rowSiteBlock 100000000 1422016427065

theorem rowChecks_wf :
    rowChecks.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- Each site's bound is well inside a machine word — the reason row 7 needs no
wide arithmetic once `rowOK_of_strengthened` has divided `n` out. -/
theorem rowChecks_bounds_lt_M :
    697945070501 < M ∧ 787520908427 < M ∧
    1080508544974 < M ∧ 1422016427065 < M := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Row 7's magnitude: |decodeZ w|, branch-free

`intervalAbsUpper rLo rHi = max |rLo| |rHi|`, and the accumulators hold
two's-complement encodings.  `encodeZ_sign` says the sign test is just
`H63 ≤ w`, and `encodeZ_mag_neg` says the magnitude of a negative encoding is
`B64 - w` — the same modular negation used elsewhere.  So the absolute value is
a sign test, a negation, and the usual two-way select.

⚠ `src` is CONCRETE here, not a parameter: the block reads `src` after writing
`rT4`/`rT5`/`rA`, so an aliasing `src` would break it.  Two instances, one per
accumulator. -/
def absAccLo : List AInstr :=
  [ .scalar (.binop rT4 .ge (.reg rAccLo) (.lit 9223372036854775808))
  , .scalar (.binop rT5 .lt (.reg rAccLo) (.lit 9223372036854775808))
  , .scalar (.binop rA .sub (.lit 0) (.reg rAccLo))
  , .scalar (.binop rA .mul (.reg rT4) (.reg rA))
  , .scalar (.binop rB .mul (.reg rT5) (.reg rAccLo))
  , .scalar (.binop rOut .add (.reg rA) (.reg rB)) ]

theorem absAccLo_run (k : Nat) (s : AState) (hsrc : s.regs rAccLo < M) :
    (arun k s absAccLo).regs rOut =
      (if 9223372036854775808 ≤ s.regs rAccLo then M - s.regs rAccLo
       else s.regs rAccLo) := by
  have hM1 : (1 : Nat) < M := by decide
  simp only [rAccLo] at hsrc
  rcases Nat.lt_or_ge (s.regs 262) 9223372036854775808 with h | h
  · have h' : ¬ (9223372036854775808 ≤ s.regs 262) := Nat.not_le.mpr h
    simp [absAccLo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rOut, rAccLo, h, h',
      Nat.mod_eq_of_lt hsrc,
      Nat.mod_eq_of_lt (show (9223372036854775808 : Nat) < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  · have h' : ¬ (s.regs 262 < 9223372036854775808) := Nat.not_lt.mpr h
    have hpos : M - s.regs 262 < M := by
      have : (0 : Nat) < s.regs 262 := by omega
      omega
    simp [absAccLo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rOut, rAccLo, h, h',
      Nat.mod_eq_of_lt hsrc, Nat.mod_eq_of_lt hpos,
      Nat.mod_eq_of_lt (show (9223372036854775808 : Nat) < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]

/-- The same, for `rHi`. -/
def absAccHi : List AInstr :=
  [ .scalar (.binop rT4 .ge (.reg rAccHi) (.lit 9223372036854775808))
  , .scalar (.binop rT5 .lt (.reg rAccHi) (.lit 9223372036854775808))
  , .scalar (.binop rA .sub (.lit 0) (.reg rAccHi))
  , .scalar (.binop rA .mul (.reg rT4) (.reg rA))
  , .scalar (.binop rB .mul (.reg rT5) (.reg rAccHi))
  , .scalar (.binop rOut .add (.reg rA) (.reg rB)) ]

theorem absAccHi_run (k : Nat) (s : AState) (hsrc : s.regs rAccHi < M) :
    (arun k s absAccHi).regs rOut =
      (if 9223372036854775808 ≤ s.regs rAccHi then M - s.regs rAccHi
       else s.regs rAccHi) := by
  have hM1 : (1 : Nat) < M := by decide
  simp only [rAccHi] at hsrc
  rcases Nat.lt_or_ge (s.regs 306) 9223372036854775808 with h | h
  · have h' : ¬ (9223372036854775808 ≤ s.regs 306) := Nat.not_le.mpr h
    simp [absAccHi, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rOut, rAccHi, h, h',
      Nat.mod_eq_of_lt hsrc,
      Nat.mod_eq_of_lt (show (9223372036854775808 : Nat) < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  · have h' : ¬ (s.regs 306 < 9223372036854775808) := Nat.not_lt.mpr h
    have hpos : M - s.regs 306 < M := by
      have : (0 : Nat) < s.regs 306 := by omega
      omega
    simp [absAccHi, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rA, rB, rT4, rT5, rOut, rAccHi, h, h',
      Nat.mod_eq_of_lt hsrc, Nat.mod_eq_of_lt hpos,
      Nat.mod_eq_of_lt (show (9223372036854775808 : Nat) < M by decide),
      Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]

/-- `rMx := max |rLo| |rHi|` — `intervalAbsUpper` on the encoded accumulators.

Order matters: `absAccLo` leaves its result in `rOut` and uses `rA`/`rB` as
scratch, so the first magnitude must be moved to `rX` before the second runs. -/
def intervalMagnitude : List AInstr :=
  absAccLo ++ movReg rX rOut ++ absAccHi ++ movReg rA rX ++ movReg rB rOut ++
    maxBlock

theorem intervalMagnitude_wf :
    intervalMagnitude.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- `dst := |src|` on a two's-complement encoding, generic in both registers.

⚠ Same aliasing side condition as `absAccLo`: `src` is read after `rT4`,
`rT5`, `rA` and `rB` are written, so `src` must not be one of them.  Both call
sites below pass `rIlo` / `rIhi`, which nothing else touches. -/
def absOf (dst src : Nat) : List AInstr :=
  [ .scalar (.binop rT4 .ge (.reg src) (.lit 9223372036854775808))
  , .scalar (.binop rT5 .lt (.reg src) (.lit 9223372036854775808))
  , .scalar (.binop rA .sub (.lit 0) (.reg src))
  , .scalar (.binop rA .mul (.reg rT4) (.reg rA))
  , .scalar (.binop rB .mul (.reg rT5) (.reg src))
  , .scalar (.binop dst .add (.reg rA) (.reg rB)) ]

/-- **The model's `weightedAbs`, which nothing was producing.**

    weighted := st.weightedAbs + divUpper32 (intervalAbsUpper I.1 I.2) n

⚠ Note what this accumulates: the magnitude of THIS CANDIDATE's interval `I`,
divided by `n` and rounded UP — not the magnitude of the running `rLo`/`rHi`
pair, which is a different quantity that `intervalMagnitude` computes for the
row bound.  The two were easy to conflate; `rAccW` was declared, initialised,
gated, guarded and consumed while no block ever added to it, so `rowCheck` saw
`W = 0` on every candidate.

`divUpper32` is `ceilDiv`, emitted as floor plus a remainder bit rather than
`(x + d - 1) / d`, which would need a `.sub` against a literal.  The divisor
carries the same zero guard as `rowWitnessCompute`: `sCand` is 0 on marking
steps and x86_64 traps on division by zero. -/
def weightedStep : List AInstr :=
  absOf rWmag rIlo ++ absOf rWq rIhi ++
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

/-! ## Row 7's quotient witness

`rowOK_of_strengthened` needs `intervalAbsUpper rLo rHi` as `q * n + rem` with
`rem < n`.  Rather than divide, the classifier supplies `(q, rem)` and the block
verifies them — the same idiom as `divWitnessCheck`, and fail-closed for the
same reason: a bad witness sets `rBad`.

Unlike the divisibility test this needs no `0 < rem`; only that the pair is a
genuine division of the magnitude now in `rMx`. -/
/-- **Supply the witness that `rowWitnessCheck` verifies.**

⚠ Nothing else writes `rY`/`rShR`.  `rowWitnessCheck` was written to the
"classifier supplies the witness, the block verifies it" idiom, but no
classifier supplies one here, so the check compared against a stale `rY` and a
never-written `rShR` and failed on the FIRST candidate.  A fail-closed check
whose witness is never produced is a check that always fails.

⚠ THE DIVISOR IS GUARDED.  `sCand` is 0 on marking steps, and division by zero
is undefined in C: on x86_64 it TRAPS, while aarch64 returns 0 silently — so an
unguarded divide here would be an architecture-dependent crash inside the
enclave rather than a wrong answer on the host.  `rB := sCand + (sCand = 0)` is
`n` on a candidate step and 1 otherwise; the verdict is gated either way, and
`denote` never hits the `none` branch of `udiv`/`urem`. -/
def rowWitnessCompute : List AInstr :=
  [ .scalar (.binop rB .eq (.reg sCand) (.lit 0))
  , .scalar (.binop rB .add (.reg rB) (.reg sCand))
  , .scalar (.binop rY .udiv (.reg rMx) (.reg rB))
  , .scalar (.binop rShR .urem (.reg rMx) (.reg rB)) ]

def rowWitnessCheck : List AInstr :=
  [ .scalar (.binop rA .mul (.reg rY) (.reg sCand))
  , .scalar (.binop rA .add (.reg rA) (.reg rShR))
  , .scalar (.binop rT4 .ne (.reg rA) (.reg rMx))
  , .scalar (.binop rT5 .ge (.reg rShR) (.reg sCand))
  , .scalar (.binop rBad .bor (.reg rT4) (.reg rT5)) ]

theorem rowWitnessCheck_run (k : Nat) (s : AState)
    (hm : s.regs rY * s.regs sCand < M)
    (hs : s.regs rY * s.regs sCand + s.regs rShR < M)
    (hx : s.regs rMx < M) :
    (arun k s rowWitnessCheck).regs rBad =
      (if s.regs rY * s.regs sCand + s.regs rShR = s.regs rMx
          ∧ s.regs rShR < s.regs sCand
       then 0 else 1) := by
  simp only [rY, sCand, rShR, rMx] at hm hs hx
  simp [rowWitnessCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rA, rY, sCand, rShR, rMx, rT4, rT5, rBad,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show (0 : Nat) < M by decide)]
  rw [or2_bits (ite_bit' _) (ite_bit _)]
  by_cases hA : s.regs 292 * s.regs 132 + s.regs 305 = s.regs 270 <;>
    by_cases hB : s.regs 132 ≤ s.regs 305 <;>
      simp [hA, hB] <;> omega

theorem rowWitnessCheck_wf :
    rowWitnessCheck.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-! ## The extension, assembled

Rows 3-8 plus row 1/2's lower endpoint, in one block.  What is still outside it
is the UPPER endpoint's two folds (the mirror of `lowerFoldB`/`lowerFoldAStep`
with `negFloorProduct`/`doubleCeilProduct` — all four composites proved, the
folds are the same shape) and the `output`/`init` wiring, which is part of the
splice rather than the body. -/
def candidateChecksV3 (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower
    logLen loBase sink egammaLo : Nat) : List AInstr :=
  candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++
    lowerEndpointBlock logLen loBase sink egammaLo ++
    intervalMagnitude ++ rowWitnessCompute ++ rowWitnessCheck ++ commitBad ++
    movReg rX rAccW ++ rowChecks

set_option maxRecDepth 100000 in
theorem candidateChecksV3_wf (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase sink egammaLo : Nat) :
    (candidateChecksV3 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower logLen loBase sink egammaLo).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rw [candidateChecksV3, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append]
  rfl

/-! ### The upper endpoint's branch A

Mirror of `branchABlock`: the model's upper branch A is `-(mulLower lp.1 lp.1)`,
so it reads `lp.1` = `rTabL` (not `rTabU`) and uses the FLOOR product, because
negating a floor moves the endpoint UP. -/
def branchAUpperStage : List AInstr := movReg rA rPLo ++ movReg rB rPLo

theorem branchAUpperStage_run (k : Nat) (s : AState) :
    (arun k s branchAUpperStage).regs rA = s.regs rPLo ∧
    (arun k s branchAUpperStage).regs rB = s.regs rPLo := by
  rw [branchAUpperStage, arun_append]
  refine ⟨?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), movReg_run]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

def branchAUpperBlock : List AInstr := branchAUpperStage ++ negFloorProduct

theorem branchAUpperBlock_run (k : Nat) (s : AState)
    (hA : s.regs rPLo < M)
    (hp : s.regs rPLo / 65536 * (s.regs rPLo / 65536) < M) :
    (arun k s branchAUpperBlock).regs rProd =
      Section413Cells.encodeZ
        (-((s.regs rPLo / 65536 * (s.regs rPLo / 65536) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchAUpperStage_run k s
  rw [branchAUpperBlock, arun_append,
    negFloorProduct_run _ _ (by rw [ha]; exact hA) (by rw [hb]; exact hA)
      (by rw [ha, hb]; exact hp), ha, hb]

theorem branchAUpperBlock_wf :
    branchAUpperBlock.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-! ### The upper endpoint's branch B

`2 * mulUpper lp.2 lq.2`, so it reads `lp.2` = `rTabU` and the q-table's UPPER
entry — the same `qIndexBlock`, instantiated at `hiBase` instead of `loBase`,
which is why that block took its base as a parameter.  CEIL product, since the
endpoint is a positive upper. -/
def branchBUpperStage (logLen hiBase sink : Nat) : List AInstr :=
  qIndexBlock logLen hiBase sink ++ loadCell rB rA ++ movReg rA sTabU

theorem branchBUpperStage_run (k : Nat) (s : AState) (logLen hiBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M) :
    (arun k s (branchBUpperStage logLen hiBase sink)).regs rA = s.regs sTabU ∧
    (arun k s (branchBUpperStage logLen hiBase sink)).regs rB =
      s.arr (if s.regs sShapeQ < logLen then s.regs sShapeQ + hiBase else sink) := by
  rw [branchBUpperStage, arun_append, arun_append]
  have hidx := qIndexBlock_run k s logLen hiBase sink hlen hsink hsum
  refine ⟨?_, ?_⟩
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      loadCell_run, hidx]
    rfl

def branchBUpperBlock (logLen hiBase sink : Nat) : List AInstr :=
  branchBUpperStage logLen hiBase sink ++ doubleCeilProduct

theorem branchBUpperBlock_wf (logLen hiBase sink : Nat) :
    (branchBUpperBlock logLen hiBase sink).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-! ### The upper endpoint's folds

Same shape as the lower endpoint's, over the upper branch composites. -/
def upperFoldAStep : List AInstr :=
  branchAUpperBlock ++ movReg rX rProd ++ restEqOneToC ++ selectIntoY

theorem upperFoldAStep_run (k : Nat) (s : AState) (prev : Nat)
    (hprev : s.regs rY = prev) (hprevM : prev < M)
    (hA : s.regs rPLo < M)
    (hp : s.regs rPLo / 65536 * (s.regs rPLo / 65536) < M) :
    (arun k s upperFoldAStep).regs rY =
      (if s.regs sShapeRest = 1 then
        Section413Cells.encodeZ
          (-((s.regs rPLo / 65536 * (s.regs rPLo / 65536) : Nat) : Int))
       else prev) := by
  rw [upperFoldAStep, arun_append, arun_append, arun_append]
  have hbb := branchAUpperBlock_run k s hA hp
  have hx : (arun k (arun k s branchAUpperBlock) (movReg rX rProd)).regs rX =
      Section413Cells.encodeZ
        (-((s.regs rPLo / 65536 * (s.regs rPLo / 65536) : Nat) : Int)) := by
    rw [movReg_run, hbb]
  have hy : (arun k (arun k s branchAUpperBlock) (movReg rX rProd)).regs rY = prev := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide), hprev]
  have hr : (arun k (arun k s branchAUpperBlock) (movReg rX rProd)).regs sShapeRest =
      s.regs sShapeRest := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]
  have hc := restEqOneToC_run k (arun k (arun k s branchAUpperBlock) (movReg rX rProd))
  rw [hr] at hc
  have hxc : (arun k (arun k (arun k s branchAUpperBlock) (movReg rX rProd))
      restEqOneToC).regs rX = _ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  have hyc : (arun k (arun k (arun k s branchAUpperBlock) (movReg rX rProd))
      restEqOneToC).regs rY = _ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide) _
  rw [selectIntoY_run _ _ (by rw [hc]; exact ite_bit _)
      (by rw [hxc, hx]; exact M_eq_B64 ▸ Section413Cells.encodeZ_lt _)
      (by rw [hyc, hy]; exact hprevM),
    hc, hxc, hyc, hx, hy]
  by_cases h : s.regs sShapeRest = 1 <;> simp [h]

def upperFoldB (logLen hiBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBUpperBlock logLen hiBase sink ++ movReg rX rProd ++
    tailEqOneToC ++ selectIntoY

theorem upperFoldB_wf (logLen hiBase sink : Nat) :
    (upperFoldB logLen hiBase sink).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

theorem upperFoldAStep_wf :
    upperFoldAStep.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-- The upper endpoint, assembled: fold branch B, fold branch A over it, add
`2 * gammaUpper32`, accumulate into `rHi`. -/
def upperEndpointBlock (logLen hiBase sink gammaHi : Nat) : List AInstr :=
  upperFoldB logLen hiBase sink ++ upperFoldAStep ++ upperEndpointTail gammaHi

set_option maxRecDepth 100000 in
theorem upperEndpointBlock_wf (logLen hiBase sink gammaHi : Nat) :
    (upperEndpointBlock logLen hiBase sink gammaHi).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  rfl

/-! ## Exact production endpoint assembly

The earlier endpoint assembly is retained as an audit trail for the outward
shifted approximation.  The live production body uses these structurally
identical folds with the exact widening-product composites. -/

def branchALowerExact : List AInstr := branchAStage ++ negExactCeilProduct

def branchBRegLowerStage : List AInstr := movReg rA rPLo ++ movReg rB rQLo

theorem branchBRegLowerStage_run (k : Nat) (s : AState) :
    (arun k s branchBRegLowerStage).regs rA = s.regs rPLo ∧
    (arun k s branchBRegLowerStage).regs rB = s.regs rQLo := by
  rw [branchBRegLowerStage, arun_append]
  refine ⟨?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

def branchBLowerExact (_logLen _loBase _sink : Nat) : List AInstr :=
  branchBRegLowerStage ++ doubleExactFloorProduct

def lowerFoldBExact (logLen loBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBLowerExact logLen loBase sink ++ movReg rX rProd ++
    tailEqOneToC ++ selectIntoY

def lowerFoldAExact : List AInstr :=
  branchALowerExact ++ movReg rX rProd ++ restEqOneToC ++ selectIntoY

def lowerEndpointExactBlock (logLen loBase sink gammaLo : Nat) : List AInstr :=
  lowerFoldBExact logLen loBase sink ++ lowerFoldAExact ++
    lowerGammaStep gammaLo ++ movReg rIlo rY ++ accumulateLo

def branchAUpperExact : List AInstr := branchAUpperStage ++ negExactFloorProduct

def branchBRegUpperStage : List AInstr := movReg rA rPHi ++ movReg rB rQHi

theorem branchBRegUpperStage_run (k : Nat) (s : AState) :
    (arun k s branchBRegUpperStage).regs rA = s.regs rPHi ∧
    (arun k s branchBRegUpperStage).regs rB = s.regs rQHi := by
  rw [branchBRegUpperStage, arun_append]
  refine ⟨?_, ?_⟩
  · rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide),
      movReg_run]
  · rw [movReg_run,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by decide)]

def branchBUpperExact (_logLen _hiBase _sink : Nat) : List AInstr :=
  branchBRegUpperStage ++ doubleExactCeilProduct

def upperFoldBExact (logLen hiBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBUpperExact logLen hiBase sink ++ movReg rX rProd ++
    tailEqOneToC ++ selectIntoY

def upperFoldAExact : List AInstr :=
  branchAUpperExact ++ movReg rX rProd ++ restEqOneToC ++ selectIntoY

def upperEndpointExactBlock (logLen hiBase sink gammaHi : Nat) : List AInstr :=
  upperFoldBExact logLen hiBase sink ++ upperFoldAExact ++ upperEndpointTail gammaHi

theorem branchALowerExact_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rPHi)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rPHi) (s.regs rPHi) < M) :
    (arun k s branchALowerExact).regs rProd =
      Section413Cells.encodeZ
        (-((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchAStage_run k s
  have hw' : ∀ j, (arun k s branchAStage).regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k branchAStage s hw haW).1
  rw [branchALowerExact, arun_append,
    negExactCeilProduct_run k _ hw'
      (by rw [ha, hb]; exact hfit) (by rw [ha, hb]; exact hout), ha, hb]

theorem branchBLowerExact_run (k : Nat) (s : AState)
    (logLen loBase sink : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rQLo)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rPLo) (s.regs rQLo) < M) :
    (arun k s (branchBLowerExact logLen loBase sink)).regs rProd =
      Section413Cells.encodeZ
        (2 * ((mulLower (s.regs rPLo) (s.regs rQLo) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchBRegLowerStage_run k s
  have hw' : ∀ j, (arun k s branchBRegLowerStage).regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      branchBRegLowerStage s hw haW).1
  rw [branchBLowerExact, arun_append,
    doubleExactFloorProduct_run k _ hw'
      (by rw [ha, hb]; exact hfit) (by rw [ha, hb]; exact hout), ha, hb]

theorem branchAUpperExact_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rPLo)).2 < 2 ^ 32)
    (hout : mulLower (s.regs rPLo) (s.regs rPLo) < M) :
    (arun k s branchAUpperExact).regs rProd =
      Section413Cells.encodeZ
        (-((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchAUpperStage_run k s
  have hw' : ∀ j, (arun k s branchAUpperStage).regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k branchAUpperStage s hw haW).1
  rw [branchAUpperExact, arun_append,
    negExactFloorProduct_run k _ hw'
      (by rw [ha, hb]; exact hfit) (by rw [ha, hb]; exact hout), ha, hb]

theorem branchBUpperExact_run (k : Nat) (s : AState)
    (logLen hiBase sink : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rQHi)).2 < 2 ^ 32)
    (hout : mulUpper (s.regs rPHi) (s.regs rQHi) < M) :
    (arun k s (branchBUpperExact logLen hiBase sink)).regs rProd =
      Section413Cells.encodeZ
        (2 * ((mulUpper (s.regs rPHi) (s.regs rQHi) : Nat) : Int)) := by
  obtain ⟨ha, hb⟩ := branchBRegUpperStage_run k s
  have hw' : ∀ j, (arun k s branchBRegUpperStage).regs j < M :=
    (LeanCompCert.Ports.Section413G1Denote.arun_lt k
      branchBRegUpperStage s hw haW).1
  rw [branchBUpperExact, arun_append,
    doubleExactCeilProduct_run k _ hw'
      (by rw [ha, hb]; exact hfit) (by rw [ha, hb]; exact hout), ha, hb]

set_option maxRecDepth 100000 in
theorem exactEndpointAssembly_wf (logLen loBase hiBase sink gammaLo gammaHi : Nat) :
    (lowerEndpointExactBlock logLen loBase sink gammaLo).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true ∧
      (upperEndpointExactBlock logLen hiBase sink gammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
  constructor <;> rfl

/-- **The complete extension**: every check the model performs that the current
artifact omits, both interval endpoints included.

⚠ ORDER, NOT JUST MEMBERSHIP.  This was previously
`candidateChecksV3 ++ upperEndpointBlock`, which put the UPPER endpoint's
accumulation *after* `intervalMagnitude` and `rowChecks` had already consumed
the magnitude.  `rAccHi` then lagged `rAccLo` by a full candidate at every
checkpoint, so `intervalAbsUpper rLo rHi` was taken over a mismatched pair.

The model computes `I`, accumulates BOTH endpoints, updates `weightedAbs`, and
only then evaluates `rowAt`.  The emitted sequence has to do the same, so
`candidateChecksFull` is spelled out here rather than layered on `V3` --
`V3` remains as a diagnostic prefix only, and is no longer a prefix of the
artifact. -/
def candidateChecksFull (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower
    logLen loBase hiBase sink egammaLo egammaHi : Nat) : List AInstr :=
  candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++
    lowerEndpointExactBlock logLen loBase sink egammaLo ++
    upperEndpointExactBlock logLen hiBase sink egammaHi ++
    weightedStep ++
    intervalMagnitude ++ rowWitnessCompute ++ rowWitnessCheck ++ commitBad ++
    movReg rX rAccW ++ rowChecks

/-! ## Well-formedness is monotone in `regCount`

The sweep's own `init`/`body`/`epilogue` are proved well formed at 260; the
extended program uses 261.  A larger register file only weakens the constraint,
so the existing proofs transfer — but that needs saying, and the `Bool` version
was missing (`Instr.WF_mono` covers the `Prop` version only).

This is what makes the `regCount` bump cheap: nothing about the sweep has to be
re-proved. -/
theorem operandWFB_mono {r r' : Nat} (h : r ≤ r') {o : LeanCompCert.Verified.Reflect.Operand}
    (ho : LeanCompCert.Ports.ArraySegSieve.operandWFB r o = true) :
    LeanCompCert.Ports.ArraySegSieve.operandWFB r' o = true := by
  cases o with
  | reg i =>
      simp only [LeanCompCert.Ports.ArraySegSieve.operandWFB,
        decide_eq_true_eq] at ho ⊢
      omega
  | lit _ => rfl
  | idx => rfl

theorem instrWFB_mono {r r' : Nat} (h : r ≤ r') {i : LeanCompCert.Verified.Reflect.Instr}
    (hi : LeanCompCert.Ports.ArraySegSieve.instrWFB r i = true) :
    LeanCompCert.Ports.ArraySegSieve.instrWFB r' i = true := by
  cases i with
  | mov d sO =>
      simp only [LeanCompCert.Ports.ArraySegSieve.instrWFB, Bool.and_eq_true,
        decide_eq_true_eq] at hi ⊢
      exact ⟨by omega, operandWFB_mono h hi.2⟩
  | binop d op l rr =>
      simp only [LeanCompCert.Ports.ArraySegSieve.instrWFB, Bool.and_eq_true,
        decide_eq_true_eq] at hi ⊢
      exact ⟨⟨by omega, operandWFB_mono h hi.1.2⟩, operandWFB_mono h hi.2⟩

theorem ainstrWFB_mono {r r' : Nat} (h : r ≤ r') {a : AInstr}
    (ha : LeanCompCert.Ports.ArraySegSieve.ainstrWFB r a = true) :
    LeanCompCert.Ports.ArraySegSieve.ainstrWFB r' a = true := by
  cases a with
  | scalar i => exact instrWFB_mono h ha
  | load d i =>
      simp only [LeanCompCert.Ports.ArraySegSieve.ainstrWFB, Bool.and_eq_true,
        decide_eq_true_eq] at ha ⊢
      exact ⟨by omega, by omega⟩
  | store i sR =>
      simp only [LeanCompCert.Ports.ArraySegSieve.ainstrWFB, Bool.and_eq_true,
        decide_eq_true_eq] at ha ⊢
      exact ⟨by omega, by omega⟩

theorem all_ainstrWFB_mono {r r' : Nat} (h : r ≤ r') {l : List AInstr}
    (hl : l.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB r) = true) :
    l.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB r') = true := by
  rw [List.all_eq_true] at hl ⊢
  exact fun a ha => ainstrWFB_mono h (hl a ha)

set_option maxRecDepth 200000 in
theorem candidateChecksFull_wf (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    (candidateChecksFull gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower logLen loBase hiBase sink egammaLo egammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
  rw [candidateChecksFull, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append,
    all_ainstrWFB_mono (show 327 ≤ 340 by decide)
      (candidateChecksV2_wf gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower),
    all_ainstrWFB_mono (show 327 ≤ 340 by decide) pLogRecompute_wf,
    (exactEndpointAssembly_wf logLen loBase hiBase sink egammaLo egammaHi).1,
    (exactEndpointAssembly_wf logLen loBase hiBase sink egammaLo egammaHi).2]
  rfl

/-! ## The extended program

`LambdaPsiSweep.program` with the checks spliced in: the flag and the three
accumulators seeded to zero, `candidateChecksFull` appended to the body, the
flag stored in the epilogue, and `output` repointed at it.

⚠ A NEW definition — the live `program` is untouched, so the current artifact
and receipt stay valid.  This is what gets emitted and re-run. -/
/-! ### The candidate-step gate

⚠ THE BODY IS NOT ONE CANDIDATE.  `loopCount` is `period * segCount` =
426,020,600, while the model's `run` folds over `c.len` = 99,990,000
candidates: the schedule interleaves marking steps with candidate steps, about
4.26 machine iterations per candidate.

The host sweep survives this because its candidate arithmetic ADDS ZERO on a
marking step -- `lamL`/`lamU` are 0 there, so accumulating is a no-op.  A
predicate has no such neutral element.  Committing `shapeOK` on a marking step
reads shape registers that hold cleared or half-decoded values and reports a
violation for a candidate that was never examined; that is exactly what the
first extended artifact did, returning 1 where the model returns 0.

The gate is taken from the sieve's OWN candidate counter `rSeen`, not from a
transcribed notion of "which iteration is a candidate": snapshot it before the
body, compare after, and the bit is 1 exactly on the steps the model takes.
Because it wraps the whole check suite in a select on `rViol`, no individual
block changes and no block lemma is invalidated. -/

/-- The sieve's own candidate counter (`ShapeSieveMark.rSeen`). -/
def sSeen : Nat := 9

def rViolSave : Nat := 307
def rAccWSave : Nat := 318
def rAccLoSave : Nat := 319
def rAccHiSave : Nat := 320
def rStep : Nat := 308
def rPrevSeen : Nat := 309

/-- Before the host body: snapshot the candidate counter and the verdict. -/
def candidateGatePre : List AInstr :=
  movReg rPrevSeen sSeen ++ movReg rViolSave rViol ++
    movReg rLogLPre sLogL ++ movReg rLogUPre sLogU ++
    movReg rAccWSave rAccW ++ movReg rAccLoSave rAccLo ++
    movReg rAccHiSave rAccHi

/-- After the host body: `rStep = 1` iff this iteration consumed a candidate. -/
def candidateGateStep : List AInstr :=
  [ .scalar (.binop rStep .ne (.reg sSeen) (.reg rPrevSeen)) ]

/-- `dst := if rStep = 1 then dst else save` -- one gated commit. -/
def gateBack (dst save : Nat) : List AInstr :=
  movReg rC rStep ++ movReg rX dst ++ movReg rY save ++
    selectBlock ++ movReg dst rSel

/-- After the checks: keep this iteration's updates only on a candidate step.

⚠ THE ACCUMULATORS NEED THIS AS MUCH AS THE VERDICT.  `rAccW`, `rAccLo` and
`rAccHi` are running sums the model advances ONCE PER CANDIDATE; left ungated
they advance on all 426,020,600 body iterations, roughly 4.26x too often.  The
error is one-sided -- the row bound `10000 * (K * weightedAbs + ...) <= ...`
only gets harder to satisfy -- so it can never make the artifact *falsely*
accept.  It would still be the wrong number, and `denote = value productionCfg`
is an equality, so a one-sided error is fatal to the denotation even where it
is harmless to the verdict. -/
def candidateGatePost : List AInstr :=
  gateBack rViol rViolSave ++ gateBack rAccW rAccWSave ++
    gateBack rAccLo rAccLoSave ++ gateBack rAccHi rAccHiSave

/-- ⚠ `rTwoB` is READ by `seamPsiBlock` and written NOWHERE else in this file.
It holds the loop-invariant constant `2 * scale` against which the seam test
`psiU ≤ 2 * n * scale` is decided in quotient/remainder form.  Seeding it here
is not an optimisation: without it the register is 0 for the entire run and
the seam test compares `psiU`'s quotient against zero, which is not the
intended predicate and is not a conservative substitute for it either. -/
def initV2 (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed) : List AInstr :=
  LambdaPsiSweep.init c sd ++
    movLit rViol 0 ++ movLit rAccW 0 ++ movLit rAccLo 0 ++ movLit rAccHi 0 ++
    movLit rTwoB (2 * scale)

def bodyV2 (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  candidateGatePre ++ LambdaPsiSweep.body c ++ candidateGateStep ++
    candidateChecksFull gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower logLen loBase hiBase sink egammaLo egammaHi ++
    candidateGatePost

/-- **Fold the underlying sweep's own guard count into the verdict.**

`programV2.output` is `rViol`, which accumulates only the *candidate* checks
added here.  The original `LambdaPsiSweep.program` returned
`ShapeSieve.outputReg` (register 8), its shape/marking guard count -- and V1's
driver tested exactly that.  Without this fold the extended artifact would
return 0 on a run whose factor table was silently truncated, because the new
checks say nothing about the sieve that feeds them.  `.gt _ 0` first
normalises the count to a bit, so `rViol` stays boolean and the driver's
`r == 0` test covers both halves. -/
def foldSweepGuard : List AInstr :=
  [ .scalar (.binop rBad .gt (.reg ShapeSieve.outputReg) (.lit 0))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

def epilogueV2 (c : LambdaPsiSweep.Cfg) : List AInstr :=
  LambdaPsiSweep.epilogue c ++ foldSweepGuard ++ LambdaPsiSweep.storeResult c 6 rViol

theorem initV2_all (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed) :
    (initV2 c sd).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
  rw [initV2, List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append,
    all_ainstrWFB_mono (by decide) (LambdaPsiSweep.init_all c sd)]
  rfl

set_option maxRecDepth 200000 in
theorem bodyV2_all (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    (bodyV2 c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
  rw [bodyV2, List.all_append, List.all_append, List.all_append,
    List.all_append,
    all_ainstrWFB_mono (by decide) (LambdaPsiSweep.body_all c),
    candidateChecksFull_wf]
  rfl

theorem epilogueV2_all (c : LambdaPsiSweep.Cfg) :
    (epilogueV2 c).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 340) = true := by
  rw [epilogueV2, List.all_append, List.all_append,
    all_ainstrWFB_mono (by decide) (LambdaPsiSweep.epilogue_all c)]
  rfl

/-- **The extended program.**  Same sweep, same loop count, same array — with
every check the model performs now emitted, the verdict accumulated in `rViol`,
and `output` pointing at it instead of the classifier's guard counter -- into
which `foldSweepGuard` has folded that guard counter, so nothing the original
artifact tested is lost. -/
def programV2 (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
     logLen loBase hiBase sink egammaLo egammaHi : Nat) : AProgram :=
  { regCount := 340
    -- ⚠ ONE MORE CELL than the original.  `Cfg.arrayLen = resultBase + 6`, and
    -- the six existing results occupy slots 0-5, so the verdict's
    -- `storeResult c 6 rViol` writes to `resultBase + 6` = the original
    -- `arrayLen` — one past the end.  Emitting without this widening would
    -- store the verdict out of bounds.
    arrayLen := c.arrayLen + 1
    loopCount := c.shape.period * c.shape.segCount
    init := initV2 c sd
    body := bodyV2 c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi
    epilogue := epilogueV2 c
    output := rViol }

/-- **The extended program is well formed**, so it compiles and emits by the
same verified path as the original. -/
theorem programV2_wf (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
     logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (programV2 c sd gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).WF :=
  ⟨(show rViol < 340 by decide),
   LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all (initV2_all c sd),
   LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all
     (bodyV2_all c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
       logLen loBase hiBase sink egammaLo egammaHi),
   LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all (epilogueV2_all c)⟩

/-! ## Register allocation, machine-checked

Every block in this file was proved against an arbitrary starting `AState`, so
each one stays true no matter what else uses its registers -- an isolation
proof cannot see a clobber.  That is not hypothetical, and the earlier version
of this section got it wrong in a way that only a RUN exposed.

The first attempts placed `rTwoB` at 212 (the sweep's `rT0` scratch) and then
at 224 (`rMx` below); both builds were green.  The guard added in response
asked `206 ≤ r ∧ r ≠ 212` -- a HAND-ENUMERATED list of the host sweep's
registers.  That list was wrong.  `LambdaPsiSweep.regCount` is 260, so the
sweep's well-formedness permits it to write *any* register below 260, and it
does: the emitted C shows the quotient/remainder carry using 217-238 as
scratch every iteration.  `rViol` sat at 233, inside that range, so the
verdict was overwritten on every one of the 426,020,600 trips.  The artifact
compiled, ran, and returned `281470071170241` instead of `0`.

The fix is not a longer exclusion list.  It is to place every register this
file owns strictly ABOVE the sweep's whole register file, and to state that as
the guard -- against `LambdaPsiSweep.regCount` itself, so it tracks if the
sweep ever grows, rather than against numbers transcribed by hand. -/

/-- Every register this file allocates for itself.  `rQ`/`rR` are deliberately
absent: they ARE the sweep's `rPsiUQ`/`rPsiUR`, read in place. -/
def seamBlockRegs : List Nat :=
  [rA, rB, rF, rG, rD1, rD2, rOut, rMx, rBad,
   rTwoB, rT1, rT2, rT3, rViol,
   rIL, rIU, rGL, rGU, rSave, rT4, rT5, rSh1, rSh2, rProd,
   rC, rX, rY, rSelT1, rSelT2, rSel, rGuard,
   rQsPExp, rQsLp, rQsLogU, rQsRest, rQsQ,
   rPowAcc, rPowP, rPowE, rShR,
   rAccW, rAccLo, rAccHi, rViolSave, rStep, rPrevSeen,
   rLogLPre, rLogUPre, rAccWSave, rAccLoSave, rAccHiSave,
   rIlo, rIhi, rWmag, rWq, rPLo, rPHi]

theorem seamBlockRegs_nodup : seamBlockRegs.Nodup := by
  decide

/-- **The allocation guard.**  Stated against `LambdaPsiSweep.regCount`, not
against transcribed numbers: anything below it may be clobbered by the host
sweep on the next iteration, which is exactly the bug this replaces. -/
theorem seamBlockRegs_above_sweep :
    seamBlockRegs.all
      (fun r => decide (LambdaPsiSweep.regCount ≤ r)) = true := by
  decide

/-- The guard REFUSES the allocation that shipped the broken artifact:
`rViol` at 233 is below the sweep's register file. -/
theorem seamBlockRegs_above_sweep_negative :
    ([233] : List Nat).all
      (fun r => decide (LambdaPsiSweep.regCount ≤ r)) = false := by
  decide

/-- And it refuses the whole 217-238 window the sweep's carry uses as
scratch, not just the one register that happened to break. -/
theorem seamBlockRegs_above_sweep_negative_window :
    (List.range' 217 22).all
      (fun r => decide (LambdaPsiSweep.regCount ≤ r)) = false := by
  decide

/-- Every register this file owns fits the extended program's register file. -/
theorem seamBlockRegs_lt_regCount :
    seamBlockRegs.all (fun r => decide (r < 327)) = true := by
  decide

end LeanCompCert.Ports.RamareCombined100M.SeamBlock
