import LeanCompCert.Ports.RamareCombined100MWideRow
import LeanCompCert.Ports.CDEMAbelIndexIndependence

/-!
# Wide production candidate program

This is the rerun target for the combined Ramaré suffix.  It retains the
verified sieve/classifier body, adds every candidate predicate, seeds all
three Lemma 7.1 accumulators from the certified prefix, and represents the two
signed endpoint sums with two limbs.  The definitions here are generic in the
production constants so the bridge and emitter share one program value.

The old receipted program remains untouched.  Selecting this program as the
live target requires a new receipt because its emitted digest is different.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-- The executable shape body depends only on the physical fields listed
here.  In particular it is independent of `lo`, `segCount`, and `tableHi`.
Keeping this dependency theorem at the program boundary lets downstream shard
proofs reuse one body without normalizing the generated prime table. -/
theorem Cfg.body_eq_of_fields (c d : Cfg)
    (hmark : c.markSteps = d.markSteps)
    (hlen : c.segLen = d.segLen)
    (hhi : c.hi = d.hi)
    (htableLen : c.table.length = d.table.length)
    (hhead : c.table.headD 1 = d.table.headD 1) :
    c.body = d.body := by
  set_option maxRecDepth 100000 in
    simp only [Cfg.body, Cfg.markBody, Cfg.markPhaseBody, Cfg.markCoreBody,
      Cfg.markResetBody, Cfg.markAddressBody, Cfg.markAdvanceBody,
      Cfg.markAdvanceSelectBody, Cfg.markAdvancePowerBody,
      Cfg.markAdvancePiBody, Cfg.markAdvanceLoadBody,
      Cfg.markAdvanceCursorBody, Cfg.markAdvanceOffsetBody,
      Cfg.markBudgetBody, Cfg.classBody, Cfg.classIndexBody,
      Cfg.classPostCandidateBody, Cfg.classOffsetBody,
      Cfg.classPlaneBody, Cfg.classSinkBody, Cfg.tailBody,
      Cfg.period, Cfg.tableLen, Cfg.tableBase, Cfg.sink,
      hmark, hlen, hhi, htableLen, hhead]

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert.Ports.RamareCombined100M

/-- Compact dependency boundary for the combined arithmetic body.  The log
table payload is initializer data; only its derived layout constants occur in
the repeated body. -/
theorem body_eq_of_fields (c d : Cfg)
    (hshape : c.shape.body = d.shape.body)
    (hlogLen : c.logLen = d.logLen)
    (hlo : c.logLoBase = d.logLoBase)
    (hhi : c.logHiBase = d.logHiBase)
    (hsink : c.logSink = d.logSink) :
    body c = body d := by
  simp only [body, LogSweep.body, candidateBody, selectionBody,
    hshape, hlogLen, hlo, hhi, hsink]

end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

namespace LeanCompCert.Ports.RamareCombined100M.ProgramV3

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RamareCombined100M.SeamBlock
open LeanCompCert.Ports.RamareCombined100M.WideEndpoint
open LeanCompCert.Ports.RamareCombined100M.WideMagnitude
open LeanCompCert.Ports.RamareCombined100M.WideRow

def rAccLoHiSave : Nat := 356
def rAccHiHiSave : Nat := 357

/-! Registers `358..365` snapshot the host arithmetic carry.  They are part
of the fail-closed candidate gate, not additional computation: marking rounds
restore these words structurally, while consumed-candidate rounds retain the
host transition.  This avoids relying on inactive division-by-zero behavior
to prove that a marking round is an arithmetic no-op. -/

def rHostLogLSave : Nat := 358
def rHostLogUSave : Nat := 359
def rHostSumLSave : Nat := 360
def rHostSumUSave : Nat := 361
def rHostPsiLQSave : Nat := 362
def rHostPsiLRSave : Nat := 363
def rHostPsiUQSave : Nat := 364
def rHostPsiURSave : Nat := 365

/-- Scratch word used only by the final host-arithmetic carry checks. -/
def rHostCheckTmp : Nat := 366

/-! The host rebases its persistent psi pairs from denominator `n` to
`n + 1`.  The source seam and corrected-integer predicates, however, are
about `psi(n) / n`.  These scratch words reconstruct that current-denominator
pair from the saved entry pair and the selected lambda, without ever forming
the unbounded psi value. -/
def rPsiAtNTmpL : Nat := 367
def rPsiAtNLQ : Nat := 368
def rPsiAtNTmpU : Nat := 369
def rPsiAtNUQ : Nat := 370
def rPsiAtNUR : Nat := 371
/-- Bit and result scratch words for the corrected upper-ceiling audit. -/
def rSourceCheckBit : Nat := 372
def rSourceCheckResult : Nat := 373

/-- Fail closed unless a monotone modular update retained its old value. -/
def monotoneCarryCheck (current saved : Nat) : List AInstr :=
  [ .scalar (.binop rBad .lt (.reg current) (.reg saved)) ] ++ commitBad

/-- Fail closed unless `saved + addend` is an exact word addition. -/
def addCarryCheckAt (scratch saved addend : Nat) : List AInstr :=
  [ .scalar (.binop scratch .add (.reg saved) (.reg addend))
  , .scalar (.binop rBad .lt (.reg scratch) (.reg saved)) ] ++ commitBad

def psiAddCarryCheck (saved addend : Nat) : List AInstr :=
  addCarryCheckAt rHostCheckTmp saved addend

/-- Literal-addition companion used for the two fixed gamma offsets. -/
def literalAddCarryCheck (saved addend : Nat) : List AInstr :=
  [ .scalar (.binop rHostCheckTmp .add (.reg saved) (.lit addend))
  , .scalar (.binop rBad .lt (.reg rHostCheckTmp) (.reg saved)) ] ++ commitBad

/-- Audit `logU + qU + (rU > 0)` without assuming that either modular
addition was exact.  Both carry guards are retained in the signed artifact. -/
def upperCeilCarryCheck (qU rU : Nat) : List AInstr :=
  psiAddCarryCheck rLogUPre qU ++
    [ .scalar (.binop rSourceCheckBit .gt (.reg rU) (.lit 0)) ] ++
    addCarryCheckAt rSourceCheckResult rHostCheckTmp rSourceCheckBit

/-- Reconstruct `psiL' / n`, `psiU' / n`, and `psiU' % n` from the saved
entry pairs.  The sticky carry checks make both additions fail closed.

The physical body also executes this block during marking rounds, when
`sCand = 0`.  Normalize each machine divisor to `sCand + (sCand = 0)` before
using it: this is `n` on a candidate round and `1` on a marking round.  The
gate restores all candidate-owned results on marking rounds, while the
normalization keeps CompCert's partial `udiv`/`urem` semantics defined. -/
def currentPsiAtNStage : List AInstr :=
  [ .scalar (.binop rPsiAtNTmpL .add (.reg rHostPsiLRSave)
      (.reg LambdaPsiSweep.rLamL))
  , .scalar (.binop rBad .lt (.reg rPsiAtNTmpL)
      (.reg rHostPsiLRSave)) ] ++ commitBad ++
  [ .scalar (.binop rPsiAtNLQ .eq (.reg sCand) (.lit 0))
  , .scalar (.binop rPsiAtNLQ .add (.reg rPsiAtNLQ) (.reg sCand))
  , .scalar (.binop rPsiAtNLQ .udiv (.reg rPsiAtNTmpL) (.reg rPsiAtNLQ))
  , .scalar (.binop rPsiAtNLQ .add (.reg rHostPsiLQSave)
      (.reg rPsiAtNLQ))
  , .scalar (.binop rBad .lt (.reg rPsiAtNLQ)
      (.reg rHostPsiLQSave)) ] ++ commitBad ++
  [ .scalar (.binop rPsiAtNTmpU .add (.reg rHostPsiURSave)
      (.reg LambdaPsiSweep.rLamU))
  , .scalar (.binop rBad .lt (.reg rPsiAtNTmpU)
      (.reg rHostPsiURSave)) ] ++ commitBad ++
  [ .scalar (.binop rPsiAtNUQ .eq (.reg sCand) (.lit 0))
  , .scalar (.binop rPsiAtNUQ .add (.reg rPsiAtNUQ) (.reg sCand))
  , .scalar (.binop rPsiAtNUR .urem (.reg rPsiAtNTmpU) (.reg rPsiAtNUQ))
  , .scalar (.binop rPsiAtNUQ .udiv (.reg rPsiAtNTmpU) (.reg rPsiAtNUQ))
  , .scalar (.binop rPsiAtNUQ .add (.reg rHostPsiUQSave)
      (.reg rPsiAtNUQ))
  , .scalar (.binop rBad .lt (.reg rPsiAtNUQ)
      (.reg rHostPsiUQSave)) ] ++ commitBad

/-- Corrected-integer row followed by a fixed carry audit of every natural
addition used by its source denotation.  Keeping the audit as a suffix lets
the old row theorem remain a literal prefix theorem. -/
def correctedRowCheckedAt (qL qU rU gammaLo gammaHi bound lower : Nat) :
    List AInstr :=
  correctedRowAt qL qU rU gammaLo gammaHi bound lower ++
    psiAddCarryCheck rLogLPre qL ++ upperCeilCarryCheck qU rU ++
    literalAddCarryCheck sSumL gammaLo ++
    literalAddCarryCheck sSumU gammaHi

/-- Final anchor row followed by carry audits of both gamma additions. -/
def anchorRowChecked (gammaLo gammaHi bound limit : Nat) : List AInstr :=
  anchorRow gammaLo gammaHi bound limit ++
    literalAddCarryCheck sSumL gammaLo ++
    literalAddCarryCheck sSumU gammaHi

/-- V3's source-facing fixed rows.  Unlike the legacy standalone V2 block,
the seam and corrected rows consume pairs represented at the source
denominator `n`, not the host's already-rebased `n + 1` carry. -/
def candidateChecksV2 (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower : Nat) : List AInstr :=
  SeamBlock.candidateChecksV1 ++ currentPsiAtNStage ++
    seamPsiBlockAt rPsiAtNUQ rPsiAtNUR rTwoB ++
    correctedRowCheckedAt rPsiAtNLQ rPsiAtNUQ rPsiAtNUR
      cgammaLo cgammaHi cbound lower ++
    anchorRowChecked gammaLo gammaHi bound limit

def rowWideSite (at_ bound : Nat) : List AInstr :=
  rowWideCheck bound ++ eqGuardedCommit at_

def rowWideChecks : List AInstr :=
  rowWideSite 462848 697945070501 ++
    rowWideSite 1000000 787520908427 ++
    rowWideSite 10000000 1080508544974 ++
    rowWideSite 100000000 1422016427065

/-- Fail closed if the single-word weighted accumulator wrapped during the
current candidate.  `gatePre` saved the old accumulator in `rAccWSave`, and
the update is monotone before reduction modulo `M`, so a smaller result is
exactly the carry bit. -/
def weightedOverflowCheck : List AInstr :=
  [ .scalar (.binop rBad .lt (.reg rAccW) (.reg rAccWSave)) ] ++ commitBad

/-! ## Fail-closed checks for the legacy host arithmetic

The original lambda/psi body uses word additions.  Its denotation theorem
therefore has explicit no-wrap premises.  V3 checks those premises inside the
compiled computation instead of asking Lean to establish a production-length
analytic headroom induction.

For an addition `old + increment`, with both inputs already machine words,
the modular result is smaller than `old` exactly when the addition carries.
The psi quotient transition needs only the corresponding remainder-plus-
lambda check: once that sum is below `M`, `PsiQR.advance.q` is automatically
below `M` as well.
-/

/-- Six constant-cost checks covering every genuinely cumulative premise of
the unchanged host log/sum/psi arithmetic. -/
def hostArithmeticOverflowChecks : List AInstr :=
  monotoneCarryCheck LogSweep.rLogL rHostLogLSave ++
    monotoneCarryCheck LogSweep.rLogU rHostLogUSave ++
    monotoneCarryCheck LambdaPsiSweep.rSumL rHostSumLSave ++
    monotoneCarryCheck LambdaPsiSweep.rSumU rHostSumUSave ++
    psiAddCarryCheck rHostPsiLRSave LambdaPsiSweep.rLamL ++
    psiAddCarryCheck rHostPsiURSave LambdaPsiSweep.rLamU

/-- Soundness of one guarded wide checkpoint, including the sticky-flag
commit.  The theorem is symbolic: `at_` and `bound` remain variables and no
production candidate is evaluated. -/
theorem rowWideSite_sound (k : Nat) (s : AState) (at_ bound : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M)
    (hat : at_ < M) (hcand : s.regs sCand = at_)
    (hviol : s.regs rViol = 0)
    (hzero : (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (rowWideSite at_ bound)).regs rViol = 0) :
    s.regs rAccW + 1 ≤ bound ∧
      LeanCompCert.Verified.AddWide.wval (s.regs rMaxLo, s.regs rMaxHi) ≤
        s.regs sCand * (bound - (s.regs rAccW + 1)) := by
  let checked := LeanCompCert.Verified.ArrayFoldBridge.arun k s
    (rowWideCheck bound)
  have hbad : checked.regs rBad = 0 ∨ checked.regs rBad = 1 :=
    rowWideCheck_bad_bit k s bound hw haW hsum hbound
  have hcand' : checked.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hviol' : checked.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hcommit := eqGuardedCommit_run k checked at_ hbad hat
  have hbadZero : checked.regs rBad = 0 := by
    rcases hbad with hb | hb
    · exact hb
    · exfalso
      rw [rowWideSite, LeanCompCert.Verified.ArrayFoldBridge.arun_append]
        at hzero
      rw [hcommit, hcand', hviol', hcand, hviol, hb] at hzero
      have hone : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by decide)
      simp [hone] at hzero
  exact rowWideCheck_sound k s bound hw haW hsum hbound hbadZero

/-- A nonmatching checkpoint leaves the sticky flag unchanged.  The wide
arithmetic still runs, but the equality guard makes its result observationally
irrelevant. -/
theorem rowWideSite_rViol_of_ne (k : Nat) (s : AState) (at_ bound : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsum : s.regs rAccW + 1 < M) (hbound : bound < M)
    (hat : at_ < M) (hcand : s.regs sCand ≠ at_) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (rowWideSite at_ bound)).regs rViol = s.regs rViol := by
  let checked := LeanCompCert.Verified.ArrayFoldBridge.arun k s
    (rowWideCheck bound)
  have hbad : checked.regs rBad = 0 ∨ checked.regs rBad = 1 :=
    rowWideCheck_bad_bit k s bound hw haW hsum hbound
  have hcand' : checked.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hviol' : checked.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  rw [rowWideSite, LeanCompCert.Verified.ArrayFoldBridge.arun_append,
    eqGuardedCommit_run k checked at_ hbad hat, hcand', hviol']
  have hmod : s.regs rViol % M = s.regs rViol := Nat.mod_eq_of_lt (hw rViol)
  simp [hcand, hmod]

/-- All four guarded checkpoints as a single reusable contract.  A zero
sticky flag yields the division-free row condition at whichever literal
checkpoint matches the current candidate. -/
theorem rowWideChecks_sound (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsum : s.regs rAccW + 1 < M) (hviol : s.regs rViol = 0)
    (hzero : (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      rowWideChecks).regs rViol = 0) :
    (s.regs sCand = 462848 →
      s.regs rAccW + 1 ≤ 697945070501 ∧
        LeanCompCert.Verified.AddWide.wval
            (s.regs rMaxLo, s.regs rMaxHi) ≤
          s.regs sCand * (697945070501 - (s.regs rAccW + 1))) ∧
    (s.regs sCand = 1000000 →
      s.regs rAccW + 1 ≤ 787520908427 ∧
        LeanCompCert.Verified.AddWide.wval
            (s.regs rMaxLo, s.regs rMaxHi) ≤
          s.regs sCand * (787520908427 - (s.regs rAccW + 1))) ∧
    (s.regs sCand = 10000000 →
      s.regs rAccW + 1 ≤ 1080508544974 ∧
        LeanCompCert.Verified.AddWide.wval
            (s.regs rMaxLo, s.regs rMaxHi) ≤
          s.regs sCand * (1080508544974 - (s.regs rAccW + 1))) ∧
    (s.regs sCand = 100000000 →
      s.regs rAccW + 1 ≤ 1422016427065 ∧
        LeanCompCert.Verified.AddWide.wval
            (s.regs rMaxLo, s.regs rMaxHi) ≤
          s.regs sCand * (1422016427065 - (s.regs rAccW + 1))) := by
  let b1 := rowWideSite 462848 697945070501
  let b2 := rowWideSite 1000000 787520908427
  let b3 := rowWideSite 10000000 1080508544974
  let b4 := rowWideSite 100000000 1422016427065
  let s1 := LeanCompCert.Verified.ArrayFoldBridge.arun k s b1
  let s2 := LeanCompCert.Verified.ArrayFoldBridge.arun k s1 b2
  let s3 := LeanCompCert.Verified.ArrayFoldBridge.arun k s2 b3
  let s4 := LeanCompCert.Verified.ArrayFoldBridge.arun k s3 b4
  have hout : LeanCompCert.Verified.ArrayFoldBridge.arun k s rowWideChecks = s4 := by
    simp only [rowWideChecks, b1, b2, b3, b4, s1, s2, s3, s4,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  have hz4 : s4.regs rViol = 0 := by rwa [hout] at hzero
  have hw1 := LeanCompCert.Verified.ArrayFoldBridge.arun_word k b1 s hw haW
  have hw2 := LeanCompCert.Verified.ArrayFoldBridge.arun_word k b2 s1 hw1.1 hw1.2
  have hw3 := LeanCompCert.Verified.ArrayFoldBridge.arun_word k b3 s2 hw2.1 hw2.2
  have hacc1 : s1.regs rAccW = s.regs rAccW :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccW b1 (by rfl) s
  have hacc2 : s2.regs rAccW = s1.regs rAccW :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccW b2 (by rfl) s1
  have hacc3 : s3.regs rAccW = s2.regs rAccW :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccW b3 (by rfl) s2
  have hsum1 : s1.regs rAccW + 1 < M := by rw [hacc1]; exact hsum
  have hsum2 : s2.regs rAccW + 1 < M := by rw [hacc2]; exact hsum1
  have hsum3 : s3.regs rAccW + 1 < M := by rw [hacc3]; exact hsum2
  have hc1 : s1.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand b1 (by rfl) s
  have hc2 : s2.regs sCand = s1.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand b2 (by rfl) s1
  have hc3 : s3.regs sCand = s2.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand b3 (by rfl) s2
  have framePair (t u : AState) (block : List AInstr)
      (heq : u = LeanCompCert.Verified.ArrayFoldBridge.arun k t block)
      (hlo : LeanCompCert.Verified.ArrayRegFrame.writes rMaxLo block = false)
      (hhi : LeanCompCert.Verified.ArrayRegFrame.writes rMaxHi block = false) :
      LeanCompCert.Verified.AddWide.wval (u.regs rMaxLo, u.regs rMaxHi) =
        LeanCompCert.Verified.AddWide.wval (t.regs rMaxLo, t.regs rMaxHi) := by
    subst u
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rMaxLo block hlo t,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rMaxHi block hhi t]
  have hp1 := framePair s s1 b1 (by rfl) (by rfl) (by rfl)
  have hp2 := framePair s1 s2 b2 (by rfl) (by rfl) (by rfl)
  have hp3 := framePair s2 s3 b3 (by rfl) (by rfl) (by rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have hf2 := rowWideSite_rViol_of_ne k s1 1000000 787520908427
      hw1.1 hw1.2 hsum1 (by decide) (by decide) (by rw [hc1, hc]; decide)
    have hf3 := rowWideSite_rViol_of_ne k s2 10000000 1080508544974
      hw2.1 hw2.2 hsum2 (by decide) (by decide)
      (by rw [hc2, hc1, hc]; decide)
    have hf4 := rowWideSite_rViol_of_ne k s3 100000000 1422016427065
      hw3.1 hw3.2 hsum3 (by decide) (by decide)
      (by rw [hc3, hc2, hc1, hc]; decide)
    have hz1 : s1.regs rViol = 0 := by rw [← hf2, ← hf3, ← hf4]; exact hz4
    exact rowWideSite_sound k s 462848 697945070501 hw haW hsum
      (by decide) (by decide) hc hviol hz1
  · intro hc
    have hf1 := rowWideSite_rViol_of_ne k s 462848 697945070501
      hw haW hsum (by decide) (by decide) (by rw [hc]; decide)
    have hf3 := rowWideSite_rViol_of_ne k s2 10000000 1080508544974
      hw2.1 hw2.2 hsum2 (by decide) (by decide)
      (by rw [hc2, hc1, hc]; decide)
    have hf4 := rowWideSite_rViol_of_ne k s3 100000000 1422016427065
      hw3.1 hw3.2 hsum3 (by decide) (by decide)
      (by rw [hc3, hc2, hc1, hc]; decide)
    have hz2 : s2.regs rViol = 0 := by rw [← hf3, ← hf4]; exact hz4
    have hs := rowWideSite_sound k s1 1000000 787520908427
      hw1.1 hw1.2 hsum1 (by decide) (by decide)
      (by rw [hc1, hc]) (by rw [hf1, hviol]) hz2
    simpa only [hacc1, hc1, hc, hp1] using hs
  · intro hc
    have hf1 := rowWideSite_rViol_of_ne k s 462848 697945070501
      hw haW hsum (by decide) (by decide) (by rw [hc]; decide)
    have hf2 := rowWideSite_rViol_of_ne k s1 1000000 787520908427
      hw1.1 hw1.2 hsum1 (by decide) (by decide)
      (by rw [hc1, hc]; decide)
    have hf4 := rowWideSite_rViol_of_ne k s3 100000000 1422016427065
      hw3.1 hw3.2 hsum3 (by decide) (by decide)
      (by rw [hc3, hc2, hc1, hc]; decide)
    have hz3 : s3.regs rViol = 0 := by rw [← hf4]; exact hz4
    have hs := rowWideSite_sound k s2 10000000 1080508544974
      hw2.1 hw2.2 hsum2 (by decide) (by decide)
      (by rw [hc2, hc1, hc]) (by rw [hf2, hf1, hviol]) hz3
    simpa only [hacc2, hacc1, hc2, hc1, hc, hp2, hp1] using hs
  · intro hc
    have hf1 := rowWideSite_rViol_of_ne k s 462848 697945070501
      hw haW hsum (by decide) (by decide) (by rw [hc]; decide)
    have hf2 := rowWideSite_rViol_of_ne k s1 1000000 787520908427
      hw1.1 hw1.2 hsum1 (by decide) (by decide)
      (by rw [hc1, hc]; decide)
    have hf3 := rowWideSite_rViol_of_ne k s2 10000000 1080508544974
      hw2.1 hw2.2 hsum2 (by decide) (by decide)
      (by rw [hc2, hc1, hc]; decide)
    have hs := rowWideSite_sound k s3 100000000 1422016427065
      hw3.1 hw3.2 hsum3 (by decide) (by decide)
      (by rw [hc3, hc2, hc1, hc]) (by rw [hf3, hf2, hf1, hviol]) hz4
    simpa only [hacc3, hacc2, hacc1, hc3, hc2, hc1, hc, hp3, hp2, hp1]
      using hs

/-- Unchanged candidate prefix through the weighted overflow audit. -/
def candidateChecksPreRowAudit (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++
    qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++
    weightedStep ++ weightedOverflowCheck

def candidateChecksPostRowAudit : List AInstr :=
  intervalMagnitudeWide ++ rowWideChecks

/-- The pre-audit program view is retained solely so large register-frame
scans remain stable when the tiny row-headroom check changes. -/
def candidateChecksWithoutRowAudit (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
    candidateChecksPostRowAudit

/-- Candidate-only extension in source order.  Cumulative arithmetic is
audited by the signed computation before any row consumes it. -/
def candidateChecks (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++
    weightedStep ++ weightedOverflowCheck ++ literalAddCarryCheck rAccW 1 ++
    intervalMagnitudeWide ++ rowWideChecks

set_option maxRecDepth 200000 in
/-- Word closure of the complete candidate suffix, cached beside its literal
instruction list.  Specializing the generic `arun_word` theorem directly in
a downstream proof embeds a proof term linear in this large list; this named
boundary makes every consumer constant-size. -/
theorem candidateChecks_word (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s checks
    (∀ j, out.regs j < M) ∧ ∀ j, out.arr j < M := by
  exact LeanCompCert.Verified.ArrayFoldBridge.arun_word k _ s hw ha

/-- One-pass destination check used to frame the gate registers.  Keeping the
seven comparisons in one predicate avoids normalizing the production check
list seven separate times. -/
def gateFrameSafe (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rStep i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rViolSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccWSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccLoSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccHiSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccLoHiSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccHiHiSave i

theorem writes_eq_false_of_forall_instrWrites {r : Nat} {l : List AInstr}
    (h : ∀ i ∈ l,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites r i = false) :
    LeanCompCert.Verified.ArrayRegFrame.writes r l = false := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [LeanCompCert.Verified.ArrayRegFrame.writes_cons,
        Bool.or_eq_false_iff]
      exact ⟨h i (by simp), ih (fun j hj => h j (by simp [hj]))⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- The candidate extension reads the saved weighted value for its overflow
check but never overwrites any gate snapshot or the step discriminator.  This
fact is packaged once so later proofs do not repeatedly normalize the large
instruction list. -/
theorem candidateChecks_gate_frames (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi
    (LeanCompCert.Verified.ArrayRegFrame.writes rStep checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rViolSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rAccWSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rAccLoSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rAccHiSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rAccLoHiSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rAccHiHiSave checks = false) := by
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsOld : old.all gateFrameSafe = true := by rfl
  have hs : checks.all gateFrameSafe = true := by
    have hdecomp : checks =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
      simp [checks, candidateChecks, candidateChecksPreRowAudit,
        candidateChecksPostRowAudit, List.append_assoc]
    have hsOld' := Bool.and_eq_true_iff.mp (by
      simpa only [old, candidateChecksWithoutRowAudit, List.all_append]
        using hsOld)
    rw [hdecomp, List.all_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hsOld'.1, by rfl⟩, hsOld'.2⟩
  rw [List.all_eq_true] at hs
  have hsafe (i : AInstr) (hi : i ∈ checks) :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rStep i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rViolSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccWSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccLoSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccHiSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccLoHiSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rAccHiHiSave i = false := by
    have hraw := hs i hi
    simp only [gateFrameSafe, Bool.and_eq_true] at hraw
    rcases hraw with ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    have notTrueFalse {b : Bool} (h : Bool.not b = true) : b = false := by
      cases b <;> simp_all
    exact ⟨notTrueFalse h1, notTrueFalse h2, notTrueFalse h3,
      notTrueFalse h4, notTrueFalse h5, notTrueFalse h6, notTrueFalse h7⟩
  exact
    ⟨writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2)⟩

/-! The endpoint denotation consumes thirteen read-only classifier/log-table
words.  Certify their frame in one pass here, beside the emitted block, so
downstream proofs do not independently normalize the full instruction list
thirteen times. -/
def candidateV2EndpointFrameSafe (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sCand i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeP i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapePE i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeRest i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeQ i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeQE i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeTail i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rLogLPre i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rLogUPre i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rOldL i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rOldU i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rTabL i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rTabU i

set_option maxRecDepth 200000 in
theorem candidateChecksV2_endpoint_frames (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower : Nat) :
    let checks := candidateChecksV2 gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower
    (LeanCompCert.Verified.ArrayRegFrame.writes sCand checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapeP checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapePE checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapeRest checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapeQ checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapeQE checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes sShapeTail checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rLogLPre checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rLogUPre checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rOldL checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rOldU checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rTabL checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rTabU checks = false) := by
  let checks := candidateChecksV2 gammaLo gammaHi bound limit cgammaLo
    cgammaHi cbound lower
  have hs : checks.all candidateV2EndpointFrameSafe = true := by rfl
  rw [List.all_eq_true] at hs
  have hsafe (i : AInstr) (hi : i ∈ checks) :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sCand i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeP i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapePE i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeRest i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeQ i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeQE i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites sShapeTail i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rLogLPre i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rLogUPre i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rOldL i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rOldU i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rTabL i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rTabU i = false := by
    have hraw := hs i hi
    simp only [candidateV2EndpointFrameSafe, Bool.and_eq_true] at hraw
    rcases hraw with
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩,
        h10⟩, h11⟩, h12⟩, h13⟩
    have notTrueFalse {b : Bool} (h : Bool.not b = true) : b = false := by
      cases b <;> simp_all
    exact ⟨notTrueFalse h1, notTrueFalse h2, notTrueFalse h3,
      notTrueFalse h4, notTrueFalse h5, notTrueFalse h6, notTrueFalse h7,
      notTrueFalse h8, notTrueFalse h9, notTrueFalse h10, notTrueFalse h11,
      notTrueFalse h12, notTrueFalse h13⟩
  exact
    ⟨writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2.2.2.2.2.2)⟩

/-- One-pass destination check for the host carry snapshots added around the
unchanged lambda/psi body.  This closed scan belongs beside the program
definition so downstream denotation proofs consume only cached equalities. -/
def hostCarryFrameSafe (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostLogLSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostLogUSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostSumLSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostSumUSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiLQSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiLRSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiUQSave i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiURSave i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem candidateChecks_hostCarry_frames (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi
    (LeanCompCert.Verified.ArrayRegFrame.writes rHostLogLSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostLogUSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostSumLSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostSumUSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostPsiLQSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostPsiLRSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostPsiUQSave checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes rHostPsiURSave checks = false) := by
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsOld : old.all hostCarryFrameSafe = true := by rfl
  have hs : checks.all hostCarryFrameSafe = true := by
    have hdecomp : checks =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
      simp [checks, candidateChecks, candidateChecksPreRowAudit,
        candidateChecksPostRowAudit, List.append_assoc]
    have hsOld' := Bool.and_eq_true_iff.mp (by
      simpa only [old, candidateChecksWithoutRowAudit, List.all_append]
        using hsOld)
    rw [hdecomp, List.all_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hsOld'.1, by rfl⟩, hsOld'.2⟩
  rw [List.all_eq_true] at hs
  have hsafe (i : AInstr) (hi : i ∈ checks) :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostLogLSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostLogUSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostSumLSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostSumUSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiLQSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiLRSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiUQSave i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rHostPsiURSave i = false := by
    have hraw := hs i hi
    simp only [hostCarryFrameSafe, Bool.and_eq_true] at hraw
    rcases hraw with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    have notTrueFalse {b : Bool} (h : Bool.not b = true) : b = false := by
      cases b <;> simp_all
    exact ⟨notTrueFalse h1, notTrueFalse h2, notTrueFalse h3,
      notTrueFalse h4, notTrueFalse h5, notTrueFalse h6,
      notTrueFalse h7, notTrueFalse h8⟩
  exact
    ⟨writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2.2.2)⟩

/-- One-pass destination check for the six host arithmetic results consumed
by the cumulative carry checks.  Caching this scan beside the literal
candidate verifier keeps downstream denotation proofs constant-size. -/
def hostArithmeticResultFrameSafe (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LogSweep.rLogL i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LogSweep.rLogU i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rSumL i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rSumU i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rLamL i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rLamU i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem candidateChecks_hostArithmeticResult_frames
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi
    (LeanCompCert.Verified.ArrayRegFrame.writes LogSweep.rLogL checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LogSweep.rLogU checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rSumL checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rSumU checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rLamL checks = false) ∧
      (LeanCompCert.Verified.ArrayRegFrame.writes LambdaPsiSweep.rLamU checks = false) := by
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsOld : old.all hostArithmeticResultFrameSafe = true := by rfl
  have hs : checks.all hostArithmeticResultFrameSafe = true := by
    have hdecomp : checks =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
      simp [checks, candidateChecks, candidateChecksPreRowAudit,
        candidateChecksPostRowAudit, List.append_assoc]
    have hsOld' := Bool.and_eq_true_iff.mp (by
      simpa only [old, candidateChecksWithoutRowAudit, List.all_append]
        using hsOld)
    rw [hdecomp, List.all_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hsOld'.1, by rfl⟩, hsOld'.2⟩
  rw [List.all_eq_true] at hs
  have hsafe (i : AInstr) (hi : i ∈ checks) :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LogSweep.rLogL i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LogSweep.rLogU i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rSumL i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rSumU i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rLamL i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites LambdaPsiSweep.rLamU i = false := by
    have hraw := hs i hi
    simp only [hostArithmeticResultFrameSafe, Bool.and_eq_true] at hraw
    rcases hraw with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    have notTrueFalse {b : Bool} (h : Bool.not b = true) : b = false := by
      cases b <;> simp_all
    exact ⟨notTrueFalse h1, notTrueFalse h2, notTrueFalse h3,
      notTrueFalse h4, notTrueFalse h5, notTrueFalse h6⟩
  exact
    ⟨writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2.2.2.2.2)⟩

/-- One-pass destination check for the host round/window registers. -/
def positionFrameSafe (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites ShapeSieve.rR i &&
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites ShapeSieve.rW i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem candidateChecks_position_frames
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi
    LeanCompCert.Verified.ArrayRegFrame.writes ShapeSieve.rR checks = false ∧
      LeanCompCert.Verified.ArrayRegFrame.writes ShapeSieve.rW checks = false := by
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsOld : old.all positionFrameSafe = true := by rfl
  have hs : checks.all positionFrameSafe = true := by
    have hdecomp : checks =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
      simp [checks, candidateChecks, candidateChecksPreRowAudit,
        candidateChecksPostRowAudit, List.append_assoc]
    have hsOld' := Bool.and_eq_true_iff.mp (by
      simpa only [old, candidateChecksWithoutRowAudit, List.all_append]
        using hsOld)
    rw [hdecomp, List.all_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hsOld'.1, by rfl⟩, hsOld'.2⟩
  rw [List.all_eq_true] at hs
  have hsafe (i : AInstr) (hi : i ∈ checks) :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites ShapeSieve.rR i = false ∧
      LeanCompCert.Verified.ArrayRegFrame.instrWrites ShapeSieve.rW i = false := by
    have hraw := hs i hi
    simp only [positionFrameSafe, Bool.and_eq_true] at hraw
    have notTrueFalse {b : Bool} (h : Bool.not b = true) : b = false := by
      cases b <;> simp_all
    exact ⟨notTrueFalse hraw.1, notTrueFalse hraw.2⟩
  exact ⟨writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).1),
      writes_eq_false_of_forall_instrWrites (fun i hi => (hsafe i hi).2)⟩

/-- Host registers whose values are needed by the physical marking,
classification, and live host-carry projections.  Candidate checks use only
the V3 extension and scratch register ranges, so they frame every register in
this list. -/
def shapeProjectionRegs : List Nat :=
  [ShapeSieve.rR, ShapeSieve.rW, ShapeSieve.rPi, ShapeSieve.rPow,
    ShapeSieve.rBase, ShapeSieve.rJ, 0, ShapeSieve.rViol, ShapeSieve.rVMark,
    ShapeSieve.rVShape, ShapeSieve.rSeen,
    LogSweep.rLogL, LogSweep.rLogU,
    LambdaPsiSweep.rSumL, LambdaPsiSweep.rSumU,
    LambdaPsiSweep.rPsiLQ, LambdaPsiSweep.rPsiLR,
    LambdaPsiSweep.rPsiUQ, LambdaPsiSweep.rPsiUR, rTwoB]

def shapeProjectionFrameSafe (i : AInstr) : Bool :=
  shapeProjectionRegs.all fun r =>
    !LeanCompCert.Verified.ArrayRegFrame.instrWrites r i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem candidateChecks_shape_frames
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi r : Nat)
    (hr : r ∈ shapeProjectionRegs) :
    LeanCompCert.Verified.ArrayRegFrame.writes r
      (candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
        lower logLen loBase hiBase sink egammaLo egammaHi) = false := by
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsOld : old.all shapeProjectionFrameSafe = true := by rfl
  have hs : checks.all shapeProjectionFrameSafe = true := by
    have hdecomp : checks =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
      simp [checks, candidateChecks, candidateChecksPreRowAudit,
        candidateChecksPostRowAudit, List.append_assoc]
    have hsOld' := Bool.and_eq_true_iff.mp (by
      simpa only [old, candidateChecksWithoutRowAudit, List.all_append]
        using hsOld)
    rw [hdecomp, List.all_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hsOld'.1, by rfl⟩, hsOld'.2⟩
  rw [List.all_eq_true] at hs
  apply writes_eq_false_of_forall_instrWrites
  intro i hi
  have hsafe := hs i hi
  simp only [shapeProjectionFrameSafe, List.all_eq_true] at hsafe
  have hnot := hsafe r hr
  cases h : LeanCompCert.Verified.ArrayRegFrame.instrWrites r i <;> simp_all

def hostCarryGatePre : List AInstr :=
  movReg rHostLogLSave LogSweep.rLogL ++
    movReg rHostLogUSave LogSweep.rLogU ++
    movReg rHostSumLSave LambdaPsiSweep.rSumL ++
    movReg rHostSumUSave LambdaPsiSweep.rSumU ++
    movReg rHostPsiLQSave LambdaPsiSweep.rPsiLQ ++
    movReg rHostPsiLRSave LambdaPsiSweep.rPsiLR ++
    movReg rHostPsiUQSave LambdaPsiSweep.rPsiUQ ++
    movReg rHostPsiURSave LambdaPsiSweep.rPsiUR

def gatePreCore : List AInstr :=
  candidateGatePre ++ movReg rAccLoHiSave rAccLoHi ++
    movReg rAccHiHiSave rAccHiHi

def gatePre : List AInstr :=
  hostCarryGatePre ++ gatePreCore

def hostCarryGatePost : List AInstr :=
  gateBack LogSweep.rLogL rHostLogLSave ++
    gateBack LogSweep.rLogU rHostLogUSave ++
    gateBack LambdaPsiSweep.rSumL rHostSumLSave ++
    gateBack LambdaPsiSweep.rSumU rHostSumUSave ++
    gateBack LambdaPsiSweep.rPsiLQ rHostPsiLQSave ++
    gateBack LambdaPsiSweep.rPsiLR rHostPsiLRSave ++
    gateBack LambdaPsiSweep.rPsiUQ rHostPsiUQSave ++
    gateBack LambdaPsiSweep.rPsiUR rHostPsiURSave

def gatePost : List AInstr :=
  hostCarryGatePost ++ candidateGatePost ++ gateBack rAccLoHi rAccLoHiSave ++
    gateBack rAccHiHi rAccHiHiSave

/-- Registers admissible for the generic candidate-gate restore primitive.
The predicate records the allocation facts on which the block's denotation
depends, instead of relying on the current numeric register assignments. -/
def GateBackSafe (dst save : Nat) : Prop :=
  dst ≠ rC ∧ dst ≠ rX ∧ dst ≠ rY ∧ dst ≠ rSelT1 ∧ dst ≠ rSelT2 ∧
    dst ≠ rSel ∧ save ≠ rC ∧ save ≠ rX ∧ save ≠ rY ∧
    save ≠ rSelT1 ∧ save ≠ rSelT2 ∧ save ≠ rSel ∧ dst ≠ save

/-- The V3 prefix snapshots every persistent accumulator, including the two
new high limbs, before the host sweep body can consume a physical iteration. -/
theorem gatePre_run (k : Nat) (s : AState) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
    out.regs rPrevSeen = s.regs sSeen ∧
      out.regs rViolSave = s.regs rViol ∧
      out.regs rLogLPre = s.regs sLogL ∧
      out.regs rLogUPre = s.regs sLogU ∧
      out.regs rAccWSave = s.regs rAccW ∧
      out.regs rAccLoSave = s.regs rAccLo ∧
      out.regs rAccHiSave = s.regs rAccHi ∧
      out.regs rAccLoHiSave = s.regs rAccLoHi ∧
      out.regs rAccHiHiSave = s.regs rAccHiHi := by
  let pref := LeanCompCert.Verified.ArrayFoldBridge.arun k s hostCarryGatePre
  let out := LeanCompCert.Verified.ArrayFoldBridge.arun k pref gatePreCore
  have hrun : LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre = out := by
    simp only [gatePre, LeanCompCert.Verified.ArrayFoldBridge.arun_append,
      pref, out]
  have hp (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r
        hostCarryGatePre = false) : pref.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r hostCarryGatePre hr s
  have hcore :
      out.regs rPrevSeen = pref.regs sSeen ∧
        out.regs rViolSave = pref.regs rViol ∧
        out.regs rLogLPre = pref.regs sLogL ∧
        out.regs rLogUPre = pref.regs sLogU ∧
        out.regs rAccWSave = pref.regs rAccW ∧
        out.regs rAccLoSave = pref.regs rAccLo ∧
        out.regs rAccHiSave = pref.regs rAccHi ∧
        out.regs rAccLoHiSave = pref.regs rAccLoHi ∧
        out.regs rAccHiHiSave = pref.regs rAccHiHi := by
    simp [out, gatePreCore, candidateGatePre, movReg,
    LeanCompCert.Verified.ArrayFoldBridge.arun,
    LeanCompCert.Verified.ArrayFoldBridge.astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg, rPrevSeen, sSeen, rViolSave, rViol,
    rLogLPre, sLogL, rLogUPre, sLogU, rAccWSave, rAccW,
    rAccLoSave, rAccLo, rAccHiSave, rAccHi,
    rAccLoHiSave, rAccLoHi, rAccHiHiSave, rAccHiHi]
  rw [hrun]
  exact ⟨hcore.1.trans (hp sSeen (by rfl)),
    hcore.2.1.trans (hp rViol (by rfl)),
    hcore.2.2.1.trans (hp sLogL (by rfl)),
    hcore.2.2.2.1.trans (hp sLogU (by rfl)),
    hcore.2.2.2.2.1.trans (hp rAccW (by rfl)),
    hcore.2.2.2.2.2.1.trans (hp rAccLo (by rfl)),
    hcore.2.2.2.2.2.2.1.trans (hp rAccHi (by rfl)),
    hcore.2.2.2.2.2.2.2.1.trans (hp rAccLoHi (by rfl)),
    hcore.2.2.2.2.2.2.2.2.trans (hp rAccHiHi (by rfl))⟩

/-- The physical-step discriminator is a Boolean and is one precisely when
the host sieve's own consumed-candidate counter changed. -/
theorem candidateGateStep_run (k : Nat) (s : AState) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s candidateGateStep
    out.regs rStep =
      (if s.regs sSeen ≠ s.regs rPrevSeen then 1 else 0) ∧
      (out.regs rStep = 0 ∨ out.regs rStep = 1) := by
  by_cases h : s.regs sSeen = s.regs rPrevSeen
  · simp only [sSeen, rPrevSeen] at h
    simp [candidateGateStep,
      LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rStep, sSeen, rPrevSeen, h]
  · simp only [sSeen, rPrevSeen] at h
    simp [candidateGateStep,
      LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rStep, sSeen, rPrevSeen, h,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

/-- Exact denotation of one gated restore.  A candidate step keeps the newly
computed destination; a marking step restores its snapshot. -/
theorem gateBack_run (k : Nat) (s : AState) (dst save : Nat)
    (hsafe : GateBackSafe dst save)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hdst : s.regs dst < M) (hsave : s.regs save < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (gateBack dst save)).regs dst =
      if s.regs rStep = 1 then s.regs dst else s.regs save := by
  rcases hsafe with
    ⟨hdc, hdx, hdy, hdt1, hdt2, hdsel,
      hsc, hsx, hsy, hst1, hst2, hssel, hds⟩
  rcases hstep with h0 | h1
  · simp only [rC, rX, rY, rSelT1, rSelT2, rSel] at hdc hdx hdy hdt1 hdt2 hdsel hsc hsx hsy hst1 hst2 hssel
    simp only [rStep] at h0
    simp [gateBack, movReg, selectBlock,
      LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rC, rX, rY, rSelT1, rSelT2, rSel,
      rStep, h0, hdc, hdx, hdy, hdt1, hdt2, hdsel,
      hsc, hsx, hsy, hst1, hst2, hssel, hds,
      Nat.mod_eq_of_lt hsave,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
  · simp only [rC, rX, rY, rSelT1, rSelT2, rSel] at hdc hdx hdy hdt1 hdt2 hdsel hsc hsx hsy hst1 hst2 hssel
    simp only [rStep] at h1
    simp [gateBack, movReg, selectBlock,
      LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rC, rX, rY, rSelT1, rSelT2, rSel,
      rStep, h1, hdc, hdx, hdy, hdt1, hdt2, hdsel,
      hsc, hsx, hsy, hst1, hst2, hssel, hds,
      Nat.mod_eq_of_lt hdst,
      Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]
    have hM : 1 + (M - 1) = M := by omega
    rw [hM, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdst]

/-- The complete restore suffix has the expected effect on the sticky
violation flag; later accumulator restores frame this register. -/
theorem gatePost_rViol_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rViol =
      if s.regs rStep = 1 then s.regs rViol else s.regs rViolSave := by
  let pref := LeanCompCert.Verified.ArrayFoldBridge.arun k s hostCarryGatePost
  have hpStep : pref.regs rStep = s.regs rStep :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep
      hostCarryGatePost (by rfl) s
  have hpViol : pref.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
      hostCarryGatePost (by rfl) s
  have hpSave : pref.regs rViolSave = s.regs rViolSave :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViolSave
      hostCarryGatePost (by rfl) s
  rw [gatePost, candidateGatePost,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  change (LeanCompCert.Verified.ArrayFoldBridge.arun k
    (LeanCompCert.Verified.ArrayFoldBridge.arun k pref
      (gateBack rViol rViolSave))
    (gateBack rAccW rAccWSave ++ gateBack rAccLo rAccLoSave ++
      gateBack rAccHi rAccHiSave ++ gateBack rAccLoHi rAccLoHiSave ++
      gateBack rAccHiHi rAccHiHiSave)).regs rViol = _
  let first := LeanCompCert.Verified.ArrayFoldBridge.arun k pref
    (gateBack rViol rViolSave)
  have hpBit : pref.regs rStep = 0 ∨ pref.regs rStep = 1 := by
    rw [hpStep]
    exact hstep
  have hfirst := gateBack_run k pref rViol rViolSave
    (by simp [GateBackSafe, rViol, rViolSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) hpBit
    (by rw [hpViol]; exact hw rViol)
    (by rw [hpSave]; exact hw rViolSave)
  rw [hpStep, hpViol, hpSave] at hfirst
  have hframe :
      (LeanCompCert.Verified.ArrayFoldBridge.arun k first
        (gateBack rAccW rAccWSave ++ gateBack rAccLo rAccLoSave ++
          gateBack rAccHi rAccHiSave ++ gateBack rAccLoHi rAccLoHiSave ++
          gateBack rAccHiHi rAccHiHiSave)).regs rViol = first.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol _ (by rfl) first
  exact hframe.trans hfirst

/-- Composition rule for a gated component occurring between a framed prefix
and suffix.  It prevents each persistent accumulator proof from expanding the
entire restore instruction list. -/
theorem gatePost_component_run (k : Nat) (s : AState)
    (dst save : Nat) (preBlock postBlock : List AInstr)
    (hdecomp : gatePost = preBlock ++ gateBack dst save ++ postBlock)
    (hsafe : GateBackSafe dst save)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (hpStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep preBlock = false)
    (hpDst : LeanCompCert.Verified.ArrayRegFrame.writes dst preBlock = false)
    (hpSave : LeanCompCert.Verified.ArrayRegFrame.writes save preBlock = false)
    (hsDst : LeanCompCert.Verified.ArrayRegFrame.writes dst postBlock = false) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs dst =
      if s.regs rStep = 1 then s.regs dst else s.regs save := by
  rw [hdecomp, LeanCompCert.Verified.ArrayFoldBridge.arun_append,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  let pre := LeanCompCert.Verified.ArrayFoldBridge.arun k s preBlock
  let mid := LeanCompCert.Verified.ArrayFoldBridge.arun k pre
    (gateBack dst save)
  have hpreWord := LeanCompCert.Verified.ArrayFoldBridge.arun_word
    k preBlock s hw ha
  have hpreStep : pre.regs rStep = s.regs rStep :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep preBlock hpStep s
  have hpreDst : pre.regs dst = s.regs dst :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k dst preBlock hpDst s
  have hpreSave : pre.regs save = s.regs save :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k save preBlock hpSave s
  have hpreBit : pre.regs rStep = 0 ∨ pre.regs rStep = 1 := by
    rw [hpreStep]
    exact hstep
  have hmid := gateBack_run k pre dst save hsafe hpreBit
    (hpreWord.1 dst) (hpreWord.1 save)
  have htail :
      (LeanCompCert.Verified.ArrayFoldBridge.arun k mid postBlock).regs dst =
        mid.regs dst :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k dst postBlock hsDst mid
  rw [hpreStep, hpreDst, hpreSave] at hmid
  exact htail.trans hmid

theorem gatePost_rAccW_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rAccW =
      if s.regs rStep = 1 then s.regs rAccW else s.regs rAccWSave := by
  apply gatePost_component_run k s rAccW rAccWSave
    (hostCarryGatePost ++ gateBack rViol rViolSave)
    (gateBack rAccLo rAccLoSave ++ gateBack rAccHi rAccHiSave ++
      gateBack rAccLoHi rAccLoHiSave ++ gateBack rAccHiHi rAccHiHiSave)
  · simp [gatePost, candidateGatePost, List.append_assoc]
  · simp [GateBackSafe, rAccW, rAccWSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]
  · exact hstep
  · exact hw
  · exact ha
  · rfl
  · rfl
  · rfl
  · rfl

theorem gatePost_rAccLo_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rAccLo =
      if s.regs rStep = 1 then s.regs rAccLo else s.regs rAccLoSave := by
  apply gatePost_component_run k s rAccLo rAccLoSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave)
    (gateBack rAccHi rAccHiSave ++ gateBack rAccLoHi rAccLoHiSave ++
      gateBack rAccHiHi rAccHiHiSave)
  · simp [gatePost, candidateGatePost, List.append_assoc]
  · simp [GateBackSafe, rAccLo, rAccLoSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]
  · exact hstep
  · exact hw
  · exact ha
  · rfl
  · rfl
  · rfl
  · rfl

theorem gatePost_rAccHi_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rAccHi =
      if s.regs rStep = 1 then s.regs rAccHi else s.regs rAccHiSave := by
  apply gatePost_component_run k s rAccHi rAccHiSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave ++
      gateBack rAccLo rAccLoSave)
    (gateBack rAccLoHi rAccLoHiSave ++ gateBack rAccHiHi rAccHiHiSave)
  · simp [gatePost, candidateGatePost, List.append_assoc]
  · simp [GateBackSafe, rAccHi, rAccHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]
  · exact hstep
  · exact hw
  · exact ha
  · rfl
  · rfl
  · rfl
  · rfl

theorem gatePost_rAccLoHi_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rAccLoHi =
      if s.regs rStep = 1 then s.regs rAccLoHi else s.regs rAccLoHiSave := by
  apply gatePost_component_run k s rAccLoHi rAccLoHiSave
    (hostCarryGatePost ++ candidateGatePost)
    (gateBack rAccHiHi rAccHiHiSave)
  · simp [gatePost, List.append_assoc]
  · simp [GateBackSafe, rAccLoHi, rAccLoHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]
  · exact hstep
  · exact hw
  · exact ha
  · rfl
  · rfl
  · rfl
  · rfl

theorem gatePost_rAccHiHi_run (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0 ∨ s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs rAccHiHi =
      if s.regs rStep = 1 then s.regs rAccHiHi else s.regs rAccHiHiSave := by
  apply gatePost_component_run k s rAccHiHi rAccHiHiSave
    (hostCarryGatePost ++ candidateGatePost ++
      gateBack rAccLoHi rAccLoHiSave) []
  · simp [gatePost, List.append_assoc]
  · simp [GateBackSafe, rAccHiHi, rAccHiHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]
  · exact hstep
  · exact hw
  · exact ha
  · rfl
  · rfl
  · rfl
  · rfl

/-- All persistent fields restored together on a marking step.  Packaging the
six component lemmas behind an abstract state prevents downstream symbolic
loop proofs from expanding their (large) candidate-check state argument. -/
theorem gatePost_marking_frame (k : Nat) (s : AState)
    (hstep : s.regs rStep = 0)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost
    out.regs rViol = s.regs rViolSave ∧
      out.regs rAccW = s.regs rAccWSave ∧
      out.regs rAccLo = s.regs rAccLoSave ∧
      out.regs rAccHi = s.regs rAccHiSave ∧
      out.regs rAccLoHi = s.regs rAccLoHiSave ∧
      out.regs rAccHiHi = s.regs rAccHiHiSave := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = if s.regs rStep = 1 then s.regs rViol else s.regs rViolSave :=
        gatePost_rViol_run k s (Or.inl hstep) hw
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccW else s.regs rAccWSave :=
        gatePost_rAccW_run k s (Or.inl hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccLo else s.regs rAccLoSave :=
        gatePost_rAccLo_run k s (Or.inl hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccHi else s.regs rAccHiSave :=
        gatePost_rAccHi_run k s (Or.inl hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccLoHi else s.regs rAccLoHiSave :=
        gatePost_rAccLoHi_run k s (Or.inl hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccHiHi else s.regs rAccHiHiSave :=
        gatePost_rAccHiHi_run k s (Or.inl hstep) hw haW
      _ = _ := by rw [hstep]; rfl

/-- On a consumed-candidate step the same gate keeps, rather than restores,
all six freshly computed persistent fields. -/
theorem gatePost_candidate_frame (k : Nat) (s : AState)
    (hstep : s.regs rStep = 1)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost
    out.regs rViol = s.regs rViol ∧
      out.regs rAccW = s.regs rAccW ∧
      out.regs rAccLo = s.regs rAccLo ∧
      out.regs rAccHi = s.regs rAccHi ∧
      out.regs rAccLoHi = s.regs rAccLoHi ∧
      out.regs rAccHiHi = s.regs rAccHiHi := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = if s.regs rStep = 1 then s.regs rViol else s.regs rViolSave :=
        gatePost_rViol_run k s (Or.inr hstep) hw
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccW else s.regs rAccWSave :=
        gatePost_rAccW_run k s (Or.inr hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccLo else s.regs rAccLoSave :=
        gatePost_rAccLo_run k s (Or.inr hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccHi else s.regs rAccHiSave :=
        gatePost_rAccHi_run k s (Or.inr hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccLoHi else s.regs rAccLoHiSave :=
        gatePost_rAccLoHi_run k s (Or.inr hstep) hw haW
      _ = _ := by rw [hstep]; rfl
  · calc
      _ = if s.regs rStep = 1 then s.regs rAccHiHi else s.regs rAccHiHiSave :=
        gatePost_rAccHiHi_run k s (Or.inr hstep) hw haW
      _ = _ := by rw [hstep]; rfl

def initWide (weighted : Nat) (lo hi : Int) : List AInstr :=
    movLit rViol 0 ++ movLit rAccW weighted ++
    movLit rAccLo (WideSigned.loOf lo) ++
    movLit rAccLoHi (WideSigned.hiOf lo) ++
    movLit rAccHi (WideSigned.loOf hi) ++
    movLit rAccHiHi (WideSigned.hiOf hi) ++
    movLit rTwoB (2 * scale)

def init (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int) : List AInstr :=
  LambdaPsiSweep.init c sd ++ initWide weighted lo hi

/-- The V3-only initializer has an exact, constant-size denotation.  In
particular the signed endpoints are prefix-seeded in canonical two-limb
form; no production fold is evaluated by this theorem. -/
theorem initWide_run (k : Nat) (s : AState)
    (weighted : Nat) (lo hi : Int)
    (hweighted : weighted < M)
    (htwoB : 2 * scale < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (initWide weighted lo hi)
    out.regs rViol = 0 ∧
      out.regs rAccW = weighted ∧
      WideSigned.rep (out.regs rAccLo) (out.regs rAccLoHi) lo ∧
      WideSigned.rep (out.regs rAccHi) (out.regs rAccHiHi) hi ∧
      out.regs rTwoB = 2 * scale := by
  dsimp only
  let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s
    (initWide weighted lo hi)
  have hv : out.regs rViol = 0 := by
    simp [initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB,
      out]
  have hw : out.regs rAccW = weighted := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt, hweighted,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  have hloLoM : WideSigned.loOf lo < M := by
    simpa [M, WideSigned.B64, LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Verified.MulWide.B64] using WideSigned.loOf_lt lo
  have hloHiM : WideSigned.hiOf lo < M := by
    simpa [M, WideSigned.B64, LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Verified.MulWide.B64] using WideSigned.hiOf_lt lo
  have hhiLoM : WideSigned.loOf hi < M := by
    simpa [M, WideSigned.B64, LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Verified.MulWide.B64] using WideSigned.loOf_lt hi
  have hhiHiM : WideSigned.hiOf hi < M := by
    simpa [M, WideSigned.B64, LeanCompCert.Verified.AddWide.B64,
      LeanCompCert.Verified.MulWide.B64] using WideSigned.hiOf_lt hi
  have hlo0 : out.regs rAccLo = WideSigned.loOf lo := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt,
      hloLoM,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  have hlo1 : out.regs rAccLoHi = WideSigned.hiOf lo := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt,
      hloHiM,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  have hhi0 : out.regs rAccHi = WideSigned.loOf hi := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt,
      hhiLoM,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  have hhi1 : out.regs rAccHiHi = WideSigned.hiOf hi := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt,
      hhiHiM,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  have htwo : out.regs rTwoB = 2 * scale := by
    simp [out, initWide, movLit, LeanCompCert.Verified.ArrayFoldBridge.arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt, htwoB,
      rViol, rAccW, rAccLo, rAccLoHi, rAccHi, rAccHiHi, rTwoB]
  refine ⟨hv, hw, ?_, ?_, htwo⟩
  · rw [hlo0, hlo1]
    exact WideSigned.loOf_hiOf_rep lo
  · rw [hhi0, hhi1]
    exact WideSigned.loOf_hiOf_rep hi

/-- Exact denotation of the added V3 prefix seeds after the unchanged host
initializer. -/
theorem init_run (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (sd : LambdaPsiSweep.Seed) (weighted : Nat) (lo hi : Int)
    (hweighted : weighted < M) (htwoB : 2 * scale < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (init c sd weighted lo hi)
    out.regs rViol = 0 ∧
      out.regs rAccW = weighted ∧
      WideSigned.rep (out.regs rAccLo) (out.regs rAccLoHi) lo ∧
      WideSigned.rep (out.regs rAccHi) (out.regs rAccHiHi) hi ∧
      out.regs rTwoB = 2 * scale := by
  rw [init, LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  exact initWide_run k _ weighted lo hi hweighted htwoB

def body (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  gatePre ++ LambdaPsiSweep.body c ++ candidateGateStep ++
    candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi ++
    hostArithmeticOverflowChecks ++ gatePost

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- The seam-bound literal is read-only throughout one V3 body.  Cache this
closed destination scan beside the program so schedule proofs do not unfold
the full candidate verifier. -/
theorem body_rTwoB_frame
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi : Nat) :
    LeanCompCert.Verified.ArrayRegFrame.writes rTwoB
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi) = false := by
  have hchecks := candidateChecks_shape_frames gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    rTwoB (by simp [shapeProjectionRegs])
  unfold LeanCompCert.Verified.ArrayRegFrame.writes at hchecks ⊢
  simp only [body, List.any_append, hchecks]
  rfl

/-- Expose the six semantic stages of one physical body exactly once.
Downstream proofs rewrite with this equation and keep the large candidate
suite behind a named state instead of repeatedly normalizing its list. -/
theorem body_run_eq_stages (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi : Nat) :
    LeanCompCert.Verified.ArrayFoldBridge.arun k s
        (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi) =
      let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
      let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
        (LambdaPsiSweep.body c)
      let gated := LeanCompCert.Verified.ArrayFoldBridge.arun k host
        candidateGateStep
      let checked := LeanCompCert.Verified.ArrayFoldBridge.arun k gated
        (candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi)
      let carryChecked := LeanCompCert.Verified.ArrayFoldBridge.arun k checked
        hostArithmeticOverflowChecks
      LeanCompCert.Verified.ArrayFoldBridge.arun k carryChecked gatePost := by
  simp only [body, LeanCompCert.Verified.ArrayFoldBridge.arun_append]

/- Moved to `RamareCombined100MProgramV3Denote`: keeping this large structural
proof downstream prevents every artifact-list edit from rebuilding it. -/
/-
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/-- A physical marking iteration cannot change any V3 persistent arithmetic
field.  The host-sweep premise mentions only its consumed-candidate counter;
all candidate-check instructions may still execute, but the proved gate
restores their effects. -/
theorem body_marking_persistent_frame (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
      let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
        (LambdaPsiSweep.body c)
      host.regs sSeen = snap.regs sSeen) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi)
    out.regs rViol = s.regs rViol ∧
      out.regs rAccW = s.regs rAccW ∧
      out.regs rAccLo = s.regs rAccLo ∧
      out.regs rAccHi = s.regs rAccHi ∧
      out.regs rAccLoHi = s.regs rAccLoHi ∧
      out.regs rAccHiHi = s.regs rAccHiHi := by
  dsimp only
  let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
  let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
    (LambdaPsiSweep.body c)
  let gated := LeanCompCert.Verified.ArrayFoldBridge.arun k host
    candidateGateStep
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let checkedCore := LeanCompCert.Verified.ArrayFoldBridge.arun k gated checks
  let checked := LeanCompCert.Verified.ArrayFoldBridge.arun k checkedCore
    hostArithmeticOverflowChecks
  let out := LeanCompCert.Verified.ArrayFoldBridge.arun k checked gatePost
  have hout : LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi) = out := by
    simpa only [snap, host, gated, checks, checkedCore, checked, out] using
      body_run_eq_stages k s c gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsnap := gatePre_run k s
  have hsnapSeen : snap.regs sSeen = s.regs sSeen :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sSeen gatePre (by rfl) s
  have hhostPrev : host.regs rPrevSeen = snap.regs rPrevSeen :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rPrevSeen
      (LambdaPsiSweep.body c) (by rfl) snap
  have hsame : host.regs sSeen = host.regs rPrevSeen := by
    rw [hseen, hhostPrev, hsnap.1, hsnapSeen]
  have hgate := candidateGateStep_run k host
  have hcheckFrames := candidateChecks_gate_frames gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hgatedStep : gated.regs rStep = 0 := by
    rw [hgate.1, if_neg (fun h => h hsame)]
  have hcheckedStep : checked.regs rStep = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep
      hostArithmeticOverflowChecks (by rfl) checkedCore,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep checks
        hcheckFrames.1 gated, hgatedStep]
  have hsnapWord := LeanCompCert.Verified.ArrayFoldBridge.arun_word
    k gatePre s hw haW
  have hhostWord := LeanCompCert.Verified.ArrayFoldBridge.arun_word
    k (LambdaPsiSweep.body c) snap hsnapWord.1 hsnapWord.2
  have hgatedWord := LeanCompCert.Verified.ArrayFoldBridge.arun_word
    k candidateGateStep host hhostWord.1 hhostWord.2
  have hcheckedCoreWord := candidateChecks_word gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    k gated hgatedWord.1 hgatedWord.2
  have hcheckedWord := LeanCompCert.Verified.ArrayFoldBridge.arun_word k
    hostArithmeticOverflowChecks checkedCore hcheckedCoreWord.1
      hcheckedCoreWord.2
  have saveFrame (r : Nat)
      (hHost : LeanCompCert.Verified.ArrayRegFrame.writes r
        (LambdaPsiSweep.body c) = false)
      (hGate : LeanCompCert.Verified.ArrayRegFrame.writes r
        candidateGateStep = false)
      (hChecks : LeanCompCert.Verified.ArrayRegFrame.writes r checks = false)
      (hCarry : LeanCompCert.Verified.ArrayRegFrame.writes r
        hostArithmeticOverflowChecks = false) :
      checked.regs r = snap.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
        hostArithmeticOverflowChecks hCarry checkedCore,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r checks hChecks gated,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r candidateGateStep
        hGate host,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
        (LambdaPsiSweep.body c) hHost snap]
  have hvSave : checked.regs rViolSave = s.regs rViol := by
    rw [saveFrame rViolSave (by rfl) (by rfl) hcheckFrames.2.1 (by rfl),
      hsnap.2.1]
  have hwSave : checked.regs rAccWSave = s.regs rAccW := by
    rw [saveFrame rAccWSave (by rfl) (by rfl) hcheckFrames.2.2.1 (by rfl),
      hsnap.2.2.2.2.1]
  have hloSave : checked.regs rAccLoSave = s.regs rAccLo := by
    rw [saveFrame rAccLoSave (by rfl) (by rfl) hcheckFrames.2.2.2.1 (by rfl),
      hsnap.2.2.2.2.2.1]
  have hhiSave : checked.regs rAccHiSave = s.regs rAccHi := by
    rw [saveFrame rAccHiSave (by rfl) (by rfl) hcheckFrames.2.2.2.2.1 (by rfl),
      hsnap.2.2.2.2.2.2.1]
  have hloHiSave : checked.regs rAccLoHiSave = s.regs rAccLoHi := by
    rw [saveFrame rAccLoHiSave (by rfl) (by rfl)
        hcheckFrames.2.2.2.2.2.1 (by rfl),
      hsnap.2.2.2.2.2.2.2.1]
  have hhiHiSave : checked.regs rAccHiHiSave = s.regs rAccHiHi := by
    rw [saveFrame rAccHiHiSave (by rfl) (by rfl)
        hcheckFrames.2.2.2.2.2.2 (by rfl),
      hsnap.2.2.2.2.2.2.2.2]
  let P (t : AState) : Prop :=
    t.regs rViol = s.regs rViol ∧
      t.regs rAccW = s.regs rAccW ∧
      t.regs rAccLo = s.regs rAccLo ∧
      t.regs rAccHi = s.regs rAccHi ∧
      t.regs rAccLoHi = s.regs rAccLoHi ∧
      t.regs rAccHiHi = s.regs rAccHiHi
  have hrestore := gatePost_marking_frame k checked hcheckedStep
    hcheckedWord.1 hcheckedWord.2
  have hfinal : P out := by
    change P (LeanCompCert.Verified.ArrayFoldBridge.arun k checked gatePost)
    exact ⟨hrestore.1.trans hvSave,
      hrestore.2.1.trans hwSave,
      hrestore.2.2.1.trans hloSave,
      hrestore.2.2.2.1.trans hhiSave,
      hrestore.2.2.2.2.1.trans hloHiSave,
      hrestore.2.2.2.2.2.trans hhiHiSave⟩
  exact hout.symm ▸ hfinal

-/
/-! ### Symbolic iteration

These definitions factor the production loop without evaluating a candidate.
They are the V3 counterpart of `BodyRefinement.bodyRun`: proofs can induct on
100 windows while the emitted body's instruction denotation stays opaque. -/

/-- A named transition packaged with its exact concrete denotation and word
closure.  The package is sealed after these fields are checked, so consumers
can use either fact without unfolding the large instruction list. -/
structure WordTransition (k : Nat) (code : List AInstr) where
  run : AState → AState
  run_eq : ∀ s, run s =
    LeanCompCert.Verified.ArrayFoldBridge.arun k s code
  word : ∀ s, (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
    (∀ j, (run s).regs j < M) ∧ (∀ j, (run s).arr j < M)

opaque bodyTransition (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    WordTransition k
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi) :=
  { run := fun s => LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi)
    run_eq := fun _ => rfl
    word := fun s hw haW => LeanCompCert.Verified.ArrayFoldBridge.arun_word k
      (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi) s hw haW }

def bodyNext (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) : AState → AState :=
  (bodyTransition k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
    logLen loBase hiBase sink egammaLo egammaHi).run

theorem bodyNext_eq_arun (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) (s : AState) :
    bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi s =
      LeanCompCert.Verified.ArrayFoldBridge.arun k s
        (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi) :=
  (bodyTransition k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
    logLen loBase hiBase sink egammaLo egammaHi).run_eq s

/- The marking-frame proof is supplied downstream by the denotation module. -/
/-
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
/-- Compact marking-step interface for symbolic schedule proofs.  Its public
type mentions only the opaque `bodyNext` transition, so downstream induction
does not normalize the complete candidate-check instruction list. -/
theorem bodyNext_marking_persistent_frame (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
      let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
        (LambdaPsiSweep.body c)
      host.regs sSeen = snap.regs sSeen) :
    let out := bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s
    out.regs rViol = s.regs rViol ∧
      out.regs rAccW = s.regs rAccW ∧
      out.regs rAccLo = s.regs rAccLo ∧
      out.regs rAccHi = s.regs rAccHi ∧
      out.regs rAccLoHi = s.regs rAccLoHi ∧
      out.regs rAccHiHi = s.regs rAccHiHi := by
  rw [bodyNext_eq_arun]
  exact body_marking_persistent_frame k s c gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    hw haW hseen
-/

theorem bodyNext_word (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    (∀ j, (bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower logLen loBase hiBase sink egammaLo egammaHi s).regs j < M) ∧
    (∀ j, (bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower logLen loBase hiBase sink egammaLo egammaHi s).arr j < M) :=
  (bodyTransition k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
    logLen loBase hiBase sink egammaLo egammaHi).word s hw haW

def bodyRun (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    Nat → AState → AState
  | 0, s => s
  | fuel + 1, s =>
      bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi
        (bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi fuel s)

@[simp] theorem bodyRun_zero (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) (s : AState) :
    bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi 0 s = s := rfl

@[simp] theorem bodyRun_succ (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi fuel : Nat) (s : AState) :
    bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi (fuel + 1) s =
      LeanCompCert.Verified.ArrayFoldBridge.arun k
        (bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi fuel s)
        (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi) :=
  bodyNext_eq_arun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
    lower logLen loBase hiBase sink egammaLo egammaHi _

@[simp] theorem bodyRun_succ_next (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi fuel : Nat) (s : AState) :
    bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi (fuel + 1) s =
      bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi
        (bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi fuel s) := rfl

theorem bodyRun_add (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi a b : Nat) (s : AState) :
    bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi (a + b) s =
      bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi b
        (bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        bodyRun_succ_next, ih, bodyRun_succ_next]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Cached index-freedom of the candidate verifier.  The old full scan is
reused and only the inserted carry-audit instructions are checked anew. -/
theorem candidateChecks_indexFree
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).all
        LeanCompCert.Ports.CDEMAbelIndexIndependence.ainstrIndexFree = true := by
  let old := candidateChecksWithoutRowAudit gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hold : old.all
      LeanCompCert.Ports.CDEMAbelIndexIndependence.ainstrIndexFree = true := by
    rfl
  have hdecomp : candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi =
        candidateChecksPreRowAudit gammaLo gammaHi bound limit cgammaLo
            cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi ++
          literalAddCarryCheck rAccW 1 ++ candidateChecksPostRowAudit := by
    simp [candidateChecks, candidateChecksPreRowAudit,
      candidateChecksPostRowAudit, List.append_assoc]
  have hold' := Bool.and_eq_true_iff.mp (by
    simpa only [old, candidateChecksWithoutRowAudit, List.all_append] using hold)
  rw [hdecomp, List.all_append, List.all_append]
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨hold'.1, by rfl⟩, hold'.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Cached index-freedom of the complete physical body.  This is assembled
from stage-local scans so consumers never normalize the whole emitted list. -/
theorem body_indexFree (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).all
        LeanCompCert.Ports.CDEMAbelIndexIndependence.ainstrIndexFree = true := by
  rw [body, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append,
    candidateChecks_indexFree gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi]
  all_goals rfl

/-- The body contains no loop-index operand, so changing `arun`'s index does
not change its denotation. -/
theorem body_index_irrel (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi k l : Nat) (s : AState) :
    LeanCompCert.Verified.ArrayFoldBridge.arun k s
        (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi) =
      LeanCompCert.Verified.ArrayFoldBridge.arun l s
        (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
          logLen loBase hiBase sink egammaLo egammaHi) := by
  apply LeanCompCert.Ports.CDEMAbelIndexIndependence.arun_indexFree
  exact body_indexFree c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
    lower logLen loBase hiBase sink egammaLo egammaHi

/-- The changing-index fold in `AProgram.denote` is the constant-index
symbolic iterator. -/
theorem foldl_range_body_eq_bodyRun (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi fuel : Nat) (s : AState) :
    (List.range fuel).foldl (fun st index =>
        LeanCompCert.Verified.ArrayFoldBridge.arun index st
          (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
            logLen loBase hiBase sink egammaLo egammaHi)) s =
      bodyRun 0 c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi fuel s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih, bodyRun_succ]
      exact body_index_irrel c gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi fuel 0 _

/-- Iteration factored into complete host-sieve periods. -/
def windowRun (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    Nat → AState → AState
  | 0, s => s
  | windows + 1, s =>
      bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi c.shape.period
        (windowRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi windows s)

/-- Window factoring is definitionally the same flat body iteration. -/
theorem windowRun_eq_bodyRun_mul (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi windows : Nat) (s : AState) :
    windowRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi windows s =
      bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi
        (windows * c.shape.period) s := by
  induction windows with
  | zero => simp only [windowRun, Nat.zero_mul, bodyRun_zero]
  | succ windows ih =>
      simp only [windowRun]
      rw [ih, Nat.add_mul, Nat.one_mul, bodyRun_add]

def epilogue (c : LambdaPsiSweep.Cfg) : List AInstr := epilogueV2 c

def program (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) : AProgram :=
  { regCount := 384
    arrayLen := c.arrayLen + 1
    loopCount := c.shape.period * c.shape.segCount
    init := init c sd weighted lo hi
    body := body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi
    epilogue := epilogue c
    output := rViol }

/-- The exact loop fold occurring in the V3 program denotation is the
period-factored symbolic window run.  This theorem performs no loop
evaluation; it combines index-freedom with arithmetic on the two fuel
factors. -/
theorem program_loopFold_eq_windowRun
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) (s : AState) :
    (List.range (program c sd weighted lo hi gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).loopCount).foldl (fun st index =>
        LeanCompCert.Verified.ArrayFoldBridge.arun index st
          (program c sd weighted lo hi gammaLo gammaHi bound limit
            cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
            egammaHi).body) s =
      windowRun 0 c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi c.shape.segCount s := by
  change
    (List.range (c.shape.period * c.shape.segCount)).foldl (fun st index =>
        LeanCompCert.Verified.ArrayFoldBridge.arun index st
          (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
            logLen loBase hiBase sink egammaLo egammaHi)) s = _
  rw [foldl_range_body_eq_bodyRun, windowRun_eq_bodyRun_mul, Nat.mul_comm]

theorem rowWideSite_wf (at_ bound : Nat) :
    (rowWideSite at_ bound).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [rowWideSite, List.all_append, rowWideCheck_wf]
  rfl

theorem rowWideChecks_wf :
    rowWideChecks.all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [rowWideChecks, List.all_append, List.all_append, List.all_append,
    rowWideSite_wf, rowWideSite_wf, rowWideSite_wf, rowWideSite_wf]
  rfl

theorem hostArithmeticOverflowChecks_wf :
    hostArithmeticOverflowChecks.all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rfl

theorem currentPsiAtNStage_wf :
    currentPsiAtNStage.all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rfl

theorem seamPsiBlockAt_wf (q r twoB : Nat)
    (hq : q < 384) (hr : r < 384) (ht : twoB < 384) :
    (seamPsiBlockAt q r twoB).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  simp [seamPsiBlockAt, LeanCompCert.Ports.ArraySegSieve.ainstrWFB,
    LeanCompCert.Ports.ArraySegSieve.instrWFB,
    LeanCompCert.Ports.ArraySegSieve.operandWFB, hq, hr, ht]
  simp [rT1, rT2, rT3, rViol]

theorem correctedRowCheckedAt_wf (qL qU rU gammaLo gammaHi bound lower : Nat)
    (hqL : qL < 384) (hqU : qU < 384) (hrU : rU < 384) :
    (correctedRowCheckedAt qL qU rU gammaLo gammaHi bound lower).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  simp [correctedRowCheckedAt, correctedRowAt, correctedStageAt,
    psiAddCarryCheck, addCarryCheckAt, literalAddCarryCheck,
    upperCeilCarryCheck,
    monotoneCarryCheck, commitBad, anchorHead, anchorTailMax,
    anchorLoad1, anchorLoad2, anchorLoad3, absDiffBlock, maxBlock,
    thresholdBit, guardedCommit,
    LeanCompCert.Ports.ArraySegSieve.ainstrWFB,
    LeanCompCert.Ports.ArraySegSieve.instrWFB,
    LeanCompCert.Ports.ArraySegSieve.operandWFB, hqL, hqU, hrU]
  simp [rIL, rIU, sSumL, sSumU, rGL, rLogLPre, rT4, rGU,
    rLogUPre, rA, rB, rF, rD1, rD2, rG, rOut, rSave, rMx, rBad,
    rT5, sCand, rViol, rHostCheckTmp, rSourceCheckBit,
    rSourceCheckResult]

theorem anchorRowChecked_wf (gammaLo gammaHi bound limit : Nat) :
    (anchorRowChecked gammaLo gammaHi bound limit).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  simp [anchorRowChecked, anchorRow, anchorStageProd, anchorStage,
    literalAddCarryCheck, monotoneCarryCheck,
    commitBad, anchorHead, anchorTailMax, anchorLoad1, anchorLoad2,
    anchorLoad3, absDiffBlock, maxBlock, thresholdBit, eqGuardedCommit,
    LeanCompCert.Ports.ArraySegSieve.ainstrWFB,
    LeanCompCert.Ports.ArraySegSieve.instrWFB,
    LeanCompCert.Ports.ArraySegSieve.operandWFB]
  simp [rIL, rIU, sSumL, sSumU, rGL, rLogLPre, rT4, rGU,
    rLogUPre, rA, rB, rF, rD1, rD2, rG, rOut, rSave, rMx, rBad,
    rT5, sCand, rViol, rHostCheckTmp]

theorem candidateChecksV2_wf (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower : Nat) :
    (candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower).all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [candidateChecksV2, List.all_append, List.all_append, List.all_append,
    List.all_append,
    all_ainstrWFB_mono (show 327 ≤ 384 by decide)
      SeamBlock.candidateChecksV1_wf,
    currentPsiAtNStage_wf,
    seamPsiBlockAt_wf rPsiAtNUQ rPsiAtNUR rTwoB (by decide) (by decide)
      (by decide),
    correctedRowCheckedAt_wf rPsiAtNLQ rPsiAtNUQ rPsiAtNUR
      cgammaLo cgammaHi cbound lower (by decide) (by decide) (by decide),
    anchorRowChecked_wf gammaLo gammaHi bound limit]
  rfl

set_option maxRecDepth 200000 in
theorem candidateChecks_wf (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    (candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [candidateChecks, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append,
    candidateChecksV2_wf gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower,
    all_ainstrWFB_mono (show 327 ≤ 384 by decide) pLogRecompute_wf,
    all_ainstrWFB_mono (show 342 ≤ 384 by decide)
      (qLogRecompute_wf logLen loBase hiBase sink),
    (WideEndpoint.endpoints_wf logLen loBase hiBase sink egammaLo egammaHi).1,
    (WideEndpoint.endpoints_wf logLen loBase hiBase sink egammaLo egammaHi).2,
    all_ainstrWFB_mono (show 327 ≤ 384 by decide) (by rfl :
      weightedStep.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true),
    (by rfl : weightedOverflowCheck.all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true),
    (by rfl : (literalAddCarryCheck rAccW 1).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true),
    intervalMagnitudeWide_wf, rowWideChecks_wf]
  rfl

theorem gatePre_wf :
    gatePre.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rfl

theorem gatePost_wf :
    gatePost.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rfl

theorem init_wf (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int) :
    (init c sd weighted lo hi).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [init, initWide, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append,
    all_ainstrWFB_mono (show 260 ≤ 384 by decide) (LambdaPsiSweep.init_all c sd)]
  rfl

set_option maxRecDepth 200000 in
theorem body_wf (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) :
    (body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi).all
        (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  rw [body, List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append,
    gatePre_wf, gatePost_wf,
    all_ainstrWFB_mono (show 260 ≤ 384 by decide) (LambdaPsiSweep.body_all c),
    candidateChecks_wf, hostArithmeticOverflowChecks_wf]
  rfl

theorem epilogue_wf (c : LambdaPsiSweep.Cfg) :
    (epilogue c).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 384) = true := by
  exact all_ainstrWFB_mono (show 327 ≤ 384 by decide) (epilogueV2_all c)

theorem program_wf (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (program c sd weighted lo hi gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi).WF :=
  ⟨show rViol < 384 by decide,
    LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all
      (init_wf c sd weighted lo hi),
    LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all
      (body_wf c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
        logLen loBase hiBase sink egammaLo egammaHi),
    LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all (epilogue_wf c)⟩

end LeanCompCert.Ports.RamareCombined100M.ProgramV3
