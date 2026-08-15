import LeanCompCert.Ports.PsiSegSieve
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.RegFrame
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Ports.CDEMAbelPrimitives

/-!
# Exact semantics of the lower comparison in the segmented `psi` program

The production `PsiSegSieve` tests the lower half of [CH25, Lemma 9.2]
immediately before adding the current prime-power logarithm.  This file
isolates the ten literal instructions actually present in `PsiCfg.logBody`
and proves their exact machine-word meaning.  No sieve range is evaluated.
-/

namespace LeanCompCert.Ports.PsiSegClauseCheck

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.PsiSegSieve

/-- The literal lower-clause island, registers 323--329 and its two counter
commits, exactly as emitted by `PsiCfg.logBody`. -/
def lowerBlock (S : Nat) : List Instr :=
  [ .binop 323 .lshr (.reg rDlo) (.lit cmpShift)
  , .binop 324 .shl (.reg rDhi) (.lit 48)
  , .binop 325 .add (.reg 323) (.reg 324)
  , .binop 326 .mul (.reg rSq) (.lit (cDown16 S))
  , .binop 327 .sub (.lit (bias16Of S)) (.reg 326)
  , .binop 328 .lt (.reg 325) (.reg 327)
  , .binop 329 .mul (.reg 328) (.reg 285)
  , .binop rViol .add (.reg rViol) (.reg 329)
  , .binop rVLo .add (.reg rVLo) (.reg 329) ]

def lowerBody (S : Nat) : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift (lowerBlock S)

/-- The isolated block is not a model invented for the proof: it is the
literal slice of the production log body. -/
theorem lowerBody_eq_logBody_slice (c : PsiCfg) :
    (c.logBody.drop 102).take 9 = lowerBody c.sc := by
  rfl

/-- Ordinary natural-number value represented by the shifted accumulator. -/
def shiftedD (dlo dhi : Nat) : Nat :=
  dlo / 2 ^ cmpShift + dhi * 2 ^ 48

/-- The lower comparison threshold, after the common sixteen-bit shift. -/
def lowerThreshold (S sq : Nat) : Nat := cDown16 S * sq

/-- The bit added to the lower-clause failure counter. -/
def lowerFailure (S dlo dhi sq fin : Nat) : Nat :=
  (if shiftedD dlo dhi < bias16Of S - lowerThreshold S sq then 1 else 0) * fin

def lowerShiftStage : List Instr :=
  [ .binop 323 .lshr (.reg rDlo) (.lit cmpShift)
  , .binop 324 .shl (.reg rDhi) (.lit 48)
  , .binop 325 .add (.reg 323) (.reg 324) ]

def lowerThresholdStage (S : Nat) : List Instr :=
  [ .binop 326 .mul (.reg rSq) (.lit (cDown16 S))
  , .binop 327 .sub (.lit (bias16Of S)) (.reg 326) ]

def lowerFlagStage : List Instr :=
  [ .binop 328 .lt (.reg 325) (.reg 327)
  , .binop 329 .mul (.reg 328) (.reg 285)
  , .binop rViol .add (.reg rViol) (.reg 329)
  , .binop rVLo .add (.reg rVLo) (.reg 329) ]

theorem lowerBlock_eq_stages (S : Nat) :
    lowerBlock S = lowerShiftStage ++ lowerThresholdStage S ++ lowerFlagStage := by
  rfl

private theorem lowerShiftStage_run (idx : Nat) (s : RegState)
    (dlo dhi : Nat) (hdlo : s rDlo = dlo) (hdhi : s rDhi = dhi)
    (hdloM : dlo < M) (hdhiShift : dhi * 2 ^ 48 < M)
    (hsum : shiftedD dlo dhi < M) :
    (srun idx s lowerShiftStage) 325 = shiftedD dlo dhi := by
  let i323 : Instr := .binop 323 .lshr (.reg rDlo) (.lit cmpShift)
  let i324 : Instr := .binop 324 .shl (.reg rDhi) (.lit 48)
  let i325 : Instr := .binop 325 .add (.reg 323) (.reg 324)
  have h16 : cmpShift % M = cmpShift := by decide
  have h48 : 48 % M = 48 := by decide
  have h323 : (srun idx s [i323, i324]) 323 = dlo / 2 ^ cmpShift := by
    calc
      (srun idx s [i323, i324]) 323 = sval idx s i323 := by
        exact srun_read_head idx 323 i323 [i324] (by rfl) (by rfl) s
      _ = ((dlo >>> cmpShift) % M) := by
        simp only [i323, sval, denoteOperand, denoteOp, Option.getD_some,
          hdlo, h16]
      _ = dlo / 2 ^ cmpShift := by
        rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hdloM
  have h324 : (srun idx s [i323, i324]) 324 = dhi * 2 ^ 48 := by
    calc
      (srun idx s [i323, i324]) 324 =
          sval idx (srun idx s [i323]) i324 := by
        exact srun_read_last idx 324 [i323] i324 (by rfl) s
      _ = (((srun idx s [i323]) rDhi <<< 48) % M) := by
        simp only [i324, sval, denoteOperand, denoteOp, Option.getD_some, h48]
      _ = ((dhi <<< 48) % M) := by
        rw [srun_frame idx rDhi [i323] (by rfl) s, hdhi]
      _ = dhi * 2 ^ 48 := by
        rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hdhiShift]
  calc
    (srun idx s lowerShiftStage) 325 =
        sval idx (srun idx s [i323, i324]) i325 := by
      change srun idx s ([i323, i324] ++ [i325]) 325 = _
      exact srun_read_last idx 325 [i323, i324] i325 (by rfl) s
    _ = (((srun idx s [i323, i324]) 323 +
          (srun idx s [i323, i324]) 324) % M) := by
      rfl
    _ = shiftedD dlo dhi := by
      rw [h323, h324]
      change (shiftedD dlo dhi) % M = shiftedD dlo dhi
      exact Nat.mod_eq_of_lt hsum

private theorem lowerThresholdStage_run (idx : Nat) (s : RegState)
    (S sq : Nat) (hsq : s rSq = sq)
    (hcM : cDown16 S < M)
    (hthreshold : lowerThreshold S sq < M)
    (hle : lowerThreshold S sq ≤ bias16Of S)
    (hbias : bias16Of S < M) :
    (srun idx s (lowerThresholdStage S)) 327 =
      bias16Of S - lowerThreshold S sq := by
  let i326 : Instr := .binop 326 .mul (.reg rSq) (.lit (cDown16 S))
  let i327 : Instr := .binop 327 .sub (.lit (bias16Of S)) (.reg 326)
  have hc : cDown16 S % M = cDown16 S := by
    exact Nat.mod_eq_of_lt hcM
  have hmul : (sq * (cDown16 S % M)) % M = lowerThreshold S sq := by
    rw [hc, Nat.mul_comm]
    exact Nat.mod_eq_of_lt hthreshold
  have hbmod : bias16Of S % M = bias16Of S := Nat.mod_eq_of_lt hbias
  have hsub : (bias16Of S + (M - lowerThreshold S sq)) % M =
      bias16Of S - lowerThreshold S sq := by
    have heq : bias16Of S + (M - lowerThreshold S sq) =
        M + (bias16Of S - lowerThreshold S sq) := by omega
    have hdiff : bias16Of S - lowerThreshold S sq < M := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hdiff, Nat.mod_eq_of_lt hdiff]
  have h326 : (srun idx s [i326]) 326 = lowerThreshold S sq := by
    calc
      (srun idx s [i326]) 326 = sval idx s i326 :=
        srun_read_head idx 326 i326 [] (by rfl) (by rfl) s
      _ = (sq * (cDown16 S % M)) % M := by
        simp only [i326, sval, denoteOperand, denoteOp, Option.getD_some, hsq]
      _ = lowerThreshold S sq := hmul
  calc
    (srun idx s (lowerThresholdStage S)) 327 =
        sval idx (srun idx s [i326]) i327 := by
      change srun idx s ([i326] ++ [i327]) 327 = _
      exact srun_read_last idx 327 [i326] i327 (by rfl) s
    _ = (bias16Of S % M + (M - (srun idx s [i326]) 326)) % M := by
      rfl
    _ = bias16Of S - lowerThreshold S sq := by
      rw [h326, hbmod, hsub]

private theorem lowerFlagStage_run (idx : Nat) (s : RegState)
    (d edge fin vlo : Nat)
    (hd : s 325 = d) (hedge : s 327 = edge) (hfin : s 285 = fin)
    (hvlo : s rVLo = vlo)
    (hroom : vlo + (if d < edge then 1 else 0) * fin < M) :
    (srun idx s lowerFlagStage) rVLo =
      vlo + (if d < edge then 1 else 0) * fin := by
  let i328 : Instr := .binop 328 .lt (.reg 325) (.reg 327)
  let i329 : Instr := .binop 329 .mul (.reg 328) (.reg 285)
  let iViol : Instr := .binop rViol .add (.reg rViol) (.reg 329)
  let iVLo : Instr := .binop rVLo .add (.reg rVLo) (.reg 329)
  let pre := srun idx s [i328, i329, iViol]
  have h328 : (srun idx s [i328]) 328 = (if d < edge then 1 else 0) := by
    calc
      (srun idx s [i328]) 328 = sval idx s i328 :=
        srun_read_head idx 328 i328 [] (by rfl) (by rfl) s
      _ = (if d < edge then 1 else 0) := by
        simp only [i328, sval, denoteOperand, denoteOp, Option.getD_some,
          hd, hedge]
  have h329 : (srun idx s [i328, i329, iViol]) 329 =
      (if d < edge then 1 else 0) * fin := by
    calc
      (srun idx s [i328, i329, iViol]) 329 =
          sval idx (srun idx s [i328]) i329 := by
        exact srun_read_write idx 329 [i328] i329 [iViol]
          (by rfl) (by rfl) s
      _ = (((srun idx s [i328]) 328 *
          (srun idx s [i328]) 285) % M) := by rfl
      _ = ((if d < edge then 1 else 0) * fin) % M := by
        rw [h328, srun_frame idx 285 [i328] (by rfl) s, hfin]
      _ = (if d < edge then 1 else 0) * fin := by
        apply Nat.mod_eq_of_lt
        omega
  have hpreVLo : pre rVLo = vlo := by
    exact (srun_frame idx rVLo [i328, i329, iViol] (by decide) s).trans hvlo
  calc
    (srun idx s lowerFlagStage) rVLo = sval idx pre iVLo := by
      change srun idx s ([i328, i329, iViol] ++ [iVLo]) rVLo = _
      exact srun_read_last idx rVLo [i328, i329, iViol] iVLo (by rfl) s
    _ = (pre rVLo + pre 329) % M := by rfl
    _ = vlo + (if d < edge then 1 else 0) * fin := by
      rw [hpreVLo]
      change (vlo + (srun idx s [i328, i329, iViol]) 329) % M = _
      rw [h329, Nat.mod_eq_of_lt hroom]

/-- Exact semantics of the actual lower-clause instruction island. -/
theorem lowerBlock_run (idx : Nat) (s : RegState)
    (S dlo dhi sq fin vlo : Nat)
    (hdlo : s rDlo = dlo) (hdhi : s rDhi = dhi) (hsq : s rSq = sq)
    (hfin : s 285 = fin) (hvlo : s rVLo = vlo)
    (hdloM : dlo < M) (hdhiShift : dhi * 2 ^ 48 < M)
    (hsum : shiftedD dlo dhi < M)
    (hcM : cDown16 S < M)
    (hthreshold : lowerThreshold S sq < M)
    (hle : lowerThreshold S sq ≤ bias16Of S)
    (hbias : bias16Of S < M)
    (hroom : vlo + lowerFailure S dlo dhi sq fin < M) :
    (srun idx s (lowerBlock S)) rVLo =
      vlo + lowerFailure S dlo dhi sq fin := by
  let s1 := srun idx s lowerShiftStage
  let s2 := srun idx s1 (lowerThresholdStage S)
  have hs1 := lowerShiftStage_run idx s dlo dhi hdlo hdhi hdloM hdhiShift hsum
  have hs1sq : s1 rSq = sq :=
    (srun_frame idx rSq lowerShiftStage (by decide) s).trans hsq
  have hs1fin : s1 285 = fin :=
    (srun_frame idx 285 lowerShiftStage (by decide) s).trans hfin
  have hs1vlo : s1 rVLo = vlo :=
    (srun_frame idx rVLo lowerShiftStage (by decide) s).trans hvlo
  have hs2 := lowerThresholdStage_run idx s1 S sq hs1sq hcM hthreshold hle hbias
  have hs2d : s2 325 = shiftedD dlo dhi :=
    (srun_frame idx 325 (lowerThresholdStage S) (by rfl) s1).trans hs1
  have hs2fin : s2 285 = fin :=
    (srun_frame idx 285 (lowerThresholdStage S) (by rfl) s1).trans hs1fin
  have hs2vlo : s2 rVLo = vlo :=
    (srun_frame idx rVLo (lowerThresholdStage S) (by rfl) s1).trans hs1vlo
  rw [lowerBlock_eq_stages, srun_append, srun_append]
  exact lowerFlagStage_run idx s2 _ _ fin vlo hs2d hs2 hs2fin hs2vlo hroom

/-- Array-state lifting of `lowerBlock_run`; the block contains no loads or
stores, so this is exactly the semantics used inside `PsiCfg.logBody`. -/
theorem lowerBody_run (idx : Nat)
    (s : AState)
    (S dlo dhi sq fin vlo : Nat)
    (hdlo : s.regs rDlo = dlo) (hdhi : s.regs rDhi = dhi)
    (hsq : s.regs rSq = sq) (hfin : s.regs 285 = fin)
    (hvlo : s.regs rVLo = vlo)
    (hdloM : dlo < M) (hdhiShift : dhi * 2 ^ 48 < M)
    (hsum : shiftedD dlo dhi < M) (hcM : cDown16 S < M)
    (hthreshold : lowerThreshold S sq < M)
    (hle : lowerThreshold S sq ≤ bias16Of S)
    (hbias : bias16Of S < M)
    (hroom : vlo + lowerFailure S dlo dhi sq fin < M) :
    (arun idx s (lowerBody S)).regs rVLo =
      vlo + lowerFailure S dlo dhi sq fin := by
  rw [lowerBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact lowerBlock_run idx s.regs S dlo dhi sq fin vlo hdlo hdhi hsq hfin hvlo
    hdloM hdhiShift hsum hcM hthreshold hle hbias hroom

def bodyBeforeLower (c : PsiCfg) : List
    AInstr :=
  c.coreBody ++ c.compactBody ++ c.logBody.take 102

def bodyAfterLower (c : PsiCfg) : List
    AInstr :=
  c.logBody.drop 111 ++ c.tailBody

set_option maxRecDepth 40000 in
theorem body_eq_lower_stages (c : PsiCfg) :
    c.body = bodyBeforeLower c ++ lowerBody c.sc ++ bodyAfterLower c := by
  rfl

def beforeLower (c : PsiCfg) (idx : Nat)
    (s : AState) : AState :=
  arun idx s (bodyBeforeLower c)

set_option maxRecDepth 40000 in
/-- One complete scheduled production body adds exactly the lower comparison
bit seen at the literal instruction boundary.  The prefix and suffix are
kept opaque and are discharged by register-frame proofs. -/
theorem body_vlo_increment (c : PsiCfg) (idx : Nat)
    (s : AState)
    (hdloM :
      let pre := beforeLower c idx s
      pre.regs rDlo < M)
    (hdhiShift :
      let pre := beforeLower c idx s
      pre.regs rDhi * 2 ^ 48 < M)
    (hsum :
      let pre := beforeLower c idx s
      shiftedD (pre.regs rDlo) (pre.regs rDhi) < M)
    (hcM : cDown16 c.sc < M)
    (hthreshold :
      let pre := beforeLower c idx s
      lowerThreshold c.sc (pre.regs rSq) < M)
    (hle :
      let pre := beforeLower c idx s
      lowerThreshold c.sc (pre.regs rSq) ≤ bias16Of c.sc)
    (hbias : bias16Of c.sc < M)
    (hroom :
      let pre := beforeLower c idx s
      s.regs rVLo + lowerFailure c.sc (pre.regs rDlo) (pre.regs rDhi)
        (pre.regs rSq) (pre.regs 285) < M) :
    let pre := beforeLower c idx s
    (arun idx s c.body).regs rVLo =
      s.regs rVLo + lowerFailure c.sc (pre.regs rDlo) (pre.regs rDhi)
        (pre.regs rSq) (pre.regs 285) := by
  let pre := beforeLower c idx s
  let guarded := arun idx pre (lowerBody c.sc)
  have hpreFrame : pre.regs rVLo = s.regs rVLo :=
    arun_frame idx rVLo (bodyBeforeLower c) (by rfl) s
  have hguard := lowerBody_run idx pre c.sc
    (pre.regs rDlo) (pre.regs rDhi) (pre.regs rSq) (pre.regs 285)
    (s.regs rVLo) rfl rfl rfl rfl hpreFrame hdloM hdhiShift hsum hcM
    hthreshold hle hbias hroom
  have hsuffix :
      (arun idx guarded
        (bodyAfterLower c)).regs rVLo = guarded.regs rVLo :=
    arun_frame idx rVLo (bodyAfterLower c) (by rfl) guarded
  rw [body_eq_lower_stages,
    arun_append, arun_append]
  exact hsuffix.trans hguard

/-! ## Upper-clause 128-bit comparison and counter -/

/-- The final eight instructions of the upper clause.  Registers `(410,414)`
hold `V^2` and `(428,431)` hold `cUp16^2*n`, low limb first. -/
def upperCompareBlock : List Instr :=
  [ .binop 432 .gt (.reg 414) (.reg 431)
  , .binop 433 .eq (.reg 414) (.reg 431)
  , .binop 434 .gt (.reg 410) (.reg 428)
  , .binop 435 .mul (.reg 433) (.reg 434)
  , .binop 436 .add (.reg 432) (.reg 435)
  , .binop 437 .mul (.reg 436) (.reg 285)
  , .binop rViol .add (.reg rViol) (.reg 437)
  , .binop rVUp .add (.reg rVUp) (.reg 437) ]

def upperCompareBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift upperCompareBlock

theorem upperCompareBody_eq_logBody_slice (c : PsiCfg) :
    (c.logBody.drop 166).take 8 = upperCompareBody := by
  rfl

/-- Lexicographic strict comparison of two unsigned 128-bit limb pairs. -/
def pairGreater (aLo aHi bLo bHi : Nat) : Bool :=
  decide (aHi > bHi ∨ (aHi = bHi ∧ aLo > bLo))

def upperFailure (aLo aHi bLo bHi fin : Nat) : Nat :=
  (if pairGreater aLo aHi bLo bHi then 1 else 0) * fin

theorem upperFailure_le_fin (aLo aHi bLo bHi fin : Nat) :
    upperFailure aLo aHi bLo bHi fin ≤ fin := by
  simp only [upperFailure]
  split <;> omega

def pairValue (lo hi : Nat) : Nat := lo + M * hi

/-- Lexicographic limb order agrees with ordinary order on canonical
unsigned-128 representations. -/
theorem pairValue_le_of_not_greater (aLo aHi bLo bHi : Nat)
    (haLo : aLo < M) (hbLo : bLo < M)
    (h : pairGreater aLo aHi bLo bHi = false) :
    pairValue aLo aHi ≤ pairValue bLo bHi := by
  have hn : ¬(aHi > bHi ∨ (aHi = bHi ∧ aLo > bLo)) := by
    exact of_decide_eq_false h
  by_cases heq : aHi = bHi
  · have hlo : aLo ≤ bLo := by omega
    simp only [pairValue, heq]
    omega
  · have hlt : aHi < bHi := by omega
    simp only [pairValue, M] at haLo hbLo ⊢
    have hstep : 18446744073709551616 * (aHi + 1) ≤
        18446744073709551616 * bHi := Nat.mul_le_mul_left _ hlt
    simp only [Nat.mul_add, Nat.mul_one] at hstep
    omega

/-- Exact semantics of the emitted unsigned-128 comparison and upper failure
counter.  The two comparison disjuncts are mutually exclusive, so the
machine's `add` is exactly Boolean `or`, never the value two. -/
theorem upperCompareBlock_run (idx : Nat) (s : RegState)
    (aLo aHi bLo bHi fin up : Nat)
    (haLo : s 410 = aLo) (haHi : s 414 = aHi)
    (hbLo : s 428 = bLo) (hbHi : s 431 = bHi)
    (hfin : s 285 = fin) (hup : s rVUp = up)
    (hroom : up + upperFailure aLo aHi bLo bHi fin < M) :
    (srun idx s upperCompareBlock) rVUp =
      up + upperFailure aLo aHi bLo bHi fin := by
  have hup' : s 345 = up := by simpa only [rVUp] using hup
  by_cases hhi : aHi > bHi
  · have hne : aHi ≠ bHi := by omega
    have hroom' : up + fin < M := by
      simpa [upperFailure, pairGreater, hhi, hne] using hroom
    have hfinM : fin < M := by omega
    simp [upperCompareBlock, upperFailure, pairGreater, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, Option.getD_some, haLo, haHi,
      hbLo, hbHi, hfin, hup', hhi, hne,
      rViol, rVUp, Nat.mod_eq_of_lt hfinM, Nat.mod_eq_of_lt hroom']
  · by_cases heq : aHi = bHi
    · by_cases hlo : aLo > bLo
      · have hroom' : up + fin < M := by
          simpa [upperFailure, pairGreater, hhi, heq, hlo] using hroom
        have hfinM : fin < M := by omega
        simp [upperCompareBlock, upperFailure, pairGreater, srun, RegState.set,
          sdest, sval, denoteOperand, denoteOp, Option.getD_some, haLo, haHi,
          hbLo, hbHi, hfin, hup', heq, hlo, rViol, rVUp,
          Nat.mod_eq_of_lt hfinM, Nat.mod_eq_of_lt hroom']
      · have hupM : up < M := by
          simpa [upperFailure, pairGreater, hhi, heq, hlo] using hroom
        simp [upperCompareBlock, upperFailure, pairGreater, srun, RegState.set,
          sdest, sval, denoteOperand, denoteOp, Option.getD_some, haLo, haHi,
          hbLo, hbHi, hfin, hup', heq, hlo, rViol, rVUp,
          Nat.mod_eq_of_lt hupM]
    · have hupM : up < M := by
        simpa [upperFailure, pairGreater, hhi, heq] using hroom
      simp [upperCompareBlock, upperFailure, pairGreater, srun, RegState.set,
        sdest, sval, denoteOperand, denoteOp, Option.getD_some, haLo, haHi,
        hbLo, hbHi, hfin, hup', hhi, heq, rViol, rVUp,
        Nat.mod_eq_of_lt hupM]

/-- A zero live upper counter yields the exact non-strict 128-bit inequality
that the production program intends to certify. -/
theorem upperPairBound_of_counter_zero (idx : Nat) (s : RegState)
    (aLo aHi bLo bHi : Nat)
    (haLo : s 410 = aLo) (haHi : s 414 = aHi)
    (hbLo : s 428 = bLo) (hbHi : s 431 = bHi)
    (hfin : s 285 = 1) (hup : s rVUp = 0)
    (haLoM : aLo < M) (hbLoM : bLo < M)
    (hout : (srun idx s upperCompareBlock) rVUp = 0) :
    pairValue aLo aHi ≤ pairValue bLo bHi := by
  have hroom : 0 + upperFailure aLo aHi bLo bHi 1 < M := by
    have hle := upperFailure_le_fin aLo aHi bLo bHi 1
    simp only [Nat.zero_add, M]
    omega
  have hrun := upperCompareBlock_run idx s aLo aHi bLo bHi 1 0
    haLo haHi hbLo hbHi hfin hup hroom
  rw [hout] at hrun
  have hpass : pairGreater aLo aHi bLo bHi = false := by
    cases hp : pairGreater aLo aHi bLo bHi
    · rfl
    · simp [upperFailure, hp] at hrun
  exact pairValue_le_of_not_greater aLo aHi bLo bHi haLoM hbLoM hpass

/-! ### The two products feeding the upper comparison -/

/-- The ψ emitter's multiplication block is literally the already-proved
CDEM/Section413 half-limb circuit.  This theorem reuses its exact product
specification; no arithmetic circuit is reproved here. -/
theorem psiMulWideBody_exact (idx : Nat) (s : AState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : LeanCompCert.Ports.Section413G1Denote.Distinct8
      s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : LeanCompCert.Ports.Section413G1Denote.NotIn8 ra
      s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : LeanCompCert.Ports.Section413G1Denote.NotIn8 rb
      s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : LeanCompCert.Ports.Section413G1Denote.NotIn8 rlo
      s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : LeanCompCert.Ports.Section413G1Denote.NotIn8 rhi
      s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, s.regs j < M) :
    let out := arun idx s
      (psiMulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)
    pairValue (out.regs rlo) (out.regs rhi) = s.regs ra * s.regs rb := by
  have h := LeanCompCert.Ports.CDEMAbelPrimitives.mulWideBody_arun_exact
    idx s ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
    hD hra hrb hrlo hrhi hlohi hword
  dsimp only at h ⊢
  rw [show psiMulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 =
      LeanCompCert.Ports.CDEMAbelScan.mulWideBody
        ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 by rfl]
  simpa only [pairValue, M, LeanCompCert.Verified.MulWide.B64] using h.1

/-- The actual emitted square stage computes exactly `V^2`. -/
theorem upperSquareBody_exact (idx : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun idx s upperSquareBody
    pairValue (out.regs 410) (out.regs 414) = s.regs 402 ^ 2 := by
  have h := psiMulWideBody_exact idx s 402 402 410 414
    403 404 405 406 407 408 409 411
    (by simp [LeanCompCert.Ports.Section413G1Denote.Distinct8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by decide)
    hword
  simpa only [upperSquareBody, Nat.pow_two] using h

/-- The actual emitted right-hand stage computes exactly `cUp16^2*n`. -/
theorem upperRhsBody_exact (c : PsiCfg) (idx : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (hc : cUp16Sq c.sc < M) :
    let out := arun idx s c.upperRhsBody
    pairValue (out.regs 428) (out.regs 431) =
      cUp16Sq c.sc * s.regs rNe := by
  let seed : List AInstr := [.scalar (.mov 415 (.lit (cUp16Sq c.sc)))]
  let seeded := arun idx s seed
  have hseed : seeded.regs 415 = cUp16Sq c.sc := by
    simp [seeded, seed, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, Nat.mod_eq_of_lt hc]
  have hn : seeded.regs rNe = s.regs rNe :=
    arun_frame idx rNe seed (by rfl) s
  have hseedRun : seeded =
      ⟨srun idx s.regs [.mov 415 (.lit (cUp16Sq c.sc))], s.arr⟩ := by
    exact LeanCompCert.Verified.ArrayScalarBlock.arun_lift idx
      [.mov 415 (.lit (cUp16Sq c.sc))] s
  have hseedWord : ∀ j, seeded.regs j < M := by
    intro j
    rw [hseedRun]
    exact srun_lt_of_lt idx _ s.regs hword j
  have h := psiMulWideBody_exact idx seeded 415 rNe 428 431
    416 417 418 419 420 421 422 423
    (by simp [LeanCompCert.Ports.Section413G1Denote.Distinct8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8, rNe])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8])
    (by decide)
    hseedWord
  change pairValue
      ((arun idx s (seed ++ psiMulWideBody 415 rNe 428 431
        416 417 418 419 420 421 422 423)).regs 428)
      ((arun idx s (seed ++ psiMulWideBody 415 rNe 428 431
        416 417 418 419 420 421 422 423)).regs 431) = _
  rw [arun_append]
  simpa only [hseed, hn] using h

def upperArithmeticBody (c : PsiCfg) : List AInstr :=
  upperSquareBody ++ c.upperRhsBody ++ upperCompareBody

theorem upperArithmeticBody_eq_logBody_slice (c : PsiCfg) :
    (c.logBody.drop 129).take 45 = upperArithmeticBody c := by
  rfl

/-- Zero from the complete emitted upper-arithmetic island implies the exact
integer squared inequality.  Thus the production comparison is genuinely
about `V^2` and `cUp16^2*n`, not merely about four unrelated output words. -/
theorem upperArithmetic_bound_of_zero (c : PsiCfg) (idx : Nat) (s : AState)
    (V n : Nat) (hV : s.regs 402 = V) (hn : s.regs rNe = n)
    (hfin : s.regs 285 = 1) (hup : s.regs rVUp = 0)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hc : cUp16Sq c.sc < M)
    (hout : (arun idx s (upperArithmeticBody c)).regs rVUp = 0) :
    V ^ 2 ≤ cUp16Sq c.sc * n := by
  let squared := arun idx s upperSquareBody
  let rhs := arun idx squared c.upperRhsBody
  have hsquare := upperSquareBody_exact idx s hword
  change pairValue (squared.regs 410) (squared.regs 414) =
    s.regs 402 ^ 2 at hsquare
  have hsword : ∀ j, squared.regs j < M :=
    arun_regs_word idx upperSquareBody s hword harr
  have hsarr : ∀ j, squared.arr j < M :=
    arun_arr_word idx upperSquareBody s hword harr
  have hsn : squared.regs rNe = n :=
    (arun_frame idx rNe upperSquareBody (by rfl) s).trans hn
  have hsfin : squared.regs 285 = 1 :=
    (arun_frame idx 285 upperSquareBody (by rfl) s).trans hfin
  have hsup : squared.regs rVUp = 0 :=
    (arun_frame idx rVUp upperSquareBody (by rfl) s).trans hup
  have hrhs := upperRhsBody_exact c idx squared hsword hc
  change pairValue (rhs.regs 428) (rhs.regs 431) =
    cUp16Sq c.sc * squared.regs rNe at hrhs
  have hrword : ∀ j, rhs.regs j < M :=
    arun_regs_word idx c.upperRhsBody squared hsword hsarr
  have hr410 : rhs.regs 410 = squared.regs 410 :=
    arun_frame idx 410 c.upperRhsBody (by rfl) squared
  have hr414 : rhs.regs 414 = squared.regs 414 :=
    arun_frame idx 414 c.upperRhsBody (by rfl) squared
  have hrfin : rhs.regs 285 = 1 :=
    (arun_frame idx 285 c.upperRhsBody (by rfl) squared).trans hsfin
  have hrup : rhs.regs rVUp = 0 :=
    (arun_frame idx rVUp c.upperRhsBody (by rfl) squared).trans hsup
  have hcmp : (srun idx rhs.regs upperCompareBlock) rVUp = 0 := by
    change (arun idx rhs upperCompareBody).regs rVUp = 0
    rw [← hout]
    simp only [upperArithmeticBody, arun_append, squared, rhs]
  have hpair := upperPairBound_of_counter_zero idx rhs.regs
    (rhs.regs 410) (rhs.regs 414) (rhs.regs 428) (rhs.regs 431)
    rfl rfl rfl rfl hrfin hrup (hrword 410) (hrword 428) hcmp
  calc
    V ^ 2 = pairValue (rhs.regs 410) (rhs.regs 414) := by
      rw [hr410, hr414, hsquare, hV]
    _ ≤ pairValue (rhs.regs 428) (rhs.regs 431) := hpair
    _ = cUp16Sq c.sc * n := by rw [hrhs, hsn]

theorem upperCompareBody_run (idx : Nat) (s : AState)
    (aLo aHi bLo bHi fin up : Nat)
    (haLo : s.regs 410 = aLo) (haHi : s.regs 414 = aHi)
    (hbLo : s.regs 428 = bLo) (hbHi : s.regs 431 = bHi)
    (hfin : s.regs 285 = fin) (hup : s.regs rVUp = up)
    (hroom : up + upperFailure aLo aHi bLo bHi fin < M) :
    (arun idx s upperCompareBody).regs rVUp =
      up + upperFailure aLo aHi bLo bHi fin := by
  rw [upperCompareBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact upperCompareBlock_run idx s.regs aLo aHi bLo bHi fin up
    haLo haHi hbLo hbHi hfin hup hroom

def bodyBeforeUpperCompare (c : PsiCfg) : List AInstr :=
  c.coreBody ++ c.compactBody ++ c.logBody.take 166

def bodyAfterUpperCompare (c : PsiCfg) : List AInstr :=
  c.logBody.drop 174 ++ c.tailBody

set_option maxRecDepth 40000 in
theorem body_eq_upper_compare_stages (c : PsiCfg) :
    c.body = bodyBeforeUpperCompare c ++ upperCompareBody ++
      bodyAfterUpperCompare c := by
  rfl

def beforeUpperCompare (c : PsiCfg) (idx : Nat) (s : AState) : AState :=
  arun idx s (bodyBeforeUpperCompare c)

set_option maxRecDepth 40000 in
/-- Full scheduled-body refinement for the upper failure counter, conditional
only on the ordinary word bounds at the comparison boundary. -/
theorem body_vup_increment (c : PsiCfg) (idx : Nat) (s : AState)
    (hroom :
      let pre := beforeUpperCompare c idx s
      s.regs rVUp + upperFailure (pre.regs 410) (pre.regs 414)
        (pre.regs 428) (pre.regs 431) (pre.regs 285) < M) :
    let pre := beforeUpperCompare c idx s
    (arun idx s c.body).regs rVUp =
      s.regs rVUp + upperFailure (pre.regs 410) (pre.regs 414)
        (pre.regs 428) (pre.regs 431) (pre.regs 285) := by
  let pre := beforeUpperCompare c idx s
  let guarded := arun idx pre upperCompareBody
  have hpreFrame : pre.regs rVUp = s.regs rVUp :=
    arun_frame idx rVUp (bodyBeforeUpperCompare c) (by rfl) s
  have hguard := upperCompareBody_run idx pre
    (pre.regs 410) (pre.regs 414) (pre.regs 428) (pre.regs 431)
    (pre.regs 285) (s.regs rVUp) rfl rfl rfl rfl rfl hpreFrame
    hroom
  have hsuffix :
      (arun idx guarded (bodyAfterUpperCompare c)).regs rVUp =
        guarded.regs rVUp :=
    arun_frame idx rVUp (bodyAfterUpperCompare c) (by rfl) guarded
  rw [body_eq_upper_compare_stages, arun_append, arun_append]
  exact hsuffix.trans hguard

/-- A zero terminal lower counter forces the exact integer comparison tested
by the machine at every live (`fin = 1`) event. -/
theorem lowerBound_of_counter_zero (idx : Nat) (s : RegState)
    (S dlo dhi sq : Nat)
    (hdlo : s rDlo = dlo) (hdhi : s rDhi = dhi) (hsq : s rSq = sq)
    (hfin : s 285 = 1) (hvlo : s rVLo = 0)
    (hdloM : dlo < M) (hdhiShift : dhi * 2 ^ 48 < M)
    (hsum : shiftedD dlo dhi < M)
    (hcM : cDown16 S < M)
    (hthreshold : lowerThreshold S sq < M)
    (hle : lowerThreshold S sq ≤ bias16Of S)
    (hbias : bias16Of S < M)
    (hout : (srun idx s (lowerBlock S)) rVLo = 0) :
    bias16Of S - lowerThreshold S sq ≤ shiftedD dlo dhi := by
  have hroom : 0 + lowerFailure S dlo dhi sq 1 < M := by
    simp only [lowerFailure]
    split <;> simp [M]
  have hrun := lowerBlock_run idx s S dlo dhi sq 1 0 hdlo hdhi hsq hfin hvlo
    hdloM hdhiShift hsum hcM hthreshold hle hbias hroom
  rw [hout] at hrun
  by_cases hcmp : shiftedD dlo dhi < bias16Of S - lowerThreshold S sq
  · simp [lowerFailure, hcmp] at hrun
  · exact Nat.le_of_not_gt hcmp

#print axioms lowerBlock_run
#print axioms body_vlo_increment
#print axioms upperCompareBlock_run
#print axioms upperPairBound_of_counter_zero
#print axioms psiMulWideBody_exact
#print axioms upperSquareBody_exact
#print axioms upperRhsBody_exact
#print axioms upperArithmetic_bound_of_zero
#print axioms body_vup_increment
#print axioms lowerBound_of_counter_zero

end LeanCompCert.Ports.PsiSegClauseCheck
