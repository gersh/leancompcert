import LeanCompCert.Ports.RamareCombined100MSeamBlock

/-! Denotation of the V3 q-log recomputation block. -/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.Reflect

theorem qLogDirectLoad_run (k : Nat) (s : AState)
    (logLen loBase hiBase sink : Nat)
    (hlen : logLen < M) (hsink : sink < M)
    (hlo : s.regs sShapeQ + loBase < M)
    (hhi : s.regs sShapeQ + hiBase < M)
    (hloWord : s.arr (if s.regs sShapeQ < logLen then
      s.regs sShapeQ + loBase else sink) < M)
    (hhiAdd : s.arr (if s.regs sShapeQ < logLen then
      s.regs sShapeQ + hiBase else sink) + 65535 < M) :
    let out := arun k s (qLogDirectLoad logLen loBase hiBase sink)
    out.regs rQLo = s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + loBase else sink) / 65536 ∧
      out.regs rQHi = (s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + hiBase else sink) + 65535) / 65536 := by
  dsimp only
  let lowerIndexed := arun k s (qIndexBlock logLen loBase sink)
  let lowerLoaded := arun k lowerIndexed (loadCell rQLo rA)
  let lowerScaled := arun k lowerLoaded (shrReg rQLo rQLo 16)
  let upperIndexed := arun k lowerScaled (qIndexBlock logLen hiBase sink)
  let upperLoaded := arun k upperIndexed (loadCell rQHi rA)
  have hloIndex := qIndexBlock_run k s logLen loBase sink hlen hsink hlo
  have hloLoad := loadCell_run k lowerIndexed rQLo rA
  have harrLower : lowerIndexed.arr = s.arr := by
    simp [lowerIndexed, qIndexBlock, arun, astep, AState.writeReg]
  have hloLoaded : lowerLoaded.regs rQLo =
      s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + loBase else sink) := by
    rw [hloLoad, hloIndex, harrLower]
  have hloLoadedWord : lowerLoaded.regs rQLo < M := by
    rw [hloLoaded]
    exact hloWord
  have hloScaled : lowerScaled.regs rQLo =
      s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + loBase else sink) / 65536 := by
    rw [shrReg_run k lowerLoaded rQLo rQLo 16 (by decide) hloLoadedWord,
      hloLoaded]
  have hqFrame : lowerScaled.regs sShapeQ = s.regs sShapeQ := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hloFrame : upperLoaded.regs rQLo = lowerScaled.regs rQLo := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
      LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
  have hloOutFrame :
      (arun k upperLoaded (ceilShift16Reg rQHi rQHi)).regs rQLo =
        upperLoaded.regs rQLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hupperIndex := qIndexBlock_run k lowerScaled logLen hiBase sink
    hlen hsink (by rw [hqFrame]; exact hhi)
  have harrLoaded : lowerLoaded.arr = s.arr := by
    rw [show lowerLoaded.arr = lowerIndexed.arr by
      simp [lowerLoaded, loadCell, arun, astep, AState.writeReg], harrLower]
  have harrScaled : lowerScaled.arr = s.arr := by
    simp [lowerScaled, shrReg, arun, astep, AState.writeReg, harrLoaded]
  have harrUpper : upperIndexed.arr = s.arr := by
    simp [upperIndexed, qIndexBlock, arun, astep, AState.writeReg, harrScaled]
  have hupperLoaded : upperLoaded.regs rQHi =
      s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + hiBase else sink) := by
    rw [loadCell_run, hupperIndex, hqFrame, harrUpper]
  have hupperAdd : upperLoaded.regs rQHi + 65535 < M := by
    rw [hupperLoaded]
    exact hhiAdd
  rw [qLogDirectLoad, arun_append, arun_append, arun_append, arun_append,
    arun_append]
  constructor
  · exact hloOutFrame.trans (hloFrame.trans hloScaled)
  · rw [ceilShift16Reg_run k upperLoaded rQHi rQHi hupperAdd,
      hupperLoaded]

set_option maxRecDepth 100000 in
theorem qLogDerivedLower_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hpMul : s.regs sShapePE * s.regs rPHi < M) :
    (arun k s qLogDerivedLower).regs 334 =
      (s.regs rLogLPre / 65536 -
        s.regs sShapePE * s.regs rPHi) := by
  have hlogDiv : s.regs rLogLPre / 65536 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hw _)
  have h16 : 16 % M = 16 := by decide
  have hpow : 2 ^ (16 : Nat) = 65536 := by decide
  have hpMulMod :
      (s.regs 101 * s.regs 326) % M = s.regs 101 * s.regs 326 := by
    apply Nat.mod_eq_of_lt
    simpa only [sShapePE, rPHi] using hpMul
  have hlogMod : (s.regs 316 / 65536) % M = s.regs 316 / 65536 := by
    apply Nat.mod_eq_of_lt
    simpa only [rLogLPre] using hlogDiv
  by_cases hle : s.regs sShapePE *
      s.regs rPHi ≤ s.regs rLogLPre / 65536
  · simp [qLogDerivedLower, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, RegState.set, Nat.shiftRight_eq_div_pow,
      sShapePE, rPHi, rLogLPre, hpMul, hlogDiv, hle,
      Nat.mod_eq_of_lt hpMul, Nat.mod_eq_of_lt hlogDiv,
      sub_mod_ge, h16, hpow, hpMulMod, hlogMod]
    rw [if_pos (by simpa only [sShapePE, rPHi, rLogLPre] using hle),
      Nat.mul_one]
    exact sub_mod_ge
      (by simpa only [sShapePE, rPHi, rLogLPre] using hle)
      (by simpa only [rLogLPre] using hlogDiv)
  · have hlt : s.regs rLogLPre / 65536 <
        s.regs sShapePE * s.regs rPHi := by omega
    have hsub : s.regs rLogLPre / 65536 -
        s.regs sShapePE * s.regs rPHi = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    simp [qLogDerivedLower, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, RegState.set, Nat.shiftRight_eq_div_pow,
      sShapePE, rPHi, rLogLPre, hpMul, hlogDiv, hle, hlt,
      Nat.mod_eq_of_lt hpMul, Nat.mod_eq_of_lt hlogDiv,
      h16, hpow, hpMulMod, hlogMod, hsub]
    rw [if_neg (by
      simpa only [sShapePE, rPHi, rLogLPre] using Nat.not_le_of_lt hlt)]
    have hsub' : s.regs 316 / 65536 - s.regs 101 * s.regs 326 = 0 := by
      simpa only [sShapePE, rPHi, rLogLPre] using hsub
    rw [hsub']
    simp

set_option maxRecDepth 100000 in
theorem qLogDerivedUpper_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hlogAdd : s.regs rLogUPre + 65535 < M)
    (hpMul : s.regs sShapePE * s.regs rPLo < M) :
    (arun k s qLogDerivedUpper).regs 337 =
      ((s.regs rLogUPre + 65535) / 65536 -
        s.regs sShapePE * s.regs rPLo) := by
  have hlogDiv : (s.regs rLogUPre + 65535) / 65536 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlogAdd
  have h16 : 16 % M = 16 := by decide
  have hpow : 2 ^ (16 : Nat) = 65536 := by decide
  have hlogAddMod : (s.regs 317 + 65535) % M = s.regs 317 + 65535 := by
    apply Nat.mod_eq_of_lt
    simpa only [rLogUPre] using hlogAdd
  have hpMulMod : (s.regs 101 * s.regs 325) % M =
      s.regs 101 * s.regs 325 := by
    apply Nat.mod_eq_of_lt
    simpa only [sShapePE, rPLo] using hpMul
  have hlogMod : ((s.regs 317 + 65535) / 65536) % M =
      (s.regs 317 + 65535) / 65536 := by
    apply Nat.mod_eq_of_lt
    simpa only [rLogUPre] using hlogDiv
  by_cases hle : s.regs sShapePE * s.regs rPLo ≤
      (s.regs rLogUPre + 65535) / 65536
  · simp [qLogDerivedUpper, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, RegState.set, Nat.shiftRight_eq_div_pow,
      sShapePE, rPLo, rLogUPre, hlogAdd,
      hpMul, hlogDiv, hle,
      Nat.mod_eq_of_lt hlogAdd, Nat.mod_eq_of_lt hpMul,
      Nat.mod_eq_of_lt hlogDiv, sub_mod_ge, h16, hpow,
      hlogAddMod, hpMulMod, hlogMod]
    rw [if_pos (by simpa only [sShapePE, rPLo, rLogUPre] using hle),
      Nat.mul_one]
    exact sub_mod_ge
      (by simpa only [sShapePE, rPLo, rLogUPre] using hle)
      (by simpa only [rLogUPre] using hlogDiv)
  · have hlt : (s.regs rLogUPre + 65535) / 65536 <
        s.regs sShapePE * s.regs rPLo := by omega
    have hsub : (s.regs rLogUPre + 65535) / 65536 -
        s.regs sShapePE * s.regs rPLo = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    simp [qLogDerivedUpper, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, RegState.set, Nat.shiftRight_eq_div_pow,
      sShapePE, rPLo, rLogUPre, hlogAdd,
      hpMul, hlogDiv, hle, hlt,
      Nat.mod_eq_of_lt hlogAdd, Nat.mod_eq_of_lt hpMul,
      Nat.mod_eq_of_lt hlogDiv, h16, hpow, hlogAddMod, hpMulMod,
      hlogMod, hsub]
    rw [if_neg (by
      simpa only [sShapePE, rPLo, rLogUPre] using Nat.not_le_of_lt hlt)]
    have hsub' : (s.regs 317 + 65535) / 65536 -
        s.regs 101 * s.regs 325 = 0 := by
      simpa only [sShapePE, rPLo, rLogUPre] using hsub
    rw [hsub']
    simp

theorem qLogSelectGuard_run (k : Nat) (s : AState) :
    (arun k s qLogSelectGuard).regs rC =
      (if s.regs sShapeRest ≠ 1 ∧
          s.regs sShapeQ = s.regs sShapeRest then 1 else 0) := by
  by_cases hr : s.regs sShapeRest = 1 <;>
    by_cases hq : s.regs sShapeQ = s.regs sShapeRest <;>
    simp only [sShapeRest] at hr <;>
    simp only [sShapeQ, sShapeRest] at hq <;>
    simp [qLogSelectGuard, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, RegState.set, sShapeRest, sShapeQ, rT4, rT5, rC,
      hr, hq, M]

set_option maxRecDepth 100000 in
theorem qLogSelect_run (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    let out := arun k s qLogSelect
    out.regs rQLo =
        (if s.regs sShapeRest ≠ 1 ∧
              s.regs sShapeQ = s.regs sShapeRest then s.regs 334
         else s.regs rQLo) ∧
      out.regs rQHi =
        (if s.regs sShapeRest ≠ 1 ∧
              s.regs sShapeQ = s.regs sShapeRest then s.regs 337
         else s.regs rQHi) := by
  dsimp only
  let guarded := arun k s qLogSelectGuard
  let lower := arun k guarded (selectRegs rQLo 334 rQLo)
  have hc := qLogSelectGuard_run k s
  have hguardWord := arun_word k qLogSelectGuard s hw ha
  have hguard334 : guarded.regs 334 = s.regs 334 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hguard337 : guarded.regs 337 = s.regs 337 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hguardQLo : guarded.regs rQLo = s.regs rQLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hguardQHi : guarded.regs rQHi = s.regs rQHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have lowerRun : lower.regs rQLo =
      (if guarded.regs rC = 1 then guarded.regs 334 else guarded.regs rQLo) := by
    let sx := arun k guarded (movReg rX 334)
    let staged := arun k sx (movReg rY rQLo)
    have ec : staged.regs rC = guarded.regs rC := by
      rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
    have ex : staged.regs rX = guarded.regs 334 := by
      rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
        movReg_run]
    have ey : staged.regs rY = guarded.regs rQLo := by
      rw [movReg_run,
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
    have hcbit : staged.regs rC = 0 ∨ staged.regs rC = 1 := by
      rw [ec, hc]
      split <;> simp
    have hsel := selectBlock_run k staged hcbit
      (by rw [ex]; exact hguardWord.1 _)
      (by rw [ey]; exact hguardWord.1 _)
    dsimp only [lower]
    rw [selectRegs, arun_append, arun_append, arun_append,
      movReg_run, hsel, ec, ex, ey]
  have hlowerC : lower.regs rC = guarded.regs rC :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hlower337 : lower.regs 337 = guarded.regs 337 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hlowerQHi : lower.regs rQHi = guarded.regs rQHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hlowerWord := arun_word k (selectRegs rQLo 334 rQLo) guarded
    hguardWord.1 hguardWord.2
  have upperRun :
      (arun k lower (selectRegs rQHi 337 rQHi)).regs rQHi =
        (if lower.regs rC = 1 then lower.regs 337 else lower.regs rQHi) := by
    let sx := arun k lower (movReg rX 337)
    let staged := arun k sx (movReg rY rQHi)
    have ec : staged.regs rC = lower.regs rC := by
      rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
    have ex : staged.regs rX = lower.regs 337 := by
      rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl),
        movReg_run]
    have ey : staged.regs rY = lower.regs rQHi := by
      rw [movReg_run,
        LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl)]
    have hcbit : staged.regs rC = 0 ∨ staged.regs rC = 1 := by
      rw [ec, hlowerC, hc]
      split <;> simp
    have hsel := selectBlock_run k staged hcbit
      (by rw [ex]; exact hlowerWord.1 _)
      (by rw [ey]; exact hlowerWord.1 _)
    rw [selectRegs, arun_append, arun_append, arun_append,
      movReg_run, hsel, ec, ex, ey]
  have upperQLo :
      (arun k lower (selectRegs rQHi 337 rQHi)).regs rQLo =
        lower.regs rQLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  rw [qLogSelect, arun_append, arun_append]
  rw [upperQLo, lowerRun, upperRun, hlowerC, hlower337, hlowerQHi,
    hc, hguard334, hguard337, hguardQLo, hguardQHi]
  simp

set_option maxRecDepth 200000 in
/-- End-to-end denotation of the q-log block at the model's `2^32` scale.
The table lookup and the derived `q = rest` formula are both computed by the
emitted instructions; this theorem only composes their fixed-size symbolic
denotations. -/
theorem qLogRecompute_run (k : Nat) (s : AState)
    (logLen loBase hiBase sink : Nat)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hlo : s.regs sShapeQ + loBase < M)
    (hhi : s.regs sShapeQ + hiBase < M)
    (hhiAdd : s.arr (if s.regs sShapeQ < logLen then
      s.regs sShapeQ + hiBase else sink) + 65535 < M)
    (hlogAdd : s.regs rLogUPre + 65535 < M)
    (hpMulLo : s.regs sShapePE * s.regs rPHi < M)
    (hpMulHi : s.regs sShapePE * s.regs rPLo < M) :
    let out := arun k s (qLogRecompute logLen loBase hiBase sink)
    out.regs rQLo =
        (if s.regs sShapeRest ≠ 1 ∧
              s.regs sShapeQ = s.regs sShapeRest then
          s.regs rLogLPre / 65536 - s.regs sShapePE * s.regs rPHi
         else s.arr (if s.regs sShapeQ < logLen then
           s.regs sShapeQ + loBase else sink) / 65536) ∧
      out.regs rQHi =
        (if s.regs sShapeRest ≠ 1 ∧
              s.regs sShapeQ = s.regs sShapeRest then
          (s.regs rLogUPre + 65535) / 65536 -
            s.regs sShapePE * s.regs rPLo
         else (s.arr (if s.regs sShapeQ < logLen then
           s.regs sShapeQ + hiBase else sink) + 65535) / 65536) := by
  dsimp only
  let direct := arun k s (qLogDirectLoad logLen loBase hiBase sink)
  let lower := arun k direct qLogDerivedLower
  let upper := arun k lower qLogDerivedUpper
  have hdirect := qLogDirectLoad_run k s logLen loBase hiBase sink
    hlen hsink hlo hhi (ha _) hhiAdd
  have hdWord := arun_word k
    (qLogDirectLoad logLen loBase hiBase sink) s hw ha
  have directFrame (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r
        (qLogDirectLoad logLen loBase hiBase sink) = false) :
      direct.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hr s
  have hlower := qLogDerivedLower_run k direct hdWord.1 (by
    rw [directFrame sShapePE (by rfl), directFrame rPHi (by rfl)]
    exact hpMulLo)
  have hlWord := arun_word k qLogDerivedLower direct hdWord.1 hdWord.2
  have lowerFrame (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r
        qLogDerivedLower = false) : lower.regs r = direct.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hr direct
  have hupper := qLogDerivedUpper_run k lower hlWord.1
    (by
      rw [lowerFrame rLogUPre (by rfl), directFrame rLogUPre (by rfl)]
      exact hlogAdd)
    (by
      rw [lowerFrame sShapePE (by rfl), lowerFrame rPLo (by rfl),
        directFrame sShapePE (by rfl), directFrame rPLo (by rfl)]
      exact hpMulHi)
  have huWord := arun_word k qLogDerivedUpper lower hlWord.1 hlWord.2
  have upperFrame (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r
        qLogDerivedUpper = false) : upper.regs r = lower.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hr lower
  have hselect := qLogSelect_run k upper huWord.1 huWord.2
  have hshapeRest : upper.regs sShapeRest = s.regs sShapeRest := by
    rw [upperFrame sShapeRest (by rfl), lowerFrame sShapeRest (by rfl),
      directFrame sShapeRest (by rfl)]
  have hshapeQ : upper.regs sShapeQ = s.regs sShapeQ := by
    rw [upperFrame sShapeQ (by rfl), lowerFrame sShapeQ (by rfl),
      directFrame sShapeQ (by rfl)]
  have h334 : upper.regs 334 =
      s.regs rLogLPre / 65536 - s.regs sShapePE * s.regs rPHi := by
    rw [upperFrame 334 (by rfl), hlower,
      directFrame rLogLPre (by rfl), directFrame sShapePE (by rfl),
      directFrame rPHi (by rfl)]
  have h337 : upper.regs 337 =
      (s.regs rLogUPre + 65535) / 65536 -
        s.regs sShapePE * s.regs rPLo := by
    rw [hupper, lowerFrame rLogUPre (by rfl),
      lowerFrame sShapePE (by rfl), lowerFrame rPLo (by rfl),
      directFrame rLogUPre (by rfl), directFrame sShapePE (by rfl),
      directFrame rPLo (by rfl)]
  have hqlo : upper.regs rQLo = direct.regs rQLo := by
    rw [upperFrame rQLo (by rfl), lowerFrame rQLo (by rfl)]
  have hqhi : upper.regs rQHi = direct.regs rQHi := by
    rw [upperFrame rQHi (by rfl), lowerFrame rQHi (by rfl)]
  have hqlo' : upper.regs rQLo =
      s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + loBase else sink) / 65536 := by
    rw [hqlo, hdirect.1]
  have hqhi' : upper.regs rQHi =
      (s.arr (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + hiBase else sink) + 65535) / 65536 := by
    rw [hqhi, hdirect.2]
  rw [qLogRecompute, arun_append, arun_append, arun_append]
  simpa only [hshapeRest, hshapeQ, h334, h337, hqlo', hqhi'] using hselect

end LeanCompCert.Ports.RamareCombined100M.SeamBlock
