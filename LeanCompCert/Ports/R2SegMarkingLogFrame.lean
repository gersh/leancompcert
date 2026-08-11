import LeanCompCert.Ports.R2SegMarkingClassFrame

/-! # Logarithm-block framing during an `R₂*` marking round -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

def logGateBody (c : R2Cfg) : List AInstr := c.logBody.take 9
def logFirstCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 9).take 15
def logFirstBeforeGateBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 9).take 13
def logFirstGateBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 22).take 1
def logFirstViolBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 23).take 1
def logBeforeFinishBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 24).take 27
def logFinishBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 51).take 7
def logFinishBeforeGateBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 51).take 6
def logFinishGateBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 57).take 1
def logBeforeGapCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 58).take 42
def logKZeroBody (c : R2Cfg) : List AInstr :=
  (logBeforeGapCommitBody c).take 3
def logAfterKZeroBeforeGapBody (c : R2Cfg) : List AInstr :=
  (logBeforeGapCommitBody c).drop 3
def logGapCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 100).take 2
def logBeforeUpCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 102).take 9
def logUpCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 111).take 2
def logBeforeSqrtCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 113).take 11
def logSqrtCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 124).take 2
def logBeforeLowCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 126).take 25
def logLowCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 151).take 2
def logAfterLowCommitBody (c : R2Cfg) : List AInstr := c.logBody.drop 153
def logAfterLowBeforeEcBody (c : R2Cfg) : List AInstr :=
  (logAfterLowCommitBody c).take 4
def logEcCommitBody (c : R2Cfg) : List AInstr :=
  (logAfterLowCommitBody c).drop 4

theorem logBody_eq_mark_stages (c : R2Cfg) :
    c.logBody = logGateBody c ++ logFirstCommitBody c ++
      logBeforeFinishBody c ++ logFinishBody c ++
      logBeforeGapCommitBody c ++ logGapCommitBody c ++
      logBeforeUpCommitBody c ++ logUpCommitBody c ++
      logBeforeSqrtCommitBody c ++ logSqrtCommitBody c ++
      logBeforeLowCommitBody c ++ logLowCommitBody c ++
      logAfterLowCommitBody c := by
  rfl

theorem logFirstCommitBody_eq_stages (c : R2Cfg) :
    logFirstCommitBody c = logFirstBeforeGateBody c ++
      logFirstGateBody c ++ logFirstViolBody c := by
  rfl

theorem logFinishBody_eq_stages (c : R2Cfg) :
    logFinishBody c = logFinishBeforeGateBody c ++ logFinishGateBody c := by
  rfl

/-- The log-phase gate is zero in a marking round, so neither a new stream
entry nor a logarithm round is active. -/
theorem logGateBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h15 : s.regs 15 = 0) :
    let out := arun k s (logGateBody c)
    out.regs 206 = 0 ∧ out.regs 208 = 0 ∧ out.arr = s.arr := by
  simp [logGateBody, R2Cfg.logBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, h15]

/-- The first guarded log-failure commit adds zero when the start gate is
zero. -/
theorem logFirstCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h206 : s.regs 206 = 0) (h208 : s.regs 208 = 0)
    (hviol : s.regs rViol < M) :
    let out := arun k s (logFirstCommitBody c)
    out.regs 206 = 0 ∧ out.regs rViol = s.regs rViol ∧
      out.arr = s.arr := by
  let before := arun k s (logFirstBeforeGateBody c)
  have hb206 : before.regs 206 = 0 :=
    (arun_frame k 206 (logFirstBeforeGateBody c) (by rfl) s).trans h206
  have hb208 : before.regs 208 = 0 :=
    (arun_frame k 208 (logFirstBeforeGateBody c) (by rfl) s).trans h208
  have hbViol : before.regs rViol = s.regs rViol :=
    arun_frame k rViol (logFirstBeforeGateBody c) (by rfl) s
  let gated := arun k before (logFirstGateBody c)
  have hg218 : gated.regs 218 = 0 := by
    simp [gated, logFirstGateBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp, hb208]
  have hg206 : gated.regs 206 = 0 :=
    (arun_frame k 206 (logFirstGateBody c) (by rfl) before).trans hb206
  have hgViol : gated.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logFirstGateBody c) (by rfl) before).trans hbViol
  have hgViolM : gated.regs rViol < M := by rw [hgViol]; exact hviol
  have hcommit :
      let out := arun k gated (logFirstViolBody c)
      out.regs rViol = gated.regs rViol := by
    have hgViol' : gated.regs 190 < M := by
      simpa [rViol] using hgViolM
    simp [logFirstViolBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp, hg218,
      rViol, Nat.mod_eq_of_lt hgViol']
  dsimp only at hcommit
  have harr : (arun k s (logFirstCommitBody c)).arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logFirstCommitBody c) s (by rfl)
  rw [logFirstCommitBody_eq_stages, arun_append, arun_append]
  exact ⟨(arun_frame k 206 (logFirstViolBody c) (by rfl) gated).trans
      hg206, hcommit.trans hgViol, harr⟩

/-- The final-round bit is zero because it is multiplied by the disabled
live-entry gate. -/
theorem logFinishBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h206 : s.regs 206 = 0) :
    let out := arun k s (logFinishBody c)
    out.regs 206 = 0 ∧ out.regs 247 = 0 ∧ out.arr = s.arr := by
  let before := arun k s (logFinishBeforeGateBody c)
  have hb206 : before.regs 206 = 0 :=
    (arun_frame k 206 (logFinishBeforeGateBody c) (by rfl) s).trans h206
  have hgate :
      let out := arun k before (logFinishGateBody c)
      out.regs 206 = 0 ∧ out.regs 247 = 0 := by
    simp [logFinishGateBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp, hb206]
  dsimp only at hgate
  have harr : (arun k s (logFinishBody c)).arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logFinishBody c) s (by rfl)
  rw [logFinishBody_eq_stages, arun_append]
  exact ⟨hgate.1, hgate.2, harr⟩

theorem logBeforeGapCommitBody_eq_k_stages (c : R2Cfg) :
    logBeforeGapCommitBody c = logKZeroBody c ++
      logAfterKZeroBeforeGapBody c := by
  rfl

/-- Once the live-entry gate is zero, the guarded assignment to the
logarithm round counter stores zero. -/
theorem logBeforeGapCommitBody_mark_k_zero (c : R2Cfg) (k : Nat)
    (s : AState) (h206 : s.regs 206 = 0) :
    (arun k s (logBeforeGapCommitBody c)).regs rK = 0 := by
  let zeroed := arun k s (logKZeroBody c)
  have hz : zeroed.regs rK = 0 := by
    simp [zeroed, logKZeroBody, logBeforeGapCommitBody, R2Cfg.logBody,
      arun, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      h206, rK]
  rw [logBeforeGapCommitBody_eq_k_stages, arun_append]
  exact (arun_frame k rK (logAfterKZeroBeforeGapBody c) (by rfl) zeroed).trans hz

theorem logGapCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h247 : s.regs 247 = 0) (hviol : s.regs rViol < M) :
    let out := arun k s (logGapCommitBody c)
    out.regs 247 = 0 ∧ out.regs rViol = s.regs rViol := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  simp [logGapCommitBody, R2Cfg.logBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, h247, rViol,
    Nat.mod_eq_of_lt hviol']

theorem logUpCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h247 : s.regs 247 = 0) (hviol : s.regs rViol < M) :
    let out := arun k s (logUpCommitBody c)
    out.regs 247 = 0 ∧ out.regs rViol = s.regs rViol := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  simp [logUpCommitBody, R2Cfg.logBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, h247, rViol,
    Nat.mod_eq_of_lt hviol']

theorem logSqrtCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h247 : s.regs 247 = 0) (hviol : s.regs rViol < M) :
    let out := arun k s (logSqrtCommitBody c)
    out.regs 247 = 0 ∧ out.regs rViol = s.regs rViol := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  simp [logSqrtCommitBody, R2Cfg.logBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, h247, rViol,
    Nat.mod_eq_of_lt hviol']

theorem logLowCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h247 : s.regs 247 = 0) (hviol : s.regs rViol < M) :
    let out := arun k s (logLowCommitBody c)
    out.regs 247 = 0 ∧ out.regs rViol = s.regs rViol := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  simp [logLowCommitBody, R2Cfg.logBody, arun, astep, AState.writeReg,
    sdest, sval, denoteOperand, denoteOp, h247, rViol,
    Nat.mod_eq_of_lt hviol']

/-- The disabled finish bit makes the final read-cursor increment zero; the
remaining suffix also leaves the already-zero logarithm round counter alone. -/
theorem logAfterLowCommitBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h247 : s.regs 247 = 0) (hec : s.regs rEc < M) :
    let out := arun k s (logAfterLowCommitBody c)
    out.regs rK = s.regs rK ∧ out.regs rEc = s.regs rEc ∧
      out.arr = s.arr := by
  let before := arun k s (logAfterLowBeforeEcBody c)
  have hb247 : before.regs 247 = 0 :=
    (arun_frame k 247 (logAfterLowBeforeEcBody c) (by rfl) s).trans h247
  have hbEc : before.regs rEc = s.regs rEc :=
    arun_frame k rEc (logAfterLowBeforeEcBody c) (by rfl) s
  have hbEcM : before.regs rEc < M := by rw [hbEc]; exact hec
  have hbEc' : before.regs 192 < M := by simpa [rEc] using hbEcM
  have hcommit :
      (arun k before (logEcCommitBody c)).regs rEc = before.regs rEc := by
    simp [logEcCommitBody, logAfterLowCommitBody, R2Cfg.logBody,
      arun, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hb247, rEc, Nat.mod_eq_of_lt hbEc']
  have hkFrame := arun_frame k rK (logAfterLowCommitBody c) (by rfl) s
  have harr := LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
    k (logAfterLowCommitBody c) s (by rfl)
  rw [show logAfterLowCommitBody c = logAfterLowBeforeEcBody c ++
      logEcCommitBody c by rfl, arun_append]
  exact ⟨hkFrame, hcommit.trans hbEc, harr⟩

/-- With the log-phase gate disabled, all five guarded failure commits add
zero.  The complete 158-instruction block is therefore an array, marking
cursor, and marking-counter frame. -/
theorem logBody_mark_frame (c : R2Cfg) (k : Nat) (s : AState)
    (h15 : s.regs 15 = 0) (hviol : s.regs rViol < M)
    (hec : s.regs rEc < M) :
    let out := arun k s c.logBody
    out.arr = s.arr ∧ out.regs rPi = s.regs rPi ∧
      out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rWt = s.regs rWt ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ ∧ out.regs rR = s.regs rR ∧
      out.regs rW = s.regs rW ∧ out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark ∧
      out.regs rVCap = s.regs rVCap ∧ out.regs rWc = s.regs rWc ∧
      out.regs rEc = s.regs rEc ∧ out.regs rK = 0 := by
  let gate := arun k s (logGateBody c)
  have hg := logGateBody_mark_run c k s h15
  dsimp only at hg
  let first := arun k gate (logFirstCommitBody c)
  have hf := logFirstCommitBody_mark_run c k gate hg.1 hg.2.1
    (by
      rw [arun_frame k rViol (logGateBody c) (by rfl) s]
      exact hviol)
  dsimp only at hf
  let beforeFinish := arun k first (logBeforeFinishBody c)
  have hbf206 : beforeFinish.regs 206 = 0 :=
    (arun_frame k 206 (logBeforeFinishBody c) (by rfl) first).trans hf.1
  have hbfViol : beforeFinish.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeFinishBody c) (by rfl) first).trans
      hf.2.1
  let finished := arun k beforeFinish (logFinishBody c)
  have hfin := logFinishBody_mark_run c k beforeFinish hbf206
  dsimp only at hfin
  have hfinViol : finished.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logFinishBody c) (by rfl) beforeFinish).trans
      hbfViol
  let beforeGap := arun k finished (logBeforeGapCommitBody c)
  have hbg247 : beforeGap.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeGapCommitBody c) (by rfl) finished).trans
      hfin.2.1
  have hbgViol : beforeGap.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeGapCommitBody c) (by rfl) finished).trans
      hfinViol
  let gap := arun k beforeGap (logGapCommitBody c)
  have hgap := logGapCommitBody_mark_run c k beforeGap hbg247
    (by rw [hbgViol]; exact hviol)
  dsimp only at hgap
  have hgapViol : gap.regs rViol = s.regs rViol :=
    hgap.2.trans hbgViol
  let beforeUp := arun k gap (logBeforeUpCommitBody c)
  have hbu247 : beforeUp.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeUpCommitBody c) (by rfl) gap).trans hgap.1
  have hbuViol : beforeUp.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeUpCommitBody c) (by rfl) gap).trans
      hgapViol
  let up := arun k beforeUp (logUpCommitBody c)
  have hup := logUpCommitBody_mark_run c k beforeUp hbu247
    (by rw [hbuViol]; exact hviol)
  dsimp only at hup
  have hupViol : up.regs rViol = s.regs rViol := hup.2.trans hbuViol
  let beforeSqrt := arun k up (logBeforeSqrtCommitBody c)
  have hbs247 : beforeSqrt.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeSqrtCommitBody c) (by rfl) up).trans hup.1
  have hbsViol : beforeSqrt.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeSqrtCommitBody c) (by rfl) up).trans
      hupViol
  let sqrt := arun k beforeSqrt (logSqrtCommitBody c)
  have hsqrt := logSqrtCommitBody_mark_run c k beforeSqrt hbs247
    (by rw [hbsViol]; exact hviol)
  dsimp only at hsqrt
  have hsqrtViol : sqrt.regs rViol = s.regs rViol :=
    hsqrt.2.trans hbsViol
  let beforeLow := arun k sqrt (logBeforeLowCommitBody c)
  have hbl247 : beforeLow.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeLowCommitBody c) (by rfl) sqrt).trans
      hsqrt.1
  have hblViol : beforeLow.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeLowCommitBody c) (by rfl) sqrt).trans
      hsqrtViol
  let low := arun k beforeLow (logLowCommitBody c)
  have hlow := logLowCommitBody_mark_run c k beforeLow hbl247
    (by rw [hblViol]; exact hviol)
  dsimp only at hlow
  have hlowViol : low.regs rViol = s.regs rViol := hlow.2.trans hblViol
  let out := arun k low (logAfterLowCommitBody c)
  have hbgK : beforeGap.regs rK = 0 :=
    logBeforeGapCommitBody_mark_k_zero c k finished hfin.1
  have hgapK : gap.regs rK = 0 :=
    (arun_frame k rK (logGapCommitBody c) (by rfl) beforeGap).trans hbgK
  have hbuK : beforeUp.regs rK = 0 :=
    (arun_frame k rK (logBeforeUpCommitBody c) (by rfl) gap).trans hgapK
  have hupK : up.regs rK = 0 :=
    (arun_frame k rK (logUpCommitBody c) (by rfl) beforeUp).trans hbuK
  have hbsK : beforeSqrt.regs rK = 0 :=
    (arun_frame k rK (logBeforeSqrtCommitBody c) (by rfl) up).trans hupK
  have hsqrtK : sqrt.regs rK = 0 :=
    (arun_frame k rK (logSqrtCommitBody c) (by rfl) beforeSqrt).trans hbsK
  have hblK : beforeLow.regs rK = 0 :=
    (arun_frame k rK (logBeforeLowCommitBody c) (by rfl) sqrt).trans hsqrtK
  have hlowK : low.regs rK = 0 :=
    (arun_frame k rK (logLowCommitBody c) (by rfl) beforeLow).trans hblK
  have hgEc : gate.regs rEc = s.regs rEc :=
    arun_frame k rEc (logGateBody c) (by rfl) s
  have hfEc : first.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logFirstCommitBody c) (by rfl) gate).trans hgEc
  have hbfEc : beforeFinish.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logBeforeFinishBody c) (by rfl) first).trans hfEc
  have hfinEc : finished.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logFinishBody c) (by rfl) beforeFinish).trans hbfEc
  have hbgEc : beforeGap.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logBeforeGapCommitBody c) (by rfl) finished).trans hfinEc
  have hgapEc : gap.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logGapCommitBody c) (by rfl) beforeGap).trans hbgEc
  have hbuEc : beforeUp.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logBeforeUpCommitBody c) (by rfl) gap).trans hgapEc
  have hupEc : up.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logUpCommitBody c) (by rfl) beforeUp).trans hbuEc
  have hbsEc : beforeSqrt.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logBeforeSqrtCommitBody c) (by rfl) up).trans hupEc
  have hsqrtEc : sqrt.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logSqrtCommitBody c) (by rfl) beforeSqrt).trans hbsEc
  have hblEc : beforeLow.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logBeforeLowCommitBody c) (by rfl) sqrt).trans hsqrtEc
  have hlowEc : low.regs rEc = s.regs rEc :=
    (arun_frame k rEc (logLowCommitBody c) (by rfl) beforeLow).trans hblEc
  have hafter := logAfterLowCommitBody_mark_run c k low hlow.1
    (by rw [hlowEc]; exact hec)
  dsimp only at hafter
  have houtViol : out.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logAfterLowCommitBody c) (by rfl) low).trans
      hlowViol
  have houtEc : out.regs rEc = s.regs rEc := hafter.2.1.trans hlowEc
  have houtK : out.regs rK = 0 := hafter.1.trans hlowK
  have hviolAll : (arun k s c.logBody).regs rViol = s.regs rViol := by
    rw [logBody_eq_mark_stages, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append]
    exact houtViol
  have hecAll : (arun k s c.logBody).regs rEc = s.regs rEc := by
    rw [logBody_eq_mark_stages, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append]
    exact houtEc
  have hkAll : (arun k s c.logBody).regs rK = 0 := by
    rw [logBody_eq_mark_stages, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append, arun_append,
      arun_append, arun_append, arun_append, arun_append]
    exact houtK
  have frame (r : Nat) (h : writes r c.logBody = false) :
      (arun k s c.logBody).regs r = s.regs r :=
    arun_frame k r c.logBody h s
  exact ⟨
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.logBody s (by rfl),
    frame rPi (by rfl), frame rQ (by rfl), frame rBp (by rfl),
    frame rWt (by rfl), frame rFs (by rfl), frame rJ (by rfl),
    frame rR (by rfl), frame rW (by rfl), hviolAll,
    frame rVMark (by rfl), frame rVCap (by rfl), frame rWc (by rfl),
    hecAll, hkAll⟩

#print axioms logBody_eq_mark_stages
#print axioms logGateBody_mark_run
#print axioms logFirstCommitBody_mark_run
#print axioms logFinishBody_mark_run
#print axioms logGapCommitBody_mark_run
#print axioms logUpCommitBody_mark_run
#print axioms logSqrtCommitBody_mark_run
#print axioms logLowCommitBody_mark_run
#print axioms logBody_mark_frame

end LeanCompCert.Ports.R2SegSieve
