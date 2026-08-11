import LeanCompCert.Ports.R2SegMarkingCursorPast
import LeanCompCert.Ports.ArraySegMobiusSignal

/-! # Classifier framing during an `R₂*` marking round -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

def classIndexBody (c : R2Cfg) : List AInstr :=
  lift
    [ .binop 85 .sub (.reg rR) (.lit c.markSteps)
    , .binop 86 .mul (.reg 9) (.reg 85)
    , .binop 87 .add (.reg 86) (.reg rW)
    , .binop 88 .add (.reg 86) (.lit c.segLen)
    , .binop 89 .add (.reg 86) (.lit (2 * c.segLen)) ]

def classReadDecodeBody (c : R2Cfg) : List AInstr :=
  (c.classBody.drop 5).take 10

def classClearAddressBody (c : R2Cfg) : List AInstr :=
  lift
    [ .binop 100 .sub (.lit 1) (.reg 9)
    , .binop 101 .mul (.reg 100) (.lit c.sink)
    , .binop 102 .add (.reg 86) (.reg 101)
    , .binop 103 .add (.reg 102) (.lit c.segLen)
    , .binop 104 .add (.reg 102) (.lit (2 * c.segLen)) ]

/-- Store-free address/load prefix before the three plane-clearing stores. -/
def classBeforeClearBody (c : R2Cfg) : List AInstr :=
  c.classBody.take 20

theorem classBeforeClearBody_eq_stages (c : R2Cfg) :
    classBeforeClearBody c = classIndexBody c ++ classReadDecodeBody c ++
      classClearAddressBody c := by
  rfl

/-- The three literal plane-clearing stores. -/
def classClearBody (c : R2Cfg) : List AInstr :=
  (c.classBody.drop 20).take 3

/-- The classifier and payload selector following the clear stores. -/
def classSelectBody (c : R2Cfg) : List AInstr :=
  (c.classBody.drop 23).take 24

/-- Scalar compaction prefix through the selected stream address. -/
def classCompactPrefixBody (c : R2Cfg) : List AInstr :=
  (c.classBody.drop 47).take 11

/-- The two stream stores and final write-cursor update. -/
def classCompactTailBody (c : R2Cfg) : List AInstr :=
  c.classBody.drop 58

theorem classBody_eq_stages (c : R2Cfg) :
    c.classBody = classBeforeClearBody c ++ classClearBody c ++
      classSelectBody c ++ classCompactPrefixBody c ++
        classCompactTailBody c := by
  rfl

theorem classSelectBody_eq_selector (c : R2Cfg) :
    classSelectBody c = classSelectorBody := by
  rfl

/-- With classification disabled, the clear prefix addresses exactly the
three scratch sinks at `3L`, `4L`, and `5L`. -/
theorem classBeforeClearBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h9 : s.regs 9 = 0) (h5 : 5 * c.segLen < M) :
    let out := arun k s (classBeforeClearBody c)
    out.regs 102 = 3 * c.segLen ∧
      out.regs 103 = 4 * c.segLen ∧
      out.regs 104 = 5 * c.segLen ∧ out.arr = s.arr := by
  have h3 : 3 * c.segLen < M := by omega
  have h4 : 4 * c.segLen < M := by omega
  have h34 : 3 * c.segLen + c.segLen = 4 * c.segLen := by omega
  have h35 : 3 * c.segLen + 2 * c.segLen = 5 * c.segLen := by omega
  let indexed := arun k s (classIndexBody c)
  have hi86 : indexed.regs 86 = 0 := by
    simp [indexed, classIndexBody, arun, astep, AState.writeReg,
      sdest, sval, denoteOperand, denoteOp, h9]
  have hi9 : indexed.regs 9 = 0 :=
    (arun_frame k 9 (classIndexBody c) (by rfl) s).trans h9
  let read := arun k indexed (classReadDecodeBody c)
  have hr86 : read.regs 86 = 0 :=
    (arun_frame k 86 (classReadDecodeBody c) (by rfl) indexed).trans hi86
  have hr9 : read.regs 9 = 0 :=
    (arun_frame k 9 (classReadDecodeBody c) (by rfl) indexed).trans hi9
  have harr0 : indexed.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (classIndexBody c) s (by rfl)
  have harr1 : read.arr = indexed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (classReadDecodeBody c) indexed (by rfl)
  have haddr :
      let out := arun k read (classClearAddressBody c)
      out.regs 102 = 3 * c.segLen ∧
      out.regs 103 = 4 * c.segLen ∧
        out.regs 104 = 5 * c.segLen ∧ out.arr = read.arr := by
    simp [classClearAddressBody, arun, astep, AState.writeReg,
      sdest, sval, denoteOperand, denoteOp, hr86, hr9,
      R2Cfg.sink, h34, h35, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4,
      Nat.mod_eq_of_lt h5]
  dsimp only at haddr
  rw [classBeforeClearBody_eq_stages, arun_append, arun_append]
  exact ⟨haddr.1, haddr.2.1, haddr.2.2.1,
    haddr.2.2.2.trans (harr1.trans harr0)⟩

/-- The literal clear stage zeros all three addressed cells and frames every
other array address. -/
theorem classClearBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (h102 : s.regs 102 = 3 * c.segLen)
    (h103 : s.regs 103 = 4 * c.segLen)
    (h104 : s.regs 104 = 5 * c.segLen)
    (hzero : s.regs rZero = 0) :
    let out := arun k s (classClearBody c)
    out.arr (3 * c.segLen) = 0 ∧
      out.arr (4 * c.segLen) = 0 ∧
      out.arr (5 * c.segLen) = 0 ∧
      ∀ a, a ≠ 3 * c.segLen → a ≠ 4 * c.segLen →
        a ≠ 5 * c.segLen → out.arr a = s.arr a := by
  simp [classClearBody, R2Cfg.classBody, arun, astep,
    AState.writeArr, h102, h103, h104, hzero]
  intro a ha3 ha4 ha5
  simp [ha3, ha4, ha5]

/-- The selector's production push bit is zero whenever the classification
phase gate is zero, independently of the plane contents. -/
theorem classSelectBody_mark_push_zero (c : R2Cfg) (k : Nat) (s : AState)
    (h9 : s.regs 9 = 0) :
    (arun k s (classSelectBody c)).regs 116 = 0 := by
  let flags := arun k s (lift classFlagInstrs)
  have hflags : flags.regs 116 = 0 := by
    simp [flags, classFlagInstrs, arun_lift, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, h9]
  have htail :
      (arun k flags (lift (classModeInstrs ++ classPayloadInstrs))).regs
        116 = flags.regs 116 :=
    arun_frame k 116 (lift (classModeInstrs ++ classPayloadInstrs))
      (by rfl) flags
  rw [classSelectBody_eq_selector, classSelectorBody, classSelectorInstrs,
    lift_append, arun_append]
  exact htail.trans hflags

/-- Disabled compaction selects the stream sink and adds zero to both the
shared and class-capacity violation counters. -/
theorem classCompactPrefixBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (h116 : s.regs 116 = 0)
    (hviol : s.regs rViol < M) (hvcap : s.regs rVCap < M)
    (hsink : c.streamSink < M) :
    let out := arun k s (classCompactPrefixBody c)
    out.regs 130 = 0 ∧ out.regs 131 = 0 ∧
      out.regs rViol = s.regs rViol ∧
      out.regs rVCap = s.regs rVCap ∧
      out.regs 137 = c.streamSink ∧ out.arr = s.arr := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  have hvcap' : s.regs 354 < M := by simpa [rVCap] using hvcap
  simp [classCompactPrefixBody, R2Cfg.classBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, h116,
    rViol, rVCap, Nat.mod_eq_of_lt hviol', Nat.mod_eq_of_lt hvcap',
    Nat.mod_eq_of_lt hsink]

/-- The disabled compaction tail writes only its two stream-sink cells and
keeps the stream write cursor fixed. -/
theorem classCompactTailBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (q : Nat) (h137 : s.regs 137 = c.streamSink)
    (h130 : s.regs 130 = 0) (hwc : s.regs rWc < M)
    (hsink1 : c.streamSink + 1 < M)
    (hq0 : q ≠ c.streamSink) (hq1 : q ≠ c.streamSink + 1) :
    let out := arun k s (classCompactTailBody c)
    out.arr q = s.arr q ∧ out.regs rWc = s.regs rWc := by
  have hwc' : s.regs 191 < M := by simpa [rWc] using hwc
  simp [classCompactTailBody, R2Cfg.classBody, arun, astep,
    AState.writeArr, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    h137, h130, rWc, Nat.mod_eq_of_lt hwc',
    Nat.mod_eq_of_lt hsink1, hq0, hq1]

/-- During a marking round, the complete classifier clears its three scratch
sinks, writes only the two stream-sink cells, and frames every persistent
marking cursor and counter. -/
theorem classBody_mark_frame (c : R2Cfg) (k : Nat) (s : AState) (a : Nat)
    (h9 : s.regs 9 = 0) (hzero : s.regs rZero = 0)
    (h5 : 5 * c.segLen < M) (hsink1 : c.streamSink + 1 < M)
    (hviol : s.regs rViol < M) (hvcap : s.regs rVCap < M)
    (hwc : s.regs rWc < M)
    (ha3 : a ≠ 3 * c.segLen) (ha4 : a ≠ 4 * c.segLen)
    (ha5 : a ≠ 5 * c.segLen)
    (ha0 : a ≠ c.streamSink) (ha1 : a ≠ c.streamSink + 1) :
    let out := arun k s c.classBody
    out.arr a = s.arr a ∧ out.arr (3 * c.segLen) = 0 ∧
      out.arr (4 * c.segLen) = 0 ∧ out.arr (5 * c.segLen) = 0 ∧
      out.regs rPi = s.regs rPi ∧ out.regs rQ = s.regs rQ ∧
      out.regs rBp = s.regs rBp ∧ out.regs rWt = s.regs rWt ∧
      out.regs rFs = s.regs rFs ∧ out.regs rJ = s.regs rJ ∧
      out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
      out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark ∧
      out.regs rVCap = s.regs rVCap ∧ out.regs rWc = s.regs rWc := by
  let before := arun k s (classBeforeClearBody c)
  have hb := classBeforeClearBody_mark_run c k s h9 h5
  dsimp only at hb
  let cleared := arun k before (classClearBody c)
  have hbZero : before.regs rZero = 0 :=
    (arun_frame k rZero (classBeforeClearBody c) (by rfl) s).trans hzero
  have hc := classClearBody_run c k before hb.1 hb.2.1 hb.2.2.1 hbZero
  dsimp only at hc
  let selected := arun k cleared (classSelectBody c)
  have hc9 : cleared.regs 9 = 0 :=
    (arun_frame k 9 (classClearBody c) (by rfl) before).trans
      ((arun_frame k 9 (classBeforeClearBody c) (by rfl) s).trans h9)
  have hs116 := classSelectBody_mark_push_zero c k cleared hc9
  have selectedFrame (r : Nat)
      (hbR : writes r (classBeforeClearBody c) = false)
      (hcR : writes r (classClearBody c) = false)
      (hsR : writes r (classSelectBody c) = false) :
      selected.regs r = s.regs r :=
    (arun_frame k r (classSelectBody c) hsR cleared).trans
      ((arun_frame k r (classClearBody c) hcR before).trans
        (arun_frame k r (classBeforeClearBody c) hbR s))
  have hsViol := selectedFrame rViol (by rfl) (by rfl) (by rfl)
  have hsVCap := selectedFrame rVCap (by rfl) (by rfl) (by rfl)
  have hsWc := selectedFrame rWc (by rfl) (by rfl) (by rfl)
  let compact := arun k selected (classCompactPrefixBody c)
  have hp := classCompactPrefixBody_mark_run c k selected hs116
    (by rw [hsViol]; exact hviol) (by rw [hsVCap]; exact hvcap)
    (by omega)
  dsimp only at hp
  have hcompactWc : compact.regs rWc = s.regs rWc :=
    (arun_frame k rWc (classCompactPrefixBody c) (by rfl) selected).trans hsWc
  have htail (q : Nat) (hq0 : q ≠ c.streamSink)
      (hq1 : q ≠ c.streamSink + 1) :
      (arun k compact (classCompactTailBody c)).arr q = compact.arr q :=
    (classCompactTailBody_mark_run c k compact q hp.2.2.2.2.1 hp.1
      (by rw [hcompactWc]; exact hwc) hsink1 hq0 hq1).1
  have hsink_gt : 5 * c.segLen < c.streamSink := by
    simp [R2Cfg.streamSink, R2Cfg.streamBase, R2Cfg.tableBase]
    omega
  have hsink3 : 3 * c.segLen ≠ c.streamSink := by omega
  have hsink4 : 4 * c.segLen ≠ c.streamSink := by omega
  have hsink5 : 5 * c.segLen ≠ c.streamSink := by omega
  have hsink31 : 3 * c.segLen ≠ c.streamSink + 1 := by omega
  have hsink41 : 4 * c.segLen ≠ c.streamSink + 1 := by omega
  have hsink51 : 5 * c.segLen ≠ c.streamSink + 1 := by omega
  have hselectArr : selected.arr = cleared.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (classSelectBody c) cleared (by rfl)
  have hcompactArr : compact.arr = selected.arr := hp.2.2.2.2.2
  have haClear : cleared.arr a = before.arr a :=
    hc.2.2.2 a ha3 ha4 ha5
  have haOut : (arun k compact (classCompactTailBody c)).arr a = s.arr a :=
    (htail a ha0 ha1).trans <| congrFun hcompactArr a |>.trans <|
      congrFun hselectArr a |>.trans <| haClear.trans (congrFun hb.2.2.2 a)
  have sinkOut (q : Nat) (hq0 : q ≠ c.streamSink)
      (hq1 : q ≠ c.streamSink + 1) (hqCleared : cleared.arr q = 0) :
      (arun k compact (classCompactTailBody c)).arr q = 0 :=
    (htail q hq0 hq1).trans <| congrFun hcompactArr q |>.trans <|
      congrFun hselectArr q |>.trans hqCleared
  let out := arun k compact (classCompactTailBody c)
  have frameOut (r : Nat) (h : writes r c.classBody = false) :
      out.regs r = s.regs r := arun_frame k r c.classBody h s
  have hviolCompact : compact.regs rViol = s.regs rViol :=
    hp.2.2.1.trans hsViol
  have hvCapCompact : compact.regs rVCap = s.regs rVCap :=
    hp.2.2.2.1.trans hsVCap
  have hviolOut : out.regs rViol = s.regs rViol :=
    (arun_frame k rViol (classCompactTailBody c) (by rfl) compact).trans
      hviolCompact
  have hvCapOut : out.regs rVCap = s.regs rVCap :=
    (arun_frame k rVCap (classCompactTailBody c) (by rfl) compact).trans
      hvCapCompact
  have hwcOut : out.regs rWc = s.regs rWc :=
    (classCompactTailBody_mark_run c k compact a hp.2.2.2.2.1 hp.1
      (by rw [hcompactWc]; exact hwc) hsink1 ha0 ha1).2.trans hcompactWc
  rw [classBody_eq_stages, arun_append, arun_append, arun_append,
    arun_append]
  exact ⟨haOut,
    sinkOut _ hsink3 hsink31 hc.1,
    sinkOut _ hsink4 hsink41 hc.2.1,
    sinkOut _ hsink5 hsink51 hc.2.2.1,
    frameOut rPi (by rfl), frameOut rQ (by rfl),
    frameOut rBp (by rfl), frameOut rWt (by rfl),
    frameOut rFs (by rfl), frameOut rJ (by rfl),
    frameOut rR (by rfl), frameOut rW (by rfl),
    hviolOut, frameOut rVMark (by rfl), hvCapOut, hwcOut⟩

#print axioms classBody_eq_stages
#print axioms classBeforeClearBody_mark_run
#print axioms classClearBody_run
#print axioms classSelectBody_mark_push_zero
#print axioms classCompactPrefixBody_mark_run
#print axioms classCompactTailBody_mark_run
#print axioms classBody_mark_frame

end LeanCompCert.Ports.R2SegSieve
