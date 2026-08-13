import LeanCompCert.Ports.R2RuntimeMarkDenote
import LeanCompCert.Ports.LogFixRoundSemantics
import LeanCompCert.Ports.R2SegLnFixConvert
import LeanCompCert.Verified.InstrRename
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.LogFixedBounds

/-! # Source semantics of the compiled R2 fixed-log table packer -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Verified.InstrRename

def rootPackN (index : Nat) : Nat := index / runtimeScale + 2
def rootPackRound (index : Nat) : Nat := index % runtimeScale
def rootPackLnValue (e a : Nat) : Nat :=
  (e * 2 ^ runtimeScale + a) *
    LeanCompCert.Ports.PsiSegSieve.L2 / 2 ^ 64

def rootPackNorm (index : Nat) : Nat :=
  rootPackN index <<< (62 - Nat.log2 (rootPackN index))

/-- The small observation needed to state the pack loop invariant.  It omits
all scratch registers and keeps the zero register explicit because array
stores take their value from a register, not from a literal. -/
structure RootPackModel where
  zero : Nat
  ex : Nat
  th : Nat
  xm : Nat
  aa : Nat
  write : Nat
  arr : Nat → Nat

theorem rootPackModel_ext {a b : RootPackModel}
    (hzero : a.zero = b.zero)
    (hex : a.ex = b.ex)
    (hth : a.th = b.th)
    (hxm : a.xm = b.xm)
    (haa : a.aa = b.aa)
    (hwrite : a.write = b.write)
    (harr : a.arr = b.arr) : a = b := by
  cases a
  cases b
  simp_all

def rootPackObserve (s : AState) : RootPackModel :=
  { zero := s.regs 0
    ex := s.regs rpEx
    th := s.regs rpTh
    xm := s.regs rpXm
    aa := s.regs rpAa
    write := s.regs rpWrite
    arr := s.arr }

def rootPackStart (index : Nat) : Nat :=
  if rootPackRound index = 0 then 1 else 0

def rootPackFinish (index : Nat) : Nat :=
  if rootPackRound index + 1 = runtimeScale then 1 else 0

def rootPackPrime (index : Nat) (m : RootPackModel) : Nat :=
  if m.arr (rootPackN index) = 0 then 1 else 0

def rootPackBump (index : Nat) (m : RootPackModel) : Nat :=
  if m.th ≤ rootPackN index then rootPackStart index else 0

def rootPackExNext (index : Nat) (m : RootPackModel) : Nat :=
  m.ex + rootPackBump index m

def rootPackThNext (index : Nat) (m : RootPackModel) : Nat :=
  m.th + rootPackBump index m * m.th

def rootPackXmInit (index : Nat) (m : RootPackModel) : Nat :=
  if rootPackStart index = 1 then
    rootPackN index <<< (62 - rootPackExNext index m)
  else m.xm

def rootPackAaInit (index : Nat) (m : RootPackModel) : Nat :=
  if rootPackStart index = 1 then 0 else m.aa

def rootPackXmNext (index : Nat) (m : RootPackModel) : Nat :=
  logMant (rootPackXmInit index m)

def rootPackAaNext (index : Nat) (m : RootPackModel) : Nat :=
  (rootPackAaInit index m <<< 1) + logBit (rootPackXmInit index m)

def rootPackHit (index : Nat) (m : RootPackModel) : Nat :=
  rootPackFinish index * rootPackPrime index m

def rootPackStoreTargetSpec (c : R2Cfg) (index : Nat)
    (m : RootPackModel) : Nat :=
  if rootPackHit index m = 1 then m.write + c.tableBase else c.streamSink

def rootPackClearTargetSpec (c : R2Cfg) (index : Nat) : Nat :=
  if rootPackFinish index = 1 then rootPackN index else c.streamSink

/-- Sufficient word/range/bounds facts for one symbolic body step.  Later
loop invariants discharge these algebraically; no field asks Lean to execute
the production range. -/
structure RootPackStepSafe (c : R2Cfg) (index : Nat)
    (m : RootPackModel) : Prop where
  loop : index < (r2RootPackProgram c).loopCount
  zeroIsZero : m.zero = 0
  exWord : m.ex + 1 < M
  thWord : m.th + m.th < M
  exLe62 : rootPackExNext index m ≤ 62
  normWord : rootPackN index <<< (62 - rootPackExNext index m) < M
  xmWord : m.xm < M
  aaWord : m.aa < M
  xmInitLo : B62 ≤ rootPackXmInit index m
  xmInitHi : rootPackXmInit index m < B63
  aaInitBound : rootPackAaInit index m < B62
  fixBound : rootPackExNext index m * 2 ^ runtimeScale +
    rootPackAaNext index m < 2 ^ 30
  tableWord : c.tableBase < M
  sinkWord : c.streamSink < M
  writeTableWord : m.write + c.tableBase < M
  rootCell : runtimeRoot < c.arrayLen
  candidateCell : rootPackN index < c.arrayLen
  sinkCell : c.streamSink < c.arrayLen
  writeTableCell : m.write + c.tableBase < c.arrayLen
  lnShiftWord : rootPackLnValue (rootPackExNext index m)
    (rootPackAaNext index m) * 2 ^ valBits < M
  lnLowWord : rootPackN index +
    rootPackLnValue (rootPackExNext index m) (rootPackAaNext index m) *
      2 ^ valBits < M
  packedWord : packEntry (rootPackN index)
    (rootPackLnValue (rootPackExNext index m) (rootPackAaNext index m)) 1 < M
  writeWord : m.write + rootPackHit index m < M

/-- Algebraic loop invariant used to prove word and array safety without
executing the production range in Lean. -/
structure RootPackInvariant (index : Nat) (m : RootPackModel) : Prop where
  zeroIsZero : m.zero = 0
  exLe : m.ex ≤ 17
  thEq : m.th = 2 ^ (m.ex + 1)
  candidateLeTh : rootPackN index ≤ m.th
  nextEx : rootPackExNext index m = Nat.log2 (rootPackN index)
  nextTh : rootPackThNext index m =
    2 ^ (Nat.log2 (rootPackN index) + 1)
  writeLe : m.write ≤ index / runtimeScale
  xmWord : m.xm < M
  aaWord : m.aa < M
  logState :
    rootPackXmInit index m =
        (logIter (rootPackNorm index) (rootPackRound index)).1 ∧
      rootPackAaInit index m =
        (logIter (rootPackNorm index) (rootPackRound index)).2

/-- Configuration inequalities needed by the packer.  They are all small
layout facts for the production configuration, independent of the scan. -/
structure RootPackCfgSafe (c : R2Cfg) : Prop where
  rootCell : runtimeRoot < c.arrayLen
  tableWord : c.tableBase < M
  sinkWord : c.streamSink < M
  sinkCell : c.streamSink < c.arrayLen
  rootTableWord : runtimeRoot + c.tableBase < M
  rootTableCell : runtimeRoot + c.tableBase < c.arrayLen

/-- One mathematical candidate/log round.  This is a specification, not an
evaluator used for the production range; the loop theorem rewrites one
compiled body to this expression symbolically. -/
def rootPackModelStep (c : R2Cfg) (index : Nat)
    (m : RootPackModel) : RootPackModel :=
  { zero := m.zero
    ex := rootPackExNext index m
    th := rootPackThNext index m
    xm := rootPackXmNext index m
    aa := rootPackAaNext index m
    write := m.write + rootPackHit index m
    arr := fun x =>
      if x = rootPackClearTargetSpec c index then 0
      else if x = rootPackStoreTargetSpec c index m then
        packEntry (rootPackN index)
          (rootPackLnValue (rootPackExNext index m)
            (rootPackAaNext index m)) 1
      else m.arr x }

theorem rootPack_index_bounds {index : Nat}
    (hi : index < (runtimeRoot - 1) * runtimeScale) :
    index < M ∧ rootPackN index ≤ runtimeRoot ∧
      rootPackRound index < runtimeScale := by
  have hs : 0 < runtimeScale := by decide
  have hq : index / runtimeScale < runtimeRoot - 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi)
  have hr := Nat.mod_lt index hs
  simp [rootPackN, rootPackRound, runtimeRoot, runtimeScale] at hq hr ⊢
  constructor
  · exact Nat.lt_trans hi (by decide)
  constructor <;> omega

theorem rootPackN_pos (index : Nat) : 0 < rootPackN index := by
  simp [rootPackN]

theorem rootPackNorm_range {index : Nat}
    (hi : index < (runtimeRoot - 1) * runtimeScale) :
    B62 ≤ rootPackNorm index ∧ rootPackNorm index < B63 := by
  have hb := rootPack_index_bounds (index := index) hi
  let n := rootPackN index
  have hn0 : n ≠ 0 := by simp [n, rootPackN]
  have he : Nat.log2 n ≤ 17 := by
    have hlt : Nat.log2 n < 18 := (Nat.log2_lt hn0).mpr (by
      exact Nat.lt_of_le_of_lt (by simpa [n] using hb.2.1) (by decide))
    omega
  have hlo : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hhi : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hsplit : Nat.log2 n + (62 - Nat.log2 n) = 62 := by omega
  rw [rootPackNorm, Nat.shiftLeft_eq]
  change B62 ≤ n * 2 ^ (62 - Nat.log2 n) ∧
    n * 2 ^ (62 - Nat.log2 n) < B63
  constructor
  · calc
      B62 = 2 ^ Nat.log2 n * 2 ^ (62 - Nat.log2 n) := by
        rw [← Nat.pow_add, hsplit, B62_eq]
      _ ≤ n * 2 ^ (62 - Nat.log2 n) := Nat.mul_le_mul_right _ hlo
  · calc
      n * 2 ^ (62 - Nat.log2 n) <
          2 ^ (Nat.log2 n + 1) * 2 ^ (62 - Nat.log2 n) :=
        Nat.mul_lt_mul_of_pos_right hhi (Nat.pow_pos (by decide : 0 < 2))
      _ = B63 := by
        rw [← Nat.pow_add]
        have : Nat.log2 n + 1 + (62 - Nat.log2 n) = 63 := by omega
        rw [this, B63_eq]

theorem errB_mono {a b : Nat} (hab : a ≤ b) : errB a ≤ errB b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b _ ih =>
      calc
        errB a ≤ errB b := ih
        _ ≤ errB (b + 1) := by
          rw [errB_succ]
          have hnonneg : 0 ≤ errB b * errB b / B62 := Nat.zero_le _
          omega

theorem errB_le_of_le_48 {k : Nat} (hk : k ≤ 48) : errB k ≤ B62 :=
  Nat.le_trans (errB_mono hk) errB_le_48

theorem rootPackLogIter_range {index : Nat}
    (hi : index < (runtimeRoot - 1) * runtimeScale) :
    B62 ≤ (logIter (rootPackNorm index) (rootPackRound index)).1 ∧
      (logIter (rootPackNorm index) (rootPackRound index)).1 < B63 := by
  have hn := rootPackNorm_range hi
  have hr48 : rootPackRound index ≤ 48 := by
    have hr := (rootPack_index_bounds hi).2.2
    simp only [runtimeScale] at hr
    omega
  have h := logIter_spec (rootPackNorm index) hn.1 hn.2
    (rootPackRound index)
    (errB_le_of_le_48 hr48)
  exact ⟨h.1, h.2.1⟩

theorem rootPackLnValue_lt (e a : Nat)
    (hfix : e * 2 ^ runtimeScale + a < 18 * 2 ^ runtimeScale) :
    rootPackLnValue e a < 13 * 2 ^ runtimeScale := by
  have hL : 18 * LeanCompCert.Ports.PsiSegSieve.L2 < 13 * 2 ^ 64 := by decide
  have hLpos : 0 < LeanCompCert.Ports.PsiSegSieve.L2 := by decide
  have hprod :
      (e * 2 ^ runtimeScale + a) * LeanCompCert.Ports.PsiSegSieve.L2 <
        (13 * 2 ^ runtimeScale) * 2 ^ 64 := by
    calc
      (e * 2 ^ runtimeScale + a) * LeanCompCert.Ports.PsiSegSieve.L2 <
          (18 * 2 ^ runtimeScale) * LeanCompCert.Ports.PsiSegSieve.L2 :=
        Nat.mul_lt_mul_of_pos_right hfix hLpos
      _ = (18 * LeanCompCert.Ports.PsiSegSieve.L2) * 2 ^ runtimeScale := by
        ac_rfl
      _ < (13 * 2 ^ 64) * 2 ^ runtimeScale :=
        Nat.mul_lt_mul_of_pos_right hL (Nat.pow_pos (by decide : 0 < 2))
      _ = (13 * 2 ^ runtimeScale) * 2 ^ 64 := by ac_rfl
  rw [rootPackLnValue]
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).mpr hprod

theorem rootPack_succ_before_finish {index : Nat}
    (h : rootPackRound index + 1 < runtimeScale) :
    rootPackN (index + 1) = rootPackN index ∧
      rootPackRound (index + 1) = rootPackRound index + 1 := by
  have hs : 0 < runtimeScale := by decide
  have hdm := Nat.div_add_mod index runtimeScale
  have hdecomp : index / runtimeScale * runtimeScale +
      index % runtimeScale = index := by
    simpa [Nat.mul_comm] using hdm
  have hrem : index % runtimeScale + 1 < runtimeScale := by
    simpa only [rootPackRound] using h
  have hq : (index + 1) / runtimeScale = index / runtimeScale := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  have hm : (index + 1) % runtimeScale = index % runtimeScale + 1 := by
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt (by decide : 1 < runtimeScale)]
    apply Nat.mod_eq_of_lt
    exact hrem
  exact ⟨by simp [rootPackN, hq], by simpa [rootPackRound] using hm⟩

theorem rootPack_succ_at_finish {index : Nat}
    (h : rootPackRound index + 1 = runtimeScale) :
    rootPackN (index + 1) = rootPackN index + 1 ∧
      rootPackRound (index + 1) = 0 := by
  have hs : 0 < runtimeScale := by decide
  have hdm := Nat.div_add_mod index runtimeScale
  have hdecomp : index / runtimeScale * runtimeScale +
      index % runtimeScale = index := by
    simpa [Nat.mul_comm] using hdm
  have hrem : index % runtimeScale + 1 = runtimeScale := by
    simpa only [rootPackRound] using h
  have hq : (index + 1) / runtimeScale = index / runtimeScale + 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
      omega
  have hm : (index + 1) % runtimeScale = 0 := by
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt (by decide : 1 < runtimeScale)]
    rw [hrem, Nat.mod_self]
  exact ⟨by simp [rootPackN, hq], by simpa [rootPackRound] using hm⟩

theorem log2_succ_step {n : Nat} (hn : n ≠ 0) :
    Nat.log2 (n + 1) = Nat.log2 n +
      (if 2 ^ (Nat.log2 n + 1) ≤ n + 1 then 1 else 0) := by
  have hlo : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn
  have hhi : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  split <;> rename_i hcut
  · have heq : n + 1 = 2 ^ (Nat.log2 n + 1) := by omega
    apply (Nat.log2_eq_iff (by omega)).mpr
    constructor
    · rw [heq]
      exact Nat.le_refl _
    · rw [heq]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
  · apply (Nat.log2_eq_iff (by omega)).mpr
    constructor
    · exact Nat.le_trans hlo (by omega)
    · exact Nat.lt_of_not_ge hcut

theorem rootPackInvariant_safe (c : R2Cfg) (index : Nat) (m : RootPackModel)
    (hcfg : RootPackCfgSafe c)
    (hi : index < (r2RootPackProgram c).loopCount)
    (hinv : RootPackInvariant index m) : RootPackStepSafe c index m := by
  have hi' : index < (runtimeRoot - 1) * runtimeScale := by
    simpa [r2RootPackProgram] using hi
  have hb := rootPack_index_bounds hi'
  let n := rootPackN index
  let r := rootPackRound index
  let aNext := rootPackAaNext index m
  let fix := rootPackExNext index m * 2 ^ runtimeScale + aNext
  let ln := rootPackLnValue (rootPackExNext index m) aNext
  have hexNext : rootPackExNext index m ≤ 17 := by
    rw [hinv.nextEx]
    have hn0 : n ≠ 0 := by simp [n, rootPackN]
    have : Nat.log2 n < 18 := (Nat.log2_lt hn0).mpr (by
      exact Nat.lt_of_le_of_lt (by simpa [n] using hb.2.1) (by decide))
    have hlog : Nat.log2 (rootPackN index) < 17 + 1 := by
      simpa only [n] using this
    exact Nat.lt_succ_iff.mp hlog
  have hth : m.th ≤ 2 ^ 18 := by
    rw [hinv.thEq]
    exact Nat.pow_le_pow_of_le (by decide)
      (Nat.add_le_add_right hinv.exLe 1)
  have hnorm := rootPackNorm_range hi'
  have hiter := rootPackLogIter_range hi'
  have hxInit : rootPackXmInit index m =
      (logIter (rootPackNorm index) r).1 := by
    simpa only [r] using hinv.logState.1
  have haInit : rootPackAaInit index m =
      (logIter (rootPackNorm index) r).2 := by
    simpa only [r] using hinv.logState.2
  have hr : r < runtimeScale := by simpa only [r] using hb.2.2
  have haIter : (logIter (rootPackNorm index) r).2 < 2 ^ r :=
    logIter_snd_lt_two_pow _ r
  have haInitBound : rootPackAaInit index m < B62 := by
    rw [haInit]
    have hp : 2 ^ r ≤ 2 ^ runtimeScale :=
      Nat.pow_le_pow_of_le (by decide) (Nat.le_of_lt hr)
    exact Nat.lt_of_lt_of_le haIter
      (Nat.le_trans hp (by decide))
  have haNextEq : aNext =
      (logIter (rootPackNorm index) (r + 1)).2 := by
    simp [aNext, rootPackAaNext, haInit, hxInit, logIter, logStep,
      Nat.shiftLeft_eq, Nat.mul_comm]
  have hr1 : r + 1 ≤ runtimeScale := by omega
  have haNextBound : aNext < 2 ^ runtimeScale := by
    rw [haNextEq]
    exact Nat.lt_of_lt_of_le (logIter_snd_lt_two_pow _ (r + 1))
      (Nat.pow_le_pow_of_le (by decide) hr1)
  have hfix18 : fix < 18 * 2 ^ runtimeScale := by
    dsimp only [fix]
    have heMul := Nat.mul_le_mul_right (2 ^ runtimeScale) hexNext
    omega
  have hfix30 : fix < 2 ^ 30 :=
    Nat.lt_trans hfix18 (by decide)
  have hln13 : ln < 13 * 2 ^ runtimeScale := by
    exact rootPackLnValue_lt _ _ hfix18
  have hln28 : ln < 2 ^ 28 := Nat.lt_trans hln13 (by decide)
  have hshift : ln * 2 ^ valBits < M := by
    exact Nat.lt_trans
      (Nat.mul_lt_mul_of_pos_right hln13 (Nat.pow_pos (by decide : 0 < 2)))
      (by decide)
  have hlnLe : ln ≤ 2 ^ 28 - 1 := by omega
  have hshiftLe : ln * 2 ^ valBits ≤ B63 - 2 ^ valBits := by
    have h := Nat.mul_le_mul_right (2 ^ valBits) hlnLe
    simpa [valBits, B63_eq] using h
  have hn35 : n < 2 ^ valBits :=
    Nat.lt_of_le_of_lt (by simpa [n] using hb.2.1) (by decide)
  have hlow : n + ln * 2 ^ valBits < M := by
    exact Nat.lt_trans (Nat.add_lt_add_of_lt_of_le hn35 hshiftLe) (by decide)
  have hlow63 : n + ln * 2 ^ valBits < B63 := by
    have hpartition : 2 ^ valBits + (B63 - 2 ^ valBits) = B63 := by decide
    omega
  have hpack : packEntry n ln 1 < M := by
    rw [packEntry, Nat.one_mul]
    calc
      n + ln * 2 ^ valBits + B63 < B63 + B63 :=
        Nat.add_lt_add_right hlow63 B63
      _ = M := by decide
  have hq : index / runtimeScale < runtimeRoot := by
    have := hb.2.1
    simp only [rootPackN] at this
    omega
  have hwRoot : m.write < runtimeRoot := Nat.lt_of_le_of_lt hinv.writeLe hq
  have hwriteTableWord : m.write + c.tableBase < M :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right hwRoot c.tableBase)
      (Nat.le_of_lt hcfg.rootTableWord)
  have hwriteTableCell : m.write + c.tableBase < c.arrayLen :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right hwRoot c.tableBase)
      (Nat.le_of_lt hcfg.rootTableCell)
  have hhit : rootPackHit index m ≤ 1 := by
    unfold rootPackHit rootPackFinish rootPackPrime
    split <;> split <;> simp
  refine
    { loop := hi
      zeroIsZero := hinv.zeroIsZero
      exWord := by
        have hle : m.ex + 1 ≤ 17 + 1 :=
          Nat.add_le_add_right hinv.exLe 1
        exact Nat.lt_of_le_of_lt hle (by decide)
      thWord := by
        exact Nat.lt_of_le_of_lt (Nat.add_le_add hth hth) (by decide)
      exLe62 := by omega
      normWord := by
        rw [hinv.nextEx]
        simpa only [rootPackNorm] using Nat.lt_trans hnorm.2 (by decide)
      xmWord := hinv.xmWord
      aaWord := hinv.aaWord
      xmInitLo := by rw [hxInit]; exact hiter.1
      xmInitHi := by rw [hxInit]; exact hiter.2
      aaInitBound := haInitBound
      fixBound := by simpa only [fix, aNext] using hfix30
      tableWord := hcfg.tableWord
      sinkWord := hcfg.sinkWord
      writeTableWord := hwriteTableWord
      rootCell := hcfg.rootCell
      candidateCell := Nat.lt_of_le_of_lt hb.2.1 hcfg.rootCell
      sinkCell := hcfg.sinkCell
      writeTableCell := hwriteTableCell
      lnShiftWord := by simpa only [ln, aNext] using hshift
      lnLowWord := by simpa only [ln, n, aNext] using hlow
      packedWord := by simpa only [ln, n, aNext] using hpack
      writeWord := by
        have hle : m.write + rootPackHit index m ≤
            index / runtimeScale + 1 := Nat.add_le_add hinv.writeLe hhit
        have hqLe : index / runtimeScale + 1 ≤ runtimeRoot := by omega
        exact Nat.lt_of_le_of_lt (Nat.le_trans hle hqLe) (by decide) }

theorem runtimeProductionCfg_rootPackSafe :
    RootPackCfgSafe runtimeProductionCfg := by
  constructor <;> decide

def rootPackInitialModel (arr : Nat → Nat) : RootPackModel :=
  { zero := 0, ex := 1, th := 4, xm := 0, aa := 0, write := 0, arr := arr }

theorem rootPackInit_observe (arr : Nat → Nat) :
    rootPackObserve (arun 0 (initialAStateWithArray arr) rootPackInit) =
      rootPackInitialModel arr := by
  simp [rootPackObserve, rootPackInit, PsiSegSieve.seedRegs, arun, astep,
    initialAStateWithArray, initialState, AState.writeReg,
    rootPackInitialModel, rpEx, rpTh, rpWrite, rpXm, rpAa, sval,
    denoteOperand, Nat.mod_eq_of_lt (by decide : 1 < M),
    Nat.mod_eq_of_lt (by decide : 4 < M)]

theorem rootPackInit_denote (c : R2Cfg) (arr : Nat → Nat) :
    denoteAInstrs c.arrayLen 0 (initialAStateWithArray arr) rootPackInit =
      some (arun 0 (initialAStateWithArray arr) rootPackInit) := by
  apply denoteAInstrs_eq_arun
  simp [rootPackInit, PsiSegSieve.seedRegs, AllDefined, ADefined]

theorem rootPackInitialModel_invariant (arr : Nat → Nat) :
    RootPackInvariant 0 (rootPackInitialModel arr) := by
  refine
    { zeroIsZero := rfl
      exLe := by change 1 ≤ 17; decide
      thEq := by change 4 = 2 ^ (1 + 1); decide
      candidateLeTh := by change rootPackN 0 ≤ 4; decide
      nextEx := by rfl
      nextTh := by rfl
      writeLe := by change 0 ≤ 0 / runtimeScale; decide
      xmWord := by change 0 < M; decide
      aaWord := by change 0 < M; decide
      logState := by
        have hN : rootPackN 0 = 2 := by decide
        have hR : rootPackRound 0 = 0 := by decide
        have hS : rootPackStart 0 = 1 := by decide
        have hE : rootPackExNext 0 (rootPackInitialModel arr) = 1 := by rfl
        have hL : Nat.log2 2 = 1 := by decide
        constructor
        · rw [rootPackXmInit, hS, if_pos rfl, rootPackNorm, hE, hN, hL,
            hR, logIter]
        · rw [rootPackAaInit, hS, if_pos rfl, hR, logIter] }

theorem rootPackInvariant_step (c : R2Cfg) (index : Nat) (m : RootPackModel)
    (hcfg : RootPackCfgSafe c)
    (hi : index < (r2RootPackProgram c).loopCount)
    (hinv : RootPackInvariant index m) :
    RootPackInvariant (index + 1) (rootPackModelStep c index m) := by
  have hsafe := rootPackInvariant_safe c index m hcfg hi hinv
  have hi' : index < (runtimeRoot - 1) * runtimeScale := by
    simpa [r2RootPackProgram] using hi
  have hb := rootPack_index_bounds hi'
  have hex : rootPackExNext index m ≤ 17 := by
    rw [hinv.nextEx]
    have hn0 := rootPackN_pos index
    have hlt : Nat.log2 (rootPackN index) < 18 :=
      (Nat.log2_lt (Nat.ne_of_gt hn0)).mpr
        (Nat.lt_of_le_of_lt hb.2.1 (by decide))
    exact Nat.lt_succ_iff.mp (by simpa using hlt)
  have hxm := logMant_range hsafe.xmInitLo hsafe.xmInitHi
  have haa : rootPackAaNext index m < M := by
    exact Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
      hsafe.fixBound) (by decide)
  have hround : rootPackRound index + 1 ≤ runtimeScale := by
    have := hb.2.2
    omega
  have hmEx : (rootPackModelStep c index m).ex =
      Nat.log2 (rootPackN index) := by
    simpa only [rootPackModelStep] using hinv.nextEx
  have hmTh : (rootPackModelStep c index m).th =
      2 ^ (Nat.log2 (rootPackN index) + 1) := by
    simpa only [rootPackModelStep] using hinv.nextTh
  by_cases hf : rootPackRound index + 1 = runtimeScale
  · have hrel := rootPack_succ_at_finish hf
    have hn0 := rootPackN_pos index
    have hnhi : rootPackN index + 1 ≤
        2 ^ (Nat.log2 (rootPackN index) + 1) := by
      have := Nat.lt_log2_self (n := rootPackN index)
      omega
    have hstart : rootPackStart (index + 1) = 1 := by
      simp [rootPackStart, hrel.2]
    have hnextEx : rootPackExNext (index + 1)
        (rootPackModelStep c index m) =
        Nat.log2 (rootPackN (index + 1)) := by
      simpa [rootPackExNext, rootPackBump, hstart, hmEx, hmTh, hrel.1]
        using (log2_succ_step (Nat.ne_of_gt hn0)).symm
    have hnextTh : rootPackThNext (index + 1)
        (rootPackModelStep c index m) =
        2 ^ (Nat.log2 (rootPackN (index + 1)) + 1) := by
      rw [rootPackThNext, rootPackBump, hstart, hmTh, hrel.1,
        log2_succ_step (Nat.ne_of_gt hn0)]
      by_cases hcut : 2 ^ (Nat.log2 (rootPackN index) + 1) ≤
          rootPackN index + 1
      · have hcut' : 2 * 2 ^ Nat.log2 (rootPackN index) ≤
            rootPackN index + 1 := by
          simpa [Nat.pow_succ, Nat.mul_comm] using hcut
        simp [hcut', Nat.pow_succ, Nat.mul_comm]
        simp only [Nat.two_mul]
      · simp [hcut]
    refine
      { zeroIsZero := by simpa [rootPackModelStep] using hinv.zeroIsZero
        exLe := by simpa [rootPackModelStep] using hex
        thEq := by rw [hmTh, hmEx]
        candidateLeTh := by
          rw [hrel.1, hmTh]
          exact hnhi
        nextEx := hnextEx
        nextTh := hnextTh
        writeLe := ?_
        xmWord := Nat.lt_trans hxm.2 (by decide)
        aaWord := by simpa [rootPackModelStep] using haa
        logState := ?_ }
    · have hhit : rootPackHit index m ≤ 1 := by
        unfold rootPackHit rootPackFinish rootPackPrime
        split <;> split <;> simp
      have hq : (index + 1) / runtimeScale = index / runtimeScale + 1 := by
        have h := hrel.1
        simp only [rootPackN] at h
        omega
      rw [rootPackModelStep, hq]
      exact Nat.add_le_add hinv.writeLe hhit
    · rw [rootPackXmInit, rootPackAaInit, hstart]
      simp only [if_pos, hrel.2, logIter]
      constructor
      · simpa only [rootPackNorm] using congrArg
          (fun e => rootPackN (index + 1) <<< (62 - e)) hnextEx
      · trivial
  · have hbefore : rootPackRound index + 1 < runtimeScale := by omega
    have hrel := rootPack_succ_before_finish hbefore
    have hstart : rootPackStart (index + 1) = 0 := by
      simp [rootPackStart, hrel.2]
    have hnextEx : rootPackExNext (index + 1)
        (rootPackModelStep c index m) =
        Nat.log2 (rootPackN (index + 1)) := by
      simp [rootPackExNext, rootPackBump, hstart, hmEx, hrel.1]
    have hnextTh : rootPackThNext (index + 1)
        (rootPackModelStep c index m) =
        2 ^ (Nat.log2 (rootPackN (index + 1)) + 1) := by
      simp [rootPackThNext, rootPackBump, hstart, hmTh, hrel.1]
    refine
      { zeroIsZero := by simpa [rootPackModelStep] using hinv.zeroIsZero
        exLe := by simpa [rootPackModelStep] using hex
        thEq := by rw [hmTh, hmEx]
        candidateLeTh := by
          rw [hrel.1, hmTh]
          exact Nat.le_of_lt Nat.lt_log2_self
        nextEx := hnextEx
        nextTh := hnextTh
        writeLe := ?_
        xmWord := Nat.lt_trans hxm.2 (by decide)
        aaWord := by simpa [rootPackModelStep] using haa
        logState := ?_ }
    · have hq : (index + 1) / runtimeScale = index / runtimeScale := by
        have h := hrel.1
        simp only [rootPackN] at h
        omega
      rw [rootPackModelStep, hq]
      have hfinish : rootPackFinish index = 0 := by
        simp [rootPackFinish, hf]
      simp [rootPackHit, hfinish, hinv.writeLe]
    · rw [rootPackXmInit, rootPackAaInit, hstart]
      simp only [Nat.zero_ne_one, if_false, rootPackModelStep]
      have hnorm : rootPackNorm (index + 1) = rootPackNorm index := by
        simp only [rootPackNorm, hrel.1]
      rw [hrel.2, hnorm]
      simp only [rootPackXmNext, rootPackAaNext, logIter, logStep,
        hinv.logState.1, hinv.logState.2, Nat.shiftLeft_eq, Nat.pow_one]
      refine ⟨trivial, ?_⟩
      rw [Nat.mul_comm _ 2]

theorem rootPackDecode_defined (c : R2Cfg) (index : Nat) (s : AState)
    (hRoot : runtimeRoot < c.arrayLen)
    (hi : index < (r2RootPackProgram c).loopCount) :
    AllDefined c.arrayLen index s rootPackDecode := by
  have hb := rootPack_index_bounds (index := index) (by
    simpa [r2RootPackProgram] using hi)
  have hiM : index % M = index := Nat.mod_eq_of_lt hb.1
  have hsM : runtimeScale % M = runtimeScale := Nat.mod_eq_of_lt (by decide)
  have hsne : runtimeScale % M ≠ 0 := by rw [hsM]; decide
  have hnM : rootPackN index % M = rootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.1 (by decide))
  have hncell : rootPackN index < c.arrayLen :=
    Nat.lt_of_le_of_lt hb.2.1 hRoot
  have hnRawM : (index / runtimeScale + 2) % M =
      index / runtimeScale + 2 := by
    simpa [rootPackN] using hnM
  have h24M : 24 % M = 24 := Nat.mod_eq_of_lt (by decide)
  have h24ne : 24 % M ≠ 0 := by rw [h24M]; decide
  have hqM : (index / 24) % M = index / 24 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb.1)
  have hnRaw24M : (index / 24 + 2) % M = index / 24 + 2 := by
    simpa [runtimeScale] using hnRawM
  simp [rootPackDecode, AllDefined, ADefined, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, rootPackN, runtimeScale,
    hiM, hsM, hsne, hnM, hnRawM, hncell]
  constructor
  · exact h24ne
  · rw [if_neg h24ne, Option.getD_some, h24M, hqM, hnRaw24M]
    simpa [rootPackN, runtimeScale] using hncell

theorem rootPackDecode_run (c : R2Cfg) (index : Nat) (s : AState)
    (hi : index < (r2RootPackProgram c).loopCount) :
    let out := arun index s rootPackDecode
    out.regs 11 = rootPackN index ∧
      out.regs 12 = rootPackRound index ∧
      out.regs 13 = (if rootPackRound index = 0 then 1 else 0) ∧
      out.regs 15 = (if rootPackRound index + 1 = runtimeScale then 1 else 0) ∧
      out.regs 16 = s.arr (rootPackN index) ∧
      out.regs 17 = (if s.arr (rootPackN index) = 0 then 1 else 0) ∧
      out.arr = s.arr := by
  have hb := rootPack_index_bounds (index := index) (by
    simpa [r2RootPackProgram] using hi)
  have hiM : index % M = index := Nat.mod_eq_of_lt hb.1
  have hsM : runtimeScale % M = runtimeScale := Nat.mod_eq_of_lt (by decide)
  have hsne : runtimeScale % M ≠ 0 := by rw [hsM]; decide
  have hnM : rootPackN index % M = rootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.1 (by decide))
  have hrM : rootPackRound index % M = rootPackRound index :=
    Nat.mod_eq_of_lt (Nat.lt_trans hb.2.2 (by decide))
  have hnRawM : (index / runtimeScale + 2) % M =
      index / runtimeScale + 2 := by
    simpa [rootPackN] using hnM
  have hroundRaw :
      (if runtimeScale % M = 0 then none
        else some (index % M % (runtimeScale % M))).getD 0 =
          rootPackRound index := by
    rw [if_neg hsne, Option.getD_some, hiM, hsM]
    rfl
  have hrSuccM : (rootPackRound index + 1) % M =
      rootPackRound index + 1 := Nat.mod_eq_of_lt (by
    exact Nat.lt_trans (Nat.add_lt_add_right hb.2.2 1) (by decide))
  have h24M : 24 % M = 24 := Nat.mod_eq_of_lt (by decide)
  have h24ne : 24 % M ≠ 0 := by rw [h24M]; decide
  have hqM : (index / 24) % M = index / 24 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb.1)
  have hnRaw24M : (index / 24 + 2) % M = index / 24 + 2 := by
    simpa [runtimeScale] using hnRawM
  have hNdecode :
      ((if 24 % M = 0 then none else some (index / (24 % M) % M)).getD 0 + 2) % M =
        index / 24 + 2 := by
    rw [if_neg h24ne, Option.getD_some, h24M, hqM, hnRaw24M]
  have hRdecode :
      (if 24 % M = 0 then none else some (index % (24 % M) % M)).getD 0 =
        index % 24 := by
    rw [if_neg h24ne, Option.getD_some, h24M]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  simp [rootPackDecode, arun, astep, sval, sdest, denoteOperand, denoteOp,
    AState.writeReg, rootPackN, rootPackRound, runtimeScale, hiM, hsM,
    hsne, hnM, hnRawM, hroundRaw, hrM, hrSuccM, hNdecode, hRdecode,
    h24M, h24ne]
  have hr24M : index % 24 % M = index % 24 := by
    simpa [rootPackRound, runtimeScale] using hrM
  have hrSucc24M : (index % 24 + 1) % M = index % 24 + 1 := by
    simpa [rootPackRound, runtimeScale] using hrSuccM
  have hfinish :
      (if (index % 24 + 1) % M = 24 then 1 else 0) =
        if index % 24 = 23 then 1 else 0 := by
    rw [hrSucc24M]
    have hrlt : index % 24 < 24 := Nat.mod_lt _ (by decide)
    by_cases h : index % 24 = 23 <;> simp [h] <;> omega
  exact ⟨hnRaw24M, hr24M,
    congrArg (fun z => if z = 0 then 1 else 0) hr24M,
    hfinish, congrArg s.arr hnRaw24M,
    congrArg (fun z => if s.arr z = 0 then 1 else 0) hnRaw24M⟩

theorem rootPackRoundInit_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackRoundInit := by
  rw [rootPackRoundInit, AllDefined_append]
  constructor
  · exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
      len index rootPackExponentS s (by decide)
  · exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
      len index rootPackMantissaInitS _ (by decide)

theorem rootPackLogRound_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackLogRound := by
  exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    len index rootPackLogRoundS s (by decide)

theorem rootPackLn_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackLn := by
  exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    len index rootPackLnS s (by decide)

/-! ## Incremental exponent and mantissa initialization -/

theorem rootPackExponentS_run (k : Nat) (s : RegState)
    (n e th start : Nat)
    (h11 : s 11 = n) (h13 : s 13 = start)
    (he : s rpEx = e) (hth : s rpTh = th)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M) :
    let bump := if th ≤ n then start else 0
    let out := srun k s rootPackExponentS
    out rpEx = e + bump ∧ out rpTh = th + bump * th := by
  have he0M : e < M := by omega
  have hth0M : th < M := by omega
  have he' : s 2 = e := by simpa only [rpEx] using he
  have hth' : s 3 = th := by simpa only [rpTh] using hth
  rcases hstart with rfl | rfl
  · by_cases hn : th ≤ n <;>
      simp [rootPackExponentS, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, h11, h13, he', hth', hn,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M, rpEx, rpTh]
  · by_cases hn : th ≤ n <;>
      simp [rootPackExponentS, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, h11, h13, he', hth', hn,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M,
        Nat.mod_eq_of_lt heM, Nat.mod_eq_of_lt hthM, rpEx, rpTh]

theorem rootPackExponent_run (k : Nat) (s : AState)
    (n e th start : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hth : s.regs rpTh = th)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M) :
    let bump := if th ≤ n then start else 0
    let out := arun k s rootPackExponent
    out.regs rpEx = e + bump ∧ out.regs rpTh = th + bump * th ∧
      out.arr = s.arr := by
  rw [rootPackExponent,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackExponentS_run k s.regs n e th start
    h11 h13 he hth hstart heM hthM
  exact ⟨h.1, h.2, rfl⟩

theorem rootPackMantissaInitS_run (k : Nat) (s : RegState)
    (n e start x a : Nat)
    (h11 : s 11 = n) (h13 : s 13 = start) (he : s rpEx = e)
    (hx : s rpXm = x) (ha : s rpAa = a)
    (hstart : start = 0 ∨ start = 1) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := srun k s rootPackMantissaInitS
    (out rpXm = if start = 1 then n <<< (62 - e) else x) ∧
      (out rpAa = if start = 1 then 0 else a) := by
  have hsub : (62 + (M - e)) % M = 62 - e := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 62) (b := e) he62 (by decide)
    exact Option.some.inj hs
  have hmask : (63 : Nat) % M = 63 := by decide
  have hshift : (62 - e) &&& 63 = 62 - e := by
    have hlt : 62 - e < 64 := by omega
    change (62 - e) &&& (2 ^ 6 - 1) = 62 - e
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  have hshiftM : 62 - e < M :=
    Nat.lt_trans (show 62 - e < 64 by omega) (by decide)
  have he' : s 2 = e := by simpa only [rpEx] using he
  have hx' : s 5 = x := by simpa only [rpXm] using hx
  have ha' : s 6 = a := by simpa only [rpAa] using ha
  have hOnePred : 1 + (M - 1) = M := by omega
  rcases hstart with rfl | rfl
  · simp [rootPackMantissaInitS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h11, h13, he', hx', ha', hsub, hmask, hshift,
      Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
      Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM, hOnePred,
      rpEx, rpXm, rpAa]
    all_goals simp [Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM,
      Nat.add_mod, Nat.mul_mod, hOnePred]
  · simp [rootPackMantissaInitS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h11, h13, he', hx', ha', hsub, hmask, hshift,
      Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
      Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM, hOnePred,
      rpEx, rpXm, rpAa]
    all_goals simp [Nat.mod_eq_of_lt hnorm, Nat.add_mod, Nat.mul_mod,
      hOnePred]

theorem rootPackMantissaInit_run (k : Nat) (s : AState)
    (n e start x a : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hstart : start = 0 ∨ start = 1) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := arun k s rootPackMantissaInit
    (out.regs rpXm = if start = 1 then n <<< (62 - e) else x) ∧
      (out.regs rpAa = if start = 1 then 0 else a) ∧ out.arr = s.arr := by
  rw [rootPackMantissaInit,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackMantissaInitS_run k s.regs n e start x a
    h11 h13 he hx ha hstart he62 hnorm hxM haM
  exact ⟨h.1, h.2, rfl⟩

/-- Exact composition of the two initialization slices.  This theorem is
symbolic in the candidate and persistent state; it does not enumerate the
production table. -/
theorem rootPackRoundInit_run (k : Nat) (s : AState)
    (n e th start x a : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hth : s.regs rpTh = th)
    (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M)
    (he62 : e + (if th ≤ n then start else 0) ≤ 62)
    (hnorm : n <<< (62 - (e + (if th ≤ n then start else 0))) < M)
    (hxM : x < M) (haM : a < M) :
    let bump := if th ≤ n then start else 0
    let out := arun k s rootPackRoundInit
    out.regs rpEx = e + bump ∧
      out.regs rpTh = th + bump * th ∧
      out.regs rpXm =
        (if start = 1 then n <<< (62 - (e + bump)) else x) ∧
      out.regs rpAa = (if start = 1 then 0 else a) ∧
      out.arr = s.arr := by
  let bump := if th ≤ n then start else 0
  let mid := arun k s rootPackExponent
  have hExp := rootPackExponent_run k s n e th start
    h11 h13 he hth hstart heM hthM
  dsimp only at hExp
  have h11mid : mid.regs 11 = n := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 11 rootPackExponent (by decide) s).trans h11
  have h13mid : mid.regs 13 = start := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 13 rootPackExponent (by decide) s).trans h13
  have hxmid : mid.regs rpXm = x := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpXm rootPackExponent (by decide) s).trans hx
  have hamid : mid.regs rpAa = a := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpAa rootPackExponent (by decide) s).trans ha
  have hMant := rootPackMantissaInit_run k mid n (e + bump) start x a
    h11mid h13mid (by simpa only [mid, bump] using hExp.1)
    hxmid hamid hstart (by simpa only [bump] using he62)
    (by simpa only [bump] using hnorm) hxM haM
  dsimp only at hMant
  rw [rootPackRoundInit, arun_append]
  change
    (arun k mid rootPackMantissaInit).regs rpEx = e + bump ∧
      (arun k mid rootPackMantissaInit).regs rpTh = th + bump * th ∧
      _
  have hExFrame := LeanCompCert.Verified.ArrayRegFrame.arun_frame
    k rpEx rootPackMantissaInit (by decide) mid
  have hThFrame := LeanCompCert.Verified.ArrayRegFrame.arun_frame
    k rpTh rootPackMantissaInit (by decide) mid
  exact ⟨hExFrame.trans hExp.1, hThFrame.trans hExp.2.1,
    hMant.1, hMant.2.1, hMant.2.2.trans hExp.2.2⟩

/-! ## Relocated fixed-log round -/

/-- Relocate the standalone fixed-log inputs to the packer's persistent
registers and its scratch registers to `27,...,44`. -/
def rootPackLogReg : Nat → Nat
  | 0 => rpXm
  | 1 => rpAa
  | n + 2 => n + 27

theorem rootPackLogReg_injective : Function.Injective rootPackLogReg := by
  intro a b h
  rcases a with (_ | _ | a) <;> rcases b with (_ | _ | b) <;>
    simp [rootPackLogReg, rpXm, rpAa] at h ⊢ <;> omega

theorem rootPackLogRoundS_eq_rename :
    rootPackLogRoundS =
      LeanCompCert.Ports.LogFixPort.logRoundBody.map
        (renameInstr rootPackLogReg) := by
  rfl

/-- The packer's compiled twenty-instruction block is the already verified
fixed-log recurrence, merely under a different register allocation. -/
theorem rootPackLogRoundS_run_of_range (k : Nat) (s : RegState) (x a : Nat)
    (hx : s rpXm = x) (ha : s rpAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := srun k s rootPackLogRoundS
    out rpXm = logMant x ∧ out rpAa = (a <<< 1) + logBit x := by
  let base : RegState := fun r => s (rootPackLogReg r)
  have hbase := LeanCompCert.Ports.LogFixPort.logRoundBody_srun_of_range
    k base x a (by
      simpa [base, rootPackLogReg, LeanCompCert.Ports.LogFixPort.rX] using hx)
      (by
        simpa [base, rootPackLogReg, LeanCompCert.Ports.LogFixPort.rA] using ha)
      hxlo hxhi haBound
  have hrename := srun_rename k rootPackLogReg rootPackLogReg_injective
    LeanCompCert.Ports.LogFixPort.logRoundBody base s (by
      intro r
      rfl)
  constructor
  · rw [show rpXm = rootPackLogReg LeanCompCert.Ports.LogFixPort.rX by rfl]
    rw [rootPackLogRoundS_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rX).trans hbase.1
  · rw [show rpAa = rootPackLogReg LeanCompCert.Ports.LogFixPort.rA by rfl]
    rw [rootPackLogRoundS_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rA).trans hbase.2

theorem rootPackLogRound_run_of_range (k : Nat) (s : AState) (x a : Nat)
    (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := arun k s rootPackLogRound
    out.regs rpXm = logMant x ∧
      out.regs rpAa = (a <<< 1) + logBit x ∧ out.arr = s.arr := by
  rw [rootPackLogRound,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackLogRoundS_run_of_range k s.regs x a
    hx ha hxlo hxhi haBound
  exact ⟨h.1, h.2, rfl⟩

theorem rootPack_logIter_fst_range (x0 : Nat)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) : ∀ rounds : Nat,
    B62 ≤ (logIter x0 rounds).1 ∧ (logIter x0 rounds).1 < B63 := by
  intro rounds
  induction rounds with
  | zero => exact ⟨hxlo, hxhi⟩
  | succ rounds ih =>
      simpa only [logIter, logStep] using logMant_range ih.1 ih.2

/-- Symbolic telescope for an arbitrary list of compiled round invocations.
Only the list length is used; no production candidate range is evaluated. -/
theorem rootPack_foldl_logRound_from_iter (indices : List Nat) (s : AState)
    (x0 : Nat) (j : Nat)
    (hx : s.regs rpXm = (logIter x0 j).1)
    (ha : s.regs rpAa = (logIter x0 j).2)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hcount : j + indices.length ≤ 62) :
    let out := indices.foldl (fun st k => arun k st rootPackLogRound) s
    out.regs rpXm = (logIter x0 (j + indices.length)).1 ∧
      out.regs rpAa = (logIter x0 (j + indices.length)).2 ∧
      out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [List.foldl, List.length_nil, Nat.add_zero]
      exact ⟨hx, ha, trivial⟩
  | cons k ks ih =>
      have hj : j < 62 := by
        simp only [List.length_cons] at hcount
        omega
      have haLt := logIter_snd_lt_two_pow x0 j
      have haBound : (logIter x0 j).2 < B62 := by
        have hjPow : 2 ^ j ≤ 2 ^ 61 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hpow : (2 : Nat) ^ 61 < B62 := by decide
        omega
      have hrange := rootPack_logIter_fst_range x0 hxlo hxhi j
      let next := arun k s rootPackLogRound
      have hstep := rootPackLogRound_run_of_range k s
        (logIter x0 j).1 (logIter x0 j).2 hx ha
        hrange.1 hrange.2 haBound
      dsimp only at hstep
      have hxNext : next.regs rpXm = (logIter x0 (j + 1)).1 := by
        simpa only [next, logIter, logStep] using hstep.1
      have haNext : next.regs rpAa = (logIter x0 (j + 1)).2 := by
        simpa only [next, logIter, logStep, Nat.shiftLeft_eq,
          Nat.pow_one, Nat.mul_comm] using hstep.2.1
      have hrest : j + 1 + ks.length ≤ 62 := by
        simp only [List.length_cons] at hcount
        omega
      have hout := ih next (j + 1) hxNext haNext hrest
      dsimp only at hout
      simp only [List.foldl, List.length_cons]
      have hindex : j + 1 + ks.length = j + (ks.length + 1) := by omega
      exact ⟨hout.1.trans (congrArg (fun z => (logIter x0 z).1) hindex),
        hout.2.1.trans (congrArg (fun z => (logIter x0 z).2) hindex),
        hout.2.2.trans hstep.2.2⟩

theorem rootPack_foldl_logRound_24 (indices : List Nat) (s : AState)
    (x0 : Nat) (hlen : indices.length = runtimeScale)
    (hx : s.regs rpXm = x0) (ha : s.regs rpAa = 0)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) :
    let out := indices.foldl (fun st k => arun k st rootPackLogRound) s
    out.regs rpXm = (logIter x0 runtimeScale).1 ∧
      out.regs rpAa = logFrac runtimeScale x0 ∧ out.arr = s.arr := by
  have h := rootPack_foldl_logRound_from_iter indices s x0 0
    (by simpa [logIter] using hx) (by simpa [logIter] using ha)
    hxlo hxhi (by simpa [hlen, runtimeScale])
  simpa only [Nat.zero_add, hlen, logFrac] using h

/-! ## Relocated natural-log conversion -/

/-- Swap the conversion block's production registers `251,...,262` with the
packer's compact allocation `46,...,57`, fixing every other register. -/
def rootPackLnReg (n : Nat) : Nat :=
  if n < 46 then n
  else if n < 58 then n + 205
  else if n < 251 then n
  else if n < 263 then n - 205
  else n

theorem rootPackLnReg_injective : Function.Injective rootPackLnReg := by
  intro a b h
  simp only [rootPackLnReg] at h
  repeat' first | split at h
  all_goals omega

theorem rootPackLnConvertS_eq_rename :
    rootPackLnConvertS = lnFixConvertInstrs.map (renameInstr rootPackLnReg) := by
  rfl

theorem rootPackLnConvertS_run (k : Nat) (s : RegState) (a : Nat)
    (ha : a < 2 ^ 30) (h46 : s 46 = a) :
    (srun k s rootPackLnConvertS) 57 =
      a * LeanCompCert.Ports.PsiSegSieve.L2 / 2 ^ 64 := by
  let base : RegState := fun r => s (rootPackLnReg r)
  have hbase := lnFixConvertInstrs_run k base a ha (by
    simpa [base, rootPackLnReg] using h46)
  have hrename := srun_rename k rootPackLnReg rootPackLnReg_injective
    lnFixConvertInstrs base s (by
      intro r
      rfl)
  rw [show (57 : Nat) = rootPackLnReg 262 by rfl]
  rw [rootPackLnConvertS_eq_rename]
  exact (hrename 262).trans hbase

theorem rootPackLnConvertS_logFix_run (k : Nat) (s : RegState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30) (h46 : s 46 = logFix S n) :
    (srun k s rootPackLnConvertS) 57 =
      LeanCompCert.Ports.PsiSegSieve.lnFix S n := by
  let base : RegState := fun r => s (rootPackLnReg r)
  have hbase := lnFixConvertInstrs_logFix_run k base S n ha (by
    simpa [base, rootPackLnReg] using h46)
  have hrename := srun_rename k rootPackLnReg rootPackLnReg_injective
    lnFixConvertInstrs base s (by
      intro r
      rfl)
  rw [show (57 : Nat) = rootPackLnReg 262 by rfl]
  rw [rootPackLnConvertS_eq_rename]
  exact (hrename 262).trans hbase

theorem rootPackLnConvert_logFix_run (k : Nat) (s : AState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30) (h46 : s.regs 46 = logFix S n) :
    let out := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift rootPackLnConvertS)
    out.regs 57 = LeanCompCert.Ports.PsiSegSieve.lnFix S n ∧
      out.arr = s.arr := by
  rw [LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackLnConvertS_logFix_run k s.regs S n ha h46, rfl⟩

/-! ## Fixed-log assembly and natural-log composition -/

theorem rootPackLnPrefixS_run (k : Nat) (s : RegState) (e a : Nat)
    (he : s rpEx = e) (ha : s rpAa = a)
    (heM : e * 2 ^ runtimeScale < M)
    (hsumM : e * 2 ^ runtimeScale + a < M) :
    (srun k s rootPackLnPrefixS) 46 = e * 2 ^ runtimeScale + a := by
  have h24M : runtimeScale % M = runtimeScale := by decide
  have he' : s 2 = e := by simpa only [rpEx] using he
  have ha' : s 6 = a := by simpa only [rpAa] using ha
  change
    ((((s 2 <<< (runtimeScale % M)) % M) + s 6) % M) =
      e * 2 ^ runtimeScale + a
  rw [he', ha', h24M, Nat.shiftLeft_eq, Nat.mod_eq_of_lt heM,
    Nat.mod_eq_of_lt hsumM]

theorem rootPackLnPrefixS_logFix_run (k : Nat) (s : RegState) (n : Nat)
    (he : s rpEx = Nat.log2 n)
    (ha : s rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    (srun k s rootPackLnPrefixS) 46 = logFix runtimeScale n := by
  have hfixM : logFix runtimeScale n < M :=
    Nat.lt_trans hfix (by decide)
  have heM : Nat.log2 n * 2 ^ runtimeScale < M := by
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by
      simpa only [logFix] using hfixM)
  have hp := rootPackLnPrefixS_run k s (Nat.log2 n)
    (logFrac runtimeScale (n <<< (62 - Nat.log2 n))) he ha heM (by
      simpa only [logFix] using hfixM)
  simpa only [logFix] using hp

theorem rootPackLnS_run (k : Nat) (s : RegState) (e a : Nat)
    (he : s rpEx = e) (ha : s rpAa = a)
    (hfix : e * 2 ^ runtimeScale + a < 2 ^ 30) :
    (srun k s rootPackLnS) 57 = rootPackLnValue e a := by
  let mid := srun k s rootPackLnPrefixS
  have hprefix := rootPackLnPrefixS_run k s e a he ha
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hfix)
      (by decide))
    (Nat.lt_trans hfix (by decide))
  have hconvert := rootPackLnConvertS_run k mid
    (e * 2 ^ runtimeScale + a) hfix
    (by simpa only [mid] using hprefix)
  rw [rootPackLnS, srun_append]
  exact hconvert

theorem rootPackLn_run (k : Nat) (s : AState) (e a : Nat)
    (he : s.regs rpEx = e) (ha : s.regs rpAa = a)
    (hfix : e * 2 ^ runtimeScale + a < 2 ^ 30) :
    let out := arun k s rootPackLn
    out.regs 57 = rootPackLnValue e a ∧ out.arr = s.arr := by
  rw [rootPackLn, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackLnS_run k s.regs e a he ha hfix, rfl⟩

theorem rootPackLnS_logFix_run (k : Nat) (s : RegState) (n : Nat)
    (he : s rpEx = Nat.log2 n)
    (ha : s rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    (srun k s rootPackLnS) 57 =
      LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale n := by
  let mid := srun k s rootPackLnPrefixS
  have hprefix := rootPackLnPrefixS_logFix_run k s n he ha hfix
  have hconvert := rootPackLnConvertS_logFix_run k mid runtimeScale n
    hfix (by simpa only [mid] using hprefix)
  rw [rootPackLnS, srun_append]
  exact hconvert

theorem rootPackLn_logFix_run (k : Nat) (s : AState) (n : Nat)
    (he : s.regs rpEx = Nat.log2 n)
    (ha : s.regs rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    let out := arun k s rootPackLn
    out.regs 57 = LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale n ∧
      out.arr = s.arr := by
  rw [rootPackLn, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackLnS_logFix_run k s.regs n he ha hfix, rfl⟩

/-! ## Selected-entry store islands -/

theorem rootPackStoreGateS_run (k : Nat) (s : RegState)
    (finish prime : Nat)
    (h15 : s 15 = finish) (h17 : s 17 = prime)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1) :
    (srun k s rootPackStoreGateS) 58 = finish * prime := by
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by decide)
  rcases hfinish with rfl | rfl <;> rcases hprime with rfl | rfl <;>
    simp [rootPackStoreGateS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h15, h17, h1M]

theorem rootPackStoreGate_run (k : Nat) (s : AState)
    (finish prime : Nat)
    (h15 : s.regs 15 = finish) (h17 : s.regs 17 = prime)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1) :
    let out := arun k s rootPackStoreGate
    out.regs 58 = finish * prime ∧ out.arr = s.arr := by
  rw [rootPackStoreGate,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreGateS_run k s.regs finish prime
    h15 h17 hfinish hprime, rfl⟩

theorem rootPackStoreTargetS_run (c : R2Cfg) (k : Nat) (s : RegState)
    (hit w : Nat) (h58 : s 58 = hit) (hw : s rpWrite = w)
    (hhit : hit = 0 ∨ hit = 1)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M) :
    (srun k s (rootPackStoreTargetS c)) 63 =
      if hit = 1 then w + c.tableBase else c.streamSink := by
  have htableM : c.tableBase % M = c.tableBase := Nat.mod_eq_of_lt htable
  have hsinkM : c.streamSink % M = c.streamSink := Nat.mod_eq_of_lt hsink
  have hwtableM : (w + c.tableBase) % M = w + c.tableBase :=
    Nat.mod_eq_of_lt hwtable
  have hwM : w % M = w := Nat.mod_eq_of_lt (by omega)
  have hw' : s 4 = w := by simpa only [rpWrite] using hw
  have hOnePred : 1 + (M - 1) = M := by omega
  rcases hhit with rfl | rfl <;>
    simp [rootPackStoreTargetS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h58, hw', htableM, hsinkM, hwtableM,
      hwM, hOnePred, rpWrite]

theorem rootPackStoreTarget_run (c : R2Cfg) (k : Nat) (s : AState)
    (hit w : Nat) (h58 : s.regs 58 = hit) (hw : s.regs rpWrite = w)
    (hhit : hit = 0 ∨ hit = 1)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M) :
    let out := arun k s (rootPackStoreTarget c)
    out.regs 63 =
      (if hit = 1 then w + c.tableBase else c.streamSink) ∧
      out.arr = s.arr := by
  rw [rootPackStoreTarget,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreTargetS_run c k s.regs hit w h58 hw hhit
    htable hsink hwtable, rfl⟩

theorem rootPackStoreValueS_run (k : Nat) (s : RegState) (n ln : Nat)
    (hn : s 11 = n) (hln : s 57 = ln)
    (hshift : ln * 2 ^ valBits < M)
    (hlow : n + ln * 2 ^ valBits < M)
    (hpack : packEntry n ln 1 < M) :
    (srun k s rootPackStoreValueS) 66 = packEntry n ln 1 := by
  have hvalM : valBits % M = valBits := Nat.mod_eq_of_lt (by decide)
  have hshiftM : (ln * 2 ^ valBits) % M = ln * 2 ^ valBits :=
    Nat.mod_eq_of_lt hshift
  have hlowM : (n + ln * 2 ^ valBits) % M = n + ln * 2 ^ valBits :=
    Nat.mod_eq_of_lt hlow
  have hpackEq : packEntry n ln 1 = n + ln * 2 ^ valBits + B63 := by
    rw [packEntry, Nat.one_mul, B63_eq]
  have hsum : n + ln * 2 ^ valBits + B63 < M := by
    rw [← hpackEq]
    exact hpack
  have h64 : (srun k s [rootPackStoreShiftI]) 64 =
      ln * 2 ^ valBits := by
    rw [show [rootPackStoreShiftI] = [] ++ [rootPackStoreShiftI] by rfl,
      LeanCompCert.Verified.RegFrame.srun_read_last k 64 []
        rootPackStoreShiftI (by rfl) s]
    change ((s 57 <<< (valBits % M)) % M) = ln * 2 ^ valBits
    rw [hln, hvalM, Nat.shiftLeft_eq, hshiftM]
  have h11frame : (srun k s [rootPackStoreShiftI]) 11 = s 11 :=
    LeanCompCert.Verified.RegFrame.srun_frame k 11
      [rootPackStoreShiftI] (by decide) s
  have h65 : (srun k s [rootPackStoreShiftI, rootPackStoreLowI]) 65 =
      n + ln * 2 ^ valBits := by
    rw [show [rootPackStoreShiftI, rootPackStoreLowI] =
        [rootPackStoreShiftI] ++ [rootPackStoreLowI] by rfl,
      LeanCompCert.Verified.RegFrame.srun_read_last k 65
        [rootPackStoreShiftI] rootPackStoreLowI (by rfl) s]
    change
      (((srun k s [rootPackStoreShiftI]) 11 +
        (srun k s [rootPackStoreShiftI]) 64) % M) =
          n + ln * 2 ^ valBits
    rw [h11frame, hn, h64, hlowM]
  rw [show rootPackStoreValueS =
      [rootPackStoreShiftI, rootPackStoreLowI] ++ [rootPackStoreFlagI] by rfl,
    LeanCompCert.Verified.RegFrame.srun_read_last k 66
      [rootPackStoreShiftI, rootPackStoreLowI] rootPackStoreFlagI (by rfl) s]
  rw [rootPackStoreFlagI]
  calc
    sval k (srun k s [rootPackStoreShiftI, rootPackStoreLowI])
        (.binop 66 .add (.reg 65) (.lit B63)) =
        n + ln * 2 ^ valBits + B63 :=
      LeanCompCert.Verified.BlockDefined.sval_binop_val
        (by
          rw [LeanCompCert.Verified.BlockDefined.denoteOperand_reg, h65])
        (LeanCompCert.Verified.BlockDefined.denoteOperand_lit_of_lt
          k _ (by decide))
        (LeanCompCert.Verified.BlockDefined.denoteOp_add_of_lt hsum)
    _ = packEntry n ln 1 := hpackEq.symm

theorem rootPackStoreValue_run (k : Nat) (s : AState) (n ln : Nat)
    (hn : s.regs 11 = n) (hln : s.regs 57 = ln)
    (hshift : ln * 2 ^ valBits < M)
    (hlow : n + ln * 2 ^ valBits < M)
    (hpack : packEntry n ln 1 < M) :
    let out := arun k s rootPackStoreValue
    out.regs 66 = packEntry n ln 1 ∧ out.arr = s.arr := by
  rw [rootPackStoreValue,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreValueS_run k s.regs n ln hn hln
    hshift hlow hpack, rfl⟩

theorem rootPackStoreCommit_run (k : Nat) (s : AState)
    (target value w hit : Nat)
    (h63 : s.regs 63 = target) (h66 : s.regs 66 = value)
    (hw : s.regs rpWrite = w) (h58 : s.regs 58 = hit)
    (hsum : w + hit < M) :
    let out := arun k s rootPackStoreCommit
    out.regs rpWrite = w + hit ∧
      ∀ x, out.arr x = if x = target then value else s.arr x := by
  have hsumM : (w + hit) % M = w + hit := Nat.mod_eq_of_lt hsum
  have hw' : s.regs 4 = w := by simpa only [rpWrite] using hw
  simp [rootPackStoreCommit, arun, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, AState.writeArr,
    h63, h66, hw', h58, hsumM, rpWrite]

theorem rootPackStoreCommit_defined (len k : Nat) (s : AState)
    (target : Nat) (h63 : s.regs 63 = target) (htarget : target < len) :
    AllDefined len k s rootPackStoreCommit := by
  simp [rootPackStoreCommit, AllDefined, ADefined, h63, htarget,
    astep, sval, sdest, denoteOperand, denoteOp, AState.writeArr]

theorem rootPackStore_defined (c : R2Cfg) (k : Nat) (s : AState)
    (finish prime w : Nat)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1)
    (h15 : s.regs 15 = finish) (h17 : s.regs 17 = prime)
    (hw : s.regs rpWrite = w)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M)
    (hsinkCell : c.streamSink < c.arrayLen)
    (hwtableCell : w + c.tableBase < c.arrayLen) :
    AllDefined c.arrayLen k s (rootPackStore c) := by
  let hit := finish * prime
  let sg := arun k s rootPackStoreGate
  let st := arun k sg (rootPackStoreTarget c)
  let sv := arun k st rootPackStoreValue
  have hhit : hit = 0 ∨ hit = 1 := by
    rcases hfinish with rfl | rfl <;> rcases hprime with rfl | rfl <;>
      simp [hit]
  have hG := rootPackStoreGate_run k s finish prime
    h15 h17 hfinish hprime
  dsimp only at hG
  have hwg : sg.regs rpWrite = w :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpWrite rootPackStoreGate rfl s).trans hw
  have hT := rootPackStoreTarget_run c k sg hit w
    (by simpa only [sg, hit] using hG.1) hwg hhit
    htable hsink hwtable
  dsimp only at hT
  have h63v : sv.regs 63 =
      (if hit = 1 then w + c.tableBase else c.streamSink) :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 63 rootPackStoreValue rfl st).trans hT.1
  have htarget :
      (if hit = 1 then w + c.tableBase else c.streamSink) < c.arrayLen := by
    split <;> assumption
  rw [rootPackStore]
  apply (AllDefined_append c.arrayLen k rootPackStoreGate _ s).mpr
  refine ⟨LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    c.arrayLen k rootPackStoreGateS s (by decide), ?_⟩
  apply (AllDefined_append c.arrayLen k (rootPackStoreTarget c) _ sg).mpr
  refine ⟨LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    c.arrayLen k (rootPackStoreTargetS c) sg
      (by simp [rootPackStoreTargetS, NoDivI]), ?_⟩
  apply (AllDefined_append c.arrayLen k rootPackStoreValue
    rootPackStoreCommit st).mpr
  refine ⟨LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    c.arrayLen k rootPackStoreValueS st (by decide), ?_⟩
  exact rootPackStoreCommit_defined c.arrayLen k sv _ h63v htarget

/-- Composition of the four store islands.  The theorem is parametric in one
candidate; the production candidate range is executed only by compiled C. -/
theorem rootPackStore_run (c : R2Cfg) (k : Nat) (s : AState)
    (finish prime w n ln : Nat)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1)
    (h15 : s.regs 15 = finish) (h17 : s.regs 17 = prime)
    (hw : s.regs rpWrite = w) (hn : s.regs 11 = n)
    (hln : s.regs 57 = ln)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M)
    (hshift : ln * 2 ^ valBits < M)
    (hlow : n + ln * 2 ^ valBits < M)
    (hpack : packEntry n ln 1 < M)
    (hwsum : w + finish * prime < M) :
    let hit := finish * prime
    let target := if hit = 1 then w + c.tableBase else c.streamSink
    let out := arun k s (rootPackStore c)
    out.regs rpWrite = w + hit ∧
      ∀ x, out.arr x =
        if x = target then packEntry n ln 1 else s.arr x := by
  let hit := finish * prime
  let sg := arun k s rootPackStoreGate
  let st := arun k sg (rootPackStoreTarget c)
  let sv := arun k st rootPackStoreValue
  have hhit : hit = 0 ∨ hit = 1 := by
    rcases hfinish with rfl | rfl <;> rcases hprime with rfl | rfl <;>
      simp [hit]
  have hG := rootPackStoreGate_run k s finish prime
    h15 h17 hfinish hprime
  dsimp only at hG
  have hwg : sg.regs rpWrite = w :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpWrite rootPackStoreGate rfl s).trans hw
  have h11g : sg.regs 11 = n :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 11 rootPackStoreGate rfl s).trans hn
  have h57g : sg.regs 57 = ln :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 57 rootPackStoreGate rfl s).trans hln
  have hT := rootPackStoreTarget_run c k sg hit w
    (by simpa only [sg, hit] using hG.1) hwg hhit
    htable hsink hwtable
  dsimp only at hT
  have h11t : st.regs 11 = n :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 11 (rootPackStoreTarget c) rfl sg).trans h11g
  have h57t : st.regs 57 = ln :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 57 (rootPackStoreTarget c) rfl sg).trans h57g
  have h58t : st.regs 58 = hit :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 58 (rootPackStoreTarget c) rfl sg).trans
        (by simpa only [sg, hit] using hG.1)
  have hwt : st.regs rpWrite = w :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpWrite (rootPackStoreTarget c) rfl sg).trans hwg
  have hV := rootPackStoreValue_run k st n ln h11t h57t
    hshift hlow hpack
  dsimp only at hV
  have h63v : sv.regs 63 =
      (if hit = 1 then w + c.tableBase else c.streamSink) :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 63 rootPackStoreValue rfl st).trans hT.1
  have h58v : sv.regs 58 = hit :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 58 rootPackStoreValue rfl st).trans h58t
  have hwv : sv.regs rpWrite = w :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpWrite rootPackStoreValue rfl st).trans hwt
  have hC := rootPackStoreCommit_run k sv
    (if hit = 1 then w + c.tableBase else c.streamSink)
    (packEntry n ln 1) w hit h63v
    (by simpa only [sv] using hV.1) hwv h58v (by
      simpa only [hit] using hwsum)
  dsimp only at hC
  have harr : sv.arr = s.arr := by
    exact hV.2.trans (hT.2.trans hG.2)
  dsimp only
  simp only [rootPackStore, arun_append]
  change
    (arun k sv rootPackStoreCommit).regs rpWrite = w + hit ∧
      ∀ x, (arun k sv rootPackStoreCommit).arr x =
        if x = (if hit = 1 then w + c.tableBase else c.streamSink)
        then packEntry n ln 1 else s.arr x
  exact ⟨hC.1, fun x => (hC.2 x).trans (by rw [harr])⟩

/-! ## Finished-candidate clear islands -/

theorem rootPackClearTargetS_run (c : R2Cfg) (k : Nat) (s : RegState)
    (finish n : Nat) (h15 : s 15 = finish) (h11 : s 11 = n)
    (hfinish : finish = 0 ∨ finish = 1)
    (hn : n < M) (hsink : c.streamSink < M) :
    (srun k s (rootPackClearTargetS c)) 70 =
      if finish = 1 then n else c.streamSink := by
  have hnM : n % M = n := Nat.mod_eq_of_lt hn
  have hsinkM : c.streamSink % M = c.streamSink := Nat.mod_eq_of_lt hsink
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hOnePred : 1 + (M - 1) = M := by omega
  rcases hfinish with rfl | rfl <;>
    simp [rootPackClearTargetS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h15, h11, hnM, hsinkM, h1M, hOnePred]

theorem rootPackClearTarget_run (c : R2Cfg) (k : Nat) (s : AState)
    (finish n : Nat) (h15 : s.regs 15 = finish) (h11 : s.regs 11 = n)
    (hfinish : finish = 0 ∨ finish = 1)
    (hn : n < M) (hsink : c.streamSink < M) :
    let out := arun k s (rootPackClearTarget c)
    out.regs 70 = (if finish = 1 then n else c.streamSink) ∧
      out.arr = s.arr := by
  rw [rootPackClearTarget,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackClearTargetS_run c k s.regs finish n
    h15 h11 hfinish hn hsink, rfl⟩

theorem rootPackClearCommit_run (k : Nat) (s : AState) (target : Nat)
    (h70 : s.regs 70 = target) (h0 : s.regs 0 = 0) :
    let out := arun k s rootPackClearCommit
    ∀ x, out.arr x = if x = target then 0 else s.arr x := by
  dsimp only
  intro x
  simp [rootPackClearCommit, arun, astep, AState.writeArr, h70, h0]

theorem rootPackClearCommit_defined (len k : Nat) (s : AState)
    (target : Nat) (h70 : s.regs 70 = target) (htarget : target < len) :
    AllDefined len k s rootPackClearCommit := by
  simpa [rootPackClearCommit, AllDefined, ADefined, h70] using htarget

theorem rootPackClear_run (c : R2Cfg) (k : Nat) (s : AState)
    (finish n : Nat) (h15 : s.regs 15 = finish) (h11 : s.regs 11 = n)
    (h0 : s.regs 0 = 0)
    (hfinish : finish = 0 ∨ finish = 1)
    (hn : n < M) (hsink : c.streamSink < M) :
    let target := if finish = 1 then n else c.streamSink
    let out := arun k s (rootPackClear c)
    ∀ x, out.arr x = if x = target then 0 else s.arr x := by
  let mid := arun k s (rootPackClearTarget c)
  have ht := rootPackClearTarget_run c k s finish n h15 h11
    hfinish hn hsink
  dsimp only at ht
  have h0mid : mid.regs 0 = 0 := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 0 (rootPackClearTarget c) rfl s).trans h0
  have hc := rootPackClearCommit_run k mid
    (if finish = 1 then n else c.streamSink) ht.1 h0mid
  dsimp only at hc
  dsimp only
  rw [rootPackClear, arun_append]
  intro x
  rw [hc x, ht.2]

theorem rootPackClear_defined (c : R2Cfg) (k : Nat) (s : AState)
    (finish n : Nat) (h15 : s.regs 15 = finish) (h11 : s.regs 11 = n)
    (hfinish : finish = 0 ∨ finish = 1)
    (hn : n < M) (hsink : c.streamSink < M)
    (hnCell : n < c.arrayLen) (hsinkCell : c.streamSink < c.arrayLen) :
    AllDefined c.arrayLen k s (rootPackClear c) := by
  let mid := arun k s (rootPackClearTarget c)
  have ht := rootPackClearTarget_run c k s finish n h15 h11
    hfinish hn hsink
  dsimp only at ht
  have htarget : (if finish = 1 then n else c.streamSink) < c.arrayLen := by
    split <;> assumption
  rw [rootPackClear]
  apply (AllDefined_append c.arrayLen k (rootPackClearTarget c)
    rootPackClearCommit s).mpr
  refine ⟨LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    c.arrayLen k (rootPackClearTargetS c) s
      (by simp [rootPackClearTargetS, NoDivI]), ?_⟩
  exact rootPackClearCommit_defined c.arrayLen k mid _ ht.1 htarget

/-! ## One complete compiled body -/

theorem rootPackBody_run (c : R2Cfg) (index : Nat) (s : AState)
    (hsafe : RootPackStepSafe c index (rootPackObserve s)) :
    rootPackObserve (arun index s (rootPackBody c)) =
      rootPackModelStep c index (rootPackObserve s) := by
  let m := rootPackObserve s
  let sd := arun index s rootPackDecode
  let si := arun index sd rootPackRoundInit
  let sg := arun index si rootPackLogRound
  let sl := arun index sg rootPackLn
  let ss := arun index sl (rootPackStore c)
  have hstart : rootPackStart index = 0 ∨ rootPackStart index = 1 := by
    unfold rootPackStart
    split <;> simp
  have hfinish : rootPackFinish index = 0 ∨ rootPackFinish index = 1 := by
    unfold rootPackFinish
    split <;> simp
  have hprime : rootPackPrime index m = 0 ∨ rootPackPrime index m = 1 := by
    unfold rootPackPrime
    split <;> simp
  have hD := rootPackDecode_run c index s hsafe.loop
  dsimp only at hD
  rcases hD with ⟨hd11, hd12, hd13, hd15, hd16, hd17, hdArr⟩
  have hdEx : sd.regs rpEx = m.ex :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpEx rootPackDecode rfl s).trans rfl
  have hdTh : sd.regs rpTh = m.th :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpTh rootPackDecode rfl s).trans rfl
  have hdXm : sd.regs rpXm = m.xm :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpXm rootPackDecode rfl s).trans rfl
  have hdAa : sd.regs rpAa = m.aa :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpAa rootPackDecode rfl s).trans rfl
  have hdWrite : sd.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackDecode rfl s).trans rfl
  have hdStart : sd.regs 13 = rootPackStart index := by
    simpa only [rootPackStart] using hd13
  have hdFinish : sd.regs 15 = rootPackFinish index := by
    simpa only [rootPackFinish] using hd15
  have hdPrime : sd.regs 17 = rootPackPrime index m := by
    simpa only [rootPackPrime, m, rootPackObserve] using hd17
  have hI := rootPackRoundInit_run index sd (rootPackN index)
    m.ex m.th (rootPackStart index) m.xm m.aa hd11 hdStart
    hdEx hdTh hdXm hdAa hstart hsafe.exWord hsafe.thWord
    (by simpa only [rootPackExNext, rootPackBump] using hsafe.exLe62)
    (by simpa only [rootPackExNext, rootPackBump] using hsafe.normWord)
    hsafe.xmWord hsafe.aaWord
  dsimp only at hI
  have hiEx : si.regs rpEx = rootPackExNext index m := by
    simpa only [si, rootPackExNext, rootPackBump] using hI.1
  have hiTh : si.regs rpTh = rootPackThNext index m := by
    simpa only [si, rootPackThNext, rootPackBump] using hI.2.1
  have hiXm : si.regs rpXm = rootPackXmInit index m := by
    simpa only [si, rootPackXmInit, rootPackExNext, rootPackBump]
      using hI.2.2.1
  have hiAa : si.regs rpAa = rootPackAaInit index m := by
    simpa only [si, rootPackAaInit] using hI.2.2.2.1
  have hiArr : si.arr = s.arr := hI.2.2.2.2.trans hdArr
  have hG := rootPackLogRound_run_of_range index si
    (rootPackXmInit index m) (rootPackAaInit index m) hiXm hiAa
    hsafe.xmInitLo hsafe.xmInitHi hsafe.aaInitBound
  dsimp only at hG
  have hgXm : sg.regs rpXm = rootPackXmNext index m := by
    simpa only [sg, rootPackXmNext] using hG.1
  have hgAa : sg.regs rpAa = rootPackAaNext index m := by
    simpa only [sg, rootPackAaNext] using hG.2.1
  have hgEx : sg.regs rpEx = rootPackExNext index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpEx rootPackLogRound rfl si).trans hiEx
  have hgTh : sg.regs rpTh = rootPackThNext index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpTh rootPackLogRound rfl si).trans hiTh
  have hgArr : sg.arr = s.arr := hG.2.2.trans hiArr
  have hL := rootPackLn_run index sg (rootPackExNext index m)
    (rootPackAaNext index m) hgEx hgAa hsafe.fixBound
  dsimp only at hL
  have hlArr : sl.arr = s.arr := hL.2.trans hgArr
  have hi11 : si.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackRoundInit rfl sd).trans hd11
  have hg11 : sg.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackLogRound rfl si).trans hi11
  have hl11 : sl.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackLn rfl sg).trans hg11
  have hi15 : si.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackRoundInit rfl sd).trans hdFinish
  have hg15 : sg.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackLogRound rfl si).trans hi15
  have hl15 : sl.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackLn rfl sg).trans hg15
  have hi17 : si.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackRoundInit rfl sd).trans hdPrime
  have hg17 : sg.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackLogRound rfl si).trans hi17
  have hl17 : sl.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackLn rfl sg).trans hg17
  have hiWrite : si.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackRoundInit rfl sd).trans hdWrite
  have hgWrite : sg.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackLogRound rfl si).trans hiWrite
  have hlWrite : sl.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackLn rfl sg).trans hgWrite
  have hS := rootPackStore_run c index sl
    (rootPackFinish index) (rootPackPrime index m) m.write
    (rootPackN index)
    (rootPackLnValue (rootPackExNext index m) (rootPackAaNext index m))
    hfinish hprime hl15 hl17 hlWrite hl11
    (by simpa only [sl] using hL.1)
    hsafe.tableWord hsafe.sinkWord hsafe.writeTableWord
    hsafe.lnShiftWord hsafe.lnLowWord hsafe.packedWord
    (by simpa only [rootPackHit] using hsafe.writeWord)
  dsimp only at hS
  have hs11 : ss.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 (rootPackStore c) rfl sl).trans hl11
  have hs15 : ss.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 (rootPackStore c) rfl sl).trans hl15
  have h0s : s.regs 0 = 0 := by
    simpa only [m, rootPackObserve] using hsafe.zeroIsZero
  have hd0 : sd.regs 0 = 0 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 rootPackDecode rfl s).trans h0s
  have hi0 : si.regs 0 = 0 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 rootPackRoundInit rfl sd).trans hd0
  have hg0 : sg.regs 0 = 0 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 rootPackLogRound rfl si).trans hi0
  have hl0 : sl.regs 0 = 0 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 rootPackLn rfl sg).trans hg0
  have hs0 : ss.regs 0 = 0 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 (rootPackStore c) rfl sl).trans hl0
  have hC := rootPackClear_run c index ss (rootPackFinish index)
    (rootPackN index) hs15 hs11 hs0 hfinish
    (Nat.lt_of_le_of_lt (rootPack_index_bounds (by
      simpa [r2RootPackProgram] using hsafe.loop)).2.1
      (show runtimeRoot < M by decide))
    hsafe.sinkWord
  dsimp only at hC
  have hPrefix : arun index s (rootPackBody c) =
      arun index ss (rootPackClear c) := by
    simp only [rootPackBody, arun_append, sd, si, sg, sl, ss]
  rw [hPrefix]
  change rootPackObserve (arun index ss (rootPackClear c)) =
    rootPackModelStep c index m
  apply rootPackModel_ext
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 0 (rootPackClear c) rfl ss).trans hs0
    exact h.trans h0s.symm
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpEx (rootPackClear c) rfl ss)
    have h1 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpEx (rootPackStore c) rfl sl)
    have h2 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpEx rootPackLn rfl sg)
    have h3 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpEx rootPackLogRound rfl si)
    simpa only [rootPackObserve, rootPackModelStep] using
      h.trans (h1.trans (h2.trans (h3.trans hiEx)))
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpTh (rootPackClear c) rfl ss)
    have h1 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpTh (rootPackStore c) rfl sl)
    have h2 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpTh rootPackLn rfl sg)
    have h3 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpTh rootPackLogRound rfl si)
    simpa only [rootPackObserve, rootPackModelStep] using
      h.trans (h1.trans (h2.trans (h3.trans hiTh)))
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpXm (rootPackClear c) rfl ss)
    have h1 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpXm (rootPackStore c) rfl sl)
    have h2 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpXm rootPackLn rfl sg)
    simpa only [rootPackObserve, rootPackModelStep] using
      h.trans (h1.trans (h2.trans hgXm))
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpAa (rootPackClear c) rfl ss)
    have h1 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpAa (rootPackStore c) rfl sl)
    have h2 := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpAa rootPackLn rfl sg)
    simpa only [rootPackObserve, rootPackModelStep] using
      h.trans (h1.trans (h2.trans hgAa))
  · have h := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpWrite (rootPackClear c) rfl ss)
    simpa only [rootPackObserve, rootPackModelStep, rootPackHit] using
      h.trans hS.1
  · funext x
    have hStore := hS.2 x
    rw [hlArr] at hStore
    have hClear := hC x
    rw [hStore] at hClear
    simpa only [rootPackObserve, rootPackModelStep,
      rootPackStoreTargetSpec, rootPackClearTargetSpec, rootPackHit, m]
      using hClear

theorem rootPackBody_defined (c : R2Cfg) (index : Nat) (s : AState)
    (hsafe : RootPackStepSafe c index (rootPackObserve s)) :
    AllDefined c.arrayLen index s (rootPackBody c) := by
  let m := rootPackObserve s
  let sd := arun index s rootPackDecode
  let si := arun index sd rootPackRoundInit
  let sg := arun index si rootPackLogRound
  let sl := arun index sg rootPackLn
  let ss := arun index sl (rootPackStore c)
  have hfinish : rootPackFinish index = 0 ∨ rootPackFinish index = 1 := by
    unfold rootPackFinish
    split <;> simp
  have hprime : rootPackPrime index m = 0 ∨ rootPackPrime index m = 1 := by
    unfold rootPackPrime
    split <;> simp
  have hD := rootPackDecode_run c index s hsafe.loop
  dsimp only at hD
  rcases hD with ⟨hd11, _, _, hd15, _, hd17, _⟩
  have hdFinish : sd.regs 15 = rootPackFinish index := by
    simpa only [rootPackFinish] using hd15
  have hdPrime : sd.regs 17 = rootPackPrime index m := by
    simpa only [rootPackPrime, m, rootPackObserve] using hd17
  have hdWrite : sd.regs rpWrite = m.write := by
    simpa only [m, rootPackObserve] using
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame
        index rpWrite rootPackDecode rfl s)
  have hi15 : si.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackRoundInit rfl sd).trans hdFinish
  have hg15 : sg.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackLogRound rfl si).trans hi15
  have hl15 : sl.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 rootPackLn rfl sg).trans hg15
  have hi17 : si.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackRoundInit rfl sd).trans hdPrime
  have hg17 : sg.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackLogRound rfl si).trans hi17
  have hl17 : sl.regs 17 = rootPackPrime index m :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 17 rootPackLn rfl sg).trans hg17
  have hiWrite : si.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackRoundInit rfl sd).trans hdWrite
  have hgWrite : sg.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackLogRound rfl si).trans hiWrite
  have hlWrite : sl.regs rpWrite = m.write :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index rpWrite rootPackLn rfl sg).trans hgWrite
  have hi11 : si.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackRoundInit rfl sd).trans hd11
  have hg11 : sg.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackLogRound rfl si).trans hi11
  have hl11 : sl.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 rootPackLn rfl sg).trans hg11
  have hStore := rootPackStore_defined c index sl
    (rootPackFinish index) (rootPackPrime index m) m.write
    hfinish hprime hl15 hl17 hlWrite hsafe.tableWord hsafe.sinkWord
    hsafe.writeTableWord hsafe.sinkCell hsafe.writeTableCell
  have hs15 : ss.regs 15 = rootPackFinish index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 15 (rootPackStore c) rfl sl).trans hl15
  have hs11 : ss.regs 11 = rootPackN index :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      index 11 (rootPackStore c) rfl sl).trans hl11
  have hnM : rootPackN index < M :=
    Nat.lt_of_le_of_lt (rootPack_index_bounds (by
      simpa [r2RootPackProgram] using hsafe.loop)).2.1
      (show runtimeRoot < M by decide)
  have hClear := rootPackClear_defined c index ss
    (rootPackFinish index) (rootPackN index) hs15 hs11 hfinish
    hnM hsafe.sinkWord hsafe.candidateCell hsafe.sinkCell
  rw [rootPackBody]
  apply (AllDefined_append c.arrayLen index rootPackDecode _ s).mpr
  refine ⟨rootPackDecode_defined c index s hsafe.rootCell hsafe.loop, ?_⟩
  apply (AllDefined_append c.arrayLen index rootPackRoundInit _ sd).mpr
  refine ⟨rootPackRoundInit_defined c.arrayLen index sd, ?_⟩
  apply (AllDefined_append c.arrayLen index rootPackLogRound _ si).mpr
  refine ⟨rootPackLogRound_defined c.arrayLen index si, ?_⟩
  apply (AllDefined_append c.arrayLen index rootPackLn _ sg).mpr
  refine ⟨rootPackLn_defined c.arrayLen index sg, ?_⟩
  exact (AllDefined_append c.arrayLen index (rootPackStore c)
    (rootPackClear c) sl).mpr ⟨hStore, hClear⟩

/-! ## Symbolic loop bridge

These folds remain opaque at the production trip count.  The theorem below
is an induction over the syntax of a prefix and never reduces that prefix. -/

def rootPackMachineFold (c : R2Cfg) (s : AState) (k : Nat) : AState :=
  (List.range k).foldl
    (fun st index => arun index st (rootPackBody c)) s

def rootPackModelFold (c : R2Cfg) (m : RootPackModel) (k : Nat) :
    RootPackModel :=
  (List.range k).foldl (fun z index => rootPackModelStep c index z) m

theorem rootPackMachineFold_succ (c : R2Cfg) (s : AState) (k : Nat) :
    rootPackMachineFold c s (k + 1) =
      arun k (rootPackMachineFold c s k) (rootPackBody c) := by
  simp [rootPackMachineFold, List.range_succ, List.foldl_append]

theorem rootPackModelFold_succ (c : R2Cfg) (m : RootPackModel) (k : Nat) :
    rootPackModelFold c m (k + 1) =
      rootPackModelStep c k (rootPackModelFold c m k) := by
  simp [rootPackModelFold, List.range_succ, List.foldl_append]

theorem rootPackModelFold_invariant (c : R2Cfg) (m : RootPackModel) (k : Nat)
    (hcfg : RootPackCfgSafe c)
    (hinit : RootPackInvariant 0 m)
    (hk : k ≤ (r2RootPackProgram c).loopCount) :
    RootPackInvariant k (rootPackModelFold c m k) := by
  induction k with
  | zero => simpa [rootPackModelFold] using hinit
  | succ k ih =>
      rw [rootPackModelFold_succ]
      apply rootPackInvariant_step c k (rootPackModelFold c m k) hcfg
      · omega
      · exact ih (by omega)

theorem rootPackModelFold_safe (c : R2Cfg) (m : RootPackModel)
    (hcfg : RootPackCfgSafe c)
    (hinit : RootPackInvariant 0 m) :
    ∀ i, i < (r2RootPackProgram c).loopCount →
      RootPackStepSafe c i (rootPackModelFold c m i) := by
  intro i hi
  apply rootPackInvariant_safe c i (rootPackModelFold c m i) hcfg hi
  exact rootPackModelFold_invariant c m i hcfg hinit (Nat.le_of_lt hi)

theorem rootPackProductionModelFold_safe (arr : Nat → Nat) :
    ∀ i, i < (r2RootPackProgram runtimeProductionCfg).loopCount →
      RootPackStepSafe runtimeProductionCfg i
        (rootPackModelFold runtimeProductionCfg (rootPackInitialModel arr) i) :=
  rootPackModelFold_safe runtimeProductionCfg (rootPackInitialModel arr)
    runtimeProductionCfg_rootPackSafe (rootPackInitialModel_invariant arr)

theorem rootPackFold_observe (c : R2Cfg) (s : AState) (k : Nat)
    (hsafe : ∀ i, i < k →
      RootPackStepSafe c i (rootPackModelFold c (rootPackObserve s) i)) :
    rootPackObserve (rootPackMachineFold c s k) =
      rootPackModelFold c (rootPackObserve s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hpre : rootPackObserve (rootPackMachineFold c s k) =
          rootPackModelFold c (rootPackObserve s) k :=
        ih (fun i hi => hsafe i (Nat.lt_trans hi (Nat.lt_succ_self k)))
      have hstepSafe : RootPackStepSafe c k
          (rootPackObserve (rootPackMachineFold c s k)) := by
        rw [hpre]
        exact hsafe k (Nat.lt_succ_self k)
      rw [rootPackMachineFold_succ, rootPackModelFold_succ,
        rootPackBody_run c k (rootPackMachineFold c s k) hstepSafe,
        hpre]

theorem rootPackFold_body_defined (c : R2Cfg) (s : AState) (k i : Nat)
    (hik : i < k)
    (hsafe : ∀ j, j < k →
      RootPackStepSafe c j (rootPackModelFold c (rootPackObserve s) j)) :
    AllDefined c.arrayLen i (rootPackMachineFold c s i)
      (rootPackBody c) := by
  apply rootPackBody_defined
  rw [rootPackFold_observe c s i (fun j hj =>
    hsafe j (Nat.lt_trans hj hik))]
  exact hsafe i hik

theorem rootPackDenoteFold (c : R2Cfg) (s : AState) (k : Nat)
    (hcfg : RootPackCfgSafe c)
    (hinit : RootPackInvariant 0 (rootPackObserve s))
    (hk : k ≤ (r2RootPackProgram c).loopCount) :
    (List.range k).foldlM
        (fun st index => denoteAInstrs c.arrayLen index st (rootPackBody c)) s =
      some (rootPackMachineFold c s k) := by
  have hsafe := rootPackModelFold_safe c (rootPackObserve s) hcfg hinit
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      have hsome :
          (do
            let init ← (some (rootPackMachineFold c s k) : Option AState)
            List.foldlM
              (fun st index => denoteAInstrs c.arrayLen index st
                (rootPackBody c)) init [k]) =
            List.foldlM
              (fun st index => denoteAInstrs c.arrayLen index st
                (rootPackBody c)) (rootPackMachineFold c s k) [k] :=
        Option.bind_some _ _
      rw [hsome]
      have hdef := rootPackFold_body_defined c s (k + 1) k
        (Nat.lt_succ_self k)
        (fun j hj => hsafe j (Nat.lt_of_lt_of_le hj hk))
      have hden := denoteAInstrs_eq_arun c.arrayLen k (rootPackBody c)
        (rootPackMachineFold c s k) hdef
      have htail :
          (do
            let init ← some
              (arun k (rootPackMachineFold c s k) (rootPackBody c))
            List.foldlM
              (fun st index => denoteAInstrs c.arrayLen index st
                (rootPackBody c)) init []) =
            List.foldlM
              (fun st index => denoteAInstrs c.arrayLen index st
                (rootPackBody c))
              (arun k (rootPackMachineFold c s k) (rootPackBody c)) [] :=
        Option.bind_some _ _
      rw [List.foldlM_cons, hden, htail, List.foldlM_nil,
        rootPackMachineFold_succ]
      rfl

theorem rootPackEpilogue_defined (c : R2Cfg) (s : AState)
    (hword : s.regs rpWrite + c.tableBase < M)
    (hcell : s.regs rpWrite + c.tableBase < c.arrayLen) :
    AllDefined c.arrayLen 0 s (rootPackEpilogue c) := by
  have hmod : (s.regs rpWrite + c.tableBase) % M =
      s.regs rpWrite + c.tableBase := Nat.mod_eq_of_lt hword
  simp [rootPackEpilogue, AllDefined, ADefined, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, hmod, hcell]

theorem rootPackFold_epilogue_defined (c : R2Cfg) (s : AState) (k : Nat)
    (hcfg : RootPackCfgSafe c)
    (hinit : RootPackInvariant 0 (rootPackObserve s))
    (hk : k ≤ (r2RootPackProgram c).loopCount)
    (hkRoot : k / runtimeScale < runtimeRoot) :
    AllDefined c.arrayLen 0 (rootPackMachineFold c s k)
      (rootPackEpilogue c) := by
  have hsafe := rootPackModelFold_safe c (rootPackObserve s) hcfg hinit
  have hobs := rootPackFold_observe c s k
    (fun i hi => hsafe i (Nat.lt_of_lt_of_le hi hk))
  have hinv := rootPackModelFold_invariant c (rootPackObserve s) k
    hcfg hinit hk
  have hwriteEq : (rootPackMachineFold c s k).regs rpWrite =
      (rootPackModelFold c (rootPackObserve s) k).write := by
    simpa only [rootPackObserve] using congrArg RootPackModel.write hobs
  have hwriteRoot : (rootPackMachineFold c s k).regs rpWrite <
      runtimeRoot := by
    rw [hwriteEq]
    exact Nat.lt_of_le_of_lt hinv.writeLe hkRoot
  apply rootPackEpilogue_defined
  · exact Nat.lt_of_lt_of_le
      (Nat.add_lt_add_right hwriteRoot c.tableBase)
      (Nat.le_of_lt hcfg.rootTableWord)
  · exact Nat.lt_of_lt_of_le
      (Nat.add_lt_add_right hwriteRoot c.tableBase)
      (Nat.le_of_lt hcfg.rootTableCell)

theorem rootPackRunFromArray_of_stages (c : R2Cfg) (arr : Nat → Nat)
    (s₀ sf out : AState)
    (hInit : denoteAInstrs (r2RootPackProgram c).arrayLen 0
      (initialAStateWithArray arr) (r2RootPackProgram c).init = some s₀)
    (hLoop : (List.range (r2RootPackProgram c).loopCount).foldlM
      (fun st index => denoteAInstrs (r2RootPackProgram c).arrayLen index st
        (r2RootPackProgram c).body) s₀ = some sf)
    (hEpi : denoteAInstrs (r2RootPackProgram c).arrayLen 0 sf
      (r2RootPackProgram c).epilogue = some out) :
    (r2RootPackProgram c).runFromArray arr = some out := by
  have hAfterInit :
      (do
        let st ← (some s₀ : Option AState)
        let st ← (List.range (r2RootPackProgram c).loopCount).foldlM
          (fun z index => denoteAInstrs (r2RootPackProgram c).arrayLen
            index z (r2RootPackProgram c).body) st
        denoteAInstrs (r2RootPackProgram c).arrayLen 0 st
          (r2RootPackProgram c).epilogue) =
      (do
        let st ← (List.range (r2RootPackProgram c).loopCount).foldlM
          (fun z index => denoteAInstrs (r2RootPackProgram c).arrayLen
            index z (r2RootPackProgram c).body) s₀
        denoteAInstrs (r2RootPackProgram c).arrayLen 0 st
          (r2RootPackProgram c).epilogue) := Option.bind_some _ _
  have hAfterLoop :
      (do
        let st ← (some sf : Option AState)
        denoteAInstrs (r2RootPackProgram c).arrayLen 0 st
          (r2RootPackProgram c).epilogue) =
      denoteAInstrs (r2RootPackProgram c).arrayLen 0 sf
        (r2RootPackProgram c).epilogue := Option.bind_some _ _
  unfold AProgram.runFromArray
  rw [hInit, hAfterInit, hLoop, hAfterLoop, hEpi]

def rootPackedState (c : R2Cfg) (arr : Nat → Nat) : AState :=
  let s₀ := arun 0 (initialAStateWithArray arr) rootPackInit
  arun 0 (rootPackMachineFold c s₀ (r2RootPackProgram c).loopCount)
    (rootPackEpilogue c)

def rootPackStartedState (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) rootPackInit

def rootPackLoopState (c : R2Cfg) (arr : Nat → Nat) : AState :=
  rootPackMachineFold c (rootPackStartedState arr)
    (r2RootPackProgram c).loopCount

theorem rootPackStartedState_invariant (arr : Nat → Nat) :
    RootPackInvariant 0 (rootPackObserve (rootPackStartedState arr)) := by
  rw [rootPackStartedState, rootPackInit_observe]
  exact rootPackInitialModel_invariant arr

theorem rootPackStartedState_denote (c : R2Cfg) (arr : Nat → Nat) :
    denoteAInstrs (r2RootPackProgram c).arrayLen 0
      (initialAStateWithArray arr) (r2RootPackProgram c).init =
      some (rootPackStartedState arr) := by
  simpa only [r2RootPackProgram, rootPackStartedState] using
    rootPackInit_denote c arr

theorem rootPackLoopState_denote (c : R2Cfg) (arr : Nat → Nat)
    (hcfg : RootPackCfgSafe c) :
    (List.range (r2RootPackProgram c).loopCount).foldlM
      (fun st index => denoteAInstrs (r2RootPackProgram c).arrayLen index st
        (r2RootPackProgram c).body) (rootPackStartedState arr) =
      some (rootPackLoopState c arr) := by
  exact rootPackDenoteFold c (rootPackStartedState arr)
    (r2RootPackProgram c).loopCount hcfg
    (rootPackStartedState_invariant arr) (Nat.le_refl _)

theorem rootPackLoopState_epilogue_defined (c : R2Cfg) (arr : Nat → Nat)
    (hcfg : RootPackCfgSafe c) :
    AllDefined (r2RootPackProgram c).arrayLen 0 (rootPackLoopState c arr)
      (r2RootPackProgram c).epilogue := by
  have hkRoot : (r2RootPackProgram c).loopCount / runtimeScale <
      runtimeRoot := by
    change ((runtimeRoot - 1) * runtimeScale) / runtimeScale < runtimeRoot
    rw [Nat.mul_div_cancel _ (by decide : 0 < runtimeScale)]
    have : 0 < runtimeRoot := by decide
    omega
  exact rootPackFold_epilogue_defined c (rootPackStartedState arr)
    (r2RootPackProgram c).loopCount hcfg
    (rootPackStartedState_invariant arr) (Nat.le_refl _) hkRoot

theorem rootPackLoopState_epilogue_denote (c : R2Cfg) (arr : Nat → Nat)
    (hcfg : RootPackCfgSafe c) :
    denoteAInstrs (r2RootPackProgram c).arrayLen 0 (rootPackLoopState c arr)
      (r2RootPackProgram c).epilogue =
      some (arun 0 (rootPackLoopState c arr) (rootPackEpilogue c)) := by
  exact denoteAInstrs_eq_arun c.arrayLen 0 (rootPackEpilogue c)
    (rootPackLoopState c arr)
    (rootPackLoopState_epilogue_defined c arr hcfg)

theorem rootPackProgram_runFromArray (c : R2Cfg) (arr : Nat → Nat)
    (hcfg : RootPackCfgSafe c) :
    ∃ out, (r2RootPackProgram c).runFromArray arr = some out := by
  refine ⟨arun 0 (rootPackLoopState c arr) (rootPackEpilogue c), ?_⟩
  exact rootPackRunFromArray_of_stages c arr (rootPackStartedState arr)
    (rootPackLoopState c arr)
    (arun 0 (rootPackLoopState c arr) (rootPackEpilogue c))
    (rootPackStartedState_denote c arr)
    (rootPackLoopState_denote c arr hcfg)
    (rootPackLoopState_epilogue_denote c arr hcfg)

theorem rootPackProduction_runFromArray (arr : Nat → Nat) :
    ∃ out, (r2RootPackProgram runtimeProductionCfg).runFromArray arr =
      some out :=
  rootPackProgram_runFromArray runtimeProductionCfg arr
    runtimeProductionCfg_rootPackSafe

/-- The source-level execution proof transported through the verified array
compiler.  The large production loop remains symbolic: this theorem proves
that the emitted CompCert program executes and simulates its source result;
it does not normalize the loop in Lean. -/
theorem rootPackProgram_compiled_execution (c : R2Cfg) (arr : Nat → Nat)
    (base : Int) (mem : Verified.MemFragment.Mem)
    (hcfg : RootPackCfgSafe c)
    (hBase : BaseOk (r2RootPackProgram c).arrayLen base)
    (hCells : ∀ k, k < (r2RootPackProgram c).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < (r2RootPackProgram c).arrayLen → arr k < M) :
    ∃ out m,
      (r2RootPackProgram c).runFromArray arr = some out ∧
      Verified.MemFragment.evalMCCSequence
          ((r2RootPackProgram c).initialMCCWithMem base mem)
          (r2RootPackProgram c).compile = some m ∧
      ARel (r2RootPackProgram c).regCount
        (r2RootPackProgram c).arrayLen base out m := by
  obtain ⟨out, hRun⟩ := rootPackProgram_runFromArray c arr hcfg
  obtain ⟨m, hEval, hRel⟩ :=
    AProgram.evalCC_compile_fromArray (r2RootPackProgram c)
      (r2RootPackProgram_wf c) base hBase arr mem hCells hCellsLt out hRun
  exact ⟨out, m, hRun, hEval, hRel⟩

theorem rootPackProduction_compiled_execution (arr : Nat → Nat)
    (base : Int) (mem : Verified.MemFragment.Mem)
    (hBase : BaseOk
      (r2RootPackProgram runtimeProductionCfg).arrayLen base)
    (hCells : ∀ k,
      k < (r2RootPackProgram runtimeProductionCfg).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k,
      k < (r2RootPackProgram runtimeProductionCfg).arrayLen → arr k < M) :
    ∃ out m,
      (r2RootPackProgram runtimeProductionCfg).runFromArray arr = some out ∧
      Verified.MemFragment.evalMCCSequence
          ((r2RootPackProgram runtimeProductionCfg).initialMCCWithMem base mem)
          (r2RootPackProgram runtimeProductionCfg).compile = some m ∧
      ARel (r2RootPackProgram runtimeProductionCfg).regCount
        (r2RootPackProgram runtimeProductionCfg).arrayLen base out m :=
  rootPackProgram_compiled_execution runtimeProductionCfg arr base mem
    runtimeProductionCfg_rootPackSafe hBase hCells hCellsLt

#print axioms rootPackDecode_defined
#print axioms rootPackRoundInit_defined
#print axioms rootPackLogRound_defined
#print axioms rootPackLn_defined
#print axioms rootPackDecode_run
#print axioms rootPackExponentS_run
#print axioms rootPackExponent_run
#print axioms rootPackMantissaInitS_run
#print axioms rootPackMantissaInit_run
#print axioms rootPackRoundInit_run
#print axioms rootPackLogReg_injective
#print axioms rootPackLogRoundS_run_of_range
#print axioms rootPackLogRound_run_of_range
#print axioms rootPack_logIter_fst_range
#print axioms rootPack_foldl_logRound_from_iter
#print axioms rootPack_foldl_logRound_24
#print axioms rootPackLnReg_injective
#print axioms rootPackLnConvertS_run
#print axioms rootPackLnConvertS_logFix_run
#print axioms rootPackLnConvert_logFix_run
#print axioms rootPackLnPrefixS_run
#print axioms rootPackLnPrefixS_logFix_run
#print axioms rootPackLnS_run
#print axioms rootPackLn_run
#print axioms rootPackLnS_logFix_run
#print axioms rootPackLn_logFix_run
#print axioms rootPackStoreGateS_run
#print axioms rootPackStoreGate_run
#print axioms rootPackStoreTargetS_run
#print axioms rootPackStoreTarget_run
#print axioms rootPackStoreValueS_run
#print axioms rootPackStoreValue_run
#print axioms rootPackStoreCommit_run
#print axioms rootPackStore_run
#print axioms rootPackClearTargetS_run
#print axioms rootPackClearTarget_run
#print axioms rootPackClearCommit_run
#print axioms rootPackClear_run
#print axioms rootPackBody_run
#print axioms rootPackBody_defined
#print axioms rootPackFold_observe
#print axioms rootPackFold_body_defined

end LeanCompCert.Ports.R2SegSieve
