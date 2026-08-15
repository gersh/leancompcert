import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Failure-counter telescope for the complete live Mertens residue

The last eight instructions of `mertensLiveResidue` retain the four Hurst and
CDEM comparison results in separate counters.  This file proves their exact
ordinary arithmetic meaning inside the complete residue, telescopes arbitrary
schedules, and derives pointwise zero failures from zero terminal counters.
No production range is evaluated by Lean.
-/

namespace LeanCompCert.Ports.ArraySegMertensFailureTelescope

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve

structure FailureCounts where
  mHi : Nat
  mLo : Nat
  gHi : Nat
  gLo : Nat
  deriving Repr, DecidableEq

@[ext] theorem FailureCounts.ext {a b : FailureCounts}
    (hmHi : a.mHi = b.mHi) (hmLo : a.mLo = b.mLo)
    (hgHi : a.gHi = b.gHi) (hgLo : a.gLo = b.gLo) : a = b := by
  cases a
  cases b
  simp_all

def FailureCounts.add (a b : FailureCounts) : FailureCounts :=
  ⟨a.mHi + b.mHi, a.mLo + b.mLo, a.gHi + b.gHi, a.gLo + b.gLo⟩

def FailureCounts.zero : FailureCounts := ⟨0, 0, 0, 0⟩

def readCounts (s : AState) : FailureCounts :=
  ⟨s.regs rVMHi, s.regs rVMLo, s.regs rVGHi, s.regs rVGLo⟩

def localCounts (s : AState) : FailureCounts :=
  ⟨s.regs 158 * s.regs 133, s.regs 159 * s.regs 133,
    s.regs 164 * s.regs 133, s.regs 165 * s.regs 133⟩

def counterBlock : List Instr :=
  [ .binop 178 .mul (.reg 158) (.reg 133)
  , .binop rVMHi .add (.reg rVMHi) (.reg 178)
  , .binop 179 .mul (.reg 159) (.reg 133)
  , .binop rVMLo .add (.reg rVMLo) (.reg 179)
  , .binop 180 .mul (.reg 164) (.reg 133)
  , .binop rVGHi .add (.reg rVGHi) (.reg 180)
  , .binop 181 .mul (.reg 165) (.reg 133)
  , .binop rVGLo .add (.reg rVGLo) (.reg 181) ]

def counterBody : List AInstr := lift counterBlock

def beforeCounters (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).take 31

theorem liveResidue_eq_counter_decomp (bNum bDen : Nat) :
    mertensLiveResidue bNum bDen =
      beforeCounters bNum bDen ++ counterBody := by
  rfl

structure CounterReady (s : AState) : Prop where
  mul_mHi_lt : s.regs 158 * s.regs 133 < M
  mul_mLo_lt : s.regs 159 * s.regs 133 < M
  mul_gHi_lt : s.regs 164 * s.regs 133 < M
  mul_gLo_lt : s.regs 165 * s.regs 133 < M
  room_mHi : s.regs rVMHi + s.regs 158 * s.regs 133 < M
  room_mLo : s.regs rVMLo + s.regs 159 * s.regs 133 < M
  room_gHi : s.regs rVGHi + s.regs 164 * s.regs 133 < M
  room_gLo : s.regs rVGLo + s.regs 165 * s.regs 133 < M

theorem counterBlock_run (idx : Nat) (s : RegState)
    (fMHi fMLo fGHi fGLo gate cMHi cMLo cGHi cGLo : Nat)
    (hfMHi : s 158 = fMHi) (hfMLo : s 159 = fMLo)
    (hfGHi : s 164 = fGHi) (hfGLo : s 165 = fGLo)
    (hgate : s 133 = gate)
    (hcMHi : s rVMHi = cMHi) (hcMLo : s rVMLo = cMLo)
    (hcGHi : s rVGHi = cGHi) (hcGLo : s rVGLo = cGLo)
    (hmMHi : fMHi * gate < M) (hmMLo : fMLo * gate < M)
    (hmGHi : fGHi * gate < M) (hmGLo : fGLo * gate < M)
    (hrMHi : cMHi + fMHi * gate < M)
    (hrMLo : cMLo + fMLo * gate < M)
    (hrGHi : cGHi + fGHi * gate < M)
    (hrGLo : cGLo + fGLo * gate < M) :
    let out := srun idx s counterBlock
    out rVMHi = cMHi + fMHi * gate ∧
      out rVMLo = cMLo + fMLo * gate ∧
      out rVGHi = cGHi + fGHi * gate ∧
      out rVGLo = cGLo + fGLo * gate := by
  have hcMHi' : s 172 = cMHi := by simpa only [rVMHi] using hcMHi
  have hcMLo' : s 173 = cMLo := by simpa only [rVMLo] using hcMLo
  have hcGHi' : s 174 = cGHi := by simpa only [rVGHi] using hcGHi
  have hcGLo' : s 175 = cGLo := by simpa only [rVGLo] using hcGLo
  simp [counterBlock, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, rVMHi, rVMLo, rVGHi, rVGLo,
    hfMHi, hfMLo, hfGHi, hfGLo, hgate, hcMHi', hcMLo', hcGHi', hcGLo',
    Nat.mod_eq_of_lt hmMHi, Nat.mod_eq_of_lt hmMLo,
    Nat.mod_eq_of_lt hmGHi, Nat.mod_eq_of_lt hmGLo,
    Nat.mod_eq_of_lt hrMHi, Nat.mod_eq_of_lt hrMLo,
    Nat.mod_eq_of_lt hrGHi, Nat.mod_eq_of_lt hrGLo]

theorem counterBody_run (idx : Nat) (s : AState) (h : CounterReady s) :
    readCounts (arun idx s counterBody) =
      (readCounts s).add (localCounts s) := by
  rw [counterBody, arun_lift]
  have hr := counterBlock_run idx s.regs
    (s.regs 158) (s.regs 159) (s.regs 164) (s.regs 165) (s.regs 133)
    (s.regs rVMHi) (s.regs rVMLo) (s.regs rVGHi) (s.regs rVGLo)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    h.mul_mHi_lt h.mul_mLo_lt h.mul_gHi_lt h.mul_gLo_lt
    h.room_mHi h.room_mLo h.room_gHi h.room_gLo
  apply FailureCounts.ext
  · simpa only [readCounts, FailureCounts.add, localCounts] using hr.1
  · simpa only [readCounts, FailureCounts.add, localCounts] using hr.2.1
  · simpa only [readCounts, FailureCounts.add, localCounts] using hr.2.2.1
  · simpa only [readCounts, FailureCounts.add, localCounts] using hr.2.2.2

def counterInput (bNum bDen idx : Nat) (s : AState) : AState :=
  arun idx s (beforeCounters bNum bDen)

structure LiveCounterReady (bNum bDen idx : Nat) (s : AState) : Prop where
  ready : CounterReady (counterInput bNum bDen idx s)

theorem liveResidue_counts (bNum bDen idx : Nat) (s : AState)
    (h : LiveCounterReady bNum bDen idx s) :
    readCounts (arun idx s (mertensLiveResidue bNum bDen)) =
      (readCounts s).add (localCounts (counterInput bNum bDen idx s)) := by
  have hframe : readCounts (counterInput bNum bDen idx s) = readCounts s := by
    apply FailureCounts.ext
    · exact arun_frame idx rVMHi (beforeCounters bNum bDen) (by rfl) s
    · exact arun_frame idx rVMLo (beforeCounters bNum bDen) (by rfl) s
    · exact arun_frame idx rVGHi (beforeCounters bNum bDen) (by rfl) s
    · exact arun_frame idx rVGLo (beforeCounters bNum bDen) (by rfl) s
  rw [liveResidue_eq_counter_decomp, arun_append]
  have hcounter := counterBody_run idx (counterInput bNum bDen idx s) h.ready
  change readCounts
      (arun idx (counterInput bNum bDen idx s) counterBody) = _
  rw [hcounter, hframe]

def runLive (bNum bDen : Nat) : List Nat → AState → AState
  | [], s => s
  | idx :: indices, s =>
      runLive bNum bDen indices
        (arun idx s (mertensLiveResidue bNum bDen))

def localTrace (bNum bDen : Nat) : List Nat → AState → List FailureCounts
  | [], _ => []
  | idx :: indices, s =>
      localCounts (counterInput bNum bDen idx s) ::
        localTrace bNum bDen indices
          (arun idx s (mertensLiveResidue bNum bDen))

def traceSum : List FailureCounts → FailureCounts
  | [] => FailureCounts.zero
  | x :: xs => x.add (traceSum xs)

def LiveTraceReady (bNum bDen : Nat) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      LiveCounterReady bNum bDen idx s ∧
        LiveTraceReady bNum bDen indices
          (arun idx s (mertensLiveResidue bNum bDen))

theorem runLive_counts (bNum bDen : Nat) (indices : List Nat) (s : AState)
    (htrace : LiveTraceReady bNum bDen indices s) :
    readCounts (runLive bNum bDen indices s) =
      (readCounts s).add (traceSum (localTrace bNum bDen indices s)) := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx indices ih =>
      have hstep := liveResidue_counts bNum bDen idx s htrace.1
      have htail := ih
        (s := arun idx s (mertensLiveResidue bNum bDen)) htrace.2
      rw [runLive, localTrace, traceSum, htail, hstep]
      apply FailureCounts.ext <;> simp [FailureCounts.add] <;> omega

def CountsZero (c : FailureCounts) : Prop :=
  c.mHi = 0 ∧ c.mLo = 0 ∧ c.gHi = 0 ∧ c.gLo = 0

def AllLocalPass (bNum bDen : Nat) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      CountsZero (localCounts (counterInput bNum bDen idx s)) ∧
        AllLocalPass bNum bDen indices
          (arun idx s (mertensLiveResidue bNum bDen))

theorem allLocalPass_of_traceSum_zero (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (hzero : CountsZero (traceSum (localTrace bNum bDen indices s))) :
    AllLocalPass bNum bDen indices s := by
  induction indices generalizing s with
  | nil => trivial
  | cons idx indices ih =>
      simp only [localTrace, traceSum] at hzero
      have hmHi := Nat.add_eq_zero_iff.mp hzero.1
      have hmLo := Nat.add_eq_zero_iff.mp hzero.2.1
      have hgHi := Nat.add_eq_zero_iff.mp hzero.2.2.1
      have hgLo := Nat.add_eq_zero_iff.mp hzero.2.2.2
      constructor
      · exact ⟨hmHi.1, hmLo.1, hgHi.1, hgLo.1⟩
      · apply ih
        exact ⟨hmHi.2, hmLo.2, hgHi.2, hgLo.2⟩

/-- Zero initial and terminal retained counters force all four comparison
bits to vanish at every live scheduled cell. -/
theorem allLocalPass_of_terminal_zero (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (htrace : LiveTraceReady bNum bDen indices s)
    (hinit : CountsZero (readCounts s))
    (hfinal : CountsZero (readCounts (runLive bNum bDen indices s))) :
    AllLocalPass bNum bDen indices s := by
  have hrun := runLive_counts bNum bDen indices s htrace
  have hsum : CountsZero (traceSum (localTrace bNum bDen indices s)) := by
    rcases hinit with ⟨hi0, hi1, hi2, hi3⟩
    rcases hfinal with ⟨hf0, hf1, hf2, hf3⟩
    constructor
    · have := congrArg FailureCounts.mHi hrun
      change (readCounts (runLive bNum bDen indices s)).mHi =
        (readCounts s).mHi +
          (traceSum (localTrace bNum bDen indices s)).mHi at this
      rw [hf0, hi0] at this
      simpa using this.symm
    constructor
    · have := congrArg FailureCounts.mLo hrun
      change (readCounts (runLive bNum bDen indices s)).mLo =
        (readCounts s).mLo +
          (traceSum (localTrace bNum bDen indices s)).mLo at this
      rw [hf1, hi1] at this
      simpa using this.symm
    constructor
    · have := congrArg FailureCounts.gHi hrun
      change (readCounts (runLive bNum bDen indices s)).gHi =
        (readCounts s).gHi +
          (traceSum (localTrace bNum bDen indices s)).gHi at this
      rw [hf2, hi2] at this
      simpa using this.symm
    · have := congrArg FailureCounts.gLo hrun
      change (readCounts (runLive bNum bDen indices s)).gLo =
        (readCounts s).gLo +
          (traceSum (localTrace bNum bDen indices s)).gLo at this
      rw [hf3, hi3] at this
      simpa using this.symm
  exact allLocalPass_of_traceSum_zero bNum bDen indices s hsum

#print axioms counterBlock_run
#print axioms liveResidue_counts
#print axioms runLive_counts
#print axioms allLocalPass_of_terminal_zero

end LeanCompCert.Ports.ArraySegMertensFailureTelescope
