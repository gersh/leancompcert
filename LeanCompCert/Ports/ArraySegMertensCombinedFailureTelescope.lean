import LeanCompCert.Ports.ArraySegMertensFailureTelescope
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Failure counters for the complete emitted Hurst/CDEM body

`ArraySegMertensFailureTelescope` proves the last eight instructions of the
live residue.  The emitted program executes the segmented sieve core before
that residue.  This file composes the two literally, then telescopes arbitrary
lists of complete emitted bodies.  The production endpoint remains symbolic.
-/

namespace LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMertensFailureTelescope

/-- State seen by the four comparison-counter instructions after the actual
segmented core and the comparison prefix of the residue have both run. -/
def combinedCounterInput (c : Cfg) (bNum bDen idx : Nat) (s : AState) : AState :=
  counterInput bNum bDen idx (arun idx s c.coreBody)

structure CombinedCounterReady (c : Cfg) (bNum bDen idx : Nat)
    (s : AState) : Prop where
  ready : CounterReady (combinedCounterInput c bNum bDen idx s)

/-- The segmented core does not write any retained Hurst/CDEM counter. -/
theorem coreBody_readCounts (c : Cfg) (idx : Nat) (s : AState) :
    readCounts (arun idx s c.coreBody) = readCounts s := by
  apply FailureCounts.ext
  · exact arun_frame idx rVMHi c.coreBody (by rfl) s
  · exact arun_frame idx rVMLo c.coreBody (by rfl) s
  · exact arun_frame idx rVGHi c.coreBody (by rfl) s
  · exact arun_frame idx rVGLo c.coreBody (by rfl) s

/-- One literal `coreBody ++ mertensLiveResidue` execution adds exactly its
four local failure bits to the retained counters. -/
theorem combinedBody_counts (c : Cfg) (bNum bDen idx : Nat) (s : AState)
    (h : CombinedCounterReady c bNum bDen idx s) :
    readCounts
        (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen)) =
      (readCounts s).add
        (localCounts (combinedCounterInput c bNum bDen idx s)) := by
  rw [arun_append]
  have hstep := liveResidue_counts bNum bDen idx
    (arun idx s c.coreBody) ⟨h.ready⟩
  change readCounts
      (arun idx (arun idx s c.coreBody)
        (mertensLiveResidue bNum bDen)) = _
  rw [hstep, coreBody_readCounts]
  rfl

/-- Source execution of a list of complete emitted bodies. -/
def runCombined (c : Cfg) (bNum bDen : Nat) : List Nat → AState → AState
  | [], s => s
  | idx :: indices, s =>
      runCombined c bNum bDen indices
        (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))

def combinedLocalTrace (c : Cfg) (bNum bDen : Nat) :
    List Nat → AState → List FailureCounts
  | [], _ => []
  | idx :: indices, s =>
      localCounts (combinedCounterInput c bNum bDen idx s) ::
        combinedLocalTrace c bNum bDen indices
          (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))

def CombinedTraceReady (c : Cfg) (bNum bDen : Nat) :
    List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      CombinedCounterReady c bNum bDen idx s ∧
        CombinedTraceReady c bNum bDen indices
          (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))

theorem runCombined_counts (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (htrace : CombinedTraceReady c bNum bDen indices s) :
    readCounts (runCombined c bNum bDen indices s) =
      (readCounts s).add
        (traceSum (combinedLocalTrace c bNum bDen indices s)) := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx indices ih =>
      have hstep := combinedBody_counts c bNum bDen idx s htrace.1
      have htail := ih
        (s := arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))
        htrace.2
      rw [runCombined, combinedLocalTrace, traceSum, htail, hstep]
      apply FailureCounts.ext <;> simp [FailureCounts.add] <;> omega

def CombinedAllLocalPass (c : Cfg) (bNum bDen : Nat) :
    List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      CountsZero (localCounts (combinedCounterInput c bNum bDen idx s)) ∧
        CombinedAllLocalPass c bNum bDen indices
          (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))

theorem combinedAllLocalPass_of_traceSum_zero (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (hzero : CountsZero
      (traceSum (combinedLocalTrace c bNum bDen indices s))) :
    CombinedAllLocalPass c bNum bDen indices s := by
  induction indices generalizing s with
  | nil => trivial
  | cons idx indices ih =>
      simp only [combinedLocalTrace, traceSum] at hzero
      have hmHi := Nat.add_eq_zero_iff.mp hzero.1
      have hmLo := Nat.add_eq_zero_iff.mp hzero.2.1
      have hgHi := Nat.add_eq_zero_iff.mp hzero.2.2.1
      have hgLo := Nat.add_eq_zero_iff.mp hzero.2.2.2
      constructor
      · exact ⟨hmHi.1, hmLo.1, hgHi.1, hgLo.1⟩
      · apply ih
        exact ⟨hmHi.2, hmLo.2, hgHi.2, hgLo.2⟩

/-- Zero initial and terminal counters force all four comparisons to pass at
every event of the actual complete emitted body. -/
theorem combinedAllLocalPass_of_terminal_zero (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (htrace : CombinedTraceReady c bNum bDen indices s)
    (hinit : CountsZero (readCounts s))
    (hfinal : CountsZero (readCounts
      (runCombined c bNum bDen indices s))) :
    CombinedAllLocalPass c bNum bDen indices s := by
  have hrun := runCombined_counts c bNum bDen indices s htrace
  have hsum : CountsZero
      (traceSum (combinedLocalTrace c bNum bDen indices s)) := by
    rcases hinit with ⟨hi0, hi1, hi2, hi3⟩
    rcases hfinal with ⟨hf0, hf1, hf2, hf3⟩
    constructor
    · have h := congrArg FailureCounts.mHi hrun
      change (readCounts (runCombined c bNum bDen indices s)).mHi =
        (readCounts s).mHi +
          (traceSum (combinedLocalTrace c bNum bDen indices s)).mHi at h
      rw [hf0, hi0] at h
      simpa using h.symm
    constructor
    · have h := congrArg FailureCounts.mLo hrun
      change (readCounts (runCombined c bNum bDen indices s)).mLo =
        (readCounts s).mLo +
          (traceSum (combinedLocalTrace c bNum bDen indices s)).mLo at h
      rw [hf1, hi1] at h
      simpa using h.symm
    constructor
    · have h := congrArg FailureCounts.gHi hrun
      change (readCounts (runCombined c bNum bDen indices s)).gHi =
        (readCounts s).gHi +
          (traceSum (combinedLocalTrace c bNum bDen indices s)).gHi at h
      rw [hf2, hi2] at h
      simpa using h.symm
    · have h := congrArg FailureCounts.gLo hrun
      change (readCounts (runCombined c bNum bDen indices s)).gLo =
        (readCounts s).gLo +
          (traceSum (combinedLocalTrace c bNum bDen indices s)).gLo at h
      rw [hf3, hi3] at h
      simpa using h.symm
  exact combinedAllLocalPass_of_traceSum_zero c bNum bDen indices s hsum

theorem runCombined_eq_foldl (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (s : AState) :
    runCombined c bNum bDen indices s =
      indices.foldl (fun st idx =>
        arun idx st (c.coreBody ++ mertensLiveResidue bNum bDen)) s := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx indices ih =>
      simp only [runCombined, List.foldl_cons]
      exact ih _

/-- State immediately before list position `i` in a complete-body trace. -/
def combinedPrefixState (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (i : Nat) (s : AState) : AState :=
  runCombined c bNum bDen (indices.take i) s

/-- A whole-trace pass proof exposes the local zero-count fact at every
indexed event, with the exact state produced by the preceding prefix. -/
theorem CombinedAllLocalPass.at (c : Cfg) (bNum bDen : Nat)
    (indices : List Nat) (s : AState)
    (hpass : CombinedAllLocalPass c bNum bDen indices s)
    (i : Nat) (hi : i < indices.length) :
    CountsZero (localCounts (combinedCounterInput c bNum bDen
      (indices.get ⟨i, hi⟩)
      (combinedPrefixState c bNum bDen indices i s))) := by
  induction indices generalizing s i with
  | nil => simp at hi
  | cons idx indices ih =>
      cases i with
      | zero =>
          change CountsZero
            (localCounts (combinedCounterInput c bNum bDen idx s))
          exact hpass.1
      | succ i =>
          have hi' : i < indices.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          have htail := ih
            (s := arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))
            hpass.2 i hi'
          simpa [combinedPrefixState, runCombined] using htail

#print axioms combinedBody_counts
#print axioms runCombined_counts
#print axioms combinedAllLocalPass_of_terminal_zero
#print axioms runCombined_eq_foldl
#print axioms CombinedAllLocalPass.at

end LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope
