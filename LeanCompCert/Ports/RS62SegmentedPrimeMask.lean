import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Ports.ArraySegMobiusIndexedMain
import LeanCompCert.Ports.RS62PrimeMaskLadder

/-!
# Compiled segmented prime masks for RS62

The general segmented Möbius core already contains a proved compressed sieve
schedule.  Its ordinary program continues into an accumulation phase and
clears each cell for reuse by the next window.  RS62 instead needs the
unmarked/composite bits themselves.  This module stops the same compiled core
after the first main marking phase, before any main cell is cleared.

Thus the production computation is entirely compiled: the root phase builds
the complete small-prime table, and the main phase marks one caller-selected
segment.  The proofs below expose the total trace symbolically; they do not
evaluate a production segment in Lean.
-/

namespace LeanCompCert.Ports.RS62SegmentedPrimeMask

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusPrimeInvariant
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Verified.PackedSieve

/-- Root construction followed by exactly one main marking phase. -/
def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.rootSpan + c.markSteps
  init := c.coreInit
  body := c.coreBody
  epilogue := []
  output := outputReg
}

set_option maxRecDepth 40000 in
theorem init_all (c : Cfg) :
    c.coreInit.all (ainstrWFB regCount) = true :=
  coreInit_all c

set_option maxRecDepth 40000 in
theorem body_all (c : Cfg) :
    c.coreBody.all (ainstrWFB regCount) = true :=
  coreBody_all c

/-- The mark-only producer is accepted by the proved array compiler. -/
theorem program_wf (c : Cfg) : (program c).WF :=
  ⟨show outputReg < regCount by decide,
    forall_wf_of_all (init_all c),
    forall_wf_of_all (body_all c), by simp [program]⟩

/-- Total source state of the mark-only producer.  The split is explicit so
root-table construction and main marking can reuse their existing proofs. -/
def markedState (c : Cfg) : AState :=
  indexedBodyRun 0 c (c.rootSpan + c.markSteps)
    (arun 0 initialAState c.coreInit)

theorem markedState_split (c : Cfg) :
    markedState c =
      indexedBodyRun c.rootSpan c c.markSteps
        (indexedBodyRun 0 c c.rootSpan
          (arun 0 initialAState c.coreInit)) := by
  rw [markedState, indexedBodyRun_add]
  simp only [Nat.zero_add]

/-- The unsplit total fold is the root/main decomposition above. -/
theorem markedState_eq_fold (c : Cfg) :
    markedState c =
      (List.range (c.rootSpan + c.markSteps)).foldl
        (fun s k => arun k s c.coreBody)
        (arun 0 initialAState c.coreInit) := by
  exact (foldl_range_coreBody_eq_indexedBodyRun c
    (c.rootSpan + c.markSteps)
    (arun 0 initialAState c.coreInit)).symm

/-- Any successful partial source execution ends in the symbolic mark-only
state.  A compiled audit supplies success without Lean running the fold. -/
theorem eq_markedState_of_run (c : Cfg) (out : AState)
    (hRun : (program c).runFromArray (fun _ => 0) = some out) :
    out = markedState c := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some
    (program c) (fun _ => 0) out hRun
  have hInitial : initialAStateWithArray (fun _ => 0) = initialAState := rfl
  rw [hInitial] at h
  rw [markedState_eq_fold]
  simpa [program, arun] using h

/-- The retained cell after the mark-only run is the exact finite fold over
the root phase's proved complete prime table.  The side conditions are compact
configuration facts; no main-window cell is evaluated in this proof. -/
theorem markedCell_eq_rootCellFold
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (i : Nat) (hi : i < c.segLen) :
    machineCell c (markedState c) i =
      rootCellFold (rootScanMixed c.bootPrimes bootBound 1 valid)
        (c.lo + i) := by
  let entry := arun 0 initialAState c.coreInit
  let rootOut := indexedWindowRun 0 c 1 entry
  let ps := rootScanMixed c.bootPrimes bootBound 1 valid
  have hr := indexedProductionRoot_single_mixed_padded_complete
    c bootBound valid delta h
  change RootTableInv c rootOut ps c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c rootOut j = ⟨0, 0⟩) ∧
      rootOut.regs rR = 0 ∧
      rootOut.regs rW = (1 + ((c.segLen + delta) % M)) % M ∧
      rootOut.regs rZero = 0 at hr
  obtain ⟨bootTail, hboot⟩ := h.bootShape
  obtain ⟨tail, hprefix⟩ :=
    rootScanMixed_has_prefix c.bootPrimes bootBound 1 valid
  let rest := bootTail ++ tail
  have hps : ps = c.firstPrime :: rest := by
    dsimp only [ps]
    rw [hprefix, hboot]
    rfl
  have hrootEq : indexedBodyRun 0 c c.rootSpan entry = rootOut := by
    dsimp only [rootOut]
    rw [indexedWindowRun]
    simp only [Nat.one_mul, h.rootIndex]
  rw [markedState_split, show arun 0 initialAState c.coreInit = entry by rfl,
    hrootEq]
  rw [show rootScanMixed c.bootPrimes bootBound 1 valid = ps by rfl, hps]
  apply indexedBodyRun_main_cell_eq_rootCellFold c c.rootSpan rootOut rest
    c.rootCap c.lo i
  · simpa [hps] using hr.1.toMachineTableRep
  · simpa [hps] using hr.1.primeTable
  · simpa [ps, hps] using hLen
  · exact hr.2.2.1
  · exact hr.2.2.2.1.trans hBase
  · exact Nat.le_refl _
  · rw [← hLen]
    simpa [ps, hps]
  · exact h.tableLenM
  · exact h.markM
  · exact h.periodM
  · exact hIdxM
  · exact h.spanM
  · rw [← h.rootIndex]
    exact Nat.lt_of_lt_of_le h.markPos (by simp [Cfg.period])
  · exact h.firstPrimePos
  · exact h.firstPrimeLeLen
  · exact Nat.le_trans h.firstPrimeLeBoot h.bootLeCap
  · exact h.rootCapM
  · exact hRootSqM
  · exact hSegRootM
  · exact hLoSegM
  · have hoff : firstOffset c.lo c.firstPrime < c.firstPrime :=
      Nat.mod_lt _ h.firstPrimePos
    have hpL : c.firstPrime ≤ c.segLen := h.firstPrimeLeLen
    omega
  · exact h.arrayM
  · simpa [ps, hps] using hBudget
  · exact hi
  · exact hr.2.1 i hi

/-- Above the table bound and below its square, absence of a divisor in a
complete prime table is exactly primality. -/
theorem unmarked_iff_isPrime_of_complete {ps : List Nat} {root n : Nat}
    (hTable : PrimeTableInv ps root) (hroot : root < n)
    (hn2 : 2 ≤ n) (hnSq : n ≤ root * root) :
    UnmarkedBy ps n ↔ IsPrime n := by
  constructor
  · intro hu
    apply Classical.byContradiction
    intro hnp
    obtain ⟨q, hqPrime, hqDvd, hqSq⟩ :=
      exists_prime_factor_le_sqrt hn2 hnp
    have hqRoot : q ≤ root := by
      by_cases hle : q ≤ root
      · exact hle
      · exfalso
        have hnext : root + 1 ≤ q := by omega
        have hmul : (root + 1) * (root + 1) ≤ q * q :=
          Nat.mul_le_mul hnext hnext
        have hstrict : root * root < (root + 1) * (root + 1) :=
          Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_succ_self root)
            (Nat.lt_succ_self root)
        have hbad : (root + 1) * (root + 1) ≤ root * root :=
          Nat.le_trans hmul (Nat.le_trans hqSq hnSq)
        exact (Nat.not_lt_of_ge hbad) hstrict
    exact hu q (hTable.complete q hqPrime hqRoot) hqDvd
  · intro hnPrime p hp hpd
    have hpPrime := hTable.sound p hp
    rcases hnPrime.eq_one_or_self hpd with hpOne | hpSelf
    · have := hpPrime.two_le
      omega
    · have hpRoot := hTable.upper p hp
      omega

/-- Source-facing meaning of the compiled mark-only array: a retained zero
product cell is exactly a prime in the represented segment. -/
theorem markedCell_zero_iff_isPrime
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (i : Nat) (hi : i < c.segLen) :
    (markedState c).arr i = 0 ↔ IsPrime (c.lo + i) := by
  let ps := rootScanMixed c.bootPrimes bootBound 1 valid
  have hcell := markedCell_eq_rootCellFold c bootBound valid delta h hBase
    hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM i hi
  have hprod : (markedState c).arr i = (rootCellFold ps (c.lo + i)).prod := by
    simpa [machineCell, ps] using congrArg RootCellState.prod hcell
  rw [hprod]
  let entry := arun 0 initialAState c.coreInit
  let rootOut := indexedWindowRun 0 c 1 entry
  have hr := indexedProductionRoot_single_mixed_padded_complete
    c bootBound valid delta h
  change RootTableInv c rootOut ps c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c rootOut j = ⟨0, 0⟩) ∧
      rootOut.regs rR = 0 ∧
      rootOut.regs rW = (1 + ((c.segLen + delta) % M)) % M ∧
      rootOut.regs rZero = 0 at hr
  have hnPos : 0 < c.lo + i := by omega
  have hnM : c.lo + i < M := by omega
  rw [rootCellFold_prod_eq_zero_iff_unmarked ps (c.lo + i)
    hr.1.primeTable.sound hr.1.primeTable.ordered hnPos hnM]
  apply unmarked_iff_isPrime_of_complete hr.1.primeTable
  · exact Nat.lt_of_lt_of_le hAboveRoot (Nat.le_add_right _ _)
  · have hrootTwo : 2 ≤ c.rootCap :=
      Nat.le_trans h.bootTwo h.bootLeCap
    omega
  · have hlast : c.lo + i ≤ c.lo + c.segLen - 1 := by omega
    exact Nat.le_trans hlast hCovered

/-- Physical-receipt form: compiler-verified success of the mark-only program
identifies every output cell with primality in the represented segment. -/
theorem run_cell_zero_iff_isPrime
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (out : AState)
    (hRun : (program c).runFromArray (fun _ => 0) = some out)
    (i : Nat) (hi : i < c.segLen) :
    out.arr i = 0 ↔ IsPrime (c.lo + i) := by
  rw [eq_markedState_of_run c out hRun]
  exact markedCell_zero_iff_isPrime c bootBound valid delta h hBase hLen
    hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot hCovered i hi

/-! ## Linear zero-product to `0`/`1` mask normalization -/

def zeroMarkBit (x : Nat) : Nat := if x = 0 then 1 else 0

def normalizeBody : List AInstr :=
  [ .scalar (.mov 0 .idx)
  , .load 1 0
  , .scalar (.binop 2 .eq (.reg 1) (.lit 0))
  , .store 0 2 ]

def normalizeProgram (f : Nat) : AProgram := {
  -- Register 3 is deliberately untouched and therefore remains zero.  The
  -- last normalized mask bit lives in register 2 and may legitimately be one
  -- when a segment ends at a prime; it is data, not a failure verdict.
  regCount := 4
  arrayLen := f
  loopCount := f
  init := []
  body := normalizeBody
  epilogue := []
  output := 3
}

theorem normalizeProgram_wf (f : Nat) : (normalizeProgram f).WF := by
  refine ⟨by change 3 < 4; decide, by simp [normalizeProgram], ?_,
    by simp [normalizeProgram]⟩
  apply forall_wf_of_all
  rfl

theorem normalizeBody_run (k : Nat) (s : AState) (hkM : k < M) :
    let out := arun k s normalizeBody
    out.arr = fun i => if i = k then zeroMarkBit (s.arr k) else s.arr i := by
  simp [normalizeBody, zeroMarkBit, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt hkM]

def normalizedState (arr : Nat → Nat) (f : Nat) : AState :=
  (List.range f).foldl (fun s k => arun k s normalizeBody)
    (initialAStateWithArray arr)

theorem normalizedState_succ (arr : Nat → Nat) (f : Nat) :
    normalizedState arr (f + 1) =
      arun f (normalizedState arr f) normalizeBody := by
  unfold normalizedState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem normalizedState_cell_all (arr : Nat → Nat) (f i : Nat)
    (hfM : f < M) :
    (normalizedState arr f).arr i =
      if i < f then zeroMarkBit (arr i) else arr i := by
  induction f with
  | zero => simp [normalizedState, initialAStateWithArray]
  | succ f ih =>
      rw [normalizedState_succ]
      have hbody := normalizeBody_run f (normalizedState arr f) (by omega)
      dsimp only at hbody
      rw [hbody]
      by_cases hif : i = f
      · subst i
        simp [ih (by omega)]
      · change (if i = f then zeroMarkBit ((normalizedState arr f).arr f)
          else (normalizedState arr f).arr i) = _
        rw [if_neg hif, ih (by omega)]
        by_cases hi : i < f
        · have hiSucc : i < f + 1 := by omega
          simp [hi, hiSucc]
        · have hsucc : ¬i < f + 1 := by omega
          simp [hi, hsucc]

theorem normalizedState_cell (arr : Nat → Nat) (f i : Nat)
    (hfM : f < M) (hi : i < f) :
    (normalizedState arr f).arr i = zeroMarkBit (arr i) := by
  rw [normalizedState_cell_all arr f i hfM, if_pos hi]

/-- Boolean prime predicate consumed by the compiled RS62 ladder. -/
def isPrimeBool (n : Nat) : Bool := decide (IsPrime n)

/-- Normalizing the retained product cells produces exactly the `0`/`1`
prime mask required by the linear compiled ladder.  This theorem is symbolic
in the segment length; it does not evaluate a production segment in Lean. -/
theorem normalizedMarkedState_maskCorrect
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap) :
    RS62PrimeMaskLadder.MaskCorrect isPrimeBool
      (normalizedState (markedState c).arr c.segLen).arr c.lo c.segLen := by
  intro k hk
  have hSegM : c.segLen < M := by omega
  rw [normalizedState_cell _ _ _ hSegM hk]
  have hPrime := markedCell_zero_iff_isPrime c bootBound valid delta h
    hBase hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot
    hCovered k hk
  by_cases hp : IsPrime (c.lo + k)
  · have hz : (markedState c).arr k = 0 := hPrime.mpr hp
    simp [zeroMarkBit, isPrimeBool, hp, hz]
  · have hnz : (markedState c).arr k ≠ 0 := fun hz => hp (hPrime.mp hz)
    simp [zeroMarkBit, isPrimeBool, hp, hnz]

/-- The normalizer's partial semantics is total for every word-sized length;
the theorem is symbolic in `f`. -/
theorem normalize_run (arr : Nat → Nat) (f : Nat) (hfM : f < M) :
    (normalizeProgram f).runFromArray arr = some (normalizedState arr f) := by
  apply AProgram.runFromArray_eq_foldl_mem
    (p := normalizeProgram f) (P := fun _ => True)
    (step := fun k s => arun k s normalizeBody)
    (fin := fun s => s) (arr := arr)
    (s₀ := initialAStateWithArray arr)
  · rfl
  · trivial
  · intro k s hk _
    simp only [normalizeProgram] at hk
    apply denoteAInstrs_eq_arun
    simp [normalizeProgram, normalizeBody, AllDefined, ADefined, arun,
      astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      Nat.mod_eq_of_lt (show k < M by omega), hk]
  · intros; trivial
  · intros; rfl

/-- Successful compiled marking and normalization runs expose the exact prime
mask.  The two run equations are the only physical inputs; the refinement is
proved without evaluating the segment. -/
theorem normalizedRun_maskCorrect
    (c : Cfg) (bootBound valid delta : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (marked normalized : AState)
    (hMark : (program c).runFromArray (fun _ => 0) = some marked)
    (hNormalize : (normalizeProgram c.segLen).runFromArray marked.arr =
      some normalized) :
    RS62PrimeMaskLadder.MaskCorrect isPrimeBool normalized.arr c.lo
      c.segLen := by
  have hSegM : c.segLen < M := by omega
  have hExpected := normalize_run marked.arr c.segLen hSegM
  have hNormalized : normalized = normalizedState marked.arr c.segLen := by
    exact Option.some.inj (hNormalize.symm.trans hExpected)
  have hMarked : marked = markedState c := eq_markedState_of_run c marked hMark
  rw [hNormalized, hMarked]
  exact normalizedMarkedState_maskCorrect c bootBound valid delta h hBase
    hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot hCovered

/-- End-to-end source observation for the three compiled stages.  A physical
campaign supplies the three successful run equations and compact word-room
facts; this theorem then proves the exact RS62 source recurrence. -/
theorem source_loopE_of_compiled_pipeline
    (c : Cfg) (bootBound valid delta SL SU outReg : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBase : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (hn0 : 3 ≤ c.lo) (hSL : SL < M) (hSU : SU < M)
    (hEnd : c.lo + c.segLen ≤ 2 ^ 40)
    (marked normalized ladderOut : AState)
    (hMark : (program c).runFromArray (fun _ => 0) = some marked)
    (hNormalize : (normalizeProgram c.segLen).runFromArray marked.arr =
      some normalized)
    (hSLRoom : SL + c.segLen * LeanCompCert.Ports.RS62.fpD +
      LeanCompCert.Ports.RS62.fpD < M)
    (hSURoom : SU + c.segLen * (LeanCompCert.Ports.RS62.fpD + c.lo +
      c.segLen) + (LeanCompCert.Ports.RS62.fpD + c.lo + c.segLen) < M)
    (hLadder :
      (RS62PrimeMaskLadder.program c.lo c.segLen SL SU outReg).runFromArray
        normalized.arr = some ladderOut) :
    ladderOut.regs RS62PrimeMaskLadder.rLogL =
        (LeanCompCert.Ports.RS62.loopE isPrimeBool c.segLen c.lo SL SU).1 ∧
      ladderOut.regs RS62PrimeMaskLadder.rLogU =
        (LeanCompCert.Ports.RS62.loopE isPrimeBool c.segLen c.lo SL SU).2 ∧
      ladderOut.arr = normalized.arr := by
  have hSegM : c.segLen < M := by omega
  have hMask := normalizedRun_maskCorrect c bootBound valid delta h hBase
    hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot hCovered
    marked normalized hMark hNormalize
  have hRoom := RS62PrimeMaskLadder.room_of_endpoint_bounds isPrimeBool
    normalized.arr c.lo c.segLen SL SU hn0 hMask hSLRoom hSURoom
  exact RS62PrimeMaskLadder.source_loopE_of_runFromArray isPrimeBool
    normalized.arr c.lo c.segLen SL SU outReg hn0 hSL hSU hSegM hEnd hRoom
    hMask ladderOut hLadder

#print axioms program_wf
#print axioms markedState_split
#print axioms markedState_eq_fold
#print axioms eq_markedState_of_run
#print axioms markedCell_eq_rootCellFold
#print axioms unmarked_iff_isPrime_of_complete
#print axioms markedCell_zero_iff_isPrime
#print axioms run_cell_zero_iff_isPrime
#print axioms normalizeProgram_wf
#print axioms normalizedState_cell
#print axioms normalizedMarkedState_maskCorrect
#print axioms normalize_run
#print axioms normalizedRun_maskCorrect
#print axioms source_loopE_of_compiled_pipeline

end LeanCompCert.Ports.RS62SegmentedPrimeMask
