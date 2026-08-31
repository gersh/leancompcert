import LeanCompCert.Ports.RS62SegmentedPrimeMask

/-!
# Segmented prime masks with a multi-window padded root phase

The original prime-mask consumer exposed only the one-root-window schedule.
For source-scale `u64` intervals that shape forces a resident segment larger
than the square-root table bound.  This module reuses the already proved
`PaddedProductionRootSchedule` execution and proves the same exact mask
denotation for an arbitrary number of root windows.

No root table or target segment is evaluated here.
-/

namespace LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.RS62SegmentedPrimeMask
open LeanCompCert.Verified.PackedSieve

set_option maxRecDepth 20000

/-- Exact table produced by a padded final root window. -/
def paddedRootTable (c : Cfg) (bootBound bootFuel laterFuel valid : Nat) :
    List Nat :=
  rootScanFrom
    (rootLaterWindows c
      (crossingTable c bootBound bootFuel) (laterBase c bootFuel) laterFuel)
    (laterBase c bootFuel + laterFuel * c.segLen) valid

/-- The multi-root analogue of `markedCell_eq_rootCellFold`. -/
theorem markedCell_eq_rootCellFold
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      0 delta)
    (hBase : mainBase c bootFuel laterFuel delta = c.lo)
    (hBudget : ((paddedRootTable c bootBound bootFuel laterFuel valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hLoSegM : c.lo + c.segLen < M)
    (i : Nat) (hi : i < c.segLen) :
    machineCell c
        (RS62SegmentedPrimeMask.markedState c) i =
      rootCellFold (paddedRootTable c bootBound bootFuel laterFuel valid)
        (c.lo + i) := by
  let entry := arun 0 initialAState c.coreInit
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let rootOut := indexedWindowRun 0 c rootFuel entry
  let ps := paddedRootTable c bootBound bootFuel laterFuel valid
  have hr := indexedProductionRoot_padded_complete c bootBound bootFuel
    laterFuel valid delta h.toPaddedProductionRootSchedule
  change (∀ j, j < c.segLen →
        machineCell c rootOut j = ⟨0, 0⟩) ∧
      MachineTableRep c rootOut ps ∧ rootOut.regs rR = 0 ∧
      rootOut.regs rW = mainBase c bootFuel laterFuel delta ∧
      rootOut.regs rZero = 0 at hr
  have hrootFuel : rootFuel * c.period = c.rootSpan := by
    have hfinal := h.finalIndex
    dsimp only [rootFuel]
    simp only [Nat.add_mul, Nat.one_mul] at hfinal ⊢
    omega
  have hrootEq : indexedBodyRun 0 c c.rootSpan entry = rootOut := by
    dsimp only [rootOut]
    rw [indexedWindowRun]
    rw [hrootFuel]
  obtain ⟨rest, hshape⟩ :=
    paddedFinalRootTable_shape c bootBound bootFuel laterFuel valid h.bootShape
  have hps : ps = c.firstPrime :: rest := by
    simpa [ps, paddedRootTable] using hshape
  have hPrime : PrimeTableInv ps c.rootCap := by
    simpa [ps, paddedRootTable] using h.finalPrime
  have hLen : ps.length = c.tableLen := by
    simpa [ps, paddedRootTable] using h.finalLen
  rw [RS62SegmentedPrimeMask.markedState_split,
    show arun 0 initialAState c.coreInit = entry by rfl, hrootEq]
  rw [show paddedRootTable c bootBound bootFuel laterFuel valid = ps by rfl,
    hps]
  apply indexedBodyRun_main_cell_eq_rootCellFold c c.rootSpan rootOut rest
    c.rootCap c.lo i
  · simpa [ps, hps] using hr.2.1
  · simpa [hps] using hPrime
  · simpa [hps] using hLen
  · exact hr.2.2.1
  · exact hr.2.2.2.1.trans hBase
  · exact Nat.le_refl _
  · exact h.tableLenPos
  · exact h.tableLenM
  · exact h.markM
  · exact h.periodM
  · exact hIdxM
  · exact h.spanM
  · exact h.spanPos
  · exact h.firstPrimePos
  · exact h.firstPrimeLeLen
  · exact h.firstPrimeLeCap
  · exact h.rootCapM
  · exact h.finalBoundSqM
  · exact h.segFinalM
  · exact hLoSegM
  · have hoff : firstOffset c.lo c.firstPrime <
        c.firstPrime := Nat.mod_lt _ h.firstPrimePos
    have hoffLen : firstOffset c.lo c.firstPrime < c.segLen :=
      Nat.lt_of_lt_of_le hoff h.firstPrimeLeLen
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoffLen c.lo)
      (Nat.le_of_lt hLoSegM)
  · exact h.arrayM
  · simpa [ps, hps] using hBudget
  · exact hi
  · exact hr.1 i hi

/-- Exact primality interpretation of a retained multi-root mark cell. -/
theorem markedCell_zero_iff_isPrime
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      0 delta)
    (hBase : mainBase c bootFuel laterFuel delta = c.lo)
    (hBudget : ((paddedRootTable c bootBound bootFuel laterFuel valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (i : Nat) (hi : i < c.segLen) :
    (RS62SegmentedPrimeMask.markedState c).arr i = 0 ↔
      IsPrime (c.lo + i) := by
  let ps := paddedRootTable c bootBound bootFuel laterFuel valid
  have hPrimeTable : PrimeTableInv ps c.rootCap := by
    simpa [ps, paddedRootTable] using h.finalPrime
  have hcell := markedCell_eq_rootCellFold c bootBound bootFuel laterFuel
    valid delta h hBase hBudget hIdxM hLoSegM i hi
  have hprod : (RS62SegmentedPrimeMask.markedState c).arr i =
      (rootCellFold ps (c.lo + i)).prod := by
    simpa [machineCell, ps] using
      congrArg ArraySegMobiusRootCellFold.RootCellState.prod hcell
  rw [hprod]
  have hnPos : 0 < c.lo + i := by omega
  have hnM : c.lo + i < M := by omega
  rw [rootCellFold_prod_eq_zero_iff_unmarked ps (c.lo + i)
    hPrimeTable.sound hPrimeTable.ordered hnPos hnM]
  apply RS62SegmentedPrimeMask.unmarked_iff_isPrime_of_complete hPrimeTable
  · exact Nat.lt_of_lt_of_le hAboveRoot (Nat.le_add_right _ _)
  · have hbootCap : bootBound ≤ c.rootCap := by
      exact Nat.le_trans (Nat.le_of_lt h.crossingLast) h.crossingCap
    have hrootTwo : 2 ≤ c.rootCap :=
      Nat.le_trans h.bootTwo hbootCap
    omega
  · have hlast : c.lo + i ≤ c.lo + c.segLen - 1 := by omega
    exact Nat.le_trans hlast hCovered

/-- Normalization of the multi-root marked state is the exact prime mask. -/
theorem normalizedMarkedState_maskCorrect
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      0 delta)
    (hBase : mainBase c bootFuel laterFuel delta = c.lo)
    (hBudget : ((paddedRootTable c bootBound bootFuel laterFuel valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap) :
    RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
      (RS62SegmentedPrimeMask.normalizedState
        (RS62SegmentedPrimeMask.markedState c).arr c.segLen).arr
      c.lo c.segLen := by
  intro k hk
  have hSegM : c.segLen < M := by omega
  rw [RS62SegmentedPrimeMask.normalizedState_cell _ _ _ hSegM hk]
  have hPrime := markedCell_zero_iff_isPrime c bootBound bootFuel laterFuel
    valid delta h hBase hBudget hIdxM hLoSegM hAboveRoot hCovered k hk
  by_cases hp : IsPrime (c.lo + k)
  · have hz : (RS62SegmentedPrimeMask.markedState c).arr k = 0 :=
      hPrime.mpr hp
    simp [RS62SegmentedPrimeMask.zeroMarkBit,
      RS62SegmentedPrimeMask.isPrimeBool, hp, hz]
  · have hnz : (RS62SegmentedPrimeMask.markedState c).arr k ≠ 0 :=
      fun hz => hp (hPrime.mp hz)
    simp [RS62SegmentedPrimeMask.zeroMarkBit,
      RS62SegmentedPrimeMask.isPrimeBool, hp, hnz]

/-- Successful source executions expose the exact multi-root prime mask. -/
theorem normalizedRun_maskCorrect
    (c : Cfg) (bootBound bootFuel laterFuel valid delta : Nat)
    (h : PaddedProductionCoreSchedule c bootBound bootFuel laterFuel valid
      0 delta)
    (hBase : mainBase c bootFuel laterFuel delta = c.lo)
    (hBudget : ((paddedRootTable c bootBound bootFuel laterFuel valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (marked normalized : AState)
    (hMark : (RS62SegmentedPrimeMask.program c).runFromArray (fun _ => 0) =
      some marked)
    (hNormalize : (RS62SegmentedPrimeMask.normalizeProgram c.segLen).runFromArray
      marked.arr = some normalized) :
    RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
      normalized.arr c.lo c.segLen := by
  have hSegM : c.segLen < M := by omega
  have hExpected := RS62SegmentedPrimeMask.normalize_run marked.arr c.segLen
    hSegM
  have hNormalized : normalized =
      RS62SegmentedPrimeMask.normalizedState marked.arr c.segLen := by
    exact Option.some.inj (hNormalize.symm.trans hExpected)
  have hMarked : marked = RS62SegmentedPrimeMask.markedState c :=
    RS62SegmentedPrimeMask.eq_markedState_of_run c marked hMark
  rw [hNormalized, hMarked]
  exact normalizedMarkedState_maskCorrect c bootBound bootFuel laterFuel valid
    delta h hBase hBudget hIdxM hLoSegM hAboveRoot hCovered

#print axioms markedCell_eq_rootCellFold
#print axioms markedCell_zero_iff_isPrime
#print axioms normalizedMarkedState_maskCorrect
#print axioms normalizedRun_maskCorrect

end LeanCompCert.Ports.RS62SegmentedPrimeMaskPadded
