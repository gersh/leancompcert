/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Ports.ArrayConstantUpperBoundScanner

namespace LeanCompCert.Ports.R2DenseLsumPlaneProduction

open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Ports.ArrayConstantUpperBoundScanner

abbrev bound : Nat := 2 ^ 29 - 1

theorem denseHeadFirst_segLen : denseHeadFirstCfg.segLen = 998 := by rfl
theorem denseHeadSecond_segLen : denseHeadSecondCfg.segLen = 143999 := by rfl

def firstScanner : Cfg :=
  { arrayLen := denseHeadFirstCfg.arrayLen, segLen := denseHeadFirstCfg.arrayLen
    bound := bound, iLo := denseHeadFirstCfg.segLen
    iHi := 2 * denseHeadFirstCfg.segLen }

def secondScanner0 : Cfg :=
  { arrayLen := denseHeadSecondCfg.arrayLen, segLen := denseHeadSecondCfg.arrayLen
    bound := bound, iLo := denseHeadSecondCfg.segLen
    iHi := denseHeadSecondCfg.segLen + 72000 }

def secondScanner1 : Cfg :=
  { arrayLen := denseHeadSecondCfg.arrayLen, segLen := denseHeadSecondCfg.arrayLen
    bound := bound, iLo := denseHeadSecondCfg.segLen + 72000
    iHi := 2 * denseHeadSecondCfg.segLen }

theorem first_literal : firstScanner =
    { arrayLen := 7435, segLen := 7435, bound := 536870911,
      iLo := 998, iHi := 1996 } := by rfl
theorem second0_literal : secondScanner0 =
    { arrayLen := 1008349, segLen := 1008349, bound := 536870911,
      iLo := 143999, iHi := 215999 } := by rfl
theorem second1_literal : secondScanner1 =
    { arrayLen := 1008349, segLen := 1008349, bound := 536870911,
      iLo := 215999, iHi := 287998 } := by rfl

theorem first_checked_cell {arr : Nat → Nat}
    (h : ShardChecked firstScanner arr) {i : Nat} (hi : i < 998) :
    arr (998 + i) ≤ bound := by
  rw [first_literal] at h
  change ∀ j, 998 ≤ j → j < 1996 → arr j ≤ 536870911 at h
  exact h (998 + i) (by omega) (by omega)

theorem second0_checked_cell {arr : Nat → Nat}
    (h : ShardChecked secondScanner0 arr) {i : Nat} (hi : i < 72000) :
    arr (143999 + i) ≤ bound := by
  rw [second0_literal] at h
  change ∀ j, 143999 ≤ j → j < 215999 → arr j ≤ 536870911 at h
  exact h (143999 + i) (by omega) (by omega)

theorem second1_checked_cell {arr : Nat → Nat}
    (h : ShardChecked secondScanner1 arr) {i : Nat}
    (hlo : 72000 ≤ i) (hi : i < 143999) :
    arr (143999 + i) ≤ bound := by
  rw [second1_literal] at h
  change ∀ j, 215999 ≤ j → j < 287998 → arr j ≤ 536870911 at h
  exact h (143999 + i) (by omega) (by omega)

end LeanCompCert.Ports.R2DenseLsumPlaneProduction
