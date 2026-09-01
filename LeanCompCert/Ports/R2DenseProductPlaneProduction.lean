/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Ports.R2DenseProductPlaneScanner

/-! Canonical product-plane scanner shards for the two dense producers. -/

namespace LeanCompCert.Ports.R2DenseProductPlaneProduction

open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Ports.R2DenseProductPlaneScanner

/-- The single scanner covering the first dense producer plane. -/
def firstScanner : Cfg :=
  { arrayLen := denseHeadFirstCfg.arrayLen
    segLen := denseHeadFirstCfg.segLen
    windowBase := denseHeadFirstCfg.lo
    iLo := 0
    iHi := denseHeadFirstCfg.segLen }

/-- First half of the second dense producer plane. -/
def secondScanner0 : Cfg :=
  { arrayLen := denseHeadSecondCfg.arrayLen
    segLen := denseHeadSecondCfg.segLen
    windowBase := denseHeadSecondCfg.lo
    iLo := 0
    iHi := 72000 }

/-- Remaining half-open tail of the second dense producer plane. -/
def secondScanner1 : Cfg :=
  { arrayLen := denseHeadSecondCfg.arrayLen
    segLen := denseHeadSecondCfg.segLen
    windowBase := denseHeadSecondCfg.lo
    iLo := 72000
    iHi := denseHeadSecondCfg.segLen }

theorem firstScanner_literal :
    firstScanner =
      { arrayLen := 7435
        segLen := 998
        windowBase := 3
        iLo := 0
        iHi := 998 } := by rfl

theorem secondScanner0_literal :
    secondScanner0 =
      { arrayLen := 1008349
        segLen := 143999
        windowBase := 1001
        iLo := 0
        iHi := 72000 } := by rfl

theorem secondScanner1_literal :
    secondScanner1 =
      { arrayLen := 1008349
        segLen := 143999
        windowBase := 1001
        iLo := 72000
        iHi := 143999 } := by rfl

end LeanCompCert.Ports.R2DenseProductPlaneProduction
