import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightPrefixASemanticsLiteral

/-! Exact source semantics of the second height-prefix half. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

structure HistoricalHeightBCore (idx q alt : Nat) (s : AState) : Prop where
  q : s.regs 128 = q
  tq : s.regs 152 = if 100000000 ≤ alt then alt else 100000000

theorem historicalHeightPrefixB_sourceCfg_core
    (records termDigest idx q alt : Nat) (s : AState)
    (hq : s.regs 128 = q) (halt : s.regs 148 = alt)
    (hqMax : q ≤ maxQ)
    (haltEq : alt = 200 * q +
      (if q % 2 = 1 then 37500000 else 75000000)) :
    HistoricalHeightBCore idx q alt
      (arun idx s (historicalHeightPrefixB (sourceCfg records termDigest))) := by
  let bit := if 100000000 ≤ alt then 1 else 0
  let sBit := arun idx s
    (historicalHeightSelectBit (sourceCfg records termDigest))
  let sAlt := arun idx sBit
    (historicalHeightSelectAlt (sourceCfg records termDigest))
  let sComp := arun idx sAlt
    (historicalHeightSelectComplement (sourceCfg records termDigest))
  let sFloor := arun idx sComp
    (historicalHeightSelectFloor (sourceCfg records termDigest))
  let sSum := arun idx sFloor
    (historicalHeightSelectSum (sourceCfg records termDigest))
  have altWord : alt < M := by
    change q ≤ 400000 at hqMax
    rw [haltEq]
    split <;> simp only [M] <;> omega
  have b := historicalHeightSelectBit_sourceCfg_result records termDigest idx
    alt s halt
  change sBit.regs 149 = bit at b
  have bitBound : bit ≤ 1 := by dsimp [bit]; split <;> omega
  have altBit : sBit.regs 148 = alt := by
    dsimp [sBit]
    rw [frame (idx := idx) (r := 148)
      (l := historicalHeightSelectBit (sourceCfg records termDigest)) (by rfl)]
    exact halt
  have selectedAlt := historicalHeightSelectAlt_result
    (sourceCfg records termDigest) idx bit alt sBit b altBit bitBound altWord
  change sAlt.regs 150 = bit * alt at selectedAlt
  have bitAlt : sAlt.regs 149 = bit := by
    dsimp [sAlt]
    rw [frame (idx := idx) (r := 149)
      (l := historicalHeightSelectAlt (sourceCfg records termDigest)) (by rfl)]
    exact b
  have comp := historicalHeightSelectComplement_result
    (sourceCfg records termDigest) idx bit sAlt bitAlt bitBound
  change sComp.regs 151 = 1 - bit at comp
  have floor := historicalHeightSelectFloor_sourceCfg_result records termDigest
    idx (1 - bit) sComp comp (by omega)
  change sFloor.regs 151 = (1 - bit) * 100000000 at floor
  have altFloor : sFloor.regs 150 = bit * alt := by
    dsimp [sFloor, sComp]
    rw [frame (idx := idx) (r := 150)
        (l := historicalHeightSelectFloor (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 150)
        (l := historicalHeightSelectComplement (sourceCfg records termDigest))
        (by rfl)]
    exact selectedAlt
  have sumWord : bit * alt + (1 - bit) * 100000000 < M := by
    have hfloor : 100000000 < M := by decide
    dsimp [bit]
    split <;> simp_all
  have sum := historicalHeightSelectSum_result
    (sourceCfg records termDigest) idx (bit * alt)
    ((1 - bit) * 100000000) sFloor altFloor floor sumWord
  change sSum.regs 152 = bit * alt + (1 - bit) * 100000000 at sum
  have tq : sSum.regs 152 =
      if 100000000 ≤ alt then alt else 100000000 := by
    rw [sum]
    dsimp [bit]
    split <;> simp
  have qSum : sSum.regs 128 = q := by
    dsimp [sSum, sFloor, sComp, sAlt, sBit]
    rw [frame (idx := idx) (r := 128)
        (l := historicalHeightSelectSum (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightSelectFloor (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightSelectComplement (sourceCfg records termDigest))
        (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightSelectAlt (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightSelectBit (sourceCfg records termDigest)) (by rfl)]
    exact hq
  have outEq : arun idx s
      (historicalHeightPrefixB (sourceCfg records termDigest)) = sSum := by
    simp only [historicalHeightPrefixB, arun_append, sBit, sAlt, sComp, sFloor,
      sSum]
  rw [outEq]
  exact ⟨qSum, tq⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety
