import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightInputLiteral

/-! Exact source semantics of the first height-prefix half. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

structure HistoricalHeightACore (records termDigest : Nat) (idx : Nat)
    (tag : Nat) (s : AState) : Prop where
  q : s.regs 128 = tag >>> 20
  alt : s.regs 148 =
    200 * (tag >>> 20) +
      (if (tag >>> 20) % 2 = 1 then 37500000 else 75000000)

theorem historicalHeightPrefixA_sourceCfg_core
    (records termDigest idx tag : Nat) (s : AState)
    (htag : s.regs 21 = tag) (htagWord : tag < M)
    (hqMax : tag >>> 20 ≤ maxQ) :
    HistoricalHeightACore records termDigest idx tag
      (arun idx s (historicalHeightPrefixA (sourceCfg records termDigest))) := by
  let q := tag >>> 20
  let parity := q % 2
  let sQ := arun idx s (historicalHeightQ (sourceCfg records termDigest))
  let sOdd := arun idx sQ (historicalHeightOdd (sourceCfg records termDigest))
  let sComp := arun idx sOdd
    (historicalHeightComplement (sourceCfg records termDigest))
  let sEven := arun idx sComp
    (historicalHeightEvenMul (sourceCfg records termDigest))
  let sCQ := arun idx sEven
    (historicalHeightCQSum (sourceCfg records termDigest))
  let sAlt := arun idx sCQ (historicalHeightAlt (sourceCfg records termDigest))
  have qres := historicalHeightQ_result (sourceCfg records termDigest) idx tag s
    htag htagWord
  change sQ.regs 128 = q ∧ sQ.regs 144 = parity at qres
  have parityBound : parity ≤ 1 := by
    have := Nat.mod_lt q (by decide : 0 < 2)
    omega
  have odd := historicalHeightOdd_sourceCfg_result records termDigest idx parity
    sQ qres.2 parityBound
  change sOdd.regs 145 = parity * 37500000 at odd
  have parityComp : sOdd.regs 144 = parity := by
    dsimp [sOdd]
    rw [frame (idx := idx) (r := 144)
      (l := historicalHeightOdd (sourceCfg records termDigest)) (by rfl)]
    exact qres.2
  have comp := historicalHeightComplement_result
    (sourceCfg records termDigest) idx parity sOdd parityComp parityBound
  change sComp.regs 146 = 1 - parity at comp
  have even := historicalHeightEvenMul_sourceCfg_result records termDigest idx
    (1 - parity) sComp comp (by omega)
  change sEven.regs 146 = (1 - parity) * 75000000 at even
  have oddEven : sEven.regs 145 = parity * 37500000 := by
    dsimp [sEven, sComp]
    rw [frame (idx := idx) (r := 145)
        (l := historicalHeightEvenMul (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 145)
        (l := historicalHeightComplement (sourceCfg records termDigest)) (by rfl)]
    exact odd
  have cq := historicalHeightCQSum_result (sourceCfg records termDigest) idx
    (parity * 37500000) ((1 - parity) * 75000000) sEven oddEven even (by
      have hp : parity = 0 ∨ parity = 1 := by omega
      rcases hp with hp | hp
      · rw [hp]
        decide
      · rw [hp]
        decide)
  change sCQ.regs 147 = parity * 37500000 +
    (1 - parity) * 75000000 at cq
  have qCQ : sCQ.regs 128 = q := by
    dsimp [sCQ, sEven, sComp, sOdd]
    rw [frame (idx := idx) (r := 128)
        (l := historicalHeightCQSum (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightEvenMul (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightComplement (sourceCfg records termDigest)) (by rfl),
      frame (idx := idx) (r := 128)
        (l := historicalHeightOdd (sourceCfg records termDigest)) (by rfl)]
    exact qres.1
  have alt := historicalHeightAlt_sourceCfg_result records termDigest idx q
    (parity * 37500000 + (1 - parity) * 75000000) sCQ qCQ cq (by
      change q ≤ 400000 at hqMax
      have hp : parity = 0 ∨ parity = 1 := by omega
      rcases hp with hp | hp
      · rw [hp]
        simp only [Nat.zero_mul, Nat.sub_zero, Nat.one_mul, Nat.zero_add, M]
        omega
      · rw [hp]
        simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero, M]
        omega)
  change sAlt.regs 148 = 200 * q +
    (parity * 37500000 + (1 - parity) * 75000000) at alt
  have qAlt : sAlt.regs 128 = q := by
    dsimp [sAlt]
    rw [frame (idx := idx) (r := 128)
      (l := historicalHeightAlt (sourceCfg records termDigest)) (by rfl)]
    exact qCQ
  have altRef : sAlt.regs 148 = 200 * q +
      (if parity = 1 then 37500000 else 75000000) := by
    rw [alt]
    have hp : parity = 0 ∨ parity = 1 := by omega
    rcases hp with hp | hp
    · rw [hp]
      simp
    · rw [hp]
      simp
  have outEq : arun idx s
      (historicalHeightPrefixA (sourceCfg records termDigest)) = sAlt := by
    simp only [historicalHeightPrefixA, arun_append, sQ, sOdd, sComp, sEven,
      sCQ, sAlt]
  rw [outEq]
  exact ⟨qAlt, by simpa only [q, parity] using altRef⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety
