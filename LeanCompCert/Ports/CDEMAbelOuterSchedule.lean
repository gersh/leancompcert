import LeanCompCert.Ports.CDEMAbelOuter

namespace LeanCompCert.Ports.CDEMAbelOuterSchedule

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelSchedule
open LeanCompCert.Ports.CDEMAbelOuter

def bodyIter (c : Cfg) (idx : Nat) : Nat → AState → AState
  | 0, st => st
  | n + 1, st => arun idx (bodyIter c idx n st) c.body

structure OuterMiddleTraceSpec (c : Cfg) (k : Nat) (p : Bracket)
    (n : Nat) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  sink_zero : n ≠ 0 → after.arr c.sink = 0
  low : after.regs rSl = (forwardIter c.wScale k n p).lo
  high : after.regs rSh = (forwardIter c.wScale k n p).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + n
  cell : after.regs rC = before.regs rC

theorem bodyIter_middle_contracts (c : Cfg) (idx n : Nat) (st : AState)
    (k : Nat) (p : Bracket)
    (hlo : st.regs rSl = p.lo) (hhi : st.regs rSh = p.hi)
    (hcontract : ∀ i, i < n →
      OuterMiddleSpec c k (forwardIter c.wScale k i p)
        (bodyIter c idx i st) (bodyIter c idx (i + 1) st)) :
    OuterMiddleTraceSpec c k p n st (bodyIter c idx n st) := by
  induction n with
  | zero =>
      exact
        { live := by intro j _; rfl
          sink_zero := by simp
          low := hlo
          high := hhi
          uPos := rfl
          uNeg := rfl
          viol := rfl
          vDiv := rfl
          vBisect := rfl
          v := rfl
          round := by simp [bodyIter]
          cell := rfl }
  | succ n ih =>
      have hpre : ∀ i, i < n →
          OuterMiddleSpec c k (forwardIter c.wScale k i p)
            (bodyIter c idx i st) (bodyIter c idx (i + 1) st) :=
        fun i hi => hcontract i (by omega)
      have hi := ih hpre
      have hs := hcontract n (by omega)
      exact
        { live := by
            intro j hj
            exact (hs.arr.live j hj).trans (hi.live j hj)
          sink_zero := by intro _; exact hs.arr.sink_zero
          low := hs.low
          high := hs.high
          uPos := hs.uPos.trans hi.uPos
          uNeg := hs.uNeg.trans hi.uNeg
          viol := hs.viol.trans hi.viol
          vDiv := hs.vDiv.trans hi.vDiv
          vBisect := hs.vBisect.trans hi.vBisect
          v := hs.v.trans hi.v
          round := by rw [hs.round, hi.round]; omega
          cell := hs.cell.trans hi.cell }

def bodySchedule (c : Cfg) (idx middleCount : Nat) (st : AState) : AState :=
  arun idx (bodyIter c idx middleCount (arun idx st c.body)) c.body

structure OuterFullAccSpec (c : Cfg) (k dp dn ceil floor root d : Nat)
    (before after : AState) : Prop where
  sink_zero : after.arr c.sink = 0
  live : ∀ j, j ≠ c.sink → after.arr j =
    if j = before.regs rC + c.winBase then 0 else before.arr j
  low : after.regs rSl = root
  high : after.regs rSh = root
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi) + dp * ceil
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi) + dn * floor
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * root
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

theorem bodySchedule_of_contracts (c : Cfg) (idx middleCount : Nat)
    (st : AState) (k dp dn ceil floor root d : Nat)
    (hf : OuterFirstSpec c k dp dn ceil floor st (arun idx st c.body))
    (hm : OuterMiddleTraceSpec c k (initial c.wScale k) middleCount
      (arun idx st c.body)
      (bodyIter c idx middleCount (arun idx st c.body)))
    (hl : OuterFinalSpec c root d
      (bodyIter c idx middleCount (arun idx st c.body))
      (bodySchedule c idx middleCount st)) :
    OuterFullAccSpec c k dp dn ceil floor root d st
      (bodySchedule c idx middleCount st) := by
  exact
    { sink_zero := hl.arr.sink_zero
      live := by
        intro j hj
        exact (hl.arr.live j hj).trans ((hm.live j hj).trans (hf.arr.live j hj))
      low := hl.low
      high := hl.high
      uPos := hl.uPos.trans (hm.uPos.trans hf.uPos)
      uNeg := hl.uNeg.trans (hm.uNeg.trans hf.uNeg)
      viol := hl.viol.trans (hm.viol.trans hf.viol)
      vDiv := hl.vDiv.trans (hm.vDiv.trans hf.vDiv)
      vBisect := hl.vBisect.trans (hm.vBisect.trans hf.vBisect)
      v := by rw [hl.v, hm.v, hf.v]
      round := hl.round
      cell := by rw [hl.cell, hm.cell, hf.cell] }

end LeanCompCert.Ports.CDEMAbelOuterSchedule
