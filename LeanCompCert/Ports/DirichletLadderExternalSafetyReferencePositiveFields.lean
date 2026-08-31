import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveCopies
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveProjections

/-! Assemble the split positive-state slices against the actual `refStep`. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalPositiveFields (s : AState) (st : RefState) : Prop where
  prevTag : s.regs rPrevTag = st.prevTag
  prevBlk : s.regs rPrevBlk = st.prevBlk
  prevUpper : s.regs rPrevUpper = st.prevUpper
  prevBit : s.regs rPrevBit = st.prevBit
  firstBit : s.regs rFirstBit = st.firstBit
  trI0 : s.regs rTrI0 = st.trI0
  sj0 : s.regs rSj0 = st.sj0
  trI1 : s.regs rTrI1 = st.trI1
  sj1 : s.regs rSj1 = st.sj1
  prevLast : s.regs rPrevLast = st.prevLast
  prevConj : s.regs rPrevConj = st.prevConj
  prevDig : s.regs rPrevDig = st.prevDig

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

theorem historicalPositiveFields_of_cores
    (c : Cfg) (words : List Nat) (idx : Nat) (st : RefState)
    (mux out : AState) (hout : out = arun idx mux (historicalStateCopies c))
    (hmux : HistoricalMuxCore words idx st mux)
    (hcopy : HistoricalCopiedFields words idx out) :
    HistoricalPositiveFields out (refStep c words st idx) := by
  refine {
    prevTag := hcopy.prevTag.trans (refStep_prevTag c words st idx).symm
    prevBlk := hcopy.prevBlk.trans (refStep_prevBlk c words st idx).symm
    prevUpper := hcopy.prevUpper.trans (refStep_prevUpper c words st idx).symm
    prevBit := hcopy.prevBit.trans (refStep_prevBit c words st idx).symm
    firstBit := ?_
    trI0 := ?_
    sj0 := ?_
    trI1 := ?_
    sj1 := ?_
    prevLast := hcopy.prevLast.trans (refStep_prevLast c words st idx).symm
    prevConj := hcopy.prevConj.trans (refStep_prevConj c words st idx).symm
    prevDig := hcopy.prevDig.trans (refStep_prevDig c words st idx).symm }
  · rw [hout, frame (idx := idx) (r := rFirstBit)
      (l := historicalStateCopies c) (by rfl)]
    exact hmux.firstBit.trans (refStep_firstBit c words st idx).symm
  · rw [hout, frame (idx := idx) (r := rTrI0)
      (l := historicalStateCopies c) (by rfl)]
    exact hmux.trI0.trans (refStep_trI0 c words st idx).symm
  · rw [hout, frame (idx := idx) (r := rSj0)
      (l := historicalStateCopies c) (by rfl)]
    exact hmux.sj0.trans (refStep_sj0 c words st idx).symm
  · rw [hout, frame (idx := idx) (r := rTrI1)
      (l := historicalStateCopies c) (by rfl)]
    exact hmux.trI1.trans (refStep_trI1 c words st idx).symm
  · rw [hout, frame (idx := idx) (r := rSj1)
      (l := historicalStateCopies c) (by rfl)]
    exact hmux.sj1.trans (refStep_sj1 c words st idx).symm

end LeanCompCert.Ports.DirichletLadderExternalSafety
