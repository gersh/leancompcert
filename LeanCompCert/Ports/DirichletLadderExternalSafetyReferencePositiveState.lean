import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceDerived
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag9
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceEarlyGates

/-! Low-memory positive-state slice through historical flag 9. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalFlag9Core (words : List Nat) (idx : Nat)
    (st : RefState) (s : AState) : Prop where
  tag : s.regs 21 = words.getD (recW * idx) 0
  blk : s.regs 22 = words.getD (recW * idx + 1) 0
  upper : s.regs 25 = words.getD (recW * idx + 4) 0
  uElem : s.regs 29 = words.getD (recW * idx + 8) 0
  henc : s.regs 30 = words.getD (recW * idx + 9) 0
  tqNum : s.regs 31 = words.getD (recW * idx + 10) 0
  cj : s.regs 32 = words.getD (recW * idx + 11) 0
  digest : s.regs 158 = words.getD (recW * idx + 12) 0
  same : s.regs 33 =
    if words.getD (recW * idx) 0 == st.prevTag then 1 else 0
  fresh : s.regs 34 =
    if !(words.getD (recW * idx) 0 == st.prevTag) then 1 else 0
  isLastGate : s.regs 48 =
    if words.getD (recW * idx + 7) 0 == 1 then 1 else 0
  trI : s.regs 77 = bitCount (transWord (words.getD (recW * idx + 5) 0))
  sj : s.regs 95 = bitMoment (transWord (words.getD (recW * idx + 5) 0))
  fb : s.regs 96 = words.getD (recW * idx + 5) 0 % 2
  lb : s.regs 97 = (words.getD (recW * idx + 5) 0 >>> 63) % 2
  cross : s.regs 98 =
    if (words.getD (recW * idx) 0 == st.prevTag) &&
      st.prevBit != words.getD (recW * idx + 5) 0 % 2 then 1 else 0
  oldTrI0 : s.regs rTrI0 = st.trI0
  oldSj0 : s.regs rSj0 = st.sj0
  oldTrI1 : s.regs rTrI1 = st.trI1
  oldSj1 : s.regs rSj1 = st.sj1
  oldFirst : s.regs rFirstBit = st.firstBit
  oldConj : s.regs rPrevConj = st.prevConj
  oldDigest : s.regs rPrevDig = st.prevDig

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxHeartbeats 1000000 in
theorem historicalFlag9_core
    (c : Cfg) (words : List Nat) (idx : Nat)
    (before loaded early derived : AState) (st : RefState)
    (hearlyState : early = arun idx loaded (historicalEarly c))
    (hderivedState : derived = arun idx early (historicalDerived c))
    (hloaded : HistoricalLoaded c words idx before loaded)
    (hstate : refStateOf before = st)
    (harrayEarly : HistoricalArrayMatches c words early)
    (hstatic : StaticBounds c)
    (hbitsWord : words.getD (recW * idx + 5) 0 < M)
    (hprevBit : st.prevBit ≤ 1)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hcounter : derived.regs rViol + 1 < M) :
    HistoricalFlag9Core words idx st
      (arun idx derived (historicalFlag9 c)) := by
  have prevTag_loaded : loaded.regs rPrevTag = st.prevTag := by
    have h := congrArg RefState.prevTag (hloaded.ref_state.trans hstate)
    simpa [refStateOf] using h
  have gates := historicalEarly_gate_values c idx
    (words.getD (recW * idx) 0) st.prevTag
    (words.getD (recW * idx + 7) 0) loaded hloaded.tag_eq prevTag_loaded
    hloaded.isLast_eq
  rw [← hearlyState] at gates
  dsimp only at gates
  have hbitsEarly : early.regs 26 = words.getD (recW * idx + 5) 0 := by
    rw [hearlyState, frame (idx := idx) (r := 26) (l := historicalEarly c)
      (by rfl)]
    exact hloaded.bits_eq
  have d := historicalDerived_result c words idx
    (words.getD (recW * idx + 5) 0) early hbitsEarly hbitsWord
    harrayEarly hstatic
  rw [← hderivedState] at d
  dsimp only at d
  have regDerived (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalDerived c) = false) : derived.regs r = early.regs r := by
    rw [hderivedState]
    exact frame h
  have prevBitDerived : derived.regs rPrevBit = st.prevBit := by
    rw [regDerived rPrevBit (by rfl), hearlyState,
      frame (idx := idx) (r := rPrevBit) (l := historicalEarly c) (by rfl)]
    have h := congrArg RefState.prevBit (hloaded.ref_state.trans hstate)
    simpa [refStateOf] using h
  have f := historicalFlag9_result c idx (derived.regs rViol)
    (words.getD (recW * idx + 5) 0) (words.getD (recW * idx + 3) 0)
    (words.getD (recW * idx + 6) 0) st.prevBit
    (words.getD (recW * idx) 0 == st.prevTag) derived rfl
    (regDerived 26 (by rfl) |>.trans hbitsEarly)
    (by
      rw [regDerived 24 (by rfl), hearlyState,
        frame (idx := idx) (r := 24) (l := historicalEarly c) (by rfl)]
      exact hloaded.slots_eq)
    (by
      rw [regDerived 27 (by rfl), hearlyState,
        frame (idx := idx) (r := 27) (l := historicalEarly c) (by rfl)]
      exact hloaded.stat_eq)
    (regDerived 33 (by rfl) |>.trans gates.1)
    prevBitDerived d.1.trI hbitsWord hprevBit hstat hcounter
  dsimp only at f
  refine {
    tag := by
      rw [frame (idx := idx) (r := 21) (l := historicalFlag9 c) (by rfl),
        regDerived 21 (by rfl), hearlyState,
        frame (idx := idx) (r := 21) (l := historicalEarly c) (by rfl)]
      exact hloaded.tag_eq
    blk := by
      rw [frame (idx := idx) (r := 22) (l := historicalFlag9 c) (by rfl),
        regDerived 22 (by rfl), hearlyState,
        frame (idx := idx) (r := 22) (l := historicalEarly c) (by rfl)]
      exact hloaded.blk_eq
    upper := by
      rw [frame (idx := idx) (r := 25) (l := historicalFlag9 c) (by rfl),
        regDerived 25 (by rfl), hearlyState,
        frame (idx := idx) (r := 25) (l := historicalEarly c) (by rfl)]
      exact hloaded.upper_eq
    uElem := by
      rw [frame (idx := idx) (r := 29) (l := historicalFlag9 c) (by rfl),
        regDerived 29 (by rfl), hearlyState,
        frame (idx := idx) (r := 29) (l := historicalEarly c) (by rfl)]
      exact hloaded.uElem_eq
    henc := by
      rw [frame (idx := idx) (r := 30) (l := historicalFlag9 c) (by rfl),
        regDerived 30 (by rfl), hearlyState,
        frame (idx := idx) (r := 30) (l := historicalEarly c) (by rfl)]
      exact hloaded.henc_eq
    tqNum := by
      rw [frame (idx := idx) (r := 31) (l := historicalFlag9 c) (by rfl),
        regDerived 31 (by rfl), hearlyState,
        frame (idx := idx) (r := 31) (l := historicalEarly c) (by rfl)]
      exact hloaded.tqNum_eq
    cj := by
      rw [frame (idx := idx) (r := 32) (l := historicalFlag9 c) (by rfl),
        regDerived 32 (by rfl), hearlyState,
        frame (idx := idx) (r := 32) (l := historicalEarly c) (by rfl)]
      exact hloaded.conjFirst_eq
    digest := by
      rw [frame (idx := idx) (r := 158) (l := historicalFlag9 c) (by rfl),
        regDerived 158 (by rfl), hearlyState,
        frame (idx := idx) (r := 158) (l := historicalEarly c) (by rfl)]
      exact hloaded.digest_eq
    same := by rw [frame (idx := idx) (r := 33) (l := historicalFlag9 c)
      (by rfl), regDerived 33 (by rfl)]; exact gates.1
    fresh := by rw [frame (idx := idx) (r := 34) (l := historicalFlag9 c)
      (by rfl), regDerived 34 (by rfl)]; exact gates.2.1
    isLastGate := by
      rw [frame (idx := idx) (r := 48) (l := historicalFlag9 c) (by rfl),
        regDerived 48 (by rfl)]
      exact gates.2.2
    trI := by rw [frame (idx := idx) (r := 77) (l := historicalFlag9 c)
      (by rfl)]; exact d.1.trI
    sj := by rw [frame (idx := idx) (r := 95) (l := historicalFlag9 c)
      (by rfl)]; exact d.1.sj
    fb := f.2.1
    lb := f.2.2.1
    cross := f.2.2.2.1
    oldTrI0 := by
      rw [frame (idx := idx) (r := rTrI0) (l := historicalFlag9 c) (by rfl),
        regDerived rTrI0 (by rfl), hearlyState,
        frame (idx := idx) (r := rTrI0) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.trI0 (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldSj0 := by
      rw [frame (idx := idx) (r := rSj0) (l := historicalFlag9 c) (by rfl),
        regDerived rSj0 (by rfl), hearlyState,
        frame (idx := idx) (r := rSj0) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.sj0 (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldTrI1 := by
      rw [frame (idx := idx) (r := rTrI1) (l := historicalFlag9 c) (by rfl),
        regDerived rTrI1 (by rfl), hearlyState,
        frame (idx := idx) (r := rTrI1) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.trI1 (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldSj1 := by
      rw [frame (idx := idx) (r := rSj1) (l := historicalFlag9 c) (by rfl),
        regDerived rSj1 (by rfl), hearlyState,
        frame (idx := idx) (r := rSj1) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.sj1 (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldFirst := by
      rw [frame (idx := idx) (r := rFirstBit) (l := historicalFlag9 c) (by rfl),
        regDerived rFirstBit (by rfl), hearlyState,
        frame (idx := idx) (r := rFirstBit) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.firstBit (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldConj := by
      rw [frame (idx := idx) (r := rPrevConj) (l := historicalFlag9 c) (by rfl),
        regDerived rPrevConj (by rfl), hearlyState,
        frame (idx := idx) (r := rPrevConj) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.prevConj (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h
    oldDigest := by
      rw [frame (idx := idx) (r := rPrevDig) (l := historicalFlag9 c) (by rfl),
        regDerived rPrevDig (by rfl), hearlyState,
        frame (idx := idx) (r := rPrevDig) (l := historicalEarly c) (by rfl)]
      have h := congrArg RefState.prevDig (hloaded.ref_state.trans hstate)
      simpa [refStateOf] using h }

end LeanCompCert.Ports.DirichletLadderExternalSafety
