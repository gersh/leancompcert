import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveState
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyCuts
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneLateCompose

/-! Low-memory preservation and state-mux slice after flag 9. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalMainAfterFlag9 (c : Cfg) : List AInstr :=
  historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c ++
  historicalFlag13 c ++ historicalFlag14 c ++ historicalFlag15 c ++
  historicalParity c

def historicalAfterFlag9 (c : Cfg) : List AInstr :=
  historicalMainAfterFlag9 c ++ historicalBodyHeightCoverage c ++
    historicalLateFlags c

structure HistoricalMuxCore (words : List Nat) (idx : Nat)
    (st : RefState) (s : AState) : Prop where
  lastBit : s.regs 97 = (words.getD (recW * idx + 5) 0 >>> 63) % 2
  trI0 : s.regs rTrI0 =
    if words.getD (recW * idx) 0 == st.prevTag then st.trI1 else 0
  sj0 : s.regs rSj0 =
    if words.getD (recW * idx) 0 == st.prevTag then st.sj1 else 0
  trI1 : s.regs rTrI1 =
    bitCount (transWord (words.getD (recW * idx + 5) 0))
  sj1 : s.regs rSj1 =
    bitMoment (transWord (words.getD (recW * idx + 5) 0))
  firstBit : s.regs rFirstBit =
    if words.getD (recW * idx) 0 == st.prevTag then st.firstBit
    else words.getD (recW * idx + 5) 0 % 2

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxHeartbeats 1000000 in
theorem historicalMux_core
    (c : Cfg) (words : List Nat) (idx : Nat) (s9 rest : AState)
    (st : RefState)
    (hrest : rest = arun idx s9 (historicalAfterFlag9 c))
    (hcore : HistoricalFlag9Core words idx st s9)
    (htrI1w : st.trI1 < M) (hsj1w : st.sj1 < M)
    (hfirstw : st.firstBit < M) :
    HistoricalMuxCore words idx st (arun idx rest (historicalStateMux c)) := by
  have preserve (r : Nat)
      (ha : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalMainAfterFlag9 c) = false)
      (hb : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalBodyHeightCoverage c) = false)
      (hc : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalLateFlags c) = false) : rest.regs r = s9.regs r := by
    rw [hrest]
    simp only [historicalAfterFlag9, arun_append]
    rw [frame hc, frame hb, frame ha]
  have same : rest.regs 33 =
      if words.getD (recW * idx) 0 == st.prevTag then 1 else 0 :=
    (preserve 33 (by rfl) (by rfl) (by rfl)).trans hcore.same
  have fresh : rest.regs 34 =
      if !(words.getD (recW * idx) 0 == st.prevTag) then 1 else 0 :=
    (preserve 34 (by rfl) (by rfl) (by rfl)).trans hcore.fresh
  have trI := (preserve 77 (by rfl) (by rfl) (by rfl)).trans hcore.trI
  have sj := (preserve 95 (by rfl) (by rfl) (by rfl)).trans hcore.sj
  have fb := (preserve 96 (by rfl) (by rfl) (by rfl)).trans hcore.fb
  have oldTrI1 := (preserve rTrI1 (by rfl) (by rfl) (by rfl)).trans
    hcore.oldTrI1
  have oldSj1 := (preserve rSj1 (by rfl) (by rfl) (by rfl)).trans
    hcore.oldSj1
  have oldFirst := (preserve rFirstBit (by rfl) (by rfl) (by rfl)).trans
    hcore.oldFirst
  have trIw : bitCount (transWord (words.getD (recW * idx + 5) 0)) < M := by
    have h := bitCount_transWord_le (words.getD (recW * idx + 5) 0)
    simp only [M]
    omega
  have sjw : bitMoment (transWord (words.getD (recW * idx + 5) 0)) < M := by
    have h := bitMoment_transWord_le (words.getD (recW * idx + 5) 0)
    simp only [M]
    omega
  have fbw : words.getD (recW * idx + 5) 0 % 2 < M := by
    exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2)) (by simp [M])
  have hm := historicalStateMux_result c idx st.trI1 st.sj1
    (bitCount (transWord (words.getD (recW * idx + 5) 0)))
    (bitMoment (transWord (words.getD (recW * idx + 5) 0))) st.firstBit
    (words.getD (recW * idx + 5) 0 % 2)
    (words.getD (recW * idx) 0 == st.prevTag) rest same fresh
    oldTrI1 oldSj1 trI sj oldFirst fb htrI1w hsj1w trIw sjw hfirstw fbw
  dsimp only at hm
  refine {
    lastBit := by
      rw [frame (idx := idx) (r := 97) (l := historicalStateMux c) (by rfl),
        preserve 97 (by rfl) (by rfl) (by rfl)]
      exact hcore.lb
    trI0 := hm.1
    sj0 := hm.2.1
    trI1 := hm.2.2.1
    sj1 := hm.2.2.2.1
    firstBit := hm.2.2.2.2 }

end LeanCompCert.Ports.DirichletLadderExternalSafety
