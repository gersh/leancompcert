import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceEarly

/-! Composition of the eight small historical framing checks. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

theorem historicalEarly_viol
    (c : Cfg) (words : List Nat) (idx : Nat)
    (before loaded : AState) (st : RefState)
    (hloaded : HistoricalLoaded c words idx before loaded)
    (hbefore : refStateOf before = st)
    (hword : ∀ j, loaded.regs j < M)
    (hprevLast : st.prevLast ≤ 1)
    (hprevBlk : st.prevBlk + 1 < M)
    (hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M)
    (hNoWrap : st.viol + 8 < M) :
    (arun idx loaded (historicalEarly c)).regs rViol =
      bumps (earlyConditions words st idx) st.viol := by
  let tag := words.getD (recW * idx) 0
  let blk := words.getD (recW * idx + 1) 0
  let lower := words.getD (recW * idx + 2) 0
  let slots := words.getD (recW * idx + 3) 0
  let upper := words.getD (recW * idx + 4) 0
  let stat := words.getD (recW * idx + 6) 0
  let isLast := words.getD (recW * idx + 7) 0
  let same : Bool := tag == st.prevTag
  let c1 : Bool := tag < st.prevTag
  let c2 : Bool := !same && st.prevLast != 1
  let c3 : Bool := same && st.prevLast == 1
  let c4 : Bool := blk != (if same then st.prevBlk + 1 else 0)
  let c5 : Bool := lower != (if same then st.prevUpper else 0)
  let c6 : Bool := upper != lower + slots
  let c7 : Bool := isLast > 1
  let c8 : Bool := stat > maxStat
  let v1 := bump c1 st.viol
  let v2 := bump c2 v1
  let v3 := bump c3 v2
  let v4 := bump c4 v3
  let v5 := bump c5 v4
  let v6 := bump c6 v5
  let v7 := bump c7 v6
  let v8 := bump c8 v7
  let s1 := arun idx loaded early1
  let s2 := arun idx s1 early2
  let s3 := arun idx s2 early3
  let s4 := arun idx s3 early4
  let s5 := arun idx s4 early5
  let s6 := arun idx s5 early6
  let s7 := arun idx s6 early7
  let s8 := arun idx s7 early8
  have href : refStateOf loaded = st := hloaded.ref_state.trans hbefore
  have hv0 : loaded.regs rViol = st.viol := congrArg RefState.viol href
  have htag0 : loaded.regs 21 = tag := by simpa [tag] using hloaded.tag_eq
  have hblk0 : loaded.regs 22 = blk := by simpa [blk] using hloaded.blk_eq
  have hlower0 : loaded.regs 23 = lower := by simpa [lower] using hloaded.lower_eq
  have hslots0 : loaded.regs 24 = slots := by simpa [slots] using hloaded.slots_eq
  have hupper0 : loaded.regs 25 = upper := by simpa [upper] using hloaded.upper_eq
  have hstat0 : loaded.regs 27 = stat := by simpa [stat] using hloaded.stat_eq
  have hlast0 : loaded.regs 28 = isLast := by simpa [isLast] using hloaded.isLast_eq
  have hpt0 : loaded.regs rPrevTag = st.prevTag := congrArg RefState.prevTag href
  have hpb0 : loaded.regs rPrevBlk = st.prevBlk := congrArg RefState.prevBlk href
  have hpu0 : loaded.regs rPrevUpper = st.prevUpper :=
    congrArg RefState.prevUpper href
  have hpl0 : loaded.regs rPrevLast = st.prevLast :=
    congrArg RefState.prevLast href
  have hv1le : v1 ≤ st.viol + 1 := by
    simpa [v1] using bump_le_succ c1 st.viol
  have hv2le : v2 ≤ st.viol + 2 := by
    exact Nat.le_trans (by simpa [v2] using bump_le_succ c2 v1) (by omega)
  have hv3le : v3 ≤ st.viol + 3 := by
    exact Nat.le_trans (by simpa [v3] using bump_le_succ c3 v2) (by omega)
  have hv4le : v4 ≤ st.viol + 4 := by
    exact Nat.le_trans (by simpa [v4] using bump_le_succ c4 v3) (by omega)
  have hv5le : v5 ≤ st.viol + 5 := by
    exact Nat.le_trans (by simpa [v5] using bump_le_succ c5 v4) (by omega)
  have hv6le : v6 ≤ st.viol + 6 := by
    exact Nat.le_trans (by simpa [v6] using bump_le_succ c6 v5) (by omega)
  have hv7le : v7 ≤ st.viol + 7 := by
    exact Nat.le_trans (by simpa [v7] using bump_le_succ c7 v6) (by omega)
  have h1 := early1_result idx st.viol tag st.prevTag loaded hv0 htag0 hpt0
    (by omega)
  have hv1 : s1.regs rViol = v1 := by simpa [s1, v1, c1] using h1.1
  have hs1 : s1.regs 33 = if same then 1 else 0 := by
    simpa [s1, same] using h1.2.1
  have hn1 : s1.regs 34 = if same then 0 else 1 := by
    simpa [s1, same] using h1.2.2
  have hpl1 : s1.regs rPrevLast = st.prevLast := by
    rw [frame (idx := idx) (s := loaded) (l := early1) (r := rPrevLast) (by rfl)]
    exact hpl0
  have h2 := early2_result idx v1 st.prevLast same s1 hv1 hn1 hpl1 hprevLast
    (by omega)
  have hv2 : s2.regs rViol = v2 := by simpa [s2, v2, c2] using h2
  have hs2 : s2.regs 33 = if same then 1 else 0 := by
    rw [frame (idx := idx) (s := s1) (l := early2) (r := 33) (by rfl)]
    exact hs1
  have hpl2 : s2.regs rPrevLast = st.prevLast := by
    rw [frame (idx := idx) (s := s1) (l := early2) (r := rPrevLast) (by rfl)]
    exact hpl1
  have h3 := early3_result idx v2 st.prevLast same s2 hv2 hs2 hpl2 hprevLast
    (by omega)
  have hv3 : s3.regs rViol = v3 := by simpa [s3, v3, c3] using h3
  have hs3 : s3.regs 33 = if same then 1 else 0 := by
    rw [frame (idx := idx) (s := s2) (l := early3) (r := 33) (by rfl)]
    exact hs2
  have hpb3 : s3.regs rPrevBlk = st.prevBlk := by
    rw [frame (idx := idx) (s := s2) (l := early3) (r := rPrevBlk) (by rfl),
      frame (idx := idx) (s := s1) (l := early2) (r := rPrevBlk) (by rfl),
      frame (idx := idx) (s := loaded) (l := early1) (r := rPrevBlk) (by rfl)]
    exact hpb0
  have hblk3 : s3.regs 22 = blk := by
    rw [frame (idx := idx) (s := s2) (l := early3) (r := 22) (by rfl),
      frame (idx := idx) (s := s1) (l := early2) (r := 22) (by rfl),
      frame (idx := idx) (s := loaded) (l := early1) (r := 22) (by rfl)]
    exact hblk0
  have h4 := early4_result idx v3 st.prevBlk blk same s3 hv3 hs3 hpb3 hblk3
    hprevBlk (by omega)
  have hv4 : s4.regs rViol = v4 := by simpa [s4, v4, c4] using h4
  have hs4 : s4.regs 33 = if same then 1 else 0 := by
    rw [frame (idx := idx) (s := s3) (l := early4) (r := 33) (by rfl)]
    exact hs3
  have hpu4 : s4.regs rPrevUpper = st.prevUpper := by
    rw [frame (idx := idx) (s := s3) (l := early4) (r := rPrevUpper) (by rfl),
      frame (idx := idx) (s := s2) (l := early3) (r := rPrevUpper) (by rfl),
      frame (idx := idx) (s := s1) (l := early2) (r := rPrevUpper) (by rfl),
      frame (idx := idx) (s := loaded) (l := early1) (r := rPrevUpper) (by rfl)]
    exact hpu0
  have hlower4 : s4.regs 23 = lower := by
    rw [frame (idx := idx) (s := s3) (l := early4) (r := 23) (by rfl),
      frame (idx := idx) (s := s2) (l := early3) (r := 23) (by rfl),
      frame (idx := idx) (s := s1) (l := early2) (r := 23) (by rfl),
      frame (idx := idx) (s := loaded) (l := early1) (r := 23) (by rfl)]
    exact hlower0
  have h5 := early5_result idx v4 st.prevUpper lower same s4 hv4 hs4 hpu4
    hlower4 (by simpa [← hpu0] using hword rPrevUpper) (by omega)
  have hv5 : s5.regs rViol = v5 := by simpa [s5, v5, c5] using h5
  have low5 (r : Nat) (hr : 1 ≤ r) (hr' : r ≤ 32) : s5.regs r = loaded.regs r := by
    simp only [s5, s4, s3, s2, s1]
    rw [frame (idx := idx) (l := early5) (r := r) (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, early5,
        LeanCompCert.Verified.InstrBlock.sdest, rViol]; omega)]
    rw [frame (idx := idx) (l := early4) (r := r) (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, early4,
        LeanCompCert.Verified.InstrBlock.sdest, rViol]; omega)]
    rw [frame (idx := idx) (l := early3) (r := r) (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, early3,
        LeanCompCert.Verified.InstrBlock.sdest, rViol]; omega)]
    rw [frame (idx := idx) (l := early2) (r := r) (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, early2,
        LeanCompCert.Verified.InstrBlock.sdest, rViol]; omega)]
    exact frame (idx := idx) (s := loaded) (l := early1) (r := r) (by
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, early1,
        LeanCompCert.Verified.InstrBlock.sdest, rViol]; omega)
  have h6 := early6_result idx v5 lower slots upper s5 hv5
    (by simpa using low5 23 (by omega) (by omega) |>.trans hlower0)
    (by simpa using low5 24 (by omega) (by omega) |>.trans hslots0)
    (by simpa using low5 25 (by omega) (by omega) |>.trans hupper0)
    (by simpa [lower, slots] using hslot) (by omega)
  have hv6 : s6.regs rViol = v6 := by simpa [s6, v6, c6] using h6
  have hlast6 : s6.regs 28 = isLast := by
    rw [frame (idx := idx) (s := s5) (l := early6) (r := 28) (by rfl)]
    exact (low5 28 (by omega) (by omega)).trans hlast0
  have h7 := early7_result idx v6 isLast s6 hv6 hlast6 (by omega)
  have hv7 : s7.regs rViol = v7 := by simpa [s7, v7, c7] using h7
  have hlast7 : s7.regs 28 = isLast := by
    rw [frame (idx := idx) (s := s6) (l := early7) (r := 28) (by rfl)]
    exact hlast6
  have hstat7 : s7.regs 27 = stat := by
    rw [frame (idx := idx) (s := s6) (l := early7) (r := 27) (by rfl),
      frame (idx := idx) (s := s5) (l := early6) (r := 27) (by rfl)]
    exact (low5 27 (by omega) (by omega)).trans hstat0
  have h8 := early8_result idx v7 isLast stat s7 hv7 hlast7 hstat7 (by omega)
  have hv8 : s8.regs rViol = v8 := by simpa [s8, v8, c8] using h8.1
  rw [historicalEarly_eq_parts, arun_append, arun_append, arun_append,
    arun_append, arun_append, arun_append, arun_append]
  change s8.regs rViol = _
  rw [hv8]
  rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety
