import LeanCompCert.Ports.DirichletLadderExternalSafetySticky
import LeanCompCert.Verified.ArrayRegFrame

/-! One-record backward step for the sticky external ladder audit. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame (idx r : Nat) (l : List AInstr) (s : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

private theorem loadBlock_arr (idx : Nat) (s : AState) :
    (arun idx s loadBlock).arr = s.arr := by
  simp [loadBlock, bo, arun, astep, AState.writeReg]

set_option maxRecDepth 6000
set_option maxHeartbeats 600000

theorem guardBody_zero_back
    (c : Cfg) (arr : Nat → Nat) (idx : Nat) (s : AState)
    (hsArr : s.arr = arr)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hstatic : StaticBounds c) (hidx : idx < c.records)
    (hout : BadZero (arun idx s (guardBody c))) :
    BadZero s ∧ RecordSafe c arr idx := by
  have hrecords : c.records < M := by
    have h : 13 * c.records + 256 < M := by
      simpa [Cfg.arrayLen, recW] using hstatic.array_word
    omega
  let sL := arun idx s loadBlock
  let sA := arun idx sL checkA
  let sB := arun idx sA checkB
  have hwL := arun_word idx loadBlock s hword harr
  have hwA := arun_word idx checkA sL hwL.1 hwL.2
  have hwB := arun_word idx checkB sA hwA.1 hwA.2
  have houtC : BadZero (arun idx sB (checkC c)) := by
    simpa [guardBody, checkBlock, sL, sA, sB, arun_append] using hout
  have hC := checkC_zero_back c idx sB hrecords hwB.1 hwB.2 houtC.2.2
  have hBbad : sB.regs rBad = 0 := by
    rw [← frame idx rBad (checkC c) sB (by rfl)]
    exact houtC.1
  have hBbadB : sB.regs rBadB = 0 := by
    rw [← frame idx rBadB (checkC c) sB (by rfl)]
    exact houtC.2.1
  have hB := checkB_zero_back idx sA (hwA.1 21) hwA.1 hwA.2 hBbadB
  have hAbad : sA.regs rBad = 0 := by
    rw [← frame idx rBad checkB sA (by decide)]
    exact hBbad
  have hAbadC : sA.regs rBadC = 0 := by
    rw [← frame idx rBadC checkB sA (by decide)]
    exact hC.1
  have hA := checkA_zero_back idx sL hwL.1 hwL.2 hAbad
  have hLbadB : sL.regs rBadB = 0 := by
    rw [← frame idx rBadB checkA sL (by decide)]
    exact hB.1
  have hLbadC : sL.regs rBadC = 0 := by
    rw [← frame idx rBadC checkA sL (by decide)]
    exact hAbadC
  have hsBad : s.regs rBad = 0 := by
    rw [← frame idx rBad loadBlock s (by decide)]
    exact hA.1
  have hsBadB : s.regs rBadB = 0 := by
    rw [← frame idx rBadB loadBlock s (by decide)]
    exact hLbadB
  have hsBadC : s.regs rBadC = 0 := by
    rw [← frame idx rBadC loadBlock s (by decide)]
    exact hLbadC
  have hloaded : Loaded arr idx sL := loadBlock_loaded c arr idx s hsArr
    hsBad hsBadB hsBadC hstatic hidx
  have hBSafeL : BSafe sL := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← frame idx 25 checkA sL (by decide)]; exact hB.2.1
    · rw [← frame idx 30 checkA sL (by decide)]; exact hB.2.2.1
    · rw [← frame idx 21 checkA sL (by decide)]; exact hB.2.2.2.1
    · rw [← frame idx 21 checkA sL (by decide)]; exact hB.2.2.2.2
  have hCSafeL : CSafe c sL := by
    constructor
    · rw [← frame idx 22 checkA sL (by decide),
        ← frame idx 22 checkB sA (by decide)]
      exact hC.2.1
    · rw [← frame idx 32 checkA sL (by decide),
        ← frame idx 32 checkB sA (by decide)]
      exact hC.2.2
  refine ⟨⟨hsBad, hsBadB, hsBadC⟩, ?_⟩
  simp only [RecordSafe]
  rw [← hloaded.tag_eq, ← hloaded.blk_eq, ← hloaded.lower_eq,
    ← hloaded.slots_eq, ← hloaded.upper_eq, ← hloaded.isLast_eq,
    ← hloaded.henc_eq, ← hloaded.conjFirst_eq]
  exact ⟨hA.2.1, hA.2.2.1, hA.2.2.2, hBSafeL.1,
    hBSafeL.2.1, hBSafeL.2.2.1, hBSafeL.2.2.2,
    hCSafeL.1, hCSafeL.2⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety
