import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveMux

/-! Small copy-field slices for the positive reference state. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalCopyCore (words : List Nat) (idx : Nat) (s : AState) : Prop where
  tag : s.regs 21 = words.getD (recW * idx) 0
  blk : s.regs 22 = words.getD (recW * idx + 1) 0
  upper : s.regs 25 = words.getD (recW * idx + 4) 0
  isLast : s.regs 28 = words.getD (recW * idx + 7) 0
  conj : s.regs 32 = words.getD (recW * idx + 11) 0
  digest : s.regs 158 = words.getD (recW * idx + 12) 0

structure HistoricalCopiedFields (words : List Nat) (idx : Nat) (s : AState) : Prop where
  prevTag : s.regs rPrevTag = words.getD (recW * idx) 0
  prevBlk : s.regs rPrevBlk = words.getD (recW * idx + 1) 0
  prevUpper : s.regs rPrevUpper = words.getD (recW * idx + 4) 0
  prevBit : s.regs rPrevBit = (words.getD (recW * idx + 5) 0 >>> 63) % 2
  prevLast : s.regs rPrevLast = words.getD (recW * idx + 7) 0
  prevConj : s.regs rPrevConj = words.getD (recW * idx + 11) 0
  prevDig : s.regs rPrevDig = words.getD (recW * idx + 12) 0

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

theorem historicalFlag9_copyCore
    (c : Cfg) (words : List Nat) (idx : Nat)
    (before loaded early derived s9 : AState)
    (hearly : early = arun idx loaded (historicalEarly c))
    (hderived : derived = arun idx early (historicalDerived c))
    (hs9 : s9 = arun idx derived (historicalFlag9 c))
    (hloaded : HistoricalLoaded c words idx before loaded) :
    HistoricalCopyCore words idx s9 := by
  have keep (r : Nat)
      (he : LeanCompCert.Verified.ArrayRegFrame.writes r (historicalEarly c) = false)
      (hd : LeanCompCert.Verified.ArrayRegFrame.writes r (historicalDerived c) = false)
      (h9 : LeanCompCert.Verified.ArrayRegFrame.writes r (historicalFlag9 c) = false) :
      s9.regs r = loaded.regs r := by
    rw [hs9, frame h9, hderived, frame hd, hearly, frame he]
  exact {
    tag := (keep 21 (by rfl) (by rfl) (by rfl)).trans hloaded.tag_eq
    blk := (keep 22 (by rfl) (by rfl) (by rfl)).trans hloaded.blk_eq
    upper := (keep 25 (by rfl) (by rfl) (by rfl)).trans hloaded.upper_eq
    isLast := (keep 28 (by rfl) (by rfl) (by rfl)).trans hloaded.isLast_eq
    conj := (keep 32 (by rfl) (by rfl) (by rfl)).trans hloaded.conjFirst_eq
    digest := (keep 158 (by rfl) (by rfl) (by rfl)).trans hloaded.digest_eq }

set_option maxHeartbeats 1000000 in
theorem historicalCopiedFields
    (c : Cfg) (words : List Nat) (idx : Nat)
    (s9 rest mux : AState) (st : RefState)
    (hrest : rest = arun idx s9 (historicalAfterFlag9 c))
    (hmux : mux = arun idx rest (historicalStateMux c))
    (hcopy : HistoricalCopyCore words idx s9)
    (hmuxCore : HistoricalMuxCore words idx st mux) :
    HistoricalCopiedFields words idx (arun idx mux (historicalStateCopies c)) := by
  have preserve (r : Nat)
      (ha : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalMainAfterFlag9 c) = false)
      (hb : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalBodyHeightCoverage c) = false)
      (hc : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalLateFlags c) = false)
      (hm : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalStateMux c) = false) : mux.regs r = s9.regs r := by
    rw [hmux, frame hm, hrest]
    simp only [historicalAfterFlag9, arun_append]
    rw [frame hc, frame hb, frame ha]
  have copies := historicalStateCopies_result c idx
    (words.getD (recW * idx) 0) (words.getD (recW * idx + 1) 0)
    (words.getD (recW * idx + 4) 0)
    ((words.getD (recW * idx + 5) 0 >>> 63) % 2)
    (words.getD (recW * idx + 7) 0)
    (words.getD (recW * idx + 11) 0)
    (words.getD (recW * idx + 12) 0) mux
    ((preserve 21 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.tag)
    ((preserve 22 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.blk)
    ((preserve 25 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.upper)
    hmuxCore.lastBit
    ((preserve 28 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.isLast)
    ((preserve 32 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.conj)
    ((preserve 158 (by rfl) (by rfl) (by rfl) (by rfl)).trans hcopy.digest)
  dsimp only at copies
  exact {
    prevTag := copies.1
    prevBlk := copies.2.1
    prevUpper := copies.2.2.1
    prevBit := copies.2.2.2.1
    prevLast := copies.2.2.2.2.1
    prevConj := copies.2.2.2.2.2.1
    prevDig := copies.2.2.2.2.2.2 }

end LeanCompCert.Ports.DirichletLadderExternalSafety
