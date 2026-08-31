import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterZerosLate

/-! Small register-frame lemmas for the exact source prefix ending before digest. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalDigestInput (c : Cfg) (idx : Nat) (early : AState) : AState :=
  arun idx
    (arun idx
      (arun idx
        (arun idx
          (arun idx
            (arun idx
              (arun idx
                (arun idx early (historicalDerived c))
                (historicalMainFlags c))
              (historicalMiddleFlags c))
            (historicalFlag24 c))
          (historicalFlag25 c))
        (historicalFlag21 c))
      (historicalFlag22 c))
    (historicalFlag23 c)

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

theorem historicalMiddleFrame (c : Cfg) (idx r : Nat) (s : AState)
    (ha : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightPrefixA c) = false)
    (hb : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightPrefixB c) = false)
    (hf : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalHeightFlag c) = false)
    (hc : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalCoverageBlock c) = false)
    (ho : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalOvershootBlock c) = false) :
    (arun idx s (historicalMiddleFlags c)).regs r = s.regs r := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [frame ho, frame hc, frame hf, frame hb, frame ha]

set_option maxHeartbeats 1000000 in
theorem historicalDigestInput_prevDig (c : Cfg) (idx : Nat) (early : AState) :
    (historicalDigestInput c idx early).regs rPrevDig = early.regs rPrevDig := by
  unfold historicalDigestInput
  rw [frame (idx := idx) (r := rPrevDig) (l := historicalFlag23 c) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalFlag22 c) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalFlag21 c) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalFlag25 c) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalFlag24 c) (by rfl),
    historicalMiddleFrame c idx rPrevDig _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalMainFlags c) (by rfl),
    frame (idx := idx) (r := rPrevDig) (l := historicalDerived c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalDigestInput_bits (c : Cfg) (idx : Nat) (early : AState) :
    (historicalDigestInput c idx early).regs 26 = early.regs 26 := by
  unfold historicalDigestInput
  rw [frame (idx := idx) (r := 26) (l := historicalFlag23 c) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalFlag22 c) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalFlag21 c) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalFlag25 c) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalFlag24 c) (by rfl),
    historicalMiddleFrame c idx 26 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalMainFlags c) (by rfl),
    frame (idx := idx) (r := 26) (l := historicalDerived c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalDigestInput_digest (c : Cfg) (idx : Nat) (early : AState) :
    (historicalDigestInput c idx early).regs 158 = early.regs 158 := by
  unfold historicalDigestInput
  rw [frame (idx := idx) (r := 158) (l := historicalFlag23 c) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalFlag22 c) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalFlag21 c) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalFlag25 c) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalFlag24 c) (by rfl),
    historicalMiddleFrame c idx 158 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalMainFlags c) (by rfl),
    frame (idx := idx) (r := 158) (l := historicalDerived c) (by rfl)]

end LeanCompCert.Ports.DirichletLadderExternalSafety
