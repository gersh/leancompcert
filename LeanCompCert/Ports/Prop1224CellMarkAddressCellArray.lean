import LeanCompCert.Ports.Prop1224CellMarkArray
import LeanCompCert.Ports.Prop1224CellMarkCursorLiteral

/-!
# Exact array result of the Proposition 12.2.4 address-and-cell prefix

These lemmas stop immediately before the cursor/table-load suffix.  They are
therefore the small denotational seam needed to prove that the later literal
load observes the abstract resident prime table.  No table or marking
schedule is evaluated here.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- In the resident branch the literal address-and-cell prefix performs the
one logical three-plane prime-power update. -/
theorem p1224MarkAddressCellBody_markPower_run
    (c : CellCfg) (k : Nat) (s : AState) (x : P1224MarkCell)
    (j p : Nat) (first : Bool)
    (hL : 0 < c.segLen) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : j < c.segLen)
    (haddr : j + 2 * c.segLen < M)
    (hloaded : p1224PlaneWordsAt s c.segLen j = x.encode)
    (hp : s.regs rBp = p)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp2 : 2 ≤ p) (hpM : p < M)
    (hrad : x.radical * (if first then p else 1) < M)
    (hphi : x.phiSmall * (if first then p - 1 else 1) < M)
    (hsqfBit : x.sqf ≤ 1) (hsqf : x.sqf < M) :
    (arun k s (p1224MarkAddressCellBody c)).arr =
      (writeP1224PlaneWordsAt s c.segLen j
        ((x.markPower p first).encode)).arr := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have ha := p1224MarkAddressBody_resident_run c k s j hj hactive hjL haddr
  dsimp only at ha
  rcases ha with ⟨_h27, h30, h31, h32, harr0⟩
  change addressed.arr = s.arr at harr0
  have hbp : addressed.regs rBp = s.regs rBp :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rBp
      (p1224MarkAddressBody c) (by rfl) s
  have hfs : addressed.regs rFs = s.regs rFs :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rFs
      (p1224MarkAddressBody c) (by rfl) s
  have hcell := p1224MarkCellBody_markPower_run k addressed x c.segLen j p
    first hL h30 h31 h32
    (by unfold p1224PlaneWordsAt; rw [harr0]; exact hloaded)
    (hbp.trans hp) (hfs.trans hfirst) hp2 hpM
    hrad hphi hsqfBit hsqf
  dsimp only at hcell
  simp only [p1224MarkAddressCellBody, arun_append]
  rw [hcell]
  apply funext
  intro a
  simp only [writeP1224PlaneWordsAt, AState.writeArr]
  rw [harr0]

/-- In the past-window branch the same prefix writes exactly the designated
three scratch sinks.  This exact equality, stronger than a live-plane frame,
allows the following table load to be related to `P1224MarkTableRep`. -/
theorem p1224MarkAddressCellBody_past_run
    (c : CellCfg) (k : Nat) (s : AState) (sinkCell : P1224MarkCell)
    (j p : Nat) (first : Bool)
    (hL : 0 < c.segLen) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : c.segLen ≤ j)
    (haddr : 6 * c.segLen < M)
    (hloaded : p1224PlaneWordsAt s c.segLen (4 * c.segLen) =
      sinkCell.encode)
    (hp : s.regs rBp = p)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp2 : 2 ≤ p) (hpM : p < M)
    (hrad : sinkCell.radical * (if first then p else 1) < M)
    (hphi : sinkCell.phiSmall * (if first then p - 1 else 1) < M)
    (hsqfBit : sinkCell.sqf ≤ 1) (hsqf : sinkCell.sqf < M) :
    (arun k s (p1224MarkAddressCellBody c)).arr =
      (writeP1224PlaneWordsAt s c.segLen (4 * c.segLen)
        ((sinkCell.markPower p first).encode)).arr := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have ha := p1224MarkAddressBody_past_run c k s j hj hactive hjL haddr
  dsimp only at ha
  rcases ha with ⟨_h27, h30, h31, h32, harr0⟩
  change addressed.arr = s.arr at harr0
  have hbp : addressed.regs rBp = s.regs rBp :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rBp
      (p1224MarkAddressBody c) (by rfl) s
  have hfs : addressed.regs rFs = s.regs rFs :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rFs
      (p1224MarkAddressBody c) (by rfl) s
  have hcell := p1224MarkCellBody_markPower_run k addressed sinkCell
    c.segLen (4 * c.segLen) p first hL h30
    (by simpa [show 4 * c.segLen + c.segLen = 5 * c.segLen by omega]
      using h31)
    (by simpa [show 4 * c.segLen + 2 * c.segLen = 6 * c.segLen by omega]
      using h32)
    (by unfold p1224PlaneWordsAt; rw [harr0]; exact hloaded)
    (hbp.trans hp) (hfs.trans hfirst) hp2 hpM
    hrad hphi hsqfBit hsqf
  dsimp only at hcell
  simp only [p1224MarkAddressCellBody, arun_append]
  rw [hcell]
  apply funext
  intro a
  simp only [writeP1224PlaneWordsAt, AState.writeArr]
  rw [harr0]

#print axioms p1224MarkAddressCellBody_markPower_run
#print axioms p1224MarkAddressCellBody_past_run

end LeanCompCert.Ports.Prop1224Cell
