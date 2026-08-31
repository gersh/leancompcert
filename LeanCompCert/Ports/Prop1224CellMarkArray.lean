import LeanCompCert.Ports.Prop1224CellMarkCell
import LeanCompCert.Ports.ArraySegMobiusSignal

/-!
# Whole-suffix array denotation of the Proposition 12.2.4 marker

Only the three-plane cell slice stores.  The cursor and budget suffix is
proved to frame the array, so the exact small cell theorem lifts to all
remaining production instructions without reducing them.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegMobiusSignal (avoidsStore arun_arr_frame)

def p1224MarkAdvanceBody (c : CellCfg) : List AInstr :=
  c.markBody.drop 44

def p1224MarkResidentBody (c : CellCfg) : List AInstr :=
  p1224MarkAddressBody c ++ p1224MarkCellBody ++ p1224MarkAdvanceBody c

def p1224MarkFullBody (c : CellCfg) : List AInstr :=
  p1224MarkPreludeBody c ++ p1224MarkResidentBody c

theorem p1224MarkFullBody_eq_markBody (c : CellCfg) :
    p1224MarkFullBody c = c.markBody := by
  rfl

theorem p1224MarkAdvanceBody_arr_frame (c : CellCfg) (k : Nat)
    (s : AState) :
    (arun k s (p1224MarkAdvanceBody c)).arr = s.arr := by
  apply arun_arr_frame
  rfl

/-- An active resident suffix performs exactly one logical three-plane mark;
the following 42 cursor/budget instructions do not touch the array. -/
theorem p1224MarkResidentBody_markPower_run
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
    (arun k s (p1224MarkResidentBody c)).arr =
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
  let marked := arun k addressed p1224MarkCellBody
  have htail := p1224MarkAdvanceBody_arr_frame c k marked
  simp only [p1224MarkResidentBody, arun_append]
  rw [htail, hcell]
  apply funext
  intro a
  simp only [writeP1224PlaneWordsAt, AState.writeArr]
  rw [harr0]

/-- An active cursor already past the window may update the three scratch
sinks but frames every live marking-plane address. -/
theorem p1224MarkResidentBody_past_live_frame
    (c : CellCfg) (k : Nat) (s : AState) (sinkCell : P1224MarkCell)
    (j p a : Nat) (first : Bool)
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
    (hsqfBit : sinkCell.sqf ≤ 1) (hsqf : sinkCell.sqf < M)
    (ha : a < 3 * c.segLen) :
    (arun k s (p1224MarkResidentBody c)).arr a = s.arr a := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have had := p1224MarkAddressBody_past_run c k s j hj hactive hjL haddr
  dsimp only at had
  rcases had with ⟨_h27, h30, h31, h32, harr0⟩
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
  let marked := arun k addressed p1224MarkCellBody
  have htail := p1224MarkAdvanceBody_arr_frame c k marked
  simp only [p1224MarkResidentBody, arun_append]
  rw [congrFun htail a, congrFun hcell a]
  have ha4 : a ≠ 4 * c.segLen := by omega
  have ha5 : a ≠ 5 * c.segLen := by omega
  have ha6 : a ≠ 6 * c.segLen := by omega
  simp only [writeP1224PlaneWordsAt, AState.writeArr]
  rw [show 4 * c.segLen + c.segLen = 5 * c.segLen by omega,
    show 4 * c.segLen + 2 * c.segLen = 6 * c.segLen by omega]
  simp [ha4, ha5, ha6, harr0]

#print axioms p1224MarkAdvanceBody_arr_frame
#print axioms p1224MarkResidentBody_markPower_run
#print axioms p1224MarkResidentBody_past_live_frame

end LeanCompCert.Ports.Prop1224Cell
