import LeanCompCert.Ports.Prop1224CellMarkWindowBounds
import LeanCompCert.Ports.Prop1224CellAccBodySemantics

/-!
# Marking-window to accumulation-input refinement

This is the stable seam between the source sieve proof and the already
proved literal accumulation body.  The source side supplies ordinary-natural
factorization facts; representation plus the local cell invariant derives
all physical loads and machine-word bounds.  No finite table is evaluated.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-- Arithmetic meaning required of a completed logical marking cell.  The
Mathlib-facing factorization proof constructs this record from
`P1224MarkCell.markFactors`; it is not a trusted declaration. -/
structure P1224MarkedCellAccSource
    (x : P1224MarkCell) (n : Nat) where
  phi : Nat
  radical_dvd : x.radical ∣ n
  radical_le : x.radical ≤ n
  phi_pos : 0 < phi
  phi_le : phi ≤ n
  phi_eq_source : phi = x.phiSmall *
    (if x.radical = n then 1 else n / x.radical - 1)

/-- A represented, invariant logical cell with its ordinary-natural source
meaning is exactly an `AccCellInputCorrect` for the literal accumulation
theorem. -/
def P1224MarkWindow.Rep.toAccCellInputCorrect
    {c : CellCfg} {s : AState} {window : P1224MarkWindow}
    {w i : Nat} (hrep : window.Rep c s)
    (hinv : window.CellsInv) (hi : i < c.segLen)
    (hnM : w + i < M)
    (hsource : P1224MarkedCellAccSource (window.cells i) (w + i)) :
    AccCellInputCorrect c s w i := by
  let x := window.cells i
  have hwords := hrep.2 i hi
  have hx : x.Inv := hinv i
  have hradM : x.radical < M :=
    Nat.lt_of_le_of_lt hsource.radical_le hnM
  have hphiSmallM : x.phiSmall < M :=
    Nat.lt_of_le_of_lt (Nat.le_trans hx.phi_le_radical hsource.radical_le) hnM
  have hphiM : hsource.phi < M :=
    Nat.lt_of_le_of_lt hsource.phi_le hnM
  refine {
    radical := x.radical
    phiSmall := x.phiSmall
    sqf := x.sqf
    phi := hsource.phi
    prod_eq := ?_
    phi_eq := ?_
    sqf_eq := ?_
    radical_pos := hx.radical_pos
    radical_lt := hradM
    radical_dvd := hsource.radical_dvd
    radical_le := hsource.radical_le
    phiSmall_lt := hphiSmallM
    phi_pos := hsource.phi_pos
    phi_lt := hphiM
    phi_eq_source := hsource.phi_eq_source }
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.radical hwords
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.phiSmall hwords
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.sqf hwords

/-- Data-package form used by the finite accumulation telescope. -/
theorem P1224MarkWindow.Rep.toAccCellReady_planes
    {c : CellCfg} {s : AState} {window : P1224MarkWindow}
    (hrep : window.Rep c s) (i : Nat) (hi : i < c.segLen) :
    s.arr i = (window.cells i).radical ∧
      s.arr (i + c.segLen) = (window.cells i).phiSmall ∧
      s.arr (i + 2 * c.segLen) = (window.cells i).sqf := by
  have hwords := hrep.2 i hi
  constructor
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.radical hwords
  constructor
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.phiSmall hwords
  · simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.sqf hwords

#print axioms P1224MarkWindow.Rep.toAccCellInputCorrect
#print axioms P1224MarkWindow.Rep.toAccCellReady_planes

end LeanCompCert.Ports.Prop1224Cell
