import LeanCompCert.Ports.Section413Sweep
import LeanCompCert.Ports.Section413WindowSchedule
import LeanCompCert.Verified.SqrtEquiv

/-!
# Fixed-slot divisor pairing equals the reference square-root fold

The production scanner reserves 316 divisor slots for every row.  Slots
beyond `⌊√n⌋` are branchlessly gated to zero.  This file proves once,
symbolically, that such a fixed-slot fold is exactly the reference
`kDivSum`; it never instantiates or evaluates the 99,999 production rows.
-/

namespace LeanCompCert.Ports.Section413WindowPairingBridge

open LeanCompCert.Ports.Section413Sweep

/-- One fixed scanner slot, expressed at the reference `Cell` level. -/
def slotStep (v n : Nat) (f : Nat → Cell) (c : Cell) (i : Nat) : Cell :=
  let s := i + 1
  if s * s ≤ n ∧ n % s = 0 then
    let c1 := if Nat.gcd s v = 1 then cadd c (f s) else c
    if n / s ≠ s then
      if Nat.gcd (n / s) v = 1 then cadd c1 (f (n / s)) else c1
    else c1
  else c

def slotDivSum (slotCount v n : Nat) (f : Nat → Cell) : Cell :=
  (List.range slotCount).foldl (slotStep v n f) czero

private def referenceStep (v n : Nat) (f : Nat → Cell)
    (c : Cell) (i : Nat) : Cell :=
  let s := i + 1
  if n % s = 0 then
    let c1 := if Nat.gcd s v = 1 then cadd c (f s) else c
    if n / s ≠ s then
      if Nat.gcd (n / s) v = 1 then cadd c1 (f (n / s)) else c1
    else c1
  else c

private theorem slotStep_prefix (v n : Nat) (f : Nat → Cell)
    (c : Cell) (i : Nat) (hi : i < Nat.sqrt n) :
    slotStep v n f c i = referenceStep v n f c i := by
  have hs : (i + 1) * (i + 1) ≤ n :=
    LeanCompCert.Verified.SqrtEquiv.sq_le_of_le_sqrt (by omega)
  simp only [slotStep, referenceStep, hs, true_and]

private theorem slotStep_tail (v n : Nat) (f : Nat → Cell)
    (c : Cell) (j : Nat) :
    slotStep v n f c (Nat.sqrt n + j) = c := by
  have hs : ¬ (Nat.sqrt n + j + 1) * (Nat.sqrt n + j + 1) ≤ n := by
    intro h
    have := LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le h
    omega
  simp [slotStep, hs]

private theorem prefix_fold (slotCount v n : Nat) (f : Nat → Cell)
    (hcount : slotCount ≤ Nat.sqrt n) (c : Cell) :
    (List.range slotCount).foldl (slotStep v n f) c =
      (List.range slotCount).foldl (referenceStep v n f) c := by
  induction slotCount generalizing c with
  | zero => rfl
  | succ slotCount ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      exact slotStep_prefix v n f _ slotCount (by omega)

private theorem tail_fold (tailCount v n : Nat) (f : Nat → Cell)
    (c : Cell) :
    (List.range tailCount).foldl
      (fun c j => slotStep v n f c (Nat.sqrt n + j)) c = c := by
  induction tailCount generalizing c with
  | zero => rfl
  | succ tailCount ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih]
      exact slotStep_tail v n f c tailCount

/-- A fixed-slot divisor fold is the reference `kDivSum` whenever its slot
budget covers `⌊√n⌋`. -/
theorem slotDivSum_eq_kDivSum (slotCount v n : Nat) (f : Nat → Cell)
    (hslots : Nat.sqrt n ≤ slotCount) :
    slotDivSum slotCount v n f = kDivSum v n f := by
  have hsplit : slotCount = Nat.sqrt n + (slotCount - Nat.sqrt n) := by
    omega
  unfold slotDivSum kDivSum
  change (List.range slotCount).foldl (slotStep v n f) czero =
    (List.range (Nat.sqrt n)).foldl (referenceStep v n f) czero
  rw [hsplit, List.range_add, List.foldl_append, List.foldl_map,
    prefix_fold (Nat.sqrt n) v n f (Nat.le_refl _), tail_fold]

/-- The production schedule has enough slots for every production row. -/
theorem production_sqrt_le_slots (n : Nat)
    (hn : n ≤ LeanCompCert.Ports.Section413WindowSchedule.productionRows) :
    Nat.sqrt n ≤ LeanCompCert.Ports.Section413WindowSchedule.slots := by
  simp only [LeanCompCert.Ports.Section413WindowSchedule.productionRows,
    LeanCompCert.Ports.Section413WindowSchedule.slots] at hn ⊢
  by_cases hroot : Nat.sqrt n ≤ 316
  · exact hroot
  · have h317 : 317 ≤ Nat.sqrt n := by omega
    have hsquare :=
      LeanCompCert.Verified.SqrtEquiv.sq_le_of_le_sqrt h317
    omega

#print axioms slotDivSum_eq_kDivSum
#print axioms production_sqrt_le_slots

end LeanCompCert.Ports.Section413WindowPairingBridge
