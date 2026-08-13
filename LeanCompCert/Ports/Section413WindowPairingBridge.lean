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

/-- The contribution of one fixed slot, independent of the incoming
accumulator. -/
def slotDelta (v n : Nat) (f : Nat → Cell) (i : Nat) : Cell :=
  slotStep v n f czero i

private theorem cadd_assoc (a b c : Cell) :
    cadd (cadd a b) c = cadd a (cadd b c) := by
  cases a; cases b; cases c
  simp [cadd, Int.add_assoc]

private theorem cadd_comm (a b : Cell) : cadd a b = cadd b a := by
  cases a; cases b
  simp [cadd, Int.add_comm]

private theorem cadd_zero (a : Cell) : cadd a czero = a := by
  cases a
  simp [cadd, czero]

private theorem zero_cadd (a : Cell) : cadd czero a = a := by
  rw [cadd_comm, cadd_zero]

theorem slotStep_eq_cadd_delta (v n : Nat) (f : Nat → Cell)
    (c : Cell) (i : Nat) :
    slotStep v n f c i = cadd c (slotDelta v n f i) := by
  by_cases hroot : (i + 1) * (i + 1) ≤ n ∧ n % (i + 1) = 0 <;>
    by_cases hfirst : Nat.gcd (i + 1) v = 1 <;>
    by_cases hpair : n / (i + 1) ≠ i + 1 <;>
    by_cases hsecond : Nat.gcd (n / (i + 1)) v = 1 <;>
    cases c <;>
    simp [slotDelta, slotStep, hroot, hfirst, hpair, hsecond, cadd, czero,
      Int.add_assoc]

private theorem foldl_two_deltas (xs : List Nat) (f g : Nat → Cell)
    (a b : Cell) :
    xs.foldl (fun c i => cadd c (cadd (f i) (g i))) (cadd a b) =
      cadd (xs.foldl (fun c i => cadd c (f i)) a)
        (xs.foldl (fun c i => cadd c (g i)) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [show cadd (cadd a b) (cadd (f i) (g i)) =
          cadd (cadd a (f i)) (cadd b (g i)) by
        rw [cadd_assoc, ← cadd_assoc b, cadd_comm b (f i),
          cadd_assoc (f i) b, cadd_assoc a]]
      exact ih (cadd a (f i)) (cadd b (g i))

private theorem foldl_two_deltas_zero (xs : List Nat) (f g : Nat → Cell) :
    xs.foldl (fun c i => cadd c (cadd (f i) (g i))) czero =
      cadd (xs.foldl (fun c i => cadd c (f i)) czero)
        (xs.foldl (fun c i => cadd c (g i)) czero) := by
  simpa only [zero_cadd] using foldl_two_deltas xs f g czero czero

private theorem slotFold_eq_delta_fold (xs : List Nat) (v n : Nat)
    (f : Nat → Cell) (c : Cell) :
    xs.foldl (slotStep v n f) c =
      xs.foldl (fun c i => cadd c (slotDelta v n f i)) c := by
  induction xs generalizing c with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [slotStep_eq_cadd_delta]
      exact ih (cadd c (slotDelta v n f i))

private theorem slotDivSum_eq_delta_fold (slotCount v n : Nat)
    (f : Nat → Cell) :
    slotDivSum slotCount v n f =
      (List.range slotCount).foldl
        (fun c i => cadd c (slotDelta v n f i)) czero := by
  exact slotFold_eq_delta_fold (List.range slotCount) v n f czero

/-- Per-slot K1 contribution: the ordinary divisor-pair term and, on even
rows, the doubled-denominator half-row term. -/
def k1SlotDelta (G : Nat → Cell) (v n i : Nat) : Cell :=
  cadd (slotDelta v n (k1First G n) i)
    (if n % 2 = 0 then
      slotDelta v (n / 2) (k1Second G (n / 2)) i else czero)

/-- Per-slot K2 counterpart. -/
def k2SlotDelta (G : Nat → Cell) (v n i : Nat) : Cell :=
  cadd (slotDelta v n (k2First G n) i)
    (if n % 2 = 0 then
      slotDelta v (n / 2) (k2Second G (n / 2)) i else czero)

def k1Slots (slotCount : Nat) (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range slotCount).foldl
    (fun c i => cadd c (k1SlotDelta G v n i)) czero

def k2Slots (slotCount : Nat) (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range slotCount).foldl
    (fun c i => cadd c (k2SlotDelta G v n i)) czero

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

theorem k1Slots_eq_k1Delta (slotCount : Nat) (G : Nat → Cell)
    (v n : Nat) (hn : Nat.sqrt n ≤ slotCount)
    (hhalf : Nat.sqrt (n / 2) ≤ slotCount) :
    k1Slots slotCount G v n = k1Delta G v n := by
  unfold k1Slots k1SlotDelta k1Delta
  by_cases heven : n % 2 = 0
  · simp only [heven, if_true]
    rw [foldl_two_deltas_zero,
      ← slotDivSum_eq_delta_fold slotCount v n (k1First G n),
      ← slotDivSum_eq_delta_fold slotCount v (n / 2)
        (k1Second G (n / 2)),
      slotDivSum_eq_kDivSum slotCount v n (k1First G n) hn,
      slotDivSum_eq_kDivSum slotCount v (n / 2)
        (k1Second G (n / 2)) hhalf]
  · simp only [heven, if_false, cadd_zero]
    rw [← slotDivSum_eq_delta_fold slotCount v n (k1First G n),
      slotDivSum_eq_kDivSum slotCount v n (k1First G n) hn]

theorem k2Slots_eq_k2Delta (slotCount : Nat) (G : Nat → Cell)
    (v n : Nat) (hn : Nat.sqrt n ≤ slotCount)
    (hhalf : Nat.sqrt (n / 2) ≤ slotCount) :
    k2Slots slotCount G v n = k2Delta G v n := by
  unfold k2Slots k2SlotDelta k2Delta
  by_cases heven : n % 2 = 0
  · simp only [heven, if_true]
    rw [foldl_two_deltas_zero,
      ← slotDivSum_eq_delta_fold slotCount v n (k2First G n),
      ← slotDivSum_eq_delta_fold slotCount v (n / 2)
        (k2Second G (n / 2)),
      slotDivSum_eq_kDivSum slotCount v n (k2First G n) hn,
      slotDivSum_eq_kDivSum slotCount v (n / 2)
        (k2Second G (n / 2)) hhalf]
  · simp only [heven, if_false, cadd_zero]
    rw [← slotDivSum_eq_delta_fold slotCount v n (k2First G n),
      slotDivSum_eq_kDivSum slotCount v n (k2First G n) hn]

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
#print axioms k1Slots_eq_k1Delta
#print axioms k2Slots_eq_k2Delta
#print axioms production_sqrt_le_slots

end LeanCompCert.Ports.Section413WindowPairingBridge
