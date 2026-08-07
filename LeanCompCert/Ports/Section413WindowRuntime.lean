import LeanCompCert.Ports.Section413WindowTableApplications
import LeanCompCert.Ports.WordBounds

/-!
# Runtime words for the Section 4.1.3 fixed window

Each word is the nonnegative upper endpoint of one exact event cell, shifted
so the two paper bounds share one machine bound.  The recursive trace retains
the unchanged `kStep` state.  Thus a compiled all-words bound proves the
original event scan, while small independent trace shards can certify the
expensive divisor arithmetic without a single giant kernel reduction.
-/

namespace LeanCompCert.Ports.Section413WindowRuntime

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowTableApplications

def unitScale : Nat := 10000000000000
def commonBound : Nat := 37273 * unitScale

def initialKState : KState := ⟨czero, czero, true⟩

def eventUnit (G : Nat → Cell) (v n : Nat) (p : KState) : Cell :=
  let k1' := cadd p.k1 (k1Delta G v (n + 1))
  let k2' := cadd p.k2 (k2Delta G v (n + 1))
  unitCell k1' k2' (n + 1)

def eventWord (G : Nat → Cell) (v lo offset n : Nat) (p : KState) : Nat :=
  if n + 1 < lo then 0 else (eventUnit G v n p).hi.toNat + offset

def traceStep (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (offset n : Nat) (p : KState) : KState × Nat :=
  (kStep G v lo boundNum 100000 n p, eventWord G v lo offset n p)

def trace (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (offset start : Nat) : Nat → KState → KState × List Nat
  | 0, p => (p, [])
  | len + 1, p =>
      let q := traceStep G v lo boundNum offset start p
      let tail := trace G v lo boundNum offset (start + 1) len q.1
      (tail.1, q.2 :: tail.2)

theorem trace_append (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (offset start a b : Nat) (p : KState) :
    trace G v lo boundNum offset start (a + b) p =
      let first := trace G v lo boundNum offset start a p
      let second := trace G v lo boundNum offset (start + a) b first.1
      (second.1, first.2 ++ second.2) := by
  induction a generalizing start p with
  | zero => simp [trace]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [trace]
      rw [ih]
      simp only [Nat.add_assoc, List.cons_append]
      rw [show start + (1 + a) = start + (a + 1) by omega]

private theorem int_le_of_toNat_le {z : Int} {K : Nat}
    (h : z.toNat ≤ K) : z ≤ (K : Int) := by
  by_cases hz : 0 ≤ z
  · have heq : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
    omega
  · omega

theorem traceStep_ok_of_word_le (G : Nat → Cell) (v lo : Nat)
    (boundNum : Int) (offset n : Nat) (p : KState)
    (hnum : 0 ≤ boundNum)
    (hshift : boundNum * unitScale + offset = commonBound)
    (hp : p.ok = true)
    (hw : (traceStep G v lo boundNum offset n p).2 ≤ commonBound) :
    (traceStep G v lo boundNum offset n p).1.ok = true := by
  simp only [traceStep]
  unfold kStep
  simp only [hp, Bool.true_and]
  by_cases hlo : n + 1 < lo
  · simp [hlo]
  · change (if n + 1 < lo then 0 else
        (eventUnit G v n p).hi.toNat + offset) ≤ commonBound at hw
    rw [if_neg hlo] at hw
    have hnat : (eventUnit G v n p).hi.toNat ≤ boundNum.toNat * unitScale := by
      have hnumNat : (boundNum.toNat : Int) = boundNum := Int.toNat_of_nonneg hnum
      have hshiftNat : boundNum.toNat * unitScale + offset = commonBound := by
        rw [← hnumNat] at hshift
        exact_mod_cast hshift
      omega
    have hint : (eventUnit G v n p).hi ≤ boundNum * unitScale := by
      rw [← Int.toNat_of_nonneg hnum]
      exact int_le_of_toNat_le hnat
    have hscale : (unitScale : Int) * 100000 = (SCALE : Int) := by
      decide
    have hchecked :
        (eventUnit G v n p).hi * ((100000 : Nat) : Int) ≤
          boundNum * (SCALE : Int) := by
      rw [← hscale, ← Int.mul_assoc]
      exact Int.mul_le_mul_of_nonneg_right hint (by decide)
    rw [decide_eq_true_eq]
    exact Or.inr (by simpa only [eventUnit] using hchecked)

theorem trace_safe (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (offset start len : Nat) (p : KState)
    (hnum : 0 ≤ boundNum)
    (hshift : boundNum * unitScale + offset = commonBound)
    (hp : p.ok = true)
    (hall : ∀ w ∈ (trace G v lo boundNum offset start len p).2,
      w ≤ commonBound) :
    (trace G v lo boundNum offset start len p).1.ok = true := by
  induction len generalizing start p with
  | zero => simpa [trace] using hp
  | succ len ih =>
      let q := traceStep G v lo boundNum offset start p
      have hqword : q.2 ≤ commonBound := by
        apply hall q.2
        simp [trace, q]
      have hqok : q.1.ok = true :=
        traceStep_ok_of_word_le G v lo boundNum offset start p
          hnum hshift hp hqword
      apply ih (start := start + 1) (p := q.1) hqok
      intro w hw
      apply hall w
      simp only [trace, q, List.mem_cons]
      exact Or.inr hw

theorem trace_fst_eq_segment (G : Nat → Cell) (v lo : Nat)
    (boundNum : Int) (offset start len : Nat) (p : KState) :
    (trace G v lo boundNum offset start len p).1 =
      kSegment G v lo boundNum 100000 start len p := by
  induction len generalizing start p with
  | zero => rfl
  | succ len ih =>
      rw [show len + 1 = 1 + len by omega,
        kSegment_append]
      rw [show 1 + len = len + 1 by omega]
      simp only [trace]
      change
        (trace G v lo boundNum offset (start + 1) len
          (traceStep G v lo boundNum offset start p).1).1 =
        kSegment G v lo boundNum 100000 (start + 1) len
          (kSegment G v lo boundNum 100000 start 1 p)
      have hstep :
          (traceStep G v lo boundNum offset start p).1 =
            kSegment G v lo boundNum 100000 start 1 p := rfl
      rw [hstep, ih]

end LeanCompCert.Ports.Section413WindowRuntime
