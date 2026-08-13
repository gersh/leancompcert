import LeanCompCert.Ports.Section413WindowContributionSound

/-!
# Compiled event contributions equal one paper slot

These lemmas identify the four constant-size compiled event expressions with
the paper's per-slot `K₁`/`K₂` recurrence.  They are symbolic in the row
and slot index and never enumerate the production scan.
-/

namespace LeanCompCert.Ports.Section413WindowSlotContributionBridge

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowPairingBridge
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowTableRead

def referenceDiff (G : Nat → Cell) (x : Nat) : Cell :=
  let y := safeX x
  csub (G (y - 1)) (G y)

private theorem referenceDiff_of_pos (G : Nat → Cell) (x : Nat)
    (hx : 0 < x) :
    referenceDiff G x = csub (G (x - 1)) (G x) := by
  simp [referenceDiff, safeX, Nat.ne_of_gt hx]

private theorem gcd_two (d : Nat) : Nat.gcd d 2 = 1 ↔ d % 2 = 1 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  have h : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private theorem cadd_zero (a : Cell) : cadd a czero = a := by
  cases a
  simp [cadd, czero]

private theorem zero_cadd (a : Cell) : cadd czero a = a := by
  cases a
  simp [cadd, czero]

theorem ordinaryK1 (G : Nat → Cell) (v n i : Nat)
    (hv : v = 1 ∨ v = 2) :
    let s := i + 1
    let q := n / s
    let active := if s * s ≤ n ∧ n % s = 0 then 1 else 0
    let pair := if s * s ≤ n ∧ n % s = 0 ∧ q ≠ s then 1 else 0
    cadd
      (eventK1Contribution (divisorGate v active s)
        (referenceDiff G q) (safeDen s) true)
      (eventK1Contribution (divisorGate v pair q)
        (referenceDiff G s) (safeDen q) true) =
      slotDelta v n (k1First G n) i := by
  dsimp only
  have hs : 0 < i + 1 := Nat.succ_pos _
  by_cases hroot : (i + 1) * (i + 1) ≤ n ∧ n % (i + 1) = 0
  · have hq : 0 < n / (i + 1) := by
      apply Nat.div_pos
      · exact Nat.le_trans (Nat.le_mul_self _) hroot.1
      · exact hs
    have hdiv : i + 1 ∣ n := Nat.dvd_of_mod_eq_zero hroot.2
    have hmul : n / (i + 1) * (i + 1) = n := Nat.div_mul_cancel hdiv
    have hrecip : n / (n / (i + 1)) = i + 1 := by
      calc
        n / (n / (i + 1)) =
            (n / (i + 1) * (i + 1)) / (n / (i + 1)) := by rw [hmul]
        _ = i + 1 := Nat.mul_div_right _ hq
    rw [referenceDiff_of_pos G _ hs, referenceDiff_of_pos G _ hq]
    by_cases hpair : n / (i + 1) ≠ i + 1
    · rcases hv with rfl | rfl
      · simp [slotDelta, slotStep, hroot, hpair, eventK1Contribution,
          divisorGate, safeDen, Nat.ne_of_gt hq, k1First, hrecip,
          signedOne, zero_cadd]
      · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
        have hqmod : n / (i + 1) % 2 = 0 ∨ n / (i + 1) % 2 = 1 := by omega
        rcases hsmod with hsmod | hsmod <;>
          rcases hqmod with hqmod | hqmod <;>
          simp [slotDelta, slotStep, hroot, hpair, eventK1Contribution,
            divisorGate, safeDen, Nat.ne_of_gt hq, k1First, gcd_two,
            hrecip, signedOne, cadd_zero, zero_cadd, hsmod, hqmod]
    · rcases hv with rfl | rfl
      · simp [slotDelta, slotStep, hroot, hpair, eventK1Contribution,
          divisorGate, safeDen, k1First, signedOne, cadd_zero, zero_cadd]
      · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
        rcases hsmod with hsmod | hsmod <;>
          simp [slotDelta, slotStep, hroot, hpair, eventK1Contribution,
            divisorGate, safeDen, k1First, gcd_two, signedOne, cadd_zero,
            zero_cadd, hsmod]
  · have hpair0 : ¬ ((i + 1) * (i + 1) ≤ n ∧ n % (i + 1) = 0 ∧
        n / (i + 1) ≠ i + 1) := by
      intro h
      exact hroot ⟨h.1, h.2.1⟩
    rcases hv with rfl | rfl <;>
      simp [slotDelta, slotStep, hroot, hpair0, eventK1Contribution,
        divisorGate, cadd, czero]

theorem ordinaryK2 (G : Nat → Cell) (v n i : Nat)
    (hv : v = 1 ∨ v = 2) :
    let s := i + 1
    let q := n / s
    let active := if s * s ≤ n ∧ n % s = 0 then 1 else 0
    let pair := if s * s ≤ n ∧ n % s = 0 ∧ q ≠ s then 1 else 0
    cadd
      (eventK2Contribution (divisorGate v active s)
        (referenceDiff G q) q false)
      (eventK2Contribution (divisorGate v pair q)
        (referenceDiff G s) s false) =
      slotDelta v n (k2First G n) i := by
  dsimp only
  by_cases hroot : (i + 1) * (i + 1) ≤ n ∧ n % (i + 1) = 0
  · have hs : 0 < i + 1 := Nat.succ_pos _
    have hq : 0 < n / (i + 1) :=
      Nat.div_pos (Nat.le_trans (Nat.le_mul_self _) hroot.1) hs
    have hdiv : i + 1 ∣ n := Nat.dvd_of_mod_eq_zero hroot.2
    have hmul : n / (i + 1) * (i + 1) = n := Nat.div_mul_cancel hdiv
    have hrecip : n / (n / (i + 1)) = i + 1 := by
      calc
        n / (n / (i + 1)) =
            (n / (i + 1) * (i + 1)) / (n / (i + 1)) := by rw [hmul]
        _ = i + 1 := Nat.mul_div_right _ hq
    rw [referenceDiff_of_pos G _ hs, referenceDiff_of_pos G _ hq]
    by_cases hpair : n / (i + 1) ≠ i + 1
    · rcases hv with rfl | rfl
      · simp [slotDelta, slotStep, hroot, hpair, eventK2Contribution,
          divisorGate, k2First, hrecip, signedOne, zero_cadd]
      · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
        have hqmod : n / (i + 1) % 2 = 0 ∨ n / (i + 1) % 2 = 1 := by omega
        rcases hsmod with hsmod | hsmod <;>
          rcases hqmod with hqmod | hqmod <;>
          simp [slotDelta, slotStep, hroot, hpair, eventK2Contribution,
            divisorGate, k2First, gcd_two, hrecip, signedOne, cadd_zero,
            zero_cadd, hsmod, hqmod]
    · rcases hv with rfl | rfl
      · simp [slotDelta, slotStep, hroot, hpair, eventK2Contribution,
          divisorGate, k2First, signedOne, cadd_zero, zero_cadd]
      · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
        rcases hsmod with hsmod | hsmod <;>
          simp [slotDelta, slotStep, hroot, hpair, eventK2Contribution,
            divisorGate, k2First, gcd_two, signedOne, cadd_zero, zero_cadd,
            hsmod]
  · have hpair0 : ¬ ((i + 1) * (i + 1) ≤ n ∧ n % (i + 1) = 0 ∧
        n / (i + 1) ≠ i + 1) := by
      intro h
      exact hroot ⟨h.1, h.2.1⟩
    rcases hv with rfl | rfl <;>
      simp [slotDelta, slotStep, hroot, hpair0, eventK2Contribution,
        divisorGate, cadd, czero]

theorem halfK1 (G : Nat → Cell) (v n i : Nat)
    (hv : v = 1 ∨ v = 2) :
    let s := i + 1
    let m := n / 2
    let q := m / s
    let active := if n % 2 = 0 ∧ s * s ≤ m ∧ m % s = 0 then 1 else 0
    let pair := if n % 2 = 0 ∧ s * s ≤ m ∧ m % s = 0 ∧ q ≠ s
      then 1 else 0
    cadd
      (eventK1Contribution (divisorGate v active s)
        (referenceDiff G q) (safeDen s * 2) false)
      (eventK1Contribution (divisorGate v pair q)
        (referenceDiff G s) (safeDen q * 2) false) =
      (if n % 2 = 0 then
        slotDelta v (n / 2) (k1Second G (n / 2)) i else czero) := by
  dsimp only
  by_cases heven : n % 2 = 0
  · have hs : 0 < i + 1 := Nat.succ_pos _
    by_cases hroot : (i + 1) * (i + 1) ≤ n / 2 ∧
        n / 2 % (i + 1) = 0
    · have hq : 0 < n / 2 / (i + 1) :=
        Nat.div_pos (Nat.le_trans (Nat.le_mul_self _) hroot.1) hs
      have hdiv : i + 1 ∣ n / 2 := Nat.dvd_of_mod_eq_zero hroot.2
      have hmul : n / 2 / (i + 1) * (i + 1) = n / 2 :=
        Nat.div_mul_cancel hdiv
      have hrecip : n / 2 / (n / 2 / (i + 1)) = i + 1 := by
        calc
          n / 2 / (n / 2 / (i + 1)) =
              (n / 2 / (i + 1) * (i + 1)) / (n / 2 / (i + 1)) := by
                rw [hmul]
          _ = i + 1 := Nat.mul_div_right _ hq
      rw [referenceDiff_of_pos G _ hs, referenceDiff_of_pos G _ hq]
      by_cases hpair : n / 2 / (i + 1) ≠ i + 1
      · rcases hv with rfl | rfl
        · simp [heven, slotDelta, slotStep, hroot, hpair,
            eventK1Contribution, divisorGate, safeDen, Nat.ne_of_gt hq,
            k1Second, hrecip, signedOne, zero_cadd, Nat.mul_comm]
        · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
          have hqmod : n / 2 / (i + 1) % 2 = 0 ∨
              n / 2 / (i + 1) % 2 = 1 := by omega
          rcases hsmod with hsmod | hsmod <;>
            rcases hqmod with hqmod | hqmod <;>
            simp [heven, slotDelta, slotStep, hroot, hpair,
              eventK1Contribution, divisorGate, safeDen, Nat.ne_of_gt hq,
              k1Second, gcd_two, hrecip, signedOne, cadd_zero, zero_cadd,
              hsmod, hqmod, Nat.mul_comm]
      · rcases hv with rfl | rfl
        · simp [heven, slotDelta, slotStep, hroot, hpair,
            eventK1Contribution, divisorGate, safeDen, k1Second, signedOne,
            cadd_zero, zero_cadd, Nat.mul_comm]
        · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
          rcases hsmod with hsmod | hsmod <;>
            simp [heven, slotDelta, slotStep, hroot, hpair,
              eventK1Contribution, divisorGate, safeDen, k1Second, gcd_two,
              signedOne, cadd_zero, zero_cadd, hsmod, Nat.mul_comm]
    · have hpair0 : ¬ ((i + 1) * (i + 1) ≤ n / 2 ∧
          n / 2 % (i + 1) = 0 ∧ n / 2 / (i + 1) ≠ i + 1) := by
        intro h
        exact hroot ⟨h.1, h.2.1⟩
      rcases hv with rfl | rfl <;>
        simp [heven, slotDelta, slotStep, hroot, hpair0,
          eventK1Contribution, divisorGate, cadd, czero]
  · rcases hv with rfl | rfl <;>
      simp [heven, eventK1Contribution, divisorGate, cadd, czero]

theorem halfK2 (G : Nat → Cell) (v n i : Nat)
    (hv : v = 1 ∨ v = 2) :
    let s := i + 1
    let m := n / 2
    let q := m / s
    let active := if n % 2 = 0 ∧ s * s ≤ m ∧ m % s = 0 then 1 else 0
    let pair := if n % 2 = 0 ∧ s * s ≤ m ∧ m % s = 0 ∧ q ≠ s
      then 1 else 0
    cadd
      (eventK2Contribution (divisorGate v active s)
        (referenceDiff G q) q true)
      (eventK2Contribution (divisorGate v pair q)
        (referenceDiff G s) s true) =
      (if n % 2 = 0 then
        slotDelta v (n / 2) (k2Second G (n / 2)) i else czero) := by
  dsimp only
  by_cases heven : n % 2 = 0
  · have hs : 0 < i + 1 := Nat.succ_pos _
    by_cases hroot : (i + 1) * (i + 1) ≤ n / 2 ∧
        n / 2 % (i + 1) = 0
    · have hq : 0 < n / 2 / (i + 1) :=
        Nat.div_pos (Nat.le_trans (Nat.le_mul_self _) hroot.1) hs
      have hdiv : i + 1 ∣ n / 2 := Nat.dvd_of_mod_eq_zero hroot.2
      have hmul : n / 2 / (i + 1) * (i + 1) = n / 2 :=
        Nat.div_mul_cancel hdiv
      have hrecip : n / 2 / (n / 2 / (i + 1)) = i + 1 := by
        calc
          n / 2 / (n / 2 / (i + 1)) =
              (n / 2 / (i + 1) * (i + 1)) / (n / 2 / (i + 1)) := by
                rw [hmul]
          _ = i + 1 := Nat.mul_div_right _ hq
      rw [referenceDiff_of_pos G _ hs, referenceDiff_of_pos G _ hq]
      by_cases hpair : n / 2 / (i + 1) ≠ i + 1
      · rcases hv with rfl | rfl
        · simp [heven, slotDelta, slotStep, hroot, hpair,
            eventK2Contribution, divisorGate, k2Second, hrecip, signedOne,
            zero_cadd, Int.mul_comm]
        · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
          have hqmod : n / 2 / (i + 1) % 2 = 0 ∨
              n / 2 / (i + 1) % 2 = 1 := by omega
          rcases hsmod with hsmod | hsmod <;>
            rcases hqmod with hqmod | hqmod <;>
            simp [heven, slotDelta, slotStep, hroot, hpair,
              eventK2Contribution, divisorGate, k2Second, gcd_two, hrecip,
              signedOne, cadd_zero, zero_cadd, hsmod, hqmod, Int.mul_comm]
      · rcases hv with rfl | rfl
        · simp [heven, slotDelta, slotStep, hroot, hpair,
            eventK2Contribution, divisorGate, k2Second, signedOne, cadd_zero,
            zero_cadd]
        · have hsmod : (i + 1) % 2 = 0 ∨ (i + 1) % 2 = 1 := by omega
          rcases hsmod with hsmod | hsmod <;>
            simp [heven, slotDelta, slotStep, hroot, hpair,
              eventK2Contribution, divisorGate, k2Second, gcd_two, signedOne,
              cadd_zero, zero_cadd, hsmod]
    · have hpair0 : ¬ ((i + 1) * (i + 1) ≤ n / 2 ∧
          n / 2 % (i + 1) = 0 ∧ n / 2 / (i + 1) ≠ i + 1) := by
        intro h
        exact hroot ⟨h.1, h.2.1⟩
      rcases hv with rfl | rfl <;>
        simp [heven, slotDelta, slotStep, hroot, hpair0,
          eventK2Contribution, divisorGate, cadd, czero]
  · rcases hv with rfl | rfl <;>
      simp [heven, eventK2Contribution, divisorGate, cadd, czero]

#print axioms ordinaryK1
#print axioms ordinaryK2
#print axioms halfK1
#print axioms halfK2

end LeanCompCert.Ports.Section413WindowSlotContributionBridge
