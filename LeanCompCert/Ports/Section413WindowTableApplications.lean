import LeanCompCert.Ports.Section413G1TableSound
import LeanCompCert.Ports.Section413G2TableSound

/-! Connect pointwise compiled G1/G2 tables to the Section 4.1.3 window scan. -/

namespace LeanCompCert.Ports.Section413WindowTableApplications

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G1Sound (g1Prefix g1Prefix_succ)
open LeanCompCert.Ports.Section413G2Sound (g2Prefix g2Prefix_succ)

theorem getElem!_push_lt {α : Type} [Inhabited α] (A : Array α) (x : α)
    (i : Nat) (hi : i < A.size) : (A.push x)[i]! = A[i]! := by
  have hipush : i < (A.push x).size := by simp; omega
  rw [getElem!_pos (A.push x) i hipush, getElem!_pos A i hi,
    Array.getElem_push]
  simp only [dif_pos hi]

theorem getElem!_push_eq {α : Type} [Inhabited α] (A : Array α) (x : α) :
    (A.push x)[A.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

def tabPrefix1 (R N k : Nat) : TabState :=
  (List.range k).foldl
    (fun s i => tabStep R (weightV1 R (i + 1)) s (i + 1))
    ⟨Array.replicate (N + 1) czero, czero, #[czero]⟩

def tabPrefix2 (R N k : Nat) : TabState :=
  (List.range k).foldl
    (fun s i => tabStep R (weightV2 R (i + 1)) s (i + 1))
    ⟨Array.replicate (N + 1) czero, czero, #[czero]⟩

theorem tabPrefix1_succ (R N k : Nat) :
    tabPrefix1 R N (k + 1) =
      tabStep R (weightV1 R (k + 1)) (tabPrefix1 R N k) (k + 1) := by
  unfold tabPrefix1
  rw [List.range_succ, List.foldl_append]
  rfl

theorem tabPrefix2_succ (R N k : Nat) :
    tabPrefix2 R N (k + 1) =
      tabStep R (weightV2 R (k + 1)) (tabPrefix2 R N k) (k + 1) := by
  unfold tabPrefix2
  rw [List.range_succ, List.foldl_append]
  rfl

theorem tabPrefix1_core (R checkLo N k : Nat) :
    (g1Prefix R checkLo N k).acc = (tabPrefix1 R N k).acc ∧
      (g1Prefix R checkLo N k).g = (tabPrefix1 R N k).g := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      rw [g1Prefix_succ, tabPrefix1_succ]
      simp only [g1Step, tabStep]
      rw [ih.1, ih.2]
      exact ⟨rfl, rfl⟩

theorem tabPrefix2_core (R checkLo N k : Nat) :
    (g2Prefix R checkLo N k).acc = (tabPrefix2 R N k).acc ∧
      (g2Prefix R checkLo N k).g = (tabPrefix2 R N k).g := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      rw [g2Prefix_succ, tabPrefix2_succ]
      simp only [g2Step, tabStep]
      rw [ih.1, ih.2]
      exact ⟨rfl, rfl⟩

theorem tabPrefix1_size (R N k : Nat) :
    (tabPrefix1 R N k).table.size = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tabPrefix1_succ]
      simp only [tabStep, Array.size_push, ih]

theorem tabPrefix2_size (R N k : Nat) :
    (tabPrefix2 R N k).table.size = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tabPrefix2_succ]
      simp only [tabStep, Array.size_push, ih]

theorem tabPrefix1_zero (R N k : Nat) :
    (tabPrefix1 R N k).table[0]! = czero := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tabPrefix1_succ]
      simp only [tabStep]
      rw [getElem!_push_lt]
      · exact ih
      · rw [tabPrefix1_size]; omega

theorem tabPrefix2_zero (R N k : Nat) :
    (tabPrefix2 R N k).table[0]! = czero := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tabPrefix2_succ]
      simp only [tabStep]
      rw [getElem!_push_lt]
      · exact ih
      · rw [tabPrefix2_size]; omega

theorem tabPrefix1_lookup (R checkLo N k j : Nat) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) :
    (tabPrefix1 R N k).table[j]! = (g1Prefix R checkLo N j).g := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [tabPrefix1_succ]
      simp only [tabStep]
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · rw [getElem!_push_lt]
        · exact ih (by omega)
        · rw [tabPrefix1_size]; omega
      · have hj : j = k + 1 := by omega
        subst j
        have hget := getElem!_push_eq (tabPrefix1 R N k).table
          (cadd (tabPrefix1 R N k).g
            (stepDivisors R (k + 1) (weightV1 R (k + 1))
              ((tabPrefix1 R N k).acc, czero)).2)
        rw [tabPrefix1_size] at hget
        rw [hget]
        have hcore := (tabPrefix1_core R checkLo N (k + 1)).2.symm
        rw [tabPrefix1_succ] at hcore
        simpa only [tabStep] using hcore

theorem tabPrefix2_lookup (R checkLo N k j : Nat) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) :
    (tabPrefix2 R N k).table[j]! = (g2Prefix R checkLo N j).g := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [tabPrefix2_succ]
      simp only [tabStep]
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · rw [getElem!_push_lt]
        · exact ih (by omega)
        · rw [tabPrefix2_size]; omega
      · have hj : j = k + 1 := by omega
        subst j
        have hget := getElem!_push_eq (tabPrefix2 R N k).table
          (cadd (tabPrefix2 R N k).g
            (stepDivisors R (k + 1) (weightV2 R (k + 1))
              ((tabPrefix2 R N k).acc, czero)).2)
        rw [tabPrefix2_size] at hget
        rw [hget]
        have hcore := (tabPrefix2_core R checkLo N (k + 1)).2.symm
        rw [tabPrefix2_succ] at hcore
        simpa only [tabStep] using hcore

theorem tabRun1_eq_prefix (R N : Nat) : tabRun 1 R N = tabPrefix1 R N N := by
  unfold tabRun tabPrefix1
  rfl

theorem tabRun2_eq_prefix (R N : Nat) : tabRun 2 R N = tabPrefix2 R N N := by
  unfold tabRun tabPrefix2
  rfl

theorem tabRun1_table_eq (R checkLo N : Nat) (T : Array Cell)
    (hsize : T.size = N + 1) (hzero : T[0]! = czero)
    (htable : ∀ X, 1 ≤ X → X ≤ N →
      T[X]! = (g1Prefix R checkLo N X).g) :
    (tabRun 1 R N).table = T := by
  rw [tabRun1_eq_prefix]
  apply Array.ext
  · rw [tabPrefix1_size, hsize]
  · intro i hi1 hi2
    rw [← getElem!_pos (tabPrefix1 R N N).table i hi1,
      ← getElem!_pos T i hi2]
    by_cases hi0 : i = 0
    · subst i
      rw [tabPrefix1_zero, hzero]
    · rw [tabPrefix1_lookup R checkLo N N i (by omega) (by
          rw [tabPrefix1_size] at hi1
          omega), ← htable i (by omega) (by
          rw [hsize] at hi2
          omega)]

theorem tabRun2_table_eq (R checkLo N : Nat) (T : Array Cell)
    (hsize : T.size = N + 1) (hzero : T[0]! = czero)
    (htable : ∀ X, 1 ≤ X → X ≤ N →
      T[X]! = (g2Prefix R checkLo N X).g) :
    (tabRun 2 R N).table = T := by
  rw [tabRun2_eq_prefix]
  apply Array.ext
  · rw [tabPrefix2_size, hsize]
  · intro i hi1 hi2
    rw [← getElem!_pos (tabPrefix2 R N N).table i hi1,
      ← getElem!_pos T i hi2]
    by_cases hi0 : i = 0
    · subst i
      rw [tabPrefix2_zero, hzero]
    · rw [tabPrefix2_lookup R checkLo N N i (by omega) (by
          rw [tabPrefix2_size] at hi1
          omega), ← htable i (by omega) (by
          rw [hsize] at hi2
          omega)]

def windowTableOK (T1 T2 : Array Cell) (N : Nat) : Bool :=
  (kRun (fun k => T1[k]!) 1 40 36393 100000 N).ok &&
    (kRun (fun k => T2[k]!) 2 16 37273 100000 N).ok

/-- A composable event-scan slice.  Generated certificates use literal
checkpoints so each kernel reduction covers only a bounded number of events. -/
def kSegment (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (boundDen start len : Nat) (s : KState) : KState :=
  (List.range len).foldl
    (fun p i => kStep G v lo boundNum boundDen (start + i) p) s

theorem kSegment_append (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (boundDen start a b : Nat) (s : KState) :
    kSegment G v lo boundNum boundDen start (a + b) s =
      kSegment G v lo boundNum boundDen (start + a) b
        (kSegment G v lo boundNum boundDen start a s) := by
  unfold kSegment
  rw [List.range_add, List.foldl_append, List.foldl_map]
  simpa only [Nat.add_assoc]

theorem kSegment_chain {G : Nat → Cell} {v lo : Nat} {boundNum : Int}
    {boundDen start a b : Nat} {s t u : KState}
    (h₁ : kSegment G v lo boundNum boundDen start a s = t)
    (h₂ : kSegment G v lo boundNum boundDen (start + a) b t = u) :
    kSegment G v lo boundNum boundDen start (a + b) s = u := by
  rw [kSegment_append, h₁, h₂]

theorem kRun_eq_segment (G : Nat → Cell) (v lo : Nat) (boundNum : Int)
    (boundDen N : Nat) :
    kRun G v lo boundNum boundDen N =
      kSegment G v lo boundNum boundDen 0 N ⟨czero, czero, true⟩ := by
  unfold kRun kSegment
  congr 1
  funext p i
  simp only [Nat.zero_add]

theorem windowOK_of_tables (R checkLo N : Nat) (T1 T2 : Array Cell)
    (hsize1 : T1.size = N + 1) (hzero1 : T1[0]! = czero)
    (htable1 : ∀ X, 1 ≤ X → X ≤ N →
      T1[X]! = (g1Prefix R checkLo N X).g)
    (hsize2 : T2.size = N + 1) (hzero2 : T2[0]! = czero)
    (htable2 : ∀ X, 1 ≤ X → X ≤ N →
      T2[X]! = (g2Prefix R checkLo N X).g)
    (hok : windowTableOK T1 T2 N = true) : windowOK R N = true := by
  unfold windowTableOK at hok
  unfold windowOK
  rw [tabRun1_table_eq R checkLo N T1 hsize1 hzero1 htable1,
    tabRun2_table_eq R checkLo N T2 hsize2 hzero2 htable2]
  exact hok

end LeanCompCert.Ports.Section413WindowTableApplications
