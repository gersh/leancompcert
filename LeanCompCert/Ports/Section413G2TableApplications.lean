import LeanCompCert.Ports.Section413G2TableSound

/-!
# Source applications of a certified Section 4.1.3 `g₂` table

This module converts the pointwise table conclusion of
`Section413G2TableSound` into the head-mass and main-term model Boolean.  It
contains no evaluation artifact: concrete generated tables instantiate the
general theorems in separate certificate modules.
-/

namespace LeanCompCert.Ports.Section413G2TableApplications

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G2Sound (g2Prefix)

/-- The head/main sweep after exactly `k` candidates, retaining the full
production-size accumulator array in every prefix. -/
def hmPrefix (R N k : Nat) : HMState :=
  (List.range k).foldl
    (fun s i =>
      let X := i + 1
      hmStep R (weightV2 R X) s X)
    ⟨Array.replicate (N + 1) czero, czero, 0, 0⟩

theorem hmPrefix_zero (R N : Nat) :
    hmPrefix R N 0 =
      ⟨Array.replicate (N + 1) czero, czero, 0, 0⟩ := rfl

theorem hmPrefix_succ (R N k : Nat) :
    hmPrefix R N (k + 1) =
      hmStep R (weightV2 R (k + 1)) (hmPrefix R N k) (k + 1) := by
  unfold hmPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem hmPrefix_full (R N : Nat) : hmPrefix R N N = hmRun 2 R N := by
  unfold hmPrefix hmRun
  congr 1

/-- The `g₂` reference sweep and head/main sweep carry exactly the same
divisor accumulators and current `g` interval. -/
theorem g2Prefix_hmPrefix_core (R checkLo N k : Nat) :
    (g2Prefix R checkLo N k).acc = (hmPrefix R N k).acc ∧
      (g2Prefix R checkLo N k).g = (hmPrefix R N k).g := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      rw [LeanCompCert.Ports.Section413G2Sound.g2Prefix_succ,
        hmPrefix_succ]
      simp only [g2Step, hmStep]
      rw [ih.1, ih.2]
      exact ⟨rfl, rfl⟩

/-- Aggregate a supplied table in exactly the order and with exactly the
integer formulas used by `hmRun`. -/
def hmTablePrefix (T : Array Cell) (k : Nat) : Int × Int :=
  (List.range k).foldl (fun s i =>
    let X := i + 1
    let I := T[X]!
    (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
      s.2 + mainTermUB X I)) (0, 0)

/-- A composable slice of the same aggregate, covering candidates
`start+1, …, start+len`.  Generated certificates prove these in bounded
chunks so no single kernel reduction retains the full table fold. -/
def hmTableSegment (T : Array Cell) (start len : Nat) : Int × Int :=
  (List.range len).foldl (fun s i =>
    let X := start + i + 1
    let I := T[X]!
    (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
      s.2 + mainTermUB X I)) (0, 0)

/-- The same segment aggregate for a local certificate array whose element
zero represents candidate `start+1`. -/
def hmLocalSegment (T : Array Cell) (start len : Nat) : Int × Int :=
  (List.range len).foldl (fun s i =>
    let X := start + i + 1
    let I := T[i]!
    (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
      s.2 + mainTermUB X I)) (0, 0)

theorem hmTableSegment_eq_local (T C : Array Cell) (start len : Nat)
    (hlookup : ∀ i, i < len → T[start + i + 1]! = C[i]!) :
    hmTableSegment T start len = hmLocalSegment C start len := by
  unfold hmTableSegment hmLocalSegment
  generalize hx : List.range len = xs
  have hmem : ∀ i ∈ xs, i < len := by
    intro i hi
    rw [← hx] at hi
    exact List.mem_range.mp hi
  clear hx
  have aux : ∀ (ys : List Nat) (s : Int × Int),
      (∀ i ∈ ys, i < len) →
      ys.foldl (fun s i =>
          let X := start + i + 1
          let I := T[X]!
          (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
            s.2 + mainTermUB X I)) s =
        ys.foldl (fun s i =>
          let X := start + i + 1
          let I := C[i]!
          (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
            s.2 + mainTermUB X I)) s := by
    intro ys
    induction ys with
    | nil => intro s _; rfl
    | cons i rest ih =>
        intro s hm
        simp only [List.foldl_cons]
        rw [hlookup i (hm i (by simp))]
        exact ih _ (fun j hj => hm j (by simp [hj]))
  exact aux xs (0, 0) hmem

theorem hmTableSegment_append (T : Array Cell) (start a b : Nat) :
    hmTableSegment T start (a + b) =
      let x := hmTableSegment T start a
      let y := hmTableSegment T (start + a) b
      (x.1 + y.1, x.2 + y.2) := by
  unfold hmTableSegment
  rw [List.range_add, List.foldl_append, List.foldl_map]
  have shift : ∀ (xs : List Nat) (s : Int × Int),
      xs.foldl
          (fun s i =>
            let X := start + a + i + 1
            let I := T[X]!
            (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
              s.2 + mainTermUB X I)) s =
        let z := xs.foldl
          (fun s i =>
            let X := start + a + i + 1
            let I := T[X]!
            (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
              s.2 + mainTermUB X I)) (0, 0)
        (s.1 + z.1, s.2 + z.2) := by
    intro xs
    induction xs with
    | nil => intro s; simp
    | cons i rest ih =>
        intro s
        simp only [List.foldl_cons]
        rw [ih]
        simp only [Int.zero_add, Prod.fst, Prod.snd]
        rw [ih
          (cabsUB T[start + a + i + 1]! *
              ((5 * (start + a + i + 1) * (start + a + i + 1) +
                2 * (start + a + i + 1) + 1 : Nat) : Int),
            mainTermUB (start + a + i + 1) T[start + a + i + 1]!)]
        simp only [Int.zero_add, Prod.fst, Prod.snd]
        apply Prod.ext <;> simp only <;> omega
  simpa only [Nat.add_assoc] using shift (List.range b)
    ((List.range a).foldl (fun s i =>
      let X := start + i + 1
      let I := T[X]!
      (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
        s.2 + mainTermUB X I)) (0, 0))

theorem hmTablePrefix_eq_segment (T : Array Cell) (N : Nat) :
    hmTablePrefix T N = hmTableSegment T 0 N := by
  unfold hmTablePrefix hmTableSegment
  congr 1
  funext s i
  simp only [Nat.zero_add]

theorem hmTablePrefix_zero (T : Array Cell) : hmTablePrefix T 0 = (0, 0) := rfl

theorem hmTablePrefix_succ (T : Array Cell) (k : Nat) :
    hmTablePrefix T (k + 1) =
      let I := T[k + 1]!
      let s := hmTablePrefix T k
      (s.1 + cabsUB I * ((5 * (k + 1) * (k + 1) + 2 * (k + 1) + 1 : Nat) : Int),
        s.2 + mainTermUB (k + 1) I) := by
  unfold hmTablePrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem hmPrefix_aggregates_eq_table (R checkLo N : Nat) (T : Array Cell)
    (htable : ∀ X, 1 ≤ X → X ≤ N →
      T[X]! = (g2Prefix R checkLo N X).g) :
    ∀ k, k ≤ N →
      (hmPrefix R N k).headAcc = (hmTablePrefix T k).1 ∧
      (hmPrefix R N k).mainAcc = (hmTablePrefix T k).2 := by
  intro k hk
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      have hkN : k ≤ N := by omega
      have hX : k + 1 ≤ N := by omega
      rw [hmPrefix_succ, hmTablePrefix_succ]
      simp only [hmStep]
      have hcore := g2Prefix_hmPrefix_core R checkLo N (k + 1)
      have hcell : T[k + 1]! =
          cadd (hmPrefix R N k).g
            (stepDivisors R (k + 1) (weightV2 R (k + 1))
              ((hmPrefix R N k).acc, czero)).2 := by
        calc
          T[k + 1]! = (g2Prefix R checkLo N (k + 1)).g :=
            htable (k + 1) (by omega) hX
          _ = (hmPrefix R N (k + 1)).g := hcore.2
          _ = _ := by rw [hmPrefix_succ]; rfl
      rw [hcell]
      rw [ih hkN |>.1, ih hkN |>.2]
      exact ⟨rfl, rfl⟩

def hmV2TableOK (T : Array Cell) (N : Nat) : Bool :=
  let s := hmTablePrefix T N
  decide (s.1 ≤ 47734021 * (SCALE : Int)) &&
    decide (10000000 * s.2 ≤ 4 * 3605763 * (SCALE : Int))

theorem hmV2OK_of_table (R checkLo N : Nat) (T : Array Cell)
    (htable : ∀ X, 1 ≤ X → X ≤ N →
      T[X]! = (g2Prefix R checkLo N X).g)
    (hok : hmV2TableOK T N = true) : hmV2OK R N = true := by
  have hagg := hmPrefix_aggregates_eq_table R checkLo N T htable N (Nat.le_refl _)
  rw [hmV2OK, ← hmPrefix_full]
  unfold hmV2TableOK at hok
  rw [hagg.1, hagg.2]
  exact hok

end LeanCompCert.Ports.Section413G2TableApplications
