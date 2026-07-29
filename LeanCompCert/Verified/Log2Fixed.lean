/-
Fixed-shape base-2 logarithm (roadmap M2).

`log2Fixed` performs exactly 64 rounds regardless of input: it folds over
`List.range 64`, at round `bit` selecting `bit + 1` when `2 ^ (bit + 1) ≤ n`.
The loop shape is fixed (unrollable, realizable branch-free via select), and
the result is machine-checked to be the floor base-2 logarithm on the u64
range `1 ≤ n < 2 ^ 64`.
-/

namespace LeanCompCert.Verified.Log2Fixed

/-- 64-round fixed-shape floor base-2 logarithm. Each round is a compare-and-
select, so the whole computation unrolls to a straight-line, branch-free
program on u64 inputs. -/
def log2Fixed (n : Nat) : Nat :=
  (List.range 64).foldl (fun acc bit => if 2 ^ (bit + 1) ≤ n then bit + 1 else acc) 0

/-- Foldl invariant: after folding over `List.range k`, the accumulator is
`min (Nat.log2 n) k` (for `n ≠ 0`).  The predicate `2 ^ (bit + 1) ≤ n` holds
exactly when `bit + 1 ≤ Nat.log2 n`, so the fold computes the largest such
`bit + 1` seen so far, clamped by the round count. -/
theorem foldl_range_eq_min (n : Nat) (hn : n ≠ 0) (k : Nat) :
    (List.range k).foldl (fun acc bit => if 2 ^ (bit + 1) ≤ n then bit + 1 else acc) 0
      = min (Nat.log2 n) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h : 2 ^ (k + 1) ≤ n
    · have hk : k + 1 ≤ Nat.log2 n := (Nat.le_log2 hn).mpr h
      rw [if_pos h]
      omega
    · have hk : Nat.log2 n ≤ k := by
        have hnot : ¬(k + 1 ≤ Nat.log2 n) := mt (Nat.le_log2 hn).mp h
        omega
      rw [if_neg h]
      omega

/-- On the u64 range, the fixed 64-round computation agrees with `Nat.log2`. -/
theorem log2Fixed_eq (n : Nat) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    log2Fixed n = Nat.log2 n := by
  have hn : n ≠ 0 := by omega
  have hlt : Nat.log2 n < 64 := (Nat.log2_lt hn).mpr h64
  unfold log2Fixed
  rw [foldl_range_eq_min n hn 64]
  omega

/-- Main spec: on `1 ≤ n < 2 ^ 64`, `log2Fixed n` is the floor base-2
logarithm, i.e. `2 ^ log2Fixed n ≤ n < 2 ^ (log2Fixed n + 1)`. -/
theorem log2Fixed_spec (n : Nat) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    2 ^ log2Fixed n ≤ n ∧ n < 2 ^ (log2Fixed n + 1) := by
  have hn : n ≠ 0 := by omega
  rw [log2Fixed_eq n h1 h64]
  exact ⟨Nat.log2_self_le hn, (Nat.log2_lt hn).mp (Nat.lt_succ_self _)⟩

end LeanCompCert.Verified.Log2Fixed
