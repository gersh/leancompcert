/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.LogFixed

/-!
# Structural storage bounds for `logFix`

This module is deliberately downstream of `LogFixed`: adding source-facing
bounds must not invalidate large emitter modules that import the circuit
implementation itself.
-/

namespace LeanCompCert.Verified.LogFixed

/-- The emitted fractional bits occupy exactly `S` binary places. -/
theorem logIter_snd_lt_two_pow (x0 : Nat) : ∀ S : Nat, (logIter x0 S).2 < 2 ^ S := by
  intro S
  induction S with
  | zero => simp [logIter]
  | succ S ih =>
      rw [logIter]
      simp only [logStep]
      rw [Nat.pow_succ]
      have hb := logBit_le_one (logIter x0 S).1
      omega

theorem logFrac_lt_two_pow (S x0 : Nat) : logFrac S x0 < 2 ^ S := by
  exact logIter_snd_lt_two_pow x0 S

/-- A `logFix` value for an input below `2^63` is below `63·2^S`. -/
theorem logFix_lt (S n : Nat) (hn : n < B63) : logFix S n < 63 * 2 ^ S := by
  by_cases hn0 : n = 0
  · subst n
    have hf := logFrac_lt_two_pow S (0 <<< (62 - Nat.log2 0))
    simp only [logFix, Nat.log2_zero, Nat.zero_mul, Nat.zero_add]
    calc
      logFrac S (0 <<< (62 - Nat.log2 0)) < 2 ^ S := hf
      _ ≤ 63 * 2 ^ S := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right (2 ^ S) (by decide : 1 ≤ 63)
  · have he : Nat.log2 n < 63 := by
      rw [B63_eq] at hn
      exact (Nat.log2_lt hn0).mpr hn
    have hf := logFrac_lt_two_pow S (n <<< (62 - Nat.log2 n))
    simp only [logFix]
    calc
      Nat.log2 n * 2 ^ S + logFrac S (n <<< (62 - Nat.log2 n)) <
          Nat.log2 n * 2 ^ S + 2 ^ S := Nat.add_lt_add_left hf _
      _ = (Nat.log2 n + 1) * 2 ^ S := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 63 * 2 ^ S := Nat.mul_le_mul_right _ (by omega)

end LeanCompCert.Verified.LogFixed
