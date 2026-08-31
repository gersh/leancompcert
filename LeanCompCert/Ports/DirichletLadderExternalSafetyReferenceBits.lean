import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceInit

/-! Bit-table denotation used by the historical ladder body. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.DirichletLadder

def byteAt (x b : Nat) : Nat := (x >>> (8 * b)) &&& 255

theorem byteAt_bit (x b j : Nat) (hj : j < 8) :
    ((byteAt x b >>> j) % 2) = (x >>> (8 * b + j)) % 2 := by
  rw [byteAt, Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit]
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have h255 : 255 = 2 ^ 8 - 1 := by decide
  rw [h255, Nat.testBit_two_pow_sub_one]
  simp [hj, Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit]

@[simp] theorem byteAt_mod_two (x b : Nat) :
    byteAt x b % 2 = (x >>> (8 * b)) % 2 := by
  simpa using byteAt_bit x b 0 (by omega)

private theorem range8 :
    List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

private theorem range63 :
    List.range 63 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62] := by decide

theorem bitCount_bytes (t : Nat) (h63 : (t >>> 63) % 2 = 0) :
    bitCount t =
      popc8 (byteAt t 0) + popc8 (byteAt t 1) +
      popc8 (byteAt t 2) + popc8 (byteAt t 3) +
      popc8 (byteAt t 4) + popc8 (byteAt t 5) +
      popc8 (byteAt t 6) + popc8 (byteAt t 7) := by
  rw [bitCount, range63]
  simp only [popc8, range8]
  simp [byteAt_bit, h63]
  omega

theorem bitMoment_bytes (t : Nat) (h63 : (t >>> 63) % 2 = 0) :
    bitMoment t =
      mom8 (byteAt t 0) +
      (mom8 (byteAt t 1) + 8 * popc8 (byteAt t 1)) +
      (mom8 (byteAt t 2) + 16 * popc8 (byteAt t 2)) +
      (mom8 (byteAt t 3) + 24 * popc8 (byteAt t 3)) +
      (mom8 (byteAt t 4) + 32 * popc8 (byteAt t 4)) +
      (mom8 (byteAt t 5) + 40 * popc8 (byteAt t 5)) +
      (mom8 (byteAt t 6) + 48 * popc8 (byteAt t 6)) +
      (mom8 (byteAt t 7) + 56 * popc8 (byteAt t 7)) := by
  rw [bitMoment, range63]
  simp only [mom8, popc8, range8]
  simp [byteAt_bit, h63]
  omega

theorem transWord_bit63_zero (bits : Nat) :
    (transWord bits >>> 63) % 2 = 0 := by
  rw [Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit]
  have hmask : mask63 = 2 ^ 63 - 1 := by decide
  rw [transWord, hmask, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one]
  simp

end LeanCompCert.Ports.DirichletLadderExternalSafety
