import LeanCompCert.Ports.DirichletLadderExternalSafetyCheck

/-! Natural-number consequences of the fixed-width ladder guards. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.DirichletLadder

structure ArithmeticSafe (c : Cfg) (arr : Nat → Nat) (idx : Nat) : Prop where
  previousLast_subtraction : arr (recW * idx + 7) ≤ 1
  slot_addition :
    arr (recW * idx + 2) + arr (recW * idx + 3) < M
  upper_succ : arr (recW * idx + 4) + 1 < M
  lower_turing_product :
    arr (recW * idx + 4) * arr (recW * idx + 9) < M
  upper_turing_product :
    (arr (recW * idx + 4) + 1) * arr (recW * idx + 9) < M
  height_cover_product :
    5 * (arr (recW * idx + 1) + 1) *
      (arr (recW * idx) >>> 20) < M
  conjugate_address :
    recW * arr (recW * idx + 11) + 11 < c.tblBase

/-- The runtime record guards plus the public schedule bound are exactly what
is needed to interpret the historical checker arithmetic in `Nat`, rather
than modulo `2^64`. -/
theorem RecordSafe.arithmeticSafe
    {c : Cfg} {arr : Nat → Nat} {idx : Nat}
    (h : RecordSafe c arr idx) (hc : StaticBounds c) :
    ArithmeticSafe c arr idx := by
  dsimp only [RecordSafe] at h
  rcases h with ⟨hLast, hLower, hSlots, hUpper, hHenc, hq0, hq,
    hBlk, hConj⟩
  refine {
    previousLast_subtraction := hLast
    slot_addition := ?_
    upper_succ := ?_
    lower_turing_product := ?_
    upper_turing_product := ?_
    height_cover_product := ?_
    conjugate_address := ?_ }
  · have hcap : 2 * maxPinnedUpper < M := by
      decide
    omega
  · have hcap : maxPinnedUpper + 1 < M := by decide
    omega
  · calc
      arr (recW * idx + 4) * arr (recW * idx + 9) ≤
          maxPinnedUpper * hExpect :=
        Nat.mul_le_mul hUpper hHenc
      _ < M := by decide
  · calc
      (arr (recW * idx + 4) + 1) * arr (recW * idx + 9) ≤
          (maxPinnedUpper + 1) * hExpect :=
        Nat.mul_le_mul (Nat.add_le_add_right hUpper 1) hHenc
      _ < M := by decide
  · have hcount : arr (recW * idx + 1) + 1 ≤ c.records := by omega
    calc
      5 * (arr (recW * idx + 1) + 1) *
          (arr (recW * idx) >>> 20) ≤
          5 * c.records * maxQ := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 5 hcount) hq
      _ < M := hc.height_product_word
  · change 13 * arr (13 * idx + 11) + 11 < 13 * c.records
    change arr (13 * idx + 11) < c.records at hConj
    omega

end LeanCompCert.Ports.DirichletLadderExternalSafety
