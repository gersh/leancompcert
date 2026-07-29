/-!
# Half-limb 128-bit product circuit (M2 structural theorem)

The fixed-point certificates compute 128-bit products of `u64` values via
32-bit halves with carry corrections. This module proves the underlying
arithmetic identity once and for all: the circuit-level function `hl`
mirrors the instruction sequence (every step is a `u64`-realizable
operation: `+`, `*`, `%`, `/`, comparison, all mod `2⁶⁴`), and `hl_spec`
shows that its `(lo, hi)` output satisfies `lo + 2⁶⁴ * hi = a * b` with
`lo < 2⁶⁴` (and `hi < 2⁶⁴`, from `hl_hi_lt`).

The carry recovery is the classic proved-comparison trick: for
`x, y < 2⁶⁴` the truncated sum `(x + y) % 2⁶⁴` is below `x` exactly when
the untruncated sum overflowed, so `if sum < x then 1 else 0` is the
carry bit — used once for the middle partial products and once for the
low-word accumulation.
-/

namespace LeanCompCert.Verified.MulWide

/-- `2³²`, the half-limb base. -/
def B32 : Nat := 4294967296

/-- `2⁶⁴`, the limb base. `B32 * B32 = B64` holds definitionally. -/
def B64 : Nat := 18446744073709551616

/-- The half-limb product circuit: `(lo, hi)` of `a * b` for `a, b < B64`,
computed with `u64`-realizable operations only. The four 32×32→64 partial
products are combined with two carry recoveries by proved comparison. -/
def hl (a b : Nat) : Nat × Nat :=
  let a0 := a % B32
  let a1 := a / B32
  let b0 := b % B32
  let b1 := b / B32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p01 + p10) % B64
  let carryMid := if mid < p01 then 1 else 0     -- overflow of p01 + p10
  let lo := (p00 + (mid * B32) % B64) % B64      -- mid <<< 32 (mod 2⁶⁴)
  let carryLo := if lo < p00 then 1 else 0
  let hi := p11 + mid / B32 + carryMid * B32 + carryLo
  (lo, hi)

/-- Products of naturals strictly below `n` lie strictly below `n * n`. -/
theorem mul_lt_mul_of_lt_of_lt {x y n : Nat} (hx : x < n) (hy : y < n) :
    x * y < n * n :=
  Nat.mul_lt_mul_of_lt_of_lt hx hy

/-- The carry-chain identity over the four partial products, stated for
arbitrary values below `B64`. All divisions and remainders are by the
literal bases, so after unfolding `B32`/`B64` and splitting the two carry
comparisons the whole statement is linear arithmetic. -/
theorem step (p00 p01 p10 p11 : Nat)
    (h00 : p00 < B64) (h01 : p01 < B64) (h10 : p10 < B64) :
    (p00 + (((p01 + p10) % B64) * B32) % B64) % B64
      + B64 * (p11 + ((p01 + p10) % B64) / B32
        + (if (p01 + p10) % B64 < p01 then 1 else 0) * B32
        + (if (p00 + (((p01 + p10) % B64) * B32) % B64) % B64 < p00 then 1
           else 0))
      = B64 * p11 + B32 * (p01 + p10) + p00
    ∧ (p00 + (((p01 + p10) % B64) * B32) % B64) % B64 < B64 := by
  simp only [B32, B64] at h00 h01 h10 ⊢
  constructor
  · split <;> split <;> omega
  · omega

/-- Schoolbook expansion of a product through the half-limb decomposition:
`a * b = B64 * (a₁b₁) + B32 * (a₀b₁ + a₁b₀) + a₀b₀`. -/
theorem expand (a b : Nat) :
    a * b = B64 * ((a / B32) * (b / B32))
      + B32 * ((a % B32) * (b / B32) + (a / B32) * (b % B32))
      + (a % B32) * (b % B32) := by
  conv => lhs; rw [← Nat.div_add_mod a B32, ← Nat.div_add_mod b B32]
  generalize a / B32 = q1
  generalize a % B32 = r1
  generalize b / B32 = q2
  generalize b % B32 = r2
  rw [show B64 = B32 * B32 from rfl]
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Structural theorem for the half-limb product circuit: the `(lo, hi)`
pair recombines to the exact 128-bit product, with `lo` a valid `u64`. -/
theorem hl_spec (a b : Nat) (ha : a < B64) (hb : b < B64) :
    (hl a b).1 + B64 * (hl a b).2 = a * b ∧ (hl a b).1 < B64 := by
  have ha0 : a % B32 < B32 := Nat.mod_lt _ (by decide)
  have hb0 : b % B32 < B32 := Nat.mod_lt _ (by decide)
  have ha1 : a / B32 < B32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr ha
  have hb1 : b / B32 < B32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hb
  have h00 : (a % B32) * (b % B32) < B64 := mul_lt_mul_of_lt_of_lt ha0 hb0
  have h01 : (a % B32) * (b / B32) < B64 := mul_lt_mul_of_lt_of_lt ha0 hb1
  have h10 : (a / B32) * (b % B32) < B64 := mul_lt_mul_of_lt_of_lt ha1 hb0
  have hstep := step ((a % B32) * (b % B32)) ((a % B32) * (b / B32))
    ((a / B32) * (b % B32)) ((a / B32) * (b / B32)) h00 h01 h10
  exact ⟨hstep.1.trans (expand a b).symm, hstep.2⟩

/-- The high word is also a valid `u64` (from `a * b < B64 * B64`). -/
theorem hl_hi_lt (a b : Nat) (ha : a < B64) (hb : b < B64) :
    (hl a b).2 < B64 := by
  have h := (hl_spec a b ha hb).1
  have hab : a * b < B64 * B64 := mul_lt_mul_of_lt_of_lt ha hb
  revert h hab
  generalize (hl a b).1 = lo
  generalize (hl a b).2 = hi
  generalize a * b = ab
  intro h hab
  simp only [B64] at h hab ⊢
  omega

end LeanCompCert.Verified.MulWide
