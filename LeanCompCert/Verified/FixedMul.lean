/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.MulWide

/-!
# Fixed-point multiply from the widening product

A fixed-point multiply at scale `2^S` is `(a * b) >>> S`.  The obstacle on a
64-bit machine is that `a * b` does not fit in a register, so the shift cannot
be done after the multiply — the product has to be consumed in halves.

`MulWide.hl` already supplies those halves: `lo + 2⁶⁴·hi = a·b`.  The
observation this module records is that the shift then splits **exactly**,
with no rounding decision anywhere:

```
(a·b) >>> S  =  hi · 2^(64-S)  +  lo >>> S
```

★ This is an identity, not an approximation.  Writing `lo = q·2^S + r` with
`r < 2^S` gives `a·b = 2^S·(q + 2^(64-S)·hi) + r`, and the same `r` is the
remainder of the whole product — so the truncation error of the composite
operation is exactly the truncation error of `lo >>> S`, below one ulp.

⚠ The result is only a valid register value when `a·b < 2^(64+S)`.  That is a
constraint on the *caller*, not on this identity, and it is where a fixed-point
program must budget its headroom; `fpMul_lt` states it.

## Why this is the primitive worth having

For the Riemann–Siegel main sum sampled by a fixed rotation, every sample is a
long chain of complex multiplies and nothing else — no transcendental
evaluation at all.  So the entire numerical core of that evaluator reduces to
this one operation, iterated, and its error contract is a single ulp per
product.
-/

namespace LeanCompCert.Verified.FixedMul

open LeanCompCert.Verified.MulWide

/-- The fixed-point product at scale `2^S`, from the two halves of the
widening product. -/
def fpMul (S a b : Nat) : Nat :=
  (hl a b).2 * 2 ^ (64 - S) + (hl a b).1 / 2 ^ S

/-- **The shift splits exactly.**  No rounding choice is made here; the only
truncation is the one already inside `lo / 2^S`. -/
theorem fpMul_eq (S a b : Nat) (hS : S ≤ 64) (ha : a < B64) (hb : b < B64) :
    fpMul S a b = a * b / 2 ^ S := by
  have h := hl_spec a b ha hb
  have hpow : (2 : Nat) ^ S * 2 ^ (64 - S) = B64 := by
    rw [← Nat.pow_add]
    have : S + (64 - S) = 64 := by omega
    rw [this]
    rfl
  have hSpos : 0 < 2 ^ S := Nat.two_pow_pos S
  have hrw : (hl a b).1 + B64 * (hl a b).2
      = (hl a b).1 + 2 ^ S * (2 ^ (64 - S) * (hl a b).2) := by
    rw [← Nat.mul_assoc, hpow]
  unfold fpMul
  rw [← h.1, hrw, Nat.add_mul_div_left _ _ hSpos, Nat.add_comm,
    Nat.mul_comm (hl a b).2 (2 ^ (64 - S))]

/-- **The caller's obligation.**  The fixed-point product fits in a register
exactly when the full product fits in `2^(64+S)`.

⚠ Stated separately because it is the hypothesis a program must arrange, and
folding it into `fpMul_eq` would hide the fact that the identity itself needs
no such bound. -/
theorem fpMul_lt (S a b : Nat) (hS : S ≤ 64) (ha : a < B64) (hb : b < B64)
    (hfit : a * b < 2 ^ (64 + S)) :
    fpMul S a b < B64 := by
  rw [fpMul_eq S a b hS ha hb]
  have hSpos : 0 < 2 ^ S := Nat.two_pow_pos S
  have hB : B64 = 2 ^ 64 := by rfl
  have hsplit : (2 : Nat) ^ (64 + S) = 2 ^ 64 * 2 ^ S := Nat.pow_add 2 64 S
  rw [hB]
  rw [Nat.div_lt_iff_lt_mul hSpos]
  omega

/-- **The remainder is below one ulp**, which is the error contract a
`claude_math`-side bracket consumes: the computed value times `2^S` differs
from the exact product by less than `2^S`. -/
theorem fpMul_error (S a b : Nat) (hS : S ≤ 64) (ha : a < B64) (hb : b < B64) :
    a * b - fpMul S a b * 2 ^ S < 2 ^ S ∧ fpMul S a b * 2 ^ S ≤ a * b := by
  have hSpos : 0 < 2 ^ S := Nat.two_pow_pos S
  rw [fpMul_eq S a b hS ha hb]
  have hd : 2 ^ S * (a * b / 2 ^ S) + (a * b) % 2 ^ S = a * b :=
    Nat.div_add_mod _ _
  have hm : (a * b) % 2 ^ S < 2 ^ S := Nat.mod_lt _ hSpos
  have hcomm : (a * b / 2 ^ S) * 2 ^ S = 2 ^ S * (a * b / 2 ^ S) :=
    Nat.mul_comm _ _
  exact ⟨by omega, by omega⟩

/-! ## Checks

⚠ An identity proved but never evaluated is a place for an off-by-one in the
*statement* to survive.  These are concrete instances. -/

/-- Scale `62`, the working scale: `2^62 · 2^62 >>> 62 = 2^62`, i.e. `1.0 · 1.0
= 1.0` in fixed point. -/
example : fpMul 62 (2 ^ 62) (2 ^ 62) = 2 ^ 62 := by rfl

/-- Truncation really truncates: `(2^62 - 1)^2 >>> 62` is one ulp below
`2^62 - 2`. -/
example : fpMul 62 (2 ^ 62 - 1) (2 ^ 62 - 1) = 2 ^ 62 - 2 := by rfl

/-- ⚠ And the caller's bound genuinely binds: `2^63 · 2^63 >>> 62` is exactly
`B64`, which is *not* a register value.  So `fpMul_lt`'s hypothesis cannot be
dropped — the identity still holds, but the result no longer fits. -/
example : fpMul 62 (2 ^ 63) (2 ^ 63) = B64 := by rfl

#print axioms fpMul_eq
#print axioms fpMul_lt
#print axioms fpMul_error

end LeanCompCert.Verified.FixedMul
