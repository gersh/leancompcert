import LeanCompCert.Verified.MulWide

/-!
# The two-limb accumulator, and its carry

`Verified/MulWide.lean` gives the 64×64→128 *product* as a limb pair.  What it
does not give — and what the `ψ` residue needs — is a two-limb **add with
carry**, because the accumulator `Σ lnFix(p) − 2^S·n` does not fit in one
64-bit word.

## Why one word is not enough

The residual form is forced: the direct form `2^S·ψ(n)` reaches `2^S·10¹³` and
caps `S` at `20`.  In residual form the reduced family itself bounds the
accumulator by `2^S·√2·√n = 2^S·4.472·10⁶`, so a single `u64` allows `S ≤ 40`
(at `S = 41` the bound is `9.83·10¹⁸ > 2⁶³`).  At `S = 40` the enclosure the
`logFold` bracket carries — `4` ulps per term over `π*(10¹³) = 346 065 765 710`
terms — is `1.259` absolute, i.e. `3.98·10⁻⁷` in the ratio the family prints to
eight decimals.  The margin behind `0.79059276` is at most `10⁻⁸`, which needs
`2^S ≥ 4.377·10¹³`, i.e. `S ≥ 45.32`.  One word is short by a factor of `40`.

At `S = 48` the accumulator is 71 bits: two words and a carry.

## The carry is a proved comparison, not a flag

The fragment has no carry flag and no branches.  For `u, v < 2⁶⁴` the truncated
sum `(u + v) mod 2⁶⁴` is below `v` exactly when the untruncated sum overflowed,
so `if lo < v then 1 else 0` **is** the carry bit (`carry_bit`).  That is the
same trick `MulWide.step` uses, isolated here and proved once.

Four fragment instructions realize a full two-limb add:

```
  lo ← lo + a.lo          -- add
  c  ← lo < a.lo          -- lt   (a.lo is still the old value)
  hi ← hi + a.hi          -- add
  hi ← hi + c             -- add
```

and three realize the one-word specializations `addWideLo` / `subWideLo`,
which is what the accumulator loop actually uses (`+ lnFix(p)` once per prime
power, `− 2^S·gap` once per test point).

## What is proved

`addWide_spec` and `subWide_spec` are the machine statements: the limb pair
recombines to the exact `mod 2¹²⁸` result, mirroring `denoteOp` at both limbs.
`addWide_exact` and `subWide_exact` are the no-wrap corollaries the accumulation
theorem uses, and `sumWide_spec` runs the fold: a list of `u64` values whose
sum is below `2¹²⁸` accumulates *exactly*, with no hypothesis about how the
individual carries interact.
-/

namespace LeanCompCert.Verified.AddWide

open LeanCompCert.Verified

/-- `2⁶⁴`, the limb base. -/
abbrev B64 : Nat := MulWide.B64

/-- `2¹²⁸`, the two-limb modulus. -/
def B128 : Nat := 340282366920938463463374607431768211456

theorem B128_eq : B128 = B64 * B64 := by decide

theorem B64_pos : 0 < B64 := by decide

/-- The number a limb pair `(lo, hi)` stands for. -/
def wval (x : Nat × Nat) : Nat := x.1 + B64 * x.2

/-- A limb pair is *valid* when both limbs are `u64`s — the invariant every
fragment register carries. -/
def Ok (x : Nat × Nat) : Prop := x.1 < B64 ∧ x.2 < B64

theorem wval_lt {x : Nat × Nat} (h : Ok x) : wval x < B128 := by
  obtain ⟨h1, h2⟩ := h
  simp only [wval, B128, B64, MulWide.B64] at h1 h2 ⊢
  have : B64 * x.2 ≤ B64 * (18446744073709551616 - 1) := by
    exact Nat.mul_le_mul_left _ (by omega)
  simp only [B64, MulWide.B64] at this
  omega

/-! ## The carry -/

/-- **The carry is a comparison.**  For two `u64`s the truncated sum is below
the second summand exactly when the untruncated sum overflowed, so the
comparison `lo < v` — one fragment instruction, branchless — computes the
carry-out bit. -/
theorem carry_bit (u v : Nat) (hu : u < B64) (hv : v < B64) :
    (if (u + v) % B64 < v then 1 else 0) = (u + v) / B64 := by
  simp only [B64, MulWide.B64] at hu hv ⊢
  split <;> omega

/-- **The borrow is a comparison.**  Dually, `u < v` is the borrow-out of
`u − v` at one limb, and the fragment's `sub` — `(u + (2⁶⁴ − v)) mod 2⁶⁴` —
is the true difference in each of the two cases. -/
theorem borrow_bit (u v : Nat) (hu : u < B64) (hv : v < B64) :
    (u + (B64 - v)) % B64 = if u < v then u + B64 - v else u - v := by
  simp only [B64, MulWide.B64] at hu hv ⊢
  split <;> omega

/-- Splitting a `mod K²` reduction into its two limbs: with the low limb
already reduced, only the high limb is touched. -/
theorem split_mod_gen (K lo T : Nat) (h : lo < K) :
    (lo + K * T) % (K * K) = lo + K * (T % K) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le lo) h
  have hstep : lo + K * T = (lo + K * (T % K)) + (K * K) * (T / K) := by
    conv => lhs; rw [← Nat.div_add_mod T K]
    simp only [Nat.mul_add, ← Nat.mul_assoc]
    omega
  have hlt : lo + K * (T % K) < K * K := by
    have hm : T % K < K := Nat.mod_lt _ hK
    have h1 : K * (T % K) ≤ K * (K - 1) := Nat.mul_le_mul_left K (by omega)
    have h2 : K * (K - 1) + K = K * K := by
      have hk1 : (K - 1) + 1 = K := by omega
      calc K * (K - 1) + K = K * ((K - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = K * K := by rw [hk1]
    omega
  rw [hstep, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Splitting a `mod 2¹²⁸` reduction into its two limbs. -/
theorem split_mod (lo T : Nat) (h : lo < B64) :
    (lo + B64 * T) % B128 = lo + B64 * (T % B64) := by
  rw [B128_eq]; exact split_mod_gen B64 lo T h

/-! ## Two-limb addition -/

/-- **The two-limb accumulator step.**  Every operation is `u64`-realizable:
two `add`s of the limbs, the carry as one `lt`, and one more `add`.  The
double reduction of the high limb mirrors the two `add` instructions exactly,
so the definition *is* the instruction sequence. -/
def addWide (x a : Nat × Nat) : Nat × Nat :=
  let lo := (x.1 + a.1) % B64
  let c := if lo < a.1 then 1 else 0
  (lo, ((x.2 + a.2) % B64 + c) % B64)

/-- Adding a single `u64` — the shape the accumulator loop uses for
`+ lnFix(p)`.  Three instructions: `add`, `lt`, `add`. -/
def addWideLo (x : Nat × Nat) (a : Nat) : Nat × Nat := addWide x (a, 0)

theorem addWide_ok (x a : Nat × Nat) : Ok (addWide x a) :=
  ⟨Nat.mod_lt _ B64_pos, Nat.mod_lt _ B64_pos⟩

/-- **Structural theorem for the two-limb accumulator.**  The output pair
recombines to the exact `mod 2¹²⁸` sum — the analogue of `MulWide.hl_spec`
for addition. -/
theorem addWide_spec (x a : Nat × Nat) (hx : Ok x) (ha : Ok a) :
    wval (addWide x a) = (wval x + wval a) % B128 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ha1, ha2⟩ := ha
  have hc : (if (x.1 + a.1) % B64 < a.1 then 1 else 0) = (x.1 + a.1) / B64 :=
    carry_bit x.1 a.1 hx1 ha1
  have hhi : ((x.2 + a.2) % B64 + (x.1 + a.1) / B64) % B64
      = (x.2 + a.2 + (x.1 + a.1) / B64) % B64 := by
    rw [Nat.mod_add_mod]
  have hsum : wval x + wval a
      = (x.1 + a.1) % B64 + B64 * (x.2 + a.2 + (x.1 + a.1) / B64) := by
    simp only [wval]
    have := Nat.div_add_mod (x.1 + a.1) B64
    simp only [Nat.mul_add]
    omega
  show (x.1 + a.1) % B64 + B64 * (((x.2 + a.2) % B64
      + (if (x.1 + a.1) % B64 < a.1 then 1 else 0)) % B64) = _
  rw [hc, hhi, hsum, split_mod _ _ (Nat.mod_lt _ B64_pos)]

/-- The no-wrap corollary: below `2¹²⁸` the accumulator is exact. -/
theorem addWide_exact (x a : Nat × Nat) (hx : Ok x) (ha : Ok a)
    (h : wval x + wval a < B128) :
    wval (addWide x a) = wval x + wval a := by
  rw [addWide_spec x a hx ha, Nat.mod_eq_of_lt h]

theorem wval_lo (a : Nat) : wval (a, 0) = a := by simp [wval]

theorem addWideLo_exact (x : Nat × Nat) (a : Nat) (hx : Ok x) (ha : a < B64)
    (h : wval x + a < B128) : wval (addWideLo x a) = wval x + a := by
  have := addWide_exact x (a, 0) hx ⟨ha, B64_pos⟩ (by rwa [wval_lo])
  rwa [wval_lo] at this

theorem addWideLo_ok (x : Nat × Nat) (a : Nat) : Ok (addWideLo x a) :=
  addWide_ok x (a, 0)

/-! ## Two-limb subtraction

`.sub` in the fragment is `(a + (2⁶⁴ − b)) mod 2⁶⁴`, so the borrow chain is the
mirror image of the carry chain and costs the same four instructions.
-/

/-- Two-limb subtract with borrow, in the fragment's own `sub` semantics. -/
def subWide (x a : Nat × Nat) : Nat × Nat :=
  let b := if x.1 < a.1 then 1 else 0
  ((x.1 + (B64 - a.1)) % B64,
    ((x.2 + (B64 - a.2)) % B64 + (B64 - b)) % B64)

/-- Subtracting a single `u64` — the shape the accumulator loop uses for
`− 2^S·gap`.  Three instructions: `lt`, `sub`, `sub`. -/
def subWideLo (x : Nat × Nat) (a : Nat) : Nat × Nat := subWide x (a, 0)

theorem subWide_ok (x a : Nat × Nat) : Ok (subWide x a) :=
  ⟨Nat.mod_lt _ B64_pos, Nat.mod_lt _ B64_pos⟩

/-- **The two-limb difference is exact whenever it is defined.**  No borrow
escapes: with `wval a ≤ wval x` the pair recombines to the true difference. -/
theorem subWide_exact (x a : Nat × Nat) (hx : Ok x) (ha : Ok a)
    (h : wval a ≤ wval x) : wval (subWide x a) = wval x - wval a := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ha1, ha2⟩ := ha
  simp only [wval] at h
  -- the high limbs are ordered, else the value order would already fail
  have hhi : a.2 ≤ x.2 := by
    cases Nat.lt_or_ge x.2 a.2 with
    | inl hcon =>
        exfalso
        have hstep : B64 * (x.2 + 1) ≤ B64 * a.2 := Nat.mul_le_mul_left B64 hcon
        simp only [Nat.mul_add, Nat.mul_one] at hstep
        simp only [B64, MulWide.B64] at hx1 hstep h
        omega
    | inr hok => exact hok
  -- the borrow never underflows the high limb
  have hborrow : (if x.1 < a.1 then 1 else 0) ≤ x.2 - a.2 := by
    by_cases hlt : x.1 < a.1
    · rw [if_pos hlt]
      cases Nat.lt_or_ge a.2 x.2 with
      | inl hlt2 => omega
      | inr hge2 =>
          have hEq : x.2 = a.2 := by omega
          rw [hEq] at h
          omega
    · rw [if_neg hlt]; omega
  have e1 : (x.1 + (B64 - a.1)) % B64
      = if x.1 < a.1 then x.1 + B64 - a.1 else x.1 - a.1 :=
    borrow_bit x.1 a.1 hx1 ha1
  have e2 : (x.2 + (B64 - a.2)) % B64 = x.2 - a.2 := by
    simp only [B64, MulWide.B64] at hx2 ha2 hhi ⊢
    omega
  have e3 : ((x.2 - a.2) + (B64 - (if x.1 < a.1 then 1 else 0))) % B64
      = x.2 - a.2 - (if x.1 < a.1 then 1 else 0) := by
    revert hborrow
    simp only [B64, MulWide.B64] at hx2 ha2 hhi ⊢
    split <;> intro hb <;> omega
  show (x.1 + (B64 - a.1)) % B64
      + B64 * (((x.2 + (B64 - a.2)) % B64
        + (B64 - (if x.1 < a.1 then 1 else 0))) % B64)
      = x.1 + B64 * x.2 - (a.1 + B64 * a.2)
  rw [e1, e2, e3]
  -- `B64 * (x.2 − a.2 − d)` is expanded once; the rest is linear.
  have hd0 : B64 * (x.2 - a.2 - 0) + B64 * a.2 = B64 * x.2 := by
    have : (x.2 - a.2 - 0) + a.2 = x.2 := by omega
    rw [← Nat.mul_add, this]
  have hd1 : x.1 < a.1 → B64 * (x.2 - a.2 - 1) + B64 * a.2 + B64 = B64 * x.2 := by
    intro hlt
    have hge : 1 ≤ x.2 - a.2 := by
      have := hborrow; rw [if_pos hlt] at this; omega
    rw [← Nat.mul_add, ← Nat.mul_succ]
    congr 1
    omega
  revert hborrow
  simp only [B64, MulWide.B64] at hx1 hx2 ha1 ha2 hhi h hd0 hd1 ⊢
  split
  · intro _
    have := hd1 (by assumption)
    omega
  · intro _; omega

theorem subWideLo_exact (x : Nat × Nat) (a : Nat) (hx : Ok x) (ha : a < B64)
    (h : a ≤ wval x) : wval (subWideLo x a) = wval x - a := by
  have := subWide_exact x (a, 0) hx ⟨ha, B64_pos⟩ (by rwa [wval_lo])
  rwa [wval_lo] at this

theorem subWideLo_ok (x : Nat × Nat) (a : Nat) : Ok (subWideLo x a) :=
  subWide_ok x (a, 0)

/-! ## The fold

The accumulator is used in a loop, so the statement that matters is the one
about the whole fold: a list of `u64`s whose total is below `2¹²⁸` accumulates
**exactly**.  There is no hypothesis about how the carries interact — the
induction carries the exact value, not a bound.
-/

/-- The two-limb accumulation of a list of `u64` values, from a given
carry-in. -/
def sumWideFrom (acc : Nat × Nat) (l : List Nat) : Nat × Nat :=
  l.foldl addWideLo acc

/-- The two-limb accumulation from zero: the artifact's `Σ lnFix`. -/
def sumWide (l : List Nat) : Nat × Nat := sumWideFrom (0, 0) l

@[simp] theorem sumWideFrom_nil (acc : Nat × Nat) : sumWideFrom acc [] = acc := rfl

@[simp] theorem sumWideFrom_cons (acc : Nat × Nat) (v : Nat) (l : List Nat) :
    sumWideFrom acc (v :: l) = sumWideFrom (addWideLo acc v) l := rfl

/-- **The accumulation theorem.**  Every partial sum stays a valid limb pair,
and the final pair's value is the ordinary `Nat` sum. -/
theorem sumWideFrom_spec (l : List Nat) (h : ∀ v ∈ l, v < B64) :
    ∀ acc : Nat × Nat, Ok acc → wval acc + l.sum < B128 →
      wval (sumWideFrom acc l) = wval acc + l.sum ∧ Ok (sumWideFrom acc l) := by
  induction l with
  | nil => intro acc hacc _; exact ⟨by simp, hacc⟩
  | cons v t ih =>
      intro acc hacc hb
      have hv : v < B64 := h v (List.mem_cons_self ..)
      have hsum : (v :: t).sum = v + t.sum := List.sum_cons
      have hstep : wval (addWideLo acc v) = wval acc + v :=
        addWideLo_exact acc v hacc hv (by omega)
      have hrest := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
        (addWideLo acc v) (addWideLo_ok acc v) (by rw [hstep]; omega)
      rw [sumWideFrom_cons]
      exact ⟨hrest.1.trans (by rw [hstep]; omega), hrest.2⟩

theorem sumWide_spec (l : List Nat) (h : ∀ v ∈ l, v < B64) (hb : l.sum < B128) :
    wval (sumWide l) = l.sum ∧ Ok (sumWide l) := by
  have := sumWideFrom_spec l h (0, 0) ⟨B64_pos, B64_pos⟩ (by simpa [wval] using hb)
  simpa [sumWide, wval] using this

/-! ## Kernel checks

The carry really fires, at both limbs, and the fold really is the sum.
-/

namespace Check

/-- `(2⁶⁴ − 1) + 1` carries into the high limb. -/
example : addWideLo (18446744073709551615, 0) 1 = (0, 1) := by decide

/-- …and the high limb wraps at `2¹²⁸`, as `mod 2¹²⁸` says it must. -/
example : addWideLo (18446744073709551615, 18446744073709551615) 1 = (0, 0) := by
  decide

/-- The borrow fires the other way. -/
example : subWideLo (0, 1) 1 = (18446744073709551615, 0) := by decide

/-- A 71-bit accumulator value — the size the `ψ` residual reaches at
`n = 10¹³`, `S = 48` — recombines exactly. -/
example : wval (sumWide [18446744073709551615, 18446744073709551615,
    18446744073709551615]) = 55340232221128654845 := by decide

example : wval (subWideLo (sumWide [1000000000000000000, 1000000000000000000,
    1000000000000000000]) 500000000000000000) = 2500000000000000000 := by decide

end Check

end LeanCompCert.Verified.AddWide
