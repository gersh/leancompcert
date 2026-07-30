/-!
# Montgomery modular arithmetic over `Nat` (the missing reduction)

`Verified/MulWide.lean` proves the 128-bit **product** circuit (`hl_spec`).
This module supplies the missing counterpart: the **reduction**.

The proved fragment (`Verified/Reflect.lean`) has exactly one division,
`udiv`/`urem` at 64 ÷ 64 → 64.  Reducing a 128-bit product modulo a 90-bit
modulus is a 128 ÷ 64 division, which the fragment cannot express.  Barrett
reduction replaces that division by a multiplication, but still needs a
precomputed `⌊2ᵏ / N⌋` — itself a wide division — and a wide compare-and-
correct.  **Montgomery reduction needs no division at all**: every step is
one multiply mod `2⁶⁴`, one multiply-accumulate, and one exact shift by
`2⁶⁴`, and the exactness of that shift is precisely what the algebra below
proves.  Since Proth numbers `k·2ⁿ+1` are odd, the oddness precondition
Montgomery needs is free.

Everything here is plain `Nat` arithmetic: no limb vectors, no machine
words.  `redcStep` divides by `B = 2⁶⁴`, and the content of
`redcStep_mul` is that this division is *exact*, so the machine
realization (`Verified/Mont2.lean`) may implement it as dropping a limb.

The spec theorems are the analogue of `hl_spec`:

* `montMul_spec` — `montMul s N n' a b * Bˢ ≡ a * b (mod N)`, with
  `montMul … < N`;
* `montPow_rep` — square-and-multiply in the Montgomery domain computes
  the ordinary power;
* `montExp_spec` — the end-to-end statement, in ordinary modular
  arithmetic: `montExp … = a ^ e % N`.
-/

namespace LeanCompCert.Verified.Montgomery

/-- The limb base `2⁶⁴`. -/
def B : Nat := 2 ^ 64

theorem B_pos : 0 < B := by decide +kernel

theorem one_lt_B : 1 < B := by decide +kernel

/-! ## Cancelling the Montgomery factor

`Bˢ` is a power of two and every modulus considered here is odd, so `Bˢ`
is invertible mod `N`.  These two lemmas are the only number theory the
module needs; they are stated as cancellation rather than as an inverse so
that no inverse ever has to be exhibited.
-/

/-- An odd modulus dividing `2 * m` divides `m`. -/
theorem dvd_of_odd_dvd_two_mul {p m : Nat} (hodd : p % 2 = 1)
    (h : p ∣ 2 * m) : p ∣ m := by
  obtain ⟨q, hq⟩ := h
  have hq2 : q % 2 = 0 := by
    have hz : (p * q) % 2 = 0 := by
      rw [← hq]; exact Nat.mul_mod_right 2 m
    rw [Nat.mul_mod, hodd, Nat.one_mul] at hz
    omega
  obtain ⟨t, ht⟩ : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq2
  refine ⟨t, ?_⟩
  have h2 : 2 * m = 2 * (p * t) := by
    calc 2 * m = p * q := hq
      _ = p * (2 * t) := by rw [ht]
      _ = 2 * (p * t) := by rw [Nat.mul_left_comm]
  omega

/-- An odd modulus dividing `2ⁿ * m` divides `m`. -/
theorem dvd_of_odd_dvd_two_pow_mul {p : Nat} (hodd : p % 2 = 1) :
    ∀ (n m : Nat), p ∣ 2 ^ n * m → p ∣ m := by
  intro n
  induction n with
  | zero => intro m h; simpa using h
  | succ n ih =>
      intro m h
      refine ih m (dvd_of_odd_dvd_two_mul hodd ?_)
      have e : 2 ^ (n + 1) * m = 2 * (2 ^ n * m) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
      rwa [e] at h

/-- Congruence gives divisibility of the difference. -/
theorem dvd_sub_of_mod_eq {N a b : Nat} (hle : b ≤ a) (h : a % N = b % N) :
    N ∣ a - b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.mod_zero] at h
    omega
  · refine ⟨a / N - b / N, ?_⟩
    have ha := Nat.div_add_mod a N
    have hb := Nat.div_add_mod b N
    have hmul : N * (a / N - b / N) = N * (a / N) - N * (b / N) :=
      Nat.mul_sub N (a / N) (b / N)
    generalize hA : N * (a / N) = A at ha hmul
    generalize hC : N * (b / N) = C at hb hmul
    generalize hD : N * (a / N - b / N) = D at hmul
    omega

/-- Divisibility of the difference gives congruence. -/
theorem mod_eq_of_dvd_sub {N a b : Nat} (hle : b ≤ a) (h : N ∣ a - b) :
    a % N = b % N := by
  obtain ⟨c, hc⟩ := h
  have : a = b + N * c := by omega
  subst this
  exact Nat.add_mul_mod_self_left b N c

/--
**Cancellation of a power of two modulo an odd modulus.**  This is what
makes the Montgomery domain a group homomorphism: `Bˢ` may be divided out
of a congruence.
-/
theorem cancel_two_pow (N : Nat) (hodd : N % 2 = 1) (k u v : Nat)
    (h : (u * 2 ^ k) % N = (v * 2 ^ k) % N) : u % N = v % N := by
  rcases Nat.le_total v u with hle | hle
  · have hmul : v * 2 ^ k ≤ u * 2 ^ k := Nat.mul_le_mul_right _ hle
    have hd : N ∣ u * 2 ^ k - v * 2 ^ k := dvd_sub_of_mod_eq hmul h
    have hfac : u * 2 ^ k - v * 2 ^ k = 2 ^ k * (u - v) := by
      rw [Nat.mul_comm u, Nat.mul_comm v, ← Nat.mul_sub]
    rw [hfac] at hd
    exact mod_eq_of_dvd_sub hle (dvd_of_odd_dvd_two_pow_mul hodd k (u - v) hd)
  · have hmul : u * 2 ^ k ≤ v * 2 ^ k := Nat.mul_le_mul_right _ hle
    have hd : N ∣ v * 2 ^ k - u * 2 ^ k := dvd_sub_of_mod_eq hmul h.symm
    have hfac : v * 2 ^ k - u * 2 ^ k = 2 ^ k * (v - u) := by
      rw [Nat.mul_comm v, Nat.mul_comm u, ← Nat.mul_sub]
    rw [hfac] at hd
    exact (mod_eq_of_dvd_sub hle
      (dvd_of_odd_dvd_two_pow_mul hodd k (v - u) hd)).symm

/-- `B ^ s` is the power of two `2 ^ (64 * s)`. -/
theorem B_pow (s : Nat) : B ^ s = 2 ^ (64 * s) := by
  rw [B, ← Nat.pow_mul]

/-- Cancellation of the Montgomery factor `Bˢ`. -/
theorem cancel_B_pow (N : Nat) (hodd : N % 2 = 1) (s u v : Nat)
    (h : (u * B ^ s) % N = (v * B ^ s) % N) : u % N = v % N := by
  rw [B_pow] at h
  exact cancel_two_pow N hodd (64 * s) u v h

/-! ## One Montgomery reduction step -/

/--
The Montgomery multiplier: any `n'` with `N · n' ≡ −1 (mod B)`.  For a
Proth modulus `N = k·2ⁿ+1` with `n ≥ 32` this has the closed form
`n' = k·2ⁿ − 1 (mod B)`, because then `(N·n' + 1) = (k·2ⁿ)²` is divisible
by `B = 2⁶⁴` — see `Verified/Mont2.lean`.  No Newton iteration is needed.
-/
def MontMultiplier (N n' : Nat) : Prop := (N * n' + 1) % B = 0

/-- One Montgomery reduction step: add the multiple of `N` that clears the
low limb, then drop that limb. -/
def redcStep (N n' T : Nat) : Nat := (T + (T % B * n' % B) * N) / B

/-- The quantity added by one reduction step. -/
def redcM (n' T : Nat) : Nat := T % B * n' % B

theorem redcM_lt (n' T : Nat) : redcM n' T < B := Nat.mod_lt _ B_pos

/-- From `X + b·Y = b·S` conclude `b ∣ X` (no subtraction in the hypothesis). -/
private theorem dvd_of_add_mul_eq {b X Y S : Nat}
    (h : X + b * Y = b * S) : b ∣ X := by
  refine ⟨S - Y, ?_⟩
  have hmul : b * (S - Y) = b * S - b * Y := Nat.mul_sub b S Y
  generalize hbD : b * (S - Y) = D at hmul ⊢
  generalize hbY : b * Y = BY at h hmul
  generalize hbS : b * S = BS at h hmul
  omega

/-- The single additive identity behind the exactness of the Montgomery shift. -/
private theorem mont_key {b N w t q d e m T : Nat}
    (hT : b * q + t = T) (hd : b * d = N * w + 1) (he : b * e + m = t * w) :
    T + m * N + b * (N * e) = b * (q + t * d) := by
  subst hT
  calc b * q + t + m * N + b * (N * e)
      = b * q + (N * (b * e) + N * m + t) := by
        rw [Nat.mul_left_comm b N e, Nat.mul_comm m N]
        omega
    _ = b * q + (N * (b * e + m) + t) := by rw [Nat.mul_add]
    _ = b * q + (N * (t * w) + t) := by rw [he]
    _ = b * q + t * (N * w + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    _ = b * q + t * (b * d) := by rw [hd]
    _ = b * (q + t * d) := by rw [Nat.mul_add, Nat.mul_left_comm]

/--
**Exactness of the shift.**  The whole point of Montgomery reduction: the
correction `m · N` makes the low limb vanish, so dividing by `B` loses
nothing.  This is the reduction-side analogue of `MulWide.hl_spec`.
-/
theorem redcStep_mul (N n' T : Nat) (hinv : MontMultiplier N n') :
    redcStep N n' T * B = T + redcM n' T * N := by
  have hinv' : (N * n' + 1) % B = 0 := hinv
  have hT : B * (T / B) + T % B = T := Nat.div_add_mod T B
  have hd : B * ((N * n' + 1) / B) = N * n' + 1 := by
    have h := Nat.div_add_mod (N * n' + 1) B
    rw [hinv'] at h
    omega
  have he : B * (T % B * n' / B) + redcM n' T = T % B * n' :=
    Nat.div_add_mod (T % B * n') B
  have hdvd : B ∣ T + redcM n' T * N :=
    dvd_of_add_mul_eq (mont_key hT hd he)
  exact Nat.div_mul_cancel hdvd

/-- One step keeps the value in range: `T < N·X + N` becomes
`T' < N·(X/B) + N` when `B ∣ X`.  Stated in the form the iteration needs. -/
theorem redcStep_lt (N n' T X : Nat) (hinv : MontMultiplier N n')
    (h : T < N * (B * X) + N) : redcStep N n' T < N * X + N := by
  have hm := redcM_lt n' T
  have hmul := redcStep_mul N n' T hinv
  have hbound : (redcM n' T + 1) * N ≤ B * N :=
    Nat.mul_le_mul (by omega) (Nat.le_refl N)
  have hexp : (redcM n' T + 1) * N = redcM n' T * N + N := by
    rw [Nat.add_mul, Nat.one_mul]
  have hRHS : B * (N * X + N) = N * (B * X) + B * N := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  have hkey : B * redcStep N n' T < B * (N * X + N) := by
    rw [hRHS, Nat.mul_comm B (redcStep N n' T), hmul]
    omega
  exact Nat.lt_of_mul_lt_mul_left hkey

/-! ## The iterated reduction -/

/-- `s` Montgomery reduction steps: divides by `Bˢ` modulo `N`. -/
def redcIter : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, T => T
  | s + 1, N, n', T => redcIter s N n' (redcStep N n' T)

/-- **The reduction is a division by `Bˢ` modulo `N`**: the output times
`Bˢ` differs from the input by a multiple of `N`. -/
theorem redcIter_mul (N n' : Nat) (hinv : MontMultiplier N n') :
    ∀ (s T : Nat), ∃ c, redcIter s N n' T * B ^ s = T + c * N := by
  intro s
  induction s with
  | zero =>
      intro T
      refine ⟨0, ?_⟩
      show redcIter 0 N n' T * B ^ 0 = T + 0 * N
      rw [Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.add_zero]
      rfl
  | succ s ih =>
      intro T
      obtain ⟨c, hc⟩ := ih (redcStep N n' T)
      refine ⟨c * B + redcM n' T, ?_⟩
      show redcIter s N n' (redcStep N n' T) * B ^ (s + 1)
          = T + (c * B + redcM n' T) * N
      rw [Nat.pow_succ, ← Nat.mul_assoc, hc, Nat.add_mul,
        redcStep_mul N n' T hinv, Nat.add_mul, Nat.mul_right_comm c N B]
      omega

/-- **The reduction stays small**: from `T < N·Bˢ + N` the output is
below `2N`. -/
theorem redcIter_lt (N n' : Nat) (hinv : MontMultiplier N n') :
    ∀ (s T : Nat), T < N * B ^ s + N → redcIter s N n' T < N + N := by
  intro s
  induction s with
  | zero =>
      intro T h
      rw [Nat.pow_zero, Nat.mul_one] at h
      show T < N + N
      omega
  | succ s ih =>
      intro T h
      show redcIter s N n' (redcStep N n' T) < N + N
      refine ih _ (redcStep_lt N n' T (B ^ s) hinv ?_)
      have hb : B * B ^ s = B ^ (s + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hb]
      exact h

/-! ## Montgomery multiplication -/

/-- Montgomery multiplication: reduce the full product, then correct once. -/
def montMul (s N n' a b : Nat) : Nat :=
  let t := redcIter s N n' (a * b)
  if t < N then t else t - N

/-- The output is always a reduced residue. -/
theorem montMul_lt (s N n' a b : Nat) (hinv : MontMultiplier N n')
    (hN : 0 < N) (hNR : N ≤ B ^ s) (ha : a < N) (hb : b < N) :
    montMul s N n' a b < N := by
  have hab : a * b < N * B ^ s + N := by
    have h1 : (a + 1) * (b + 1) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
    have h2 : N * N ≤ N * B ^ s := Nat.mul_le_mul (Nat.le_refl N) hNR
    have h3 : (a + 1) * (b + 1) = a * b + (a + b + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.one_mul]
      omega
    omega
  have hlt := redcIter_lt N n' hinv s (a * b) hab
  simp only [montMul]
  split <;> omega

/-- Two numbers differing by multiples of `N` on both sides are congruent. -/
private theorem mod_eq_of_add_mul (N x y c d : Nat) (h : x + c * N = y + d * N) :
    x % N = y % N := by
  have h1 : (x + c * N) % N = x % N := Nat.add_mul_mod_self_right x c N
  have h2 : (y + d * N) % N = y % N := Nat.add_mul_mod_self_right y d N
  rw [← h1, ← h2, h]

/--
**The Montgomery multiplication spec** — the analogue of `hl_spec` for the
reduction side: the result, scaled back by `Bˢ`, is the ordinary product
modulo `N`.
-/
theorem montMul_spec (s N n' a b : Nat) (hinv : MontMultiplier N n')
    (hN : 0 < N) (hNR : N ≤ B ^ s) (ha : a < N) (hb : b < N) :
    (montMul s N n' a b * B ^ s) % N = (a * b) % N := by
  obtain ⟨c, hc⟩ := redcIter_mul N n' hinv s (a * b)
  simp only [montMul]
  split
  · rw [hc]
    exact Nat.add_mul_mod_self_right _ _ _
  · rename_i hge
    have hle : N ≤ redcIter s N n' (a * b) := by omega
    have hsub : (redcIter s N n' (a * b) - N) * B ^ s + B ^ s * N
        = redcIter s N n' (a * b) * B ^ s := by
      rw [Nat.sub_mul, Nat.mul_comm (B ^ s) N]
      have hmono : N * B ^ s ≤ redcIter s N n' (a * b) * B ^ s :=
        Nat.mul_le_mul hle (Nat.le_refl _)
      generalize redcIter s N n' (a * b) * B ^ s = A at hmono ⊢
      generalize N * B ^ s = C at hmono ⊢
      omega
    exact mod_eq_of_add_mul N _ _ (B ^ s) c (by rw [hsub, hc])

/-! ## The Montgomery domain -/

/-- `u` represents `x` in the Montgomery domain of modulus `N`. -/
def Rep (s N x u : Nat) : Prop := u < N ∧ u % N = (x * B ^ s) % N

/-- Montgomery multiplication is multiplication of represented values. -/
theorem montMul_rep (s N n' : Nat) (hinv : MontMultiplier N n')
    (hodd : N % 2 = 1) (hN : 0 < N) (hNR : N ≤ B ^ s)
    (x y u v : Nat) (hu : Rep s N x u) (hv : Rep s N y v) :
    Rep s N (x * y) (montMul s N n' u v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨montMul_lt s N n' u v hinv hN hNR hu1 hv1, ?_⟩
  refine cancel_B_pow N hodd s _ _ ?_
  rw [montMul_spec s N n' u v hinv hN hNR hu1 hv1, Nat.mul_mod u v, hu2, hv2,
    ← Nat.mul_mod]
  have hval : x * B ^ s * (y * B ^ s) = x * y * B ^ s * B ^ s := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hval]

/-! ## Square-and-multiply in the Montgomery domain -/

/-- Left-to-right square-and-multiply over an MSB-first bit list. -/
def montPow (s N n' abar : Nat) : List Bool → Nat → Nat
  | [], acc => acc
  | bit :: rest, acc =>
      montPow s N n' abar rest
        (if bit then montMul s N n' (montMul s N n' acc acc) abar
         else montMul s N n' acc acc)

/-- The value of an MSB-first bit list. -/
def bitsVal : List Bool → Nat
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) * 2 ^ rest.length + bitsVal rest

/-- `(a·b)ⁿ = aⁿ·bⁿ` over `Nat`. -/
private theorem npow_mul_distrib (a b : Nat) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.one_mul]
  | n + 1 => by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, npow_mul_distrib a b n]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The exponent bookkeeping for a `1` bit of the square-and-multiply loop. -/
private theorem pow_key_true (x a r bv : Nat) :
    (x * x * a) ^ (2 ^ r) * a ^ bv
      = x ^ (2 ^ (r + 1)) * a ^ (1 * 2 ^ r + bv) := by
  have e1 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
  have e2 : 1 * 2 ^ r + bv = 2 ^ r + bv := by rw [Nat.one_mul]
  rw [e1, e2, Nat.pow_add, Nat.pow_add, npow_mul_distrib, npow_mul_distrib,
    Nat.mul_assoc]

/-- The exponent bookkeeping for a `0` bit of the square-and-multiply loop. -/
private theorem pow_key_false (x a r bv : Nat) :
    (x * x) ^ (2 ^ r) * a ^ bv
      = x ^ (2 ^ (r + 1)) * a ^ (0 * 2 ^ r + bv) := by
  have e1 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
  have e2 : 0 * 2 ^ r + bv = bv := by rw [Nat.zero_mul, Nat.zero_add]
  rw [e1, e2, Nat.pow_add, npow_mul_distrib]

/-- **Square-and-multiply is correct in the Montgomery domain.** -/
theorem montPow_rep (s N n' abar a : Nat) (hinv : MontMultiplier N n')
    (hodd : N % 2 = 1) (hN : 0 < N) (hNR : N ≤ B ^ s)
    (hAbar : Rep s N a abar) :
    ∀ (bits : List Bool) (x acc : Nat), Rep s N x acc →
      Rep s N (x ^ (2 ^ bits.length) * a ^ bitsVal bits)
        (montPow s N n' abar bits acc) := by
  intro bits
  induction bits with
  | nil =>
      intro x acc hacc
      show Rep s N (x ^ (2 ^ 0) * a ^ 0) acc
      simp only [Nat.pow_zero, Nat.pow_one, Nat.mul_one]
      exact hacc
  | cons bit rest ih =>
      intro x acc hacc
      have h2 : Rep s N (x * x) (montMul s N n' acc acc) :=
        montMul_rep s N n' hinv hodd hN hNR x x acc acc hacc hacc
      cases bit with
      | true =>
          have h3 : Rep s N (x * x * a)
              (montMul s N n' (montMul s N n' acc acc) abar) :=
            montMul_rep s N n' hinv hodd hN hNR (x * x) a _ abar h2 hAbar
          have key := ih (x * x * a) _ h3
          rw [pow_key_true x a rest.length (bitsVal rest)] at key
          exact key
      | false =>
          have key := ih (x * x) _ h2
          rw [pow_key_false x a rest.length (bitsVal rest)] at key
          exact key

/-! ## End to end: ordinary modular exponentiation -/

/--
The complete Montgomery exponentiation: `abar` is the Montgomery form of
the base, `one` the Montgomery form of `1`, and the final `montMul … 1`
leaves the domain.
-/
def montExp (s N n' one abar : Nat) (bits : List Bool) : Nat :=
  montMul s N n' (montPow s N n' abar bits one) 1

/--
**The end-to-end specification, in ordinary modular arithmetic.**  This is
what a Proth certificate needs: an exponentiation modulo a wide `N`
computed without ever dividing.
-/
theorem montExp_spec (s N n' one abar a : Nat) (bits : List Bool)
    (hinv : MontMultiplier N n') (hodd : N % 2 = 1) (hN : 1 < N)
    (hNR : N ≤ B ^ s) (hOne : Rep s N 1 one) (hAbar : Rep s N a abar) :
    montExp s N n' one abar bits = a ^ bitsVal bits % N := by
  have hp := montPow_rep s N n' abar a hinv hodd (by omega) hNR hAbar bits 1 one hOne
  rw [Nat.one_pow, Nat.one_mul] at hp
  obtain ⟨hPlt, hPmod⟩ := hp
  have hspec := montMul_spec s N n' (montPow s N n' abar bits one) 1 hinv
    (by omega) hNR hPlt (by omega)
  have hlt := montMul_lt s N n' (montPow s N n' abar bits one) 1 hinv
    (by omega) hNR hPlt (by omega)
  have hcong : (montExp s N n' one abar bits * B ^ s) % N
      = (a ^ bitsVal bits * B ^ s) % N := by
    show (montMul s N n' (montPow s N n' abar bits one) 1 * B ^ s) % N
        = (a ^ bitsVal bits * B ^ s) % N
    rw [hspec, Nat.mul_one, hPmod]
  have hfin := cancel_B_pow N hodd s _ _ hcong
  rw [← hfin]
  exact (Nat.mod_eq_of_lt hlt).symm

end LeanCompCert.Verified.Montgomery
