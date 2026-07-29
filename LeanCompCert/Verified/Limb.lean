import LeanCompCert.Verified.Reflect

/-!
# Statically-sized arbitrary-precision arithmetic (limb layer)

The goldbach certificate corpus needs integers far beyond 64 bits
(fixed-point scales at `2⁶⁴`, intermediates near `2⁹⁷`, dyadic interval
mantissas, and — at the extreme — 143-kbit rational seeds), but never
*unbounded* precision: every width is statically known per certificate. So
"arbitrary arithmetic" means statically-sized limb vectors, and this module
provides the mathematical core: little-endian `u64` limb vectors with
machine-checked value-denotation theorems for ripple carry and borrow.

Each limb operation is per-limb `u64` arithmetic with a carry chain —
exactly the pattern already proved and compiled at two limbs by the wide
Mertens certificate (carry = proved `<` comparison widened by a proved
cast) — so every operation here realizes in the reflection DSL as a
fixed-shape instruction block whose `denote` computes these functions, and
`Program.evalCC_compile` transports correctness to the CCIR and C models.

Comparison falls out of subtraction: `xs < ys` is the borrow bit of
`sbb xs ys 0` (`lt_iff`). Multiplication (schoolbook over 32-bit
half-limbs), dyadic scaling (shifts), and outward-rounded division (Newton
reciprocal, with interval rounding absorbing the approximation) are
`O(limbs²)` compositions of these primitives over the same value
denotation.
-/

namespace LeanCompCert.Verified.Limb

/-- Little-endian limb vectors: `val [l₀, l₁, …] = l₀ + 2⁶⁴·l₁ + …`. -/
abbrev Limbs := List Nat

def Limbs.val : Limbs → Nat
  | [] => 0
  | limb :: rest => limb + 2 ^ 64 * Limbs.val rest

/-- Well-formed limb vectors have every limb below the base. -/
def Limbs.WF (limbs : Limbs) : Prop := ∀ limb ∈ limbs, limb < 2 ^ 64

theorem val_lt {limbs : Limbs} (hWF : Limbs.WF limbs) :
    (Limbs.val limbs) < (2 ^ 64) ^ limbs.length := by
  induction limbs with
  | nil => simp [Limbs.val]
  | cons limb rest ih =>
      have hLimb : limb < 2 ^ 64 := hWF limb (by simp)
      have hRest : (Limbs.val rest) < (2 ^ 64) ^ rest.length :=
        ih fun l hl => hWF l (by simp [hl])
      show limb + 2 ^ 64 * (Limbs.val rest) < (2 ^ 64) ^ (rest.length + 1)
      rw [show ((2 ^ 64) : Nat) ^ (rest.length + 1) =
        2 ^ 64 * (2 ^ 64) ^ rest.length from by
          rw [Nat.pow_succ, Nat.mul_comm]]
      omega

/-- Ripple add with carry: same-length inputs, final carry-out. -/
def adc : Limbs → Limbs → Nat → Limbs × Nat
  | [], _, carry => ([], carry)
  | _ :: _, [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
      ((x + y + carry) % 2 ^ 64 ::
        (adc xs ys ((x + y + carry) / 2 ^ 64)).1,
       (adc xs ys ((x + y + carry) / 2 ^ 64)).2)

/--
**Ripple-carry correctness**: the output limbs plus the weighted carry-out
denote exactly the sum. This is the reusable induction core for all wide
addition.
-/
theorem adc_val (xs : Limbs) :
    ∀ (ys : Limbs) (carry : Nat), xs.length = ys.length →
    (Limbs.val (adc xs ys carry).1) +
        (2 ^ 64) ^ xs.length * (adc xs ys carry).2 =
      (Limbs.val xs) + (Limbs.val ys) + carry := by
  induction xs with
  | nil =>
      intro ys carry hLen
      cases ys with
      | nil => simp [adc, Limbs.val]
      | cons y ys => simp at hLen
  | cons x xs ih =>
      intro ys carry hLen
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLen
          have ihStep := ih ys ((x + y + carry) / 2 ^ 64) hLen
          have hdm := Nat.mod_add_div (x + y + carry) (2 ^ 64)
          show ((x + y + carry) % 2 ^ 64 +
              2 ^ 64 * (Limbs.val (adc xs ys ((x + y + carry) / 2 ^ 64)).1)) +
            (2 ^ 64) ^ (xs.length + 1) *
              (adc xs ys ((x + y + carry) / 2 ^ 64)).2 =
            (x + 2 ^ 64 * (Limbs.val xs)) + (y + 2 ^ 64 * (Limbs.val ys)) + carry
          rw [show ((2 ^ 64) : Nat) ^ (xs.length + 1) =
            2 ^ 64 * (2 ^ 64) ^ xs.length from by
              rw [Nat.pow_succ, Nat.mul_comm]]
          rw [Nat.mul_assoc]
          generalize (2 ^ 64) ^ xs.length *
            (adc xs ys ((x + y + carry) / 2 ^ 64)).2 = weightedCarry
            at ihStep ⊢
          omega

/-- Output limbs of `adc` are well formed. -/
theorem adc_wf (xs : Limbs) :
    ∀ (ys : Limbs) (carry : Nat), Limbs.WF (adc xs ys carry).1 := by
  induction xs with
  | nil =>
      intro ys carry limb hMem
      simp [adc] at hMem
  | cons x xs ih =>
      intro ys carry
      cases ys with
      | nil =>
          intro limb hMem
          simp [adc] at hMem
      | cons y ys =>
          intro limb hMem
          simp only [adc, List.mem_cons] at hMem
          cases hMem with
          | inl hHead =>
              subst hHead
              exact Nat.mod_lt _ (by decide)
          | inr hTail =>
              exact ih ys ((x + y + carry) / 2 ^ 64) limb hTail

/-- The carry-out of `adc` stays a flag when the inputs are well formed. -/
theorem adc_carry_le (xs : Limbs) :
    ∀ (ys : Limbs) (carry : Nat),
      Limbs.WF xs → Limbs.WF ys → carry ≤ 1 → (adc xs ys carry).2 ≤ 1 := by
  induction xs with
  | nil =>
      intro ys carry _ _ hCarry
      exact hCarry
  | cons x xs ih =>
      intro ys carry hWFx hWFy hCarry
      cases ys with
      | nil => exact hCarry
      | cons y ys =>
          have hx : x < 2 ^ 64 := hWFx x (by simp)
          have hy : y < 2 ^ 64 := hWFy y (by simp)
          show (adc xs ys ((x + y + carry) / 2 ^ 64)).2 ≤ 1
          exact ih ys _
            (fun l hl => hWFx l (by simp [hl]))
            (fun l hl => hWFy l (by simp [hl]))
            (by omega)

/--
One limb of subtraction: the difference limb and the borrow-out. The borrow
is a comparison — exactly the machine realization (`borrow = x < y + bin`
is a proved `<` instruction widened by a proved cast) — and the guarded
formulation keeps kernel reduction stuck on free variables.
-/
def sbbStep (x y borrow : Nat) : Nat × Nat :=
  if x < y + borrow then (x + 2 ^ 64 - y - borrow, 1)
  else (x - y - borrow, 0)

theorem sbbStep_borrow_le (x y borrow : Nat) :
    (sbbStep x y borrow).2 ≤ 1 := by
  unfold sbbStep
  split <;> simp

theorem sbbStep_spec (x y borrow : Nat) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (hb : borrow ≤ 1) :
    (sbbStep x y borrow).1 + y + borrow =
        x + 2 ^ 64 * (sbbStep x y borrow).2 ∧
      (sbbStep x y borrow).1 < 2 ^ 64 := by
  unfold sbbStep
  split <;> constructor <;> omega

/-- Ripple subtract with borrow: same-length inputs, final borrow-out. -/
def sbb : Limbs → Limbs → Nat → Limbs × Nat
  | [], _, borrow => ([], borrow)
  | _ :: _, [], borrow => ([], borrow)
  | x :: xs, y :: ys, borrow =>
      ((sbbStep x y borrow).1 :: (sbb xs ys (sbbStep x y borrow).2).1,
       (sbb xs ys (sbbStep x y borrow).2).2)

/--
**Ripple-borrow correctness**: subtraction with borrow satisfies
`result + subtrahend + borrowIn = minuend + weight·borrowOut`.
-/
theorem sbb_val (xs : Limbs) :
    ∀ (ys : Limbs) (borrow : Nat), xs.length = ys.length →
      Limbs.WF xs → Limbs.WF ys → borrow ≤ 1 →
    (Limbs.val (sbb xs ys borrow).1) + (Limbs.val ys) + borrow =
      (Limbs.val xs) + (2 ^ 64) ^ xs.length * (sbb xs ys borrow).2 := by
  induction xs with
  | nil =>
      intro ys borrow hLen _ _ _
      cases ys with
      | nil => simp [sbb, Limbs.val]
      | cons y ys => simp at hLen
  | cons x xs ih =>
      intro ys borrow hLen hWFx hWFy hBorrow
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLen
          have hx : x < 2 ^ 64 := hWFx x (by simp)
          have hy : y < 2 ^ 64 := hWFy y (by simp)
          obtain ⟨hStep, _⟩ := sbbStep_spec x y borrow hx hy hBorrow
          have hNext := sbbStep_borrow_le x y borrow
          have ihStep := ih ys (sbbStep x y borrow).2
            hLen
            (fun l hl => hWFx l (by simp [hl]))
            (fun l hl => hWFy l (by simp [hl]))
            hNext
          show ((sbbStep x y borrow).1 +
              2 ^ 64 * (Limbs.val (sbb xs ys (sbbStep x y borrow).2).1)) +
            (y + 2 ^ 64 * (Limbs.val ys)) + borrow =
            (x + 2 ^ 64 * (Limbs.val xs)) +
              (2 ^ 64) ^ (xs.length + 1) *
                (sbb xs ys (sbbStep x y borrow).2).2
          rw [show ((2 ^ 64) : Nat) ^ (xs.length + 1) =
            2 ^ 64 * (2 ^ 64) ^ xs.length from by
              rw [Nat.pow_succ, Nat.mul_comm]]
          rw [Nat.mul_assoc]
          generalize hWeighted : (2 ^ 64) ^ xs.length *
            (sbb xs ys (sbbStep x y borrow).2).2 = weightedBorrow
            at ihStep ⊢
          omega

/-- Output limbs of `sbb` are well formed on well-formed inputs. -/
theorem sbb_wf (xs : Limbs) :
    ∀ (ys : Limbs) (borrow : Nat),
      Limbs.WF xs → Limbs.WF ys → borrow ≤ 1 →
      Limbs.WF (sbb xs ys borrow).1 := by
  induction xs with
  | nil =>
      intro ys borrow _ _ _ limb hMem
      simp [sbb] at hMem
  | cons x xs ih =>
      intro ys borrow hWFx hWFy hBorrow
      cases ys with
      | nil =>
          intro limb hMem
          simp [sbb] at hMem
      | cons y ys =>
          intro limb hMem
          simp only [sbb, List.mem_cons] at hMem
          cases hMem with
          | inl hHead =>
              subst hHead
              exact (sbbStep_spec x y borrow
                (hWFx x (by simp)) (hWFy y (by simp)) hBorrow).2
          | inr hTail =>
              exact ih ys (sbbStep x y borrow).2
                (fun l hl => hWFx l (by simp [hl]))
                (fun l hl => hWFy l (by simp [hl]))
                (sbbStep_borrow_le x y borrow) limb hTail

/-- The borrow-out stays a flag. -/
theorem sbb_borrow_le (xs : Limbs) :
    ∀ (ys : Limbs) (borrow : Nat), borrow ≤ 1 →
      (sbb xs ys borrow).2 ≤ 1 := by
  induction xs with
  | nil =>
      intro ys borrow hBorrow
      exact hBorrow
  | cons x xs ih =>
      intro ys borrow hBorrow
      cases ys with
      | nil => exact hBorrow
      | cons y ys =>
          show (sbb xs ys (sbbStep x y borrow).2).2 ≤ 1
          exact ih ys (sbbStep x y borrow).2 (sbbStep_borrow_le x y borrow)

/-- Subtraction preserves length on same-length inputs. -/
theorem sbb_length (xs : Limbs) :
    ∀ (ys : Limbs) (borrow : Nat), xs.length = ys.length →
      (sbb xs ys borrow).1.length = xs.length := by
  induction xs with
  | nil =>
      intro ys borrow hLen
      cases ys with
      | nil => simp [sbb]
      | cons y ys => simp at hLen
  | cons x xs ih =>
      intro ys borrow hLen
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLen
          simp only [sbb, List.length_cons, Nat.succ.injEq]
          exact ih ys _ hLen

/-- Wide unsigned comparison is the borrow bit of subtraction. -/
def isLt (xs ys : Limbs) : Bool := (sbb xs ys 0).2 = 1

/--
**Comparison correctness**: the borrow flag decides `<` on the denoted
values.
-/
theorem lt_iff (xs ys : Limbs)
    (hLen : xs.length = ys.length) (hWFx : Limbs.WF xs) (hWFy : Limbs.WF ys) :
    isLt xs ys = true ↔ (Limbs.val xs) < (Limbs.val ys) := by
  have hVal := sbb_val xs ys 0 hLen hWFx hWFy (by omega)
  have hBorrow := sbb_borrow_le xs ys 0 (by omega)
  have hResult : (Limbs.val (sbb xs ys 0).1) < (2 ^ 64) ^ xs.length := by
    have hBound := val_lt (sbb_wf xs ys 0 hWFx hWFy (by omega))
    rw [sbb_length xs ys 0 hLen] at hBound
    exact hBound
  unfold isLt
  constructor
  · intro h
    have hFlag : (sbb xs ys 0).2 = 1 := by simpa using h
    rw [hFlag] at hVal
    generalize hK : ((2 ^ 64) : Nat) ^ xs.length = K at hVal hResult
    omega
  · intro h
    by_cases hFlag : (sbb xs ys 0).2 = 1
    · simp [hFlag]
    · have hZero : (sbb xs ys 0).2 = 0 := by omega
      rw [hZero] at hVal
      generalize hK : ((2 ^ 64) : Nat) ^ xs.length = K at hVal hResult
      omega

/-! ## Wide multiplication (M2): value theorems over the limb layer -/

/--
Variable-length addition with carry: continues past the shorter operand.
The general adder `mulLimbs` composes rows with.
-/
def addAny : Limbs → Limbs → Nat → Limbs
  | [], [], carry => if carry = 0 then [] else [carry]
  | [], y :: ys, carry =>
      (y + carry) % 2 ^ 64 :: addAny [] ys ((y + carry) / 2 ^ 64)
  | x :: xs, [], carry =>
      (x + carry) % 2 ^ 64 :: addAny xs [] ((x + carry) / 2 ^ 64)
  | x :: xs, y :: ys, carry =>
      (x + y + carry) % 2 ^ 64 :: addAny xs ys ((x + y + carry) / 2 ^ 64)

theorem addAny_val : ∀ (xs ys : Limbs) (carry : Nat),
    Limbs.val (addAny xs ys carry) =
      Limbs.val xs + Limbs.val ys + carry
  | [], [], carry => by
      by_cases hZero : carry = 0
      · simp [addAny, hZero, Limbs.val]
      · simp [addAny, hZero, Limbs.val]
  | [], y :: ys, carry => by
      have ih := addAny_val [] ys ((y + carry) / 2 ^ 64)
      have hdm := Nat.mod_add_div (y + carry) (2 ^ 64)
      simp only [addAny, Limbs.val]
      rw [ih]
      simp only [Limbs.val]
      omega
  | x :: xs, [], carry => by
      have ih := addAny_val xs [] ((x + carry) / 2 ^ 64)
      have hdm := Nat.mod_add_div (x + carry) (2 ^ 64)
      simp only [addAny, Limbs.val]
      rw [ih]
      simp only [Limbs.val]
      omega
  | x :: xs, y :: ys, carry => by
      have ih := addAny_val xs ys ((x + y + carry) / 2 ^ 64)
      have hdm := Nat.mod_add_div (x + y + carry) (2 ^ 64)
      simp only [addAny, Limbs.val]
      rw [ih]
      generalize Limbs.val xs = xsVal
      generalize Limbs.val ys = ysVal
      omega

/-- One schoolbook row: multiply a limb vector by a single limb, with
carry. The final carry becomes the top limb, so no precision is lost. -/
def mulByLimb : Limbs → Nat → Nat → Limbs
  | [], _, carry => [carry]
  | x :: xs, m, carry =>
      (x * m + carry) % 2 ^ 64 ::
        mulByLimb xs m ((x * m + carry) / 2 ^ 64)

theorem mulByLimb_val : ∀ (xs : Limbs) (m carry : Nat),
    Limbs.val (mulByLimb xs m carry) = Limbs.val xs * m + carry
  | [], m, carry => by
      simp [mulByLimb, Limbs.val]
  | x :: xs, m, carry => by
      have ih := mulByLimb_val xs m ((x * m + carry) / 2 ^ 64)
      have hdm := Nat.mod_add_div (x * m + carry) (2 ^ 64)
      simp only [mulByLimb, Limbs.val]
      rw [ih]
      rw [Nat.add_mul, Nat.mul_assoc]
      generalize Limbs.val xs * m = rowTail
      omega

/--
**Arbitrary-precision multiplication** by schoolbook rows: full precision,
no truncation. The value theorem below is the multiplication analogue of
`adc_val`.
-/
def mulLimbs (xs : Limbs) : Limbs → Limbs
  | [] => []
  | y :: ys => addAny (mulByLimb xs y 0) (0 :: mulLimbs xs ys) 0

/-- **Multiplication correctness**: the product of the denoted values. -/
theorem mulLimbs_val (xs : Limbs) : ∀ (ys : Limbs),
    Limbs.val (mulLimbs xs ys) = Limbs.val xs * Limbs.val ys
  | [] => by simp [mulLimbs, Limbs.val]
  | y :: ys => by
      have ih := mulLimbs_val xs ys
      simp only [mulLimbs]
      rw [addAny_val]
      simp only [Limbs.val]
      rw [mulByLimb_val, ih]
      rw [Nat.mul_add, Nat.mul_left_comm (Limbs.val xs) (2 ^ 64)
        (Limbs.val ys)]
      omega

/-! ## Single-limb division (M2): long division with value theorems -/

/-- Most-significant-first value of a digit list (the natural orientation
for long division). `valM [d₀, …, dₙ] = d₀·B^n + … + dₙ`. -/
def valM : List Nat → Nat
  | [] => 0
  | digit :: rest => digit * (2 ^ 64) ^ rest.length + valM rest

/-- One long-division step: quotient digit and next remainder for
`r·B + digit` over `d`. Guarded so kernel reduction stays stuck on free
variables (the same discipline as `sbbStep`). -/
def divStep (digit d remainder : Nat) : Nat × Nat :=
  if d = 0 then (0, 0)
  else ((remainder * 2 ^ 64 + digit) / d,
        (remainder * 2 ^ 64 + digit) % d)

/--
Long division of an MSB-first digit list by a single limb, threading the
running remainder. Each step divides `r·B + digit` — the 128-by-64 step
that realizes on the machine as 64 shift-subtract rounds.
-/
def divModMSB : List Nat → Nat → Nat → (List Nat × Nat)
  | [], _, remainder => ([], remainder)
  | digit :: rest, d, remainder =>
      ((divStep digit d remainder).1 ::
        (divModMSB rest d (divStep digit d remainder).2).1,
       (divModMSB rest d (divStep digit d remainder).2).2)

/-- **Division correctness**: quotient and final remainder reconstruct
the dividend (with the incoming remainder at full weight). -/
theorem divModMSB_val : ∀ (digits : List Nat) (d remainder : Nat),
    d ≠ 0 →
    valM (divModMSB digits d remainder).1 * d +
        (divModMSB digits d remainder).2 =
      remainder * (2 ^ 64) ^ digits.length + valM digits
  | [], d, remainder, _ => by
      simp [divModMSB, valM]
  | digit :: rest, d, remainder, hd => by
      have hQ : (divStep digit d remainder).1 =
          (remainder * 2 ^ 64 + digit) / d := by
        unfold divStep
        rw [if_neg hd]
      have hR : (divStep digit d remainder).2 =
          (remainder * 2 ^ 64 + digit) % d := by
        unfold divStep
        rw [if_neg hd]
      have ih := divModMSB_val rest d (divStep digit d remainder).2 hd
      have hLen : ((divModMSB rest d
          (divStep digit d remainder).2).1).length = rest.length := by
        clear ih hQ hR
        induction rest generalizing remainder digit with
        | nil => rfl
        | cons r rs ihLen =>
            simp only [divModMSB, List.length_cons]
            rw [ihLen]
      simp only [divModMSB, valM, hLen, List.length_cons]
      rw [Nat.add_mul, Nat.add_assoc, ih, hQ, hR]
      have hdm := Nat.div_add_mod (remainder * 2 ^ 64 + digit) d
      rw [show ((2 : Nat) ^ 64) ^ (rest.length + 1) =
        (2 ^ 64) ^ rest.length * 2 ^ 64 from
          Nat.pow_succ (2 ^ 64) rest.length]
      generalize hQ2 : (remainder * 2 ^ 64 + digit) / d = q at *
      generalize hR2 : (remainder * 2 ^ 64 + digit) % d = r at *
      generalize hK : ((2 : Nat) ^ 64) ^ rest.length = K at *
      rw [show q * K * d = q * d * K from by
        rw [Nat.mul_assoc, Nat.mul_comm K d, ← Nat.mul_assoc]]
      rw [show remainder * (K * 2 ^ 64) = remainder * 2 ^ 64 * K from by
        rw [Nat.mul_comm K (2 ^ 64), ← Nat.mul_assoc]]
      generalize hV : valM rest = restVal at *
      have hCur : q * d + r = remainder * 2 ^ 64 + digit := by
        rw [Nat.mul_comm]
        exact hdm
      calc q * d * K + (r * K + restVal)
          = (q * d + r) * K + restVal := by
            rw [Nat.add_mul]
            omega
        _ = (remainder * 2 ^ 64 + digit) * K + restVal := by rw [hCur]
        _ = remainder * 2 ^ 64 * K + digit * K + restVal := by
            rw [Nat.add_mul]
        _ = remainder * 2 ^ 64 * K + (digit * K + restVal) := by
            omega

/-- The final remainder is a genuine remainder. -/
theorem divModMSB_rem_lt : ∀ (digits : List Nat) (d remainder : Nat),
    d ≠ 0 → remainder < d →
    (divModMSB digits d remainder).2 < d
  | [], _, _, _, hRem => hRem
  | digit :: rest, d, remainder, hd, _ => by
      show (divModMSB rest d (divStep digit d remainder).2).2 < d
      have hR : (divStep digit d remainder).2 =
          (remainder * 2 ^ 64 + digit) % d := by
        unfold divStep
        rw [if_neg hd]
      rw [hR]
      exact divModMSB_rem_lt rest d _ hd
        (Nat.mod_lt _ (Nat.pos_of_ne_zero hd))

end LeanCompCert.Verified.Limb