/-!
# M3 — Fixed-shape gcd equivalent to the reference recursion

`Nat.gcd` recurses by well-founded descent on its first argument, so its
call tree depends on the data — unusable as a machine loop shape. This
module gives the fixed-shape counterpart: a fuel-indexed Euclid loop
whose per-round work is one guarded step (`if a = 0` then hold, else
`(b % a, a)`), suitable for later realization as a counted machine loop.

The step is guarded behind the `a = 0` test on a free variable, matching
the house pattern that keeps the kernel from runaway reduction on bare
big-Nat recursion arguments.

Main results:
* `gcdFuel_eq` — with fuel at least `a`, the fuel loop computes exactly
  `Nat.gcd a b`.
* `gcdFuel_u64` — machine-width corollary: `2 ^ 64` rounds suffice for
  any `a < 2 ^ 64`.
-/

namespace LeanCompCert.Verified.Gcd

/-- One Euclid round, guarded: hold the pair once `a` hits zero, else
rotate to `(b % a, a)`. This is the fixed per-round shape a machine
loop body realizes. -/
def gcdStep (a b : Nat) : Nat × Nat :=
  if a = 0 then (a, b) else (b % a, a)

/-- Fuel-indexed gcd: run `gcdStep` for at most `fuel` rounds and return
the second component. Correct whenever `fuel ≥ a` (`gcdFuel_eq`). -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | fuel + 1, a, b => if a = 0 then b else gcdFuel fuel (b % a) a

/-- The loop is inert once the first component is zero, at any fuel. -/
theorem gcdFuel_zero_left (fuel b : Nat) : gcdFuel fuel 0 b = b := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [gcdFuel]

/-- Each successor-fuel round is exactly one `gcdStep`, unconditionally:
the guarded step makes the `a = 0` case a genuine fixed point. -/
theorem gcdFuel_succ_step (fuel a b : Nat) :
    gcdFuel (fuel + 1) a b = gcdFuel fuel (gcdStep a b).1 (gcdStep a b).2 := by
  by_cases ha : a = 0
  · subst ha
    simp [gcdFuel, gcdStep, gcdFuel_zero_left]
  · simp [gcdFuel, gcdStep, ha]

/-- With fuel at least `a`, the fixed-shape loop computes `Nat.gcd`.
The bound is sufficient because `b % a < a` strictly decreases the
first component every productive round. -/
theorem gcdFuel_eq (fuel a b : Nat) (h : a ≤ fuel) :
    gcdFuel fuel a b = Nat.gcd a b := by
  induction fuel generalizing a b with
  | zero =>
      have ha : a = 0 := Nat.le_zero.mp h
      subst ha
      show b = Nat.gcd 0 b
      rw [Nat.gcd_zero_left]
  | succ fuel ih =>
      by_cases ha : a = 0
      · subst ha
        show (if (0 : Nat) = 0 then b else gcdFuel fuel (b % 0) 0) = Nat.gcd 0 b
        rw [if_pos rfl, Nat.gcd_zero_left]
      · have hlt : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero ha)
        have hle : b % a ≤ fuel := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt h)
        calc gcdFuel (fuel + 1) a b
            = gcdFuel fuel (b % a) a := by simp [gcdFuel, ha]
          _ = Nat.gcd (b % a) a := ih (b % a) a hle
          _ = Nat.gcd a b := (Nat.gcd_rec a b).symm

/-- Machine-width corollary: `2 ^ 64` rounds of the fixed-shape loop
compute `Nat.gcd` for any first argument fitting in a `u64`. -/
theorem gcdFuel_u64 (a b : Nat) (ha : a < 2 ^ 64) :
    gcdFuel (2 ^ 64) a b = Nat.gcd a b :=
  gcdFuel_eq (2 ^ 64) a b (Nat.le_of_lt ha)

end LeanCompCert.Verified.Gcd
