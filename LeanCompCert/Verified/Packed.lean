/-!
# Packed lane state: a GMP-backed state backend

The state representations already in this package are *functional*:

* `Reflect.RegState := Nat → Nat`, updated by `RegState.set`, and
* `ArrayState.AState.arr : Nat → Nat`, updated by `AState.writeArr`.

Both build a nested closure per write, so the kernel does the work one
term at a time: a read after `k` writes walks `k` closures, and a
whole-array pass is quadratic in the kernel.

This module supplies an additional representation — selectable alongside
the existing ones, not a replacement. A whole state is a single `Nat`,
viewed as a sequence of fixed-width **lanes**; lane `i` occupies bits
`[w·i, w·(i+1))`. Because the Lean kernel implements `Nat` through GMP,
one term reduction moves an entire machine word, or — for the bulk
operations at the end of the file — the entire state at once.

Everything here is ordinary `Nat` arithmetic: `lane` is
`bits / 2 ^ (w·i) % 2 ^ w` and `poke` splices one lane, so every proof is
an elementary divisibility fact.

This module deliberately imports nothing: it is the bottom of the
package, and the transfer theorems that connect it to `RegState` and
`ArrayState` live in `LeanCompCert.Verified.PackedTransfer`.

## The engineering fact the design rests on

`twoPow` is `1 <<< k`, never `2 ^ k`. **The Lean kernel's `Nat.pow`
accelerator gives up above exponent `2 ^ 24`** and then falls back on
unary unfolding, which burns two minutes and 17.8 GB before overflowing
the stack; `Nat.shiftLeft` has no such cutoff — `1 <<< 10 ^ 9`, a 125 MB
number, reduces in 0.14 s. `twoPow_eq` bridges the two so that
specifications may still be written with `2 ^ k`.

## Two cost classes, and only one of them is rescued

* A per-lane `lane` / `poke` is O(1) *kernel* steps but O(N) GMP word
  work, so a per-lane sweep over `N` lanes stays O(N) kernel steps.
* A **bulk** operation — `orAll`, `repunit`, `classMask`, `covers` —
  is O(1) kernel steps *and* O(N/64) GMP word work for the whole state.

Only algorithms expressible with bulk operations (coverage bitmaps,
sieves, residue-class unions, membership sets) get the large win. Work
that branches per element is not helped; see
`LeanCompCert.Verified.ListFold` for the lever that applies there.

## Main results

* `lane_poke_self`, `lane_poke_ne` — `poke` is a functional update of
  lane `i` that leaves every other lane alone.
* `laneState_poke` — the abstraction function `laneState` carries `poke`
  to a pointwise update, which is what makes the packed representation a
  refinement of `Nat → Nat` state.
* `lane_lt` — every lane is a `w`-bit value; at `w = 64` this discharges
  the `s i < 2 ^ 64` side condition `Reflect.StateInv` carries by hand.
* `testBit_orAll`, `testBit_repunit`, `testBit_classMask` — bit-level
  specifications of the bulk constructors.
* `covers_iff` — the acceptance test `(x &&& mask n) = mask n` holds iff
  every one of the low `n` bits of `x` is set: "check all `n` cells", in
  one kernel step.
-/

namespace LeanCompCert.Verified.Packed

/-! ## `twoPow`: powers of two the kernel can actually evaluate -/

/--
`2 ^ k`, computed as `1 <<< k`.

The Lean kernel accelerates `Nat.shiftLeft` through GMP with no size
cutoff, whereas its `Nat.pow` accelerator refuses exponents above
`2 ^ 24` and then unfolds `Nat.pow` unary. Every packed definition below
therefore goes through `twoPow`.
-/
def twoPow (k : Nat) : Nat := 1 <<< k

@[simp] theorem twoPow_eq (k : Nat) : twoPow k = 2 ^ k := by
  simp [twoPow, Nat.shiftLeft_eq]

theorem twoPow_pos (k : Nat) : 0 < twoPow k := by
  rw [twoPow_eq]; exact Nat.two_pow_pos k

/-! ## Lane geometry -/

/-- Number of distinct values a `w`-bit lane can hold. -/
def laneMod (w : Nat) : Nat := twoPow w

/-- Bit offset of lane `i` at lane width `w`, as a power of two. -/
def laneScale (w i : Nat) : Nat := twoPow (w * i)

@[simp] theorem laneMod_eq (w : Nat) : laneMod w = 2 ^ w := twoPow_eq w

@[simp] theorem laneScale_eq (w i : Nat) : laneScale w i = 2 ^ (w * i) :=
  twoPow_eq (w * i)

theorem laneMod_pos (w : Nat) : 0 < laneMod w := twoPow_pos w

theorem laneScale_pos (w i : Nat) : 0 < laneScale w i := twoPow_pos (w * i)

/-- `laneScale` steps by one lane modulus per lane. -/
theorem laneScale_succ (w i : Nat) :
    laneScale w (i + 1) = laneScale w i * laneMod w := by
  simp only [laneScale_eq, laneMod_eq, Nat.mul_succ, Nat.pow_add]

/-- Lane scales are nested: lower lanes divide higher ones. -/
theorem laneScale_dvd {w i j : Nat} (h : i ≤ j) :
    laneScale w i ∣ laneScale w j := by
  simp only [laneScale_eq]
  exact Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left w h)

/-! ## Reading and writing one lane -/

/--
Lane `i` of the packed state `bits` at lane width `w`.

The `/`, `%` form is the same pair of GMP calls that
`(bits >>> (w * i)) &&& (2 ^ w - 1)` would be, and it is far easier to
reason about.
-/
def lane (w bits i : Nat) : Nat := bits / laneScale w i % laneMod w

/-- Functional update of lane `i` to `v`, truncated to the lane width:
the part above lane `i`, the new lane, and the part below it. -/
def poke (w bits i v : Nat) : Nat :=
  bits / laneScale w (i + 1) * laneScale w (i + 1)
    + v % laneMod w * laneScale w i
    + bits % laneScale w i

/-- Every lane is a `w`-bit value. At `w = 64` this is exactly the
`s i < 2 ^ 64` invariant `Reflect.StateInv` maintains by hand. -/
theorem lane_lt (w bits i : Nat) : lane w bits i < 2 ^ w := by
  have := Nat.mod_lt (bits / laneScale w i) (laneMod_pos w)
  simpa [lane, laneMod_eq] using this

/-! ### The splice normal form

Every lane lemma below is an instance of one fact: reading lane `j` of
`hi * (S * B) + d * S + lo` (with `d < B` and `lo < S`) sees `d` at the
spliced position, sees `lo` below it, and sees `hi` above it.
-/

section Splice

/-- Dividing the splice by the spliced lane's scale exposes `hi * B + d`. -/
private theorem div_splice {S d lo hi B : Nat} (hS : 0 < S) (hlo : lo < S) :
    (hi * (S * B) + d * S + lo) / S = hi * B + d := by
  have hrw : hi * (S * B) + d * S + lo = lo + S * (hi * B + d) := by grind
  rw [hrw, Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt hlo, Nat.zero_add]

/-- At the spliced position the written value is read back. -/
private theorem lane_splice_self {S d lo hi B : Nat}
    (hS : 0 < S) (hlo : lo < S) (hd : d < B) :
    (hi * (S * B) + d * S + lo) / S % B = d := by
  rw [div_splice hS hlo, show hi * B + d = d + B * hi by grind,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- Below the spliced position only the low part is visible. -/
private theorem lane_splice_below {S d lo hi B T : Nat}
    (hT : 0 < T) (hdvd : T * B ∣ S) :
    (hi * (S * B) + d * S + lo) / T % B = lo / T % B := by
  obtain ⟨c, hc⟩ := hdvd
  have hrw : hi * (S * B) + d * S + lo
      = lo + T * (B * (hi * (c * B) + d * c)) := by subst hc; grind
  rw [hrw, Nat.add_mul_div_left _ _ hT, Nat.add_mul_mod_self_left]

/-- Above the spliced position only the high part is visible, re-indexed. -/
private theorem lane_splice_above {S d lo hi B T : Nat}
    (hS : 0 < S) (hB : 0 < B) (hlo : lo < S) (hd : d < B) (hdvd : S * B ∣ T) :
    (hi * (S * B) + d * S + lo) / T % B = hi / (T / (S * B)) % B := by
  obtain ⟨c, hc⟩ := hdvd
  have hSB : 0 < S * B := Nat.mul_pos hS hB
  have hquot : T / (S * B) = c := by rw [hc, Nat.mul_div_cancel_left _ hSB]
  have hlt : d * S + lo < S * B := by
    have h1 : (d + 1) * S ≤ B * S := Nat.mul_le_mul_right S hd
    have h2 : (d + 1) * S = d * S + S := by grind
    have h3 : B * S = S * B := Nat.mul_comm B S
    omega
  have hcancel : (hi * (S * B) + d * S + lo) / (S * B) = hi := by
    have hrw : hi * (S * B) + d * S + lo = (d * S + lo) + (S * B) * hi := by grind
    rw [hrw, Nat.add_mul_div_left _ _ hSB, Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [hquot, hc, ← Nat.div_div_eq_div_mul, hcancel]

end Splice

/-- The splice form of `poke`: high part, new lane, low part. -/
private theorem poke_eq (w bits i v : Nat) :
    poke w bits i v =
      bits / laneScale w (i + 1) * (laneScale w i * laneMod w)
        + v % laneMod w * laneScale w i
        + bits % laneScale w i := by
  rw [poke, laneScale_succ]

/-- Reading a lane back after writing it returns the written value,
truncated to the lane width. -/
theorem lane_poke_self (w bits i v : Nat) :
    lane w (poke w bits i v) i = v % laneMod w := by
  rw [lane, poke_eq]
  exact lane_splice_self (laneScale_pos w i)
    (Nat.mod_lt _ (laneScale_pos w i))
    (Nat.mod_lt _ (laneMod_pos w))

/-- Reducing modulo a higher lane scale does not disturb lower lanes. -/
private theorem div_mod_of_mod {x S T B : Nat} (hT : 0 < T) (hdvd : T * B ∣ S) :
    x % S / T % B = x / T % B := by
  obtain ⟨c, hc⟩ := hdvd
  have key : ∀ q r : Nat, (r + T * (B * c * q)) / T % B = r / T % B := by
    intro q r
    rw [Nat.add_mul_div_left _ _ hT,
      show B * c * q = B * (c * q) from by grind,
      Nat.add_mul_mod_self_left]
  have hx : x = x % S + T * (B * c * (x / S)) := by
    have h := Nat.div_add_mod x S
    subst hc; grind
  calc x % S / T % B
      = (x % S + T * (B * c * (x / S))) / T % B := (key (x / S) (x % S)).symm
    _ = x / T % B := by rw [← hx]

/-- The low part below lane `i` carries exactly the lanes below `i`. -/
private theorem lane_mod_low {w bits i j : Nat} (h : j < i) :
    lane w (bits % laneScale w i) j = lane w bits j := by
  have hdvd : laneScale w j * laneMod w ∣ laneScale w i := by
    rw [← laneScale_succ]; exact laneScale_dvd h
  exact div_mod_of_mod (laneScale_pos w j) hdvd

/-- Writing lane `i` leaves every other lane unchanged. -/
theorem lane_poke_ne (w bits i v : Nat) {j : Nat} (h : j ≠ i) :
    lane w (poke w bits i v) j = lane w bits j := by
  rcases Nat.lt_or_ge j i with hlt | hge
  · have hdvd : laneScale w j * laneMod w ∣ laneScale w i := by
      rw [← laneScale_succ]; exact laneScale_dvd hlt
    rw [lane, poke_eq, lane_splice_below (laneScale_pos w j) hdvd]
    exact lane_mod_low hlt
  · have hlt : i + 1 ≤ j := by omega
    have hdvd : laneScale w i * laneMod w ∣ laneScale w j := by
      rw [← laneScale_succ]; exact laneScale_dvd hlt
    rw [lane, poke_eq,
      lane_splice_above (laneScale_pos w i) (laneMod_pos w)
        (Nat.mod_lt _ (laneScale_pos w i)) (Nat.mod_lt _ (laneMod_pos w)) hdvd,
      lane, ← laneScale_succ, Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel' (laneScale_dvd hlt)]

/-! ## The abstraction function -/

/-- The abstract state denoted by a packed state: lane `i` is cell `i`. -/
def laneState (w bits : Nat) : Nat → Nat := fun i => lane w bits i

@[simp] theorem laneState_apply (w bits i : Nat) :
    laneState w bits i = lane w bits i := rfl

/--
`poke` denotes a pointwise update of the abstract state.

This is the equation that lets theorems proved about `Nat → Nat` state
transfer to the packed backend rather than being re-proved; see
`LeanCompCert.Verified.PackedTransfer` for the `RegState` and
`ArrayState` instances.
-/
theorem laneState_poke (w bits i v : Nat) :
    laneState w (poke w bits i v) =
      (fun c => if c = i then v % laneMod w else laneState w bits c) := by
  funext c
  by_cases h : c = i
  · subst h; simpa [laneState] using lane_poke_self w bits c v
  · simpa [laneState, h] using lane_poke_ne w bits i v h

/-- The all-zero packed state denotes the all-zero abstract state. -/
@[simp] theorem laneState_zero (w : Nat) : laneState w 0 = fun _ => 0 := by
  funext i; simp [laneState, lane]

/-- Every denoted cell is a `w`-bit value. -/
theorem laneState_lt (w bits i : Nat) : laneState w bits i < 2 ^ w :=
  lane_lt w bits i

/-! ## Bulk operations

These are the operations that pay: each is O(1) kernel steps for an
arbitrary number of lanes. They are stated at bit granularity, which is
where coverage bitmaps, sieves and membership sets live.
-/

/-- The low-`n`-bit mask: bits `0, …, n − 1` set. -/
def mask (n : Nat) : Nat := twoPow n - 1

@[simp] theorem testBit_mask (n i : Nat) :
    Nat.testBit (mask n) i = decide (i < n) := by
  rw [mask, twoPow_eq]; exact Nat.testBit_two_pow_sub_one n i

/-- Bitwise OR of a list of packed words: the packed union of sets. One
kernel step per word, each moving the whole state. -/
def orAll : List Nat → Nat
  | [] => 0
  | word :: words => word ||| orAll words

@[simp] theorem testBit_orAll (words : List Nat) (i : Nat) :
    Nat.testBit (orAll words) i =
      words.any (fun word => Nat.testBit word i) := by
  induction words with
  | nil => simp [orAll]
  | cons word words ih => simp [orAll, Nat.testBit_or, ih]

/--
`repunit m k` has bit `m * j` set for exactly the `j < k` and no other
bit: the packed indicator of an arithmetic progression of stride `m`.

The kernel computes it with **one** GMP division, whatever `k` is. It is
the most useful bulk constructor, since every residue class is a shift
of one.
-/
def repunit (m k : Nat) : Nat := (twoPow (m * k) - 1) / (twoPow m - 1)

private theorem two_pow_sub_one_pos {m : Nat} (hm : 0 < m) : 0 < 2 ^ m - 1 := by
  have h : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  simp only [Nat.pow_one] at h
  omega

private theorem two_pow_mul_succ_sub_one (m k : Nat) :
    2 ^ (m * (k + 1)) - 1 = (2 ^ (m * k) - 1) + 2 ^ (m * k) * (2 ^ m - 1) := by
  have ha : 1 ≤ 2 ^ (m * k) := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hc : 2 ^ (m * k) ≤ 2 ^ (m * k) * 2 ^ m :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos m)
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_sub, Nat.mul_one]
  omega

/-- `repunit` is the geometric sum `∑_{j < k} 2 ^ (m * j)`, in the form
that avoids ever writing the sum down. -/
theorem repunit_mul (m k : Nat) (_hm : 0 < m) :
    repunit m k * (2 ^ m - 1) = 2 ^ (m * k) - 1 := by
  have hdvd : (2 ^ m - 1) ∣ (2 ^ (m * k) - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [two_pow_mul_succ_sub_one]
        exact Nat.dvd_add ih (Nat.dvd_mul_left_of_dvd (Nat.dvd_refl _) _)
  simp only [repunit, twoPow_eq]
  exact Nat.div_mul_cancel hdvd

/-- One more stride adds exactly one more set bit, at the top. -/
theorem repunit_succ (m k : Nat) (hm : 0 < m) :
    repunit m (k + 1) = 2 ^ (m * k) + repunit m k := by
  refine Nat.eq_of_mul_eq_mul_right (two_pow_sub_one_pos hm) ?_
  rw [repunit_mul m (k + 1) hm, Nat.add_mul, repunit_mul m k hm,
    two_pow_mul_succ_sub_one]
  grind

/-- A `k`-term repunit of stride `m` fits in `m * k` bits. -/
theorem repunit_lt (m k : Nat) (hm : 0 < m) : repunit m k < 2 ^ (m * k) := by
  have hpos := two_pow_sub_one_pos hm
  have hmul := repunit_mul m k hm
  have hone : 1 ≤ 2 ^ (m * k) := Nat.one_le_two_pow
  have hle : repunit m k ≤ repunit m k * (2 ^ m - 1) :=
    Nat.le_mul_of_pos_right _ hpos
  omega

/-- Bit `i` of `repunit m k` is set exactly when `i` is one of the first
`k` multiples of `m`. -/
theorem testBit_repunit (m k i : Nat) (hm : 0 < m) :
    Nat.testBit (repunit m k) i = decide (i % m = 0 ∧ i / m < k) := by
  induction k generalizing i with
  | zero => simp [repunit, twoPow_eq, Nat.zero_testBit]
  | succ k ih =>
      rw [repunit_succ m k hm]
      rcases Nat.lt_trichotomy i (m * k) with hlt | heq | hgt
      · rw [Nat.testBit_two_pow_add_gt hlt, ih i]
        have hkey : (i % m = 0 ∧ i / m < k) ↔ (i % m = 0 ∧ i / m < k + 1) := by
          constructor
          · exact fun h => ⟨h.1, by omega⟩
          · rintro ⟨h0, _⟩
            refine ⟨h0, ?_⟩
            have hsplit := Nat.div_add_mod i m
            have : m * (i / m) < m * k := by omega
            exact Nat.lt_of_mul_lt_mul_left this
        simp only [decide_eq_decide]
        exact hkey
      · subst heq
        rw [Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow (repunit_lt m k hm)]
        have h1 : m * k % m = 0 := Nat.mul_mod_right m k
        have h2 : m * k / m = k := Nat.mul_div_cancel_left k hm
        simp [h1, h2]
      · have hbound : 2 ^ (m * k) + repunit m k < 2 ^ i := by
          have h1 := repunit_lt m k hm
          have h2 : 2 ^ (m * k + 1) ≤ 2 ^ i :=
            Nat.pow_le_pow_right (by decide) (by omega)
          have h3 : 2 ^ (m * k + 1) = 2 ^ (m * k) + 2 ^ (m * k) := by
            rw [Nat.pow_succ]; omega
          omega
        rw [Nat.testBit_lt_two_pow hbound]
        have hne : ¬ (i % m = 0 ∧ i / m < k + 1) := by
          rintro ⟨h0, hk⟩
          have hsplit := Nat.div_add_mod i m
          have : m * (i / m) ≤ m * k := Nat.mul_le_mul_left m (by omega)
          omega
        simp [hne]

/--
The packed indicator of the residue class `r mod m` inside `[0, n)`.

One shifted `repunit` and one mask: O(1) kernel steps for `n` cells.
-/
def classMask (r m n : Nat) : Nat := (repunit m (n / m + 1) <<< r) &&& mask n

/-- `classMask` is exactly the residue class it claims to be. -/
theorem testBit_classMask (r m n i : Nat) (hm : 0 < m) (hr : r < m) :
    Nat.testBit (classMask r m n) i = decide (i < n ∧ i % m = r) := by
  rw [classMask, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_mask]
  by_cases hin : i < n
  · by_cases hge : r ≤ i
    · rw [testBit_repunit m (n / m + 1) (i - r) hm]
      have hsplit := Nat.div_add_mod i m
      have hmod : ((i - r) % m = 0) ↔ (i % m = r) := by
        constructor
        · intro h
          obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
          have hi : i = m * c + r := by omega
          rw [hi, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
        · intro h
          have hi : i - r = m * (i / m) := by omega
          rw [hi, Nat.mul_mod_right]
      have hbnd : (i - r) / m < n / m + 1 := by
        have : (i - r) / m ≤ n / m := Nat.div_le_div_right (by omega)
        omega
      by_cases hclass : i % m = r
      · have hz : (i - r) % m = 0 := hmod.mpr hclass
        simp [hin, hge, hz, hbnd, hclass]
      · have hnz : (i - r) % m ≠ 0 := fun h => hclass (hmod.mp h)
        simp [hin, hge, hnz, hclass]
    · have hlt : i < m := by omega
      have hne : i % m ≠ r := by rw [Nat.mod_eq_of_lt hlt]; omega
      simp [hge, hne]
  · simp [hin]

/-! ### The acceptance test

`covers` is the whole point of the packed representation: deciding that
every one of `n` cells is set costs **one** kernel step, where the
functional representations cost `n`.
-/

/-- Machine acceptance: every one of the low `n` bits of `x` is set. -/
def covers (x n : Nat) : Bool := (x &&& mask n) == mask n

/-- `covers` is exactly "every cell below `n` is set". -/
theorem covers_iff (x n : Nat) :
    covers x n = true ↔ ∀ i, i < n → Nat.testBit x i = true := by
  simp only [covers, beq_iff_eq]
  constructor
  · intro h i hi
    have hbit := congrArg (fun value => Nat.testBit value i) h
    simp only [Nat.testBit_and, testBit_mask] at hbit
    simpa [hi] using hbit
  · intro h
    refine Nat.eq_of_testBit_eq (fun i => ?_)
    rw [Nat.testBit_and, testBit_mask]
    by_cases hi : i < n
    · simp [hi, h i hi]
    · simp [hi]

/-- The packed union of residue classes, and its acceptance test: this is
the shape of a covering-system or sieve certificate. Deciding it is O(1)
kernel steps in the number of cells. -/
def classUnion (classes : List (Nat × Nat)) (n : Nat) : Nat :=
  orAll (classes.map (fun rm => classMask rm.1 rm.2 n))

/-- A covering certificate: if the packed union accepts, every cell below
`n` lies in one of the listed residue classes. -/
theorem mem_class_of_covers_classUnion
    (classes : List (Nat × Nat)) (n : Nat)
    (hwf : ∀ rm ∈ classes, 0 < rm.2 ∧ rm.1 < rm.2)
    (hcov : covers (classUnion classes n) n = true)
    (i : Nat) (hi : i < n) :
    ∃ rm ∈ classes, i % rm.2 = rm.1 := by
  have hbit := (covers_iff _ n).mp hcov i hi
  rw [classUnion, testBit_orAll] at hbit
  simp only [List.any_eq_true, List.mem_map] at hbit
  obtain ⟨word, ⟨rm, hmem, rfl⟩, hword⟩ := hbit
  obtain ⟨hpos, hlt⟩ := hwf rm hmem
  rw [testBit_classMask rm.1 rm.2 n i hpos hlt, decide_eq_true_eq] at hword
  exact ⟨rm, hmem, hword.2⟩

end LeanCompCert.Verified.Packed
