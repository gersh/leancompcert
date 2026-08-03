import LeanCompCert.Ports.Section413G2Program

/-!
# The §4.1.3 `g₂` sweep: the transparent model with a clean flag

`Ports/Section413G2Program.lean` states two open obligations.  This file
attacks the second,

```text
(2)  c.tFlag = 0 → g2SweepOK c.rounds c.checkLo c.cap = true
                                                [model ⇒ reference model]
```

the direction in which the machine's *runtime width guards* pay for
themselves: with the violation flag still `0` at the end of the run, no
`u64` quantity the sweep computed was ever truncated, so every word is
`Section413Cells.encodeZ` of the exact `Int` the reference model
(`Ports/Section413Sweep.lean`) computes, and the wrapped machine arithmetic
transfers to `Int` arithmetic term by term.

## The architecture

1. **The flag is monotone.**  `viol` is only ever `|||`-ed, never cleared,
   by any block of the transparent model.  Hence `tFlag = 0` propagates
   *backwards* to every prefix of the run (`tRunUpto_viol_zero_of_le`),
   which is what lets the main induction run *forwards* under a hypothesis
   about the end of the run.  This is the (C.17) `accCap` discipline.
2. **A clean guard is a width bound.**  `tguard` ORs `1` exactly when the
   encoded word leaves `[−CAP, CAP]`, so a clean guard on a live gate is
   the statement `|decodeZ w| ≤ CAP` (`capped_iff_guard_clean`) — from
   which `decodeZ`/`encodeZ` round-trip and no `% M` truncated anything.
3. **Cell transfer.**  Under those width bounds the word-level blocks
   compute the reference model's cell operations: `tmag` is sign and
   `natAbs`, `tlt` is the signed order of 128-bit sign-magnitude triples,
   and `tcmul` is `Section413Sweep.cmul` of the decoded cells.
4. **Phase 1, phase 2, the run.**  Still open; see the closing `## OPEN`
   section for the precise remaining statements.

Nothing below is an axiom, a `sorry`, a `native_decide`, or a weakened
restatement of an obligation.  Everything is
`[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanCompCert.Ports.Section413G2Sound

open LeanCompCert.Ports.Section413G2Program
open LeanCompCert.Ports.Section413Cells (encodeZ decodeZ smVal smCanon
  encodeZ_lt decodeZ_encodeZ encodeZ_decodeZ encodeZ_sub)
open LeanCompCert.Verified.Reflect (M)

/-! ## §0 Admissibility

The arithmetic side conditions the obligation is stated under.  Every
conjunct is one the production configuration `⟨10⁶, 999, 33⟩` satisfies —
`production_admissible` below checks that by `decide`. -/

/-- `Nat.sqrt` never grows its argument. -/
theorem sqrt_le_self (n : Nat) : Nat.sqrt n ≤ n := by
  have h := Nat.sqrt_le n
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | h0
  · omega
  · have h1 : Nat.sqrt n * 1 ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul (Nat.le_refl _) h0
    omega

/-- **Admissibility of a configuration.**  Positivity of the loop bounds,
the covering condition that makes the shared trial division decide `μ` on
every candidate (`X ≤ N < (R+2)²`), and the two range conditions that keep
every array address and every loop index strictly inside the `u64` index
space, so nothing the program computes as an address or a counter wraps. -/
structure Admissible (c : Cfg) : Prop where
  /-- Trial divisors `2 … R+1` — at least two rounds. -/
  rounds_ge : 2 ≤ c.rounds
  /-- At least one candidate. -/
  cap_pos : 0 < c.cap
  /-- Every candidate is covered by the trial division: `X ≤ N < (R+2)²`,
  so a leftover residual above `R+1` is prime. -/
  cover : c.cap < (c.rounds + 2) * (c.rounds + 2)
  /-- The three planes fit in the `u64` address space. -/
  arr_fits : 3 * (c.cap + 1) < M
  /-- A `√`-free upper bound for the loop length, hence `loopCount < 2⁶⁴`. -/
  loop_fits : (c.cap - 1) * c.rounds + c.cap * (2 * c.cap + 2) < M
  /-- The first checked candidate is a real one. -/
  checkLo_pos : 0 < c.checkLo

theorem Admissible.p_le {c : Cfg} (_h : Admissible c) : c.p ≤ 2 * c.cap + 2 := by
  have hs : c.s ≤ c.cap := sqrt_le_self c.cap
  unfold Cfg.p
  omega

theorem Admissible.loopCount_lt {c : Cfg} (h : Admissible c) : c.loopCount < M := by
  have h1 : c.cap * c.p ≤ c.cap * (2 * c.cap + 2) :=
    Nat.mul_le_mul (Nat.le_refl _) h.p_le
  have h2 := h.loop_fits
  unfold Cfg.loopCount Cfg.phase1
  omega

/-- **The production configuration is admissible.** -/
theorem production_admissible : Admissible production :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- So is the smoke configuration. -/
theorem smoke_admissible : Admissible smoke :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## §1 The two moduli, and `bnat` -/

theorem M_val : M = 18446744073709551616 := rfl

theorem B64_val : LeanCompCert.Verified.MulWide.B64 = M := rfl

theorem CAP_val : CAP = 1152921504606846976 := rfl

theorem H63_val : H63 = 9223372036854775808 := rfl

theorem cellsH63_val :
    LeanCompCert.Ports.Section413Cells.H63 = 9223372036854775808 := rfl

theorem bnat_le_one (p : Prop) [Decidable p] : bnat p ≤ 1 := by
  unfold bnat; split <;> omega

theorem bnat_eq_zero_iff {p : Prop} [Decidable p] : bnat p = 0 ↔ ¬ p := by
  unfold bnat; split <;> simp_all

theorem bnat_eq_one_iff {p : Prop} [Decidable p] : bnat p = 1 ↔ p := by
  unfold bnat; split <;> simp_all

theorem bnat_pos_iff {p : Prop} [Decidable p] : 0 < bnat p ↔ p := by
  unfold bnat; split <;> simp_all

@[simp] theorem bnat_true {p : Prop} [Decidable p] (h : p) : bnat p = 1 :=
  bnat_eq_one_iff.mpr h

@[simp] theorem bnat_false {p : Prop} [Decidable p] (h : ¬ p) : bnat p = 0 :=
  bnat_eq_zero_iff.mpr h

/-! ## §2 `|||` is monotone, and vanishes only when both sides do -/

theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  have h1 : a ≤ a ||| b := Nat.left_le_or
  have h2 : b ≤ a ||| b := Nat.right_le_or
  omega

/-! ## §3 Machine subtraction -/

theorem tsub_lt (a b : Nat) : tsub a b < M := by
  unfold tsub
  exact Nat.mod_lt _ (by decide)

/-- `tsub 0 w` is the two's-complement negation of `w`. -/
theorem tsub_zero (w : Nat) : tsub 0 w = (M - w) % M := by
  unfold tsub
  simp only [Nat.zero_add]

/-- Machine subtraction of two encoded endpoints is the encoding of the
`Int` difference (`Section413Cells.encodeZ_sub`, transported to `tsub`). -/
theorem tsub_eq_encodeZ (a b : Nat) (ha : a < M) (hb : b < M) :
    tsub a b = encodeZ (decodeZ a - decodeZ b) := by
  have h := encodeZ_sub (decodeZ a) (decodeZ b)
  rw [encodeZ_decodeZ a (by rw [B64_val]; exact ha),
    encodeZ_decodeZ b (by rw [B64_val]; exact hb)] at h
  rw [← h]
  rfl

/-! ## §4 The width guard is a magnitude bound

`tguard` ORs `1` into the flag exactly when the encoded word leaves the
band `[−CAP, CAP]`.  So a *clean* guard on a live gate is a bound on the
`Int` the word decodes to — and, since `CAP = 2⁶⁰ < 2⁶³`, on nothing being
truncated. -/

/-- The word decodes inside the runtime cap. -/
def Capped (w : Nat) : Prop := (decodeZ w).natAbs ≤ CAP

/-- **The guard's predicate is the magnitude bound.**  The machine tests
`(w + CAP) mod 2⁶⁴ > 2·CAP`; that fails exactly when `|decodeZ w| ≤ CAP`. -/
theorem capped_iff_guard_clean (w : Nat) (hw : w < M) :
    ((w + CAP) % M ≤ 2 * CAP) ↔ Capped w := by
  unfold Capped decodeZ
  simp only [M_val, CAP_val, cellsH63_val, B64_val] at *
  split <;> omega

/-- A capped word is in the two's-complement signed range, so it round
trips through `decodeZ`/`encodeZ`. -/
theorem capped_range {w : Nat} (hw : w < M) (h : Capped w) :
    -(CAP : Int) ≤ decodeZ w ∧ decodeZ w ≤ (CAP : Int) := by
  unfold Capped decodeZ at *
  simp only [M_val, CAP_val, cellsH63_val, B64_val] at *
  split at h <;> omega

theorem encodeZ_decodeZ_self {w : Nat} (hw : w < M) : encodeZ (decodeZ w) = w :=
  encodeZ_decodeZ w (by rw [B64_val]; exact hw)

/-- The word of a capped value is recovered by `encodeZ`. -/
theorem decodeZ_encodeZ_of_cap {z : Int} (h1 : -(CAP : Int) ≤ z)
    (h2 : z ≤ (CAP : Int)) : decodeZ (encodeZ z) = z :=
  decodeZ_encodeZ z
    (by simp only [cellsH63_val, CAP_val] at *; omega)
    (by simp only [cellsH63_val, CAP_val] at *; omega)

theorem encodeZ_lt_M (z : Int) : encodeZ z < M := by
  have := encodeZ_lt z
  rw [B64_val] at this
  exact this

/-! ## §5 The guard blocks are monotone in the flag -/

theorem tguard_le (gate w viol : Nat) : viol ≤ tguard gate w viol :=
  Nat.left_le_or

/-- A clean guard: the flag was already clean, and — if the gate was live
— the word is within the cap. -/
theorem tguard_eq_zero {gate w viol : Nat} (h : tguard gate w viol = 0) :
    viol = 0 ∧ (0 < gate → (w + CAP) % M ≤ 2 * CAP) := by
  unfold tguard at h
  obtain ⟨h1, h2⟩ := or_eq_zero h
  refine ⟨h1, fun hg => ?_⟩
  have hb : bnat (2 * CAP < (w + CAP) % M) = 0 := by
    rcases Nat.mul_eq_zero.mp h2 with hb | hg0
    · exact hb
    · omega
  have := bnat_eq_zero_iff.mp hb
  omega

/-- The same, in the form the invariant uses: a live gate and a clean
guard bound the decoded magnitude. -/
theorem capped_of_tguard_eq_zero {gate w viol : Nat} (hw : w < M)
    (hg : 0 < gate) (h : tguard gate w viol = 0) : Capped w :=
  (capped_iff_guard_clean w hw).mp ((tguard_eq_zero h).2 hg)

/-- A gated `bnat` guard bit that vanished on a live gate means the guarded
proposition was false. -/
theorem gate_guard_clean {p : Prop} [Decidable p] {gate : Nat} (hg : 0 < gate)
    (h : bnat p * gate = 0) : ¬ p := by
  rcases Nat.mul_eq_zero.mp h with hb | hz
  · exact bnat_eq_zero_iff.mp hb
  · omega

/-! ## §6 The interval product's flag, and `tcmul`'s flag monotonicity -/

/-- `tcmul`'s outgoing flag, spelled out: the incoming flag, ORed with the
four gated magnitude guards on the two input cells. -/
theorem tcmul_viol_eq (gate aLo aHi bLo bHi viol : Nat) :
    (tcmul gate aLo aHi bLo bHi viol).2.2 =
      viol ||| bnat (CAP < (tmag aLo).2) * gate
        ||| bnat (CAP < (tmag aHi).2) * gate
        ||| bnat (CAP < (tmag bLo).2) * gate
        ||| bnat (CAP < (tmag bHi).2) * gate := rfl

theorem tcmul_viol_le (gate aLo aHi bLo bHi viol : Nat) :
    viol ≤ (tcmul gate aLo aHi bLo bHi viol).2.2 := by
  rw [tcmul_viol_eq]
  exact Nat.le_trans Nat.left_le_or
    (Nat.le_trans Nat.left_le_or (Nat.le_trans Nat.left_le_or Nat.left_le_or))

/-- A clean flag out of `tcmul` on a live gate bounds all four input
magnitudes. -/
theorem tcmul_viol_eq_zero {gate aLo aHi bLo bHi viol : Nat}
    (h : (tcmul gate aLo aHi bLo bHi viol).2.2 = 0) :
    viol = 0 ∧ (0 < gate →
      (tmag aLo).2 ≤ CAP ∧ (tmag aHi).2 ≤ CAP ∧
      (tmag bLo).2 ≤ CAP ∧ (tmag bHi).2 ≤ CAP) := by
  rw [tcmul_viol_eq] at h
  obtain ⟨h123, h4⟩ := or_eq_zero h
  obtain ⟨h12, h3⟩ := or_eq_zero h123
  obtain ⟨h1, h2⟩ := or_eq_zero h12
  obtain ⟨h0, hA⟩ := or_eq_zero h1
  refine ⟨h0, fun hg => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := gate_guard_clean hg hA; omega
  · have := gate_guard_clean hg h2; omega
  · have := gate_guard_clean hg h3; omega
  · have := gate_guard_clean hg h4; omega

/-! ## §7 The touch block is monotone in the flag -/

theorem ttouch_viol_le (c : Cfg) (g d : Nat) (t : TState) :
    t.viol ≤ (c.ttouch g d t).viol := by
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  exact tcmul_viol_le _ _ _ _ _ _

/-! ## §8 **The flag is monotone along the whole run**

`viol` is only ever `|||`-ed, so it never decreases; hence a clean flag at
the end of the run is a clean flag at every prefix.  This is what makes a
*forward* induction possible under a hypothesis about the run's *end*. -/

theorem tstep_viol_le (c : Cfg) (idx : Nat) (t : TState) :
    t.viol ≤ (c.tstep idx t).viol := by
  refine Nat.le_trans ?_ Nat.left_le_or
  refine Nat.le_trans ?_ Nat.left_le_or
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (tguard_le _ _ _)
  refine Nat.le_trans ?_ (ttouch_viol_le _ _ _ _)
  refine Nat.le_trans ?_ (ttouch_viol_le _ _ _ _)
  exact tcmul_viol_le _ _ _ _ _ _

/-- The run truncated to its first `k` iterations. -/
def tRunUpto (c : Cfg) (k : Nat) : TState :=
  (List.range k).foldl (fun t i => c.tstep i t) tInit

theorem tRunUpto_zero (c : Cfg) : tRunUpto c 0 = tInit := rfl

theorem tRunUpto_succ (c : Cfg) (k : Nat) :
    tRunUpto c (k + 1) = c.tstep k (tRunUpto c k) := by
  unfold tRunUpto
  rw [List.range_succ, List.foldl_append]
  rfl

theorem tRun_eq_tRunUpto (c : Cfg) : c.tRun = tRunUpto c c.loopCount := rfl

theorem tRunUpto_viol_le (c : Cfg) (d j : Nat) :
    (tRunUpto c j).viol ≤ (tRunUpto c (j + d)).viol := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      refine Nat.le_trans ih ?_
      rw [show j + (d + 1) = (j + d) + 1 from rfl, tRunUpto_succ]
      exact tstep_viol_le _ _ _

/-- **Backwards propagation of a clean flag.**  This is the lemma the whole
obligation turns on: it converts the hypothesis `tFlag c = 0`, which speaks
about the *end* of the run, into a clean flag at every *prefix*, so the
main simulation induction may be run forwards. -/
theorem tRunUpto_viol_zero_of_le (c : Cfg) {j k : Nat} (hjk : j ≤ k)
    (h : (tRunUpto c k).viol = 0) : (tRunUpto c j).viol = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have := tRunUpto_viol_le c d j
  omega

/-- The same, phrased directly against `tFlag`. -/
theorem tRunUpto_viol_zero_of_tFlag (c : Cfg) (h : c.tFlag = 0) {j : Nat}
    (hj : j ≤ c.loopCount) : (tRunUpto c j).viol = 0 :=
  tRunUpto_viol_zero_of_le c hj (by rw [← tRun_eq_tRunUpto]; exact h)

/-- Consequence, in the shape the per-step reasoning wants: at every step
inside a clean run, the flag going *in* is clean and the flag coming *out*
is clean. -/
theorem tstep_clean_of_tFlag (c : Cfg) (h : c.tFlag = 0) {k : Nat}
    (hk : k < c.loopCount) :
    (tRunUpto c k).viol = 0 ∧ (c.tstep k (tRunUpto c k)).viol = 0 := by
  refine ⟨tRunUpto_viol_zero_of_tFlag c h (Nat.le_of_lt hk), ?_⟩
  rw [← tRunUpto_succ]
  exact tRunUpto_viol_zero_of_tFlag c h hk

/-! ## §9 Sign and magnitude of an encoded endpoint

`smDecomp`, in the transparent model `tmag`, splits an encoded word into
its sign bit and its magnitude.  Both halves are exactly the sign and the
`natAbs` of the `Int` the word decodes to. -/

theorem decodeZ_eq (w : Nat) :
    decodeZ w = if w < 9223372036854775808 then (w : Int)
      else (w : Int) - 18446744073709551616 := rfl

theorem encodeZ_eq (z : Int) :
    encodeZ z = (z % 18446744073709551616).toNat := rfl

theorem bnat_eq_bnat {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    bnat p = bnat q := by
  unfold bnat
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

theorem decodeZ_lt_zero_iff (w : Nat) (hw : w < M) :
    decodeZ w < 0 ↔ 9223372036854775808 ≤ w := by
  rw [decodeZ_eq]
  simp only [M_val] at hw
  split <;> omega

theorem natAbs_decodeZ (w : Nat) (hw : w < M) :
    (decodeZ w).natAbs =
      if 9223372036854775808 ≤ w then 18446744073709551616 - w else w := by
  rw [decodeZ_eq]
  simp only [M_val] at hw
  split <;> split <;> omega

theorem tmag_sign (w : Nat) (hw : w < M) :
    (tmag w).1 = bnat (decodeZ w < 0) :=
  bnat_eq_bnat (decodeZ_lt_zero_iff w hw).symm

theorem tmag_mag (w : Nat) (hw : w < M) : (tmag w).2 = (decodeZ w).natAbs := by
  show (if H63 ≤ w then tsub 0 w else w) = (decodeZ w).natAbs
  rw [tsub_zero, natAbs_decodeZ w hw]
  simp only [M_val, H63_val] at *
  split <;> omega

/-- `encodeZ` on a small nonnegative value is the identity. -/
theorem encodeZ_ofNat (n : Nat) (h : n < 9223372036854775808) :
    encodeZ (n : Int) = n := by
  rw [encodeZ_eq]
  omega

/-- The machine's `0 − q` on a small nonnegative quotient is `encodeZ` of
its negation. -/
theorem tsub_zero_encodeZ_neg (n : Nat) (h : n < 9223372036854775808) :
    tsub 0 n = encodeZ (-(n : Int)) := by
  rw [encodeZ_eq, tsub_zero]
  simp only [M_val]
  omega

/-! ## §10 Canonical 128-bit sign-magnitude triples

`cmulBody` carries each of the four partial products as a sign bit and a
two-word magnitude, canonicalized so that a set sign bit implies a nonzero
magnitude.  `Rep s lo hi z` says that triple stands for `z`. -/

/-- `(s, lo, hi)` is the machine's canonical sign-magnitude form of `z`. -/
structure Rep (s lo hi : Nat) (z : Int) : Prop where
  /-- The sign bit. -/
  sign : s = bnat (z < 0)
  /-- The two words are the magnitude, little-endian. -/
  mag : lo + M * hi = z.natAbs
  /-- Both words are `u64`s. -/
  lo_lt : lo < M
  /-- Both words are `u64`s. -/
  hi_lt : hi < M

theorem Rep.s_le_one {s lo hi : Nat} {z : Int} (r : Rep s lo hi z) : s ≤ 1 := by
  rw [r.sign]; exact bnat_le_one _

theorem Rep.smVal_eq {s lo hi : Nat} {z : Int} (r : Rep s lo hi z) :
    smVal s (lo + M * hi) = z := by
  rw [r.sign, r.mag]
  exact LeanCompCert.Ports.Section413Cells.smVal_of_val z

/-- The 128-bit comparison of two words against a fixed limb base. -/
theorem lt128 (x y u v : Nat) (hx : x < M) (hu : u < M) :
    bnat (y < v) + bnat (y = v) * bnat (x < u)
      = bnat (x + M * y < u + M * v) := by
  simp only [M_val] at hx hu
  by_cases h1 : y < v
  · rw [bnat_true h1, bnat_false (show ¬ (y = v) by omega),
      bnat_true (show x + M * y < u + M * v by simp only [M_val]; omega)]
    omega
  · by_cases h2 : y = v
    · subst h2
      rw [bnat_false h1, bnat_true (rfl : y = y),
        bnat_eq_bnat (show (x < u) ↔ (x + M * y < u + M * y) by
          simp only [M_val]; omega)]
      omega
    · rw [bnat_false h1, bnat_false h2,
        bnat_false (show ¬ (x + M * y < u + M * v) by
          simp only [M_val]; omega)]
      omega

/-- **The branchless comparator decides the signed order** of two canonical
triples (`cmpLtBody`, in the transparent model `tlt`). -/
theorem tlt_of_Rep {s1 l1 h1 s2 l2 h2 : Nat} {z1 z2 : Int}
    (r1 : Rep s1 l1 h1 z1) (r2 : Rep s2 l2 h2 z2) :
    tlt s1 l1 h1 s2 l2 h2 = bnat (z1 < z2) := by
  have hmab : bnat (h1 < h2) + bnat (h1 = h2) * bnat (l1 < l2)
      = bnat (z1.natAbs < z2.natAbs) := by
    rw [lt128 l1 h1 l2 h2 r1.lo_lt r2.lo_lt, r1.mag, r2.mag]
  have hmba : bnat (h2 < h1) + bnat (h1 = h2) * bnat (l2 < l1)
      = bnat (z2.natAbs < z1.natAbs) := by
    rw [bnat_eq_bnat (show (h1 = h2) ↔ (h2 = h1) from ⟨Eq.symm, Eq.symm⟩),
      lt128 l2 h2 l1 h1 r2.lo_lt r1.lo_lt, r1.mag, r2.mag]
  show s1 * (1 - s2) + s1 * s2 * (bnat (h2 < h1) + bnat (h1 = h2) * bnat (l2 < l1))
      + (1 - s1) * (1 - s2) * (bnat (h1 < h2) + bnat (h1 = h2) * bnat (l1 < l2))
      = bnat (z1 < z2)
  rw [hmab, hmba, r1.sign, r2.sign]
  by_cases hz1 : z1 < 0 <;> by_cases hz2 : z2 < 0
  · rw [bnat_true hz1, bnat_true hz2,
      bnat_eq_bnat (show (z2.natAbs < z1.natAbs) ↔ (z1 < z2) by omega)]
    omega
  · rw [bnat_true hz1, bnat_false hz2, bnat_true (show z1 < z2 by omega)]
    omega
  · rw [bnat_false hz1, bnat_true hz2, bnat_false (show ¬ (z1 < z2) by omega)]
    omega
  · rw [bnat_false hz1, bnat_false hz2,
      bnat_eq_bnat (show (z1.natAbs < z2.natAbs) ↔ (z1 < z2) by omega)]
    omega

/-- The `selTriple` pair that keeps the smaller of two canonical triples. -/
def selMin (s1 l1 h1 s2 l2 h2 : Nat) : Nat × Nat × Nat :=
  if tlt s1 l1 h1 s2 l2 h2 = 1 then (s1, l1, h1) else (s2, l2, h2)

/-- The `selTriple` pair that keeps the larger. -/
def selMax (s1 l1 h1 s2 l2 h2 : Nat) : Nat × Nat × Nat :=
  if tlt s1 l1 h1 s2 l2 h2 = 1 then (s2, l2, h2) else (s1, l1, h1)

/-- The canonicalized sign of a partial product. -/
def psign (sa sb : Nat) (p : Nat × Nat) : Nat :=
  (sa ^^^ sb) * (1 - bnat (p.1 = 0) * bnat (p.2 = 0))

/-- Selecting the smaller of two canonical triples by `tlt` (`selTriple`)
yields a canonical triple for the minimum. -/
theorem Rep_min {s1 l1 h1 s2 l2 h2 : Nat} {z1 z2 : Int}
    (r1 : Rep s1 l1 h1 z1) (r2 : Rep s2 l2 h2 z2) :
    Rep (selMin s1 l1 h1 s2 l2 h2).1 (selMin s1 l1 h1 s2 l2 h2).2.1
        (selMin s1 l1 h1 s2 l2 h2).2.2 (min z1 z2) := by
  unfold selMin
  rw [tlt_of_Rep r1 r2]
  by_cases hz : z1 < z2
  · rw [bnat_true hz, if_pos (rfl : (1 : Nat) = 1),
      show min z1 z2 = z1 by omega]
    exact r1
  · rw [bnat_false hz, if_neg (by decide : ¬((0 : Nat) = 1)),
      show min z1 z2 = z2 by omega]
    exact r2

/-- Selecting the larger. -/
theorem Rep_max {s1 l1 h1 s2 l2 h2 : Nat} {z1 z2 : Int}
    (r1 : Rep s1 l1 h1 z1) (r2 : Rep s2 l2 h2 z2) :
    Rep (selMax s1 l1 h1 s2 l2 h2).1 (selMax s1 l1 h1 s2 l2 h2).2.1
        (selMax s1 l1 h1 s2 l2 h2).2.2 (max z1 z2) := by
  unfold selMax
  rw [tlt_of_Rep r1 r2]
  by_cases hz : z1 < z2
  · rw [bnat_true hz, if_pos (rfl : (1 : Nat) = 1),
      show max z1 z2 = z2 by omega]
    exact r2
  · rw [bnat_false hz, if_neg (by decide : ¬((0 : Nat) = 1)),
      show max z1 z2 = z1 by omega]
    exact r1

/-- **The canonicalized sign-magnitude product** of two decoded endpoints
represents their `Int` product: the xor of the sign bits, killed when the
128-bit magnitude is zero, is the sign of the product. -/
theorem Rep_mul {x y : Int} {sx sy : Nat} {p : Nat × Nat}
    (hsx : sx = bnat (x < 0)) (hsy : sy = bnat (y < 0))
    (hmag : p.1 + M * p.2 = x.natAbs * y.natAbs)
    (hlo : p.1 < M) (hhi : p.2 < M) :
    Rep (psign sx sy p) p.1 p.2 (x * y) := by
  unfold psign
  generalize hp1 : p.1 = plo at hmag hlo ⊢
  generalize hp2 : p.2 = phi at hmag hhi ⊢
  have hmul : plo + M * phi = (x * y).natAbs := by
    rw [hmag, Int.natAbs_mul]
  have hM : (0 : Nat) < M := by simp only [M_val]; omega
  refine ⟨?_, hmul, hlo, hhi⟩
  by_cases hz : x * y = 0
  · have h0 : plo = 0 ∧ phi = 0 := by
      simp only [M_val] at hmul hM ⊢
      omega
    rw [bnat_true h0.1, bnat_true h0.2, bnat_false (show ¬ (x * y < 0) by omega)]
    omega
  · have hne : ¬ (plo = 0 ∧ phi = 0) := by
      intro hc
      simp only [hc.1, hc.2, M_val] at hmul
      omega
    have hfac : 1 - bnat (plo = 0) * bnat (phi = 0) = 1 := by
      by_cases h1 : plo = 0
      · rw [bnat_true h1, bnat_false (show ¬ (phi = 0) by
          intro h2; exact hne ⟨h1, h2⟩)]
      · rw [bnat_false h1]
        omega
    rw [hfac, Nat.mul_one, hsx, hsy]
    have hx0 : x ≠ 0 := by intro h; apply hz; rw [h]; omega
    have hy0 : y ≠ 0 := by intro h; apply hz; rw [h]; omega
    have hcase := LeanCompCert.Ports.Section413Cells.mul_neg_cases x y
    by_cases hxn : x < 0 <;> by_cases hyn : y < 0
    · rw [bnat_true hxn, bnat_true hyn,
        bnat_false (show ¬ (x * y < 0) by omega)]
      decide
    · rw [bnat_true hxn, bnat_false hyn,
        bnat_true (show x * y < 0 by omega)]
      decide
    · rw [bnat_false hxn, bnat_true hyn,
        bnat_true (show x * y < 0 by omega)]
      decide
    · rw [bnat_false hxn, bnat_false hyn,
        bnat_false (show ¬ (x * y < 0) by omega)]
      decide

/-! ## §11 The rounding half: an exact `10¹⁸` division with the rounding
picked by the sign

`divP18Body` produces the floor and the ceiling of the *magnitude*; the
model's outward rounding then selects one of them, and negates, according
to the sign bit — exactly the four `Section413Cells` bridges
`zfloorDiv_nonneg`/`zfloorDiv_neg`/`zceilDiv_nonneg`/`zceilDiv_neg`. -/

theorem CAP_sq : CAP * CAP = 1329227995784915872903807060280344576 := by decide

open LeanCompCert.Ports.Section413Cells (divP18q divP18ceil divP18q_spec
  divP18ceil_spec zfloorDiv_nonneg zfloorDiv_neg zceilDiv_nonneg zceilDiv_neg)

/-- The exact divider, evaluated at a capped magnitude. -/
theorem tdiv18_of_Rep {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) :
    tdiv18 lo hi =
      (z.natAbs / 1000000000000000000,
       (z.natAbs + 999999999999999999) / 1000000000000000000) := by
  have hlo : lo < 18446744073709551616 := by
    have := r.lo_lt; simp only [M_val] at this; exact this
  have hhi : hi < 18446744073709551616 := by
    have := r.hi_lt; simp only [M_val] at this; exact this
  have hmag : lo + 18446744073709551616 * hi = z.natAbs := by
    have := r.mag; simp only [M_val] at this; exact this
  rw [CAP_sq] at hb
  rw [tdiv18_eq lo hi hlo hhi (by omega)]
  have hq : divP18q lo hi = z.natAbs / 1000000000000000000 := by
    rw [divP18q_spec lo hi hlo hhi]
    simp only [LeanCompCert.Ports.Section413Cells.P18,
      LeanCompCert.Verified.MulWide.B64]
    rw [hmag]
  have hc : divP18ceil lo hi =
      (z.natAbs + 999999999999999999) / 1000000000000000000 := by
    rw [divP18ceil_spec lo hi hlo hhi]
    simp only [LeanCompCert.Ports.Section413Cells.P18,
      LeanCompCert.Verified.MulWide.B64]
    rw [hmag]
  rw [hq, hc]

/-- Both quotients of a capped magnitude are small enough to encode. -/
theorem quot_small {z : Int} (hb : z.natAbs ≤ CAP * CAP) :
    z.natAbs / 1000000000000000000 < 9223372036854775808 ∧
    (z.natAbs + 999999999999999999) / 1000000000000000000
      < 9223372036854775808 := by
  rw [CAP_sq] at hb
  omega

/-- The lower endpoint of the rounded cell: outward rounding picks the
ceiling of the magnitude on the negative branch, the floor otherwise. -/
def roundLo (s lo hi : Nat) : Nat :=
  if s = 1 then tsub 0 (tdiv18 lo hi).2 else (tdiv18 lo hi).1

/-- The upper endpoint of the rounded cell. -/
def roundHi (s lo hi : Nat) : Nat :=
  if s = 1 then tsub 0 (tdiv18 lo hi).1 else (tdiv18 lo hi).2

/-! A note on tactic discipline in what follows.  `tsub` and `tdiv18` are
`% 2⁶⁴`-saturated definitions whose bodies the kernel will happily try to
*evaluate*: any tactic that forces a `whnf` through one of them (a `show`
across an `ite`, say) sends the kernel into the five-digit long division
and it reports "deep recursion".  Every `ite` below is therefore taken
apart by a **syntactic** `rw [if_pos …]` / `rw [if_neg …]`, never by
reduction, and `tdiv18` is rewritten away by `tdiv18_of_Rep` before
anything else touches it. -/

/-- The lower endpoint, negative branch. -/
theorem divLo_neg {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) (hz : z < 0) :
    tsub 0 (tdiv18 lo hi).2
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cfloorDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  obtain ⟨_, hs2⟩ := quot_small hb
  rw [tdiv18_of_Rep r hb]
  unfold LeanCompCert.Ports.Section413Sweep.cfloorDiv
  rw [zfloorDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz (by decide)]
  show tsub 0 ((z.natAbs + 999999999999999999) / 1000000000000000000)
    = encodeZ (-(((z.natAbs + 999999999999999999) / 1000000000000000000
        : Nat) : Int))
  rw [tsub_zero_encodeZ_neg _ hs2]

/-- The lower endpoint, nonnegative branch. -/
theorem divLo_nonneg {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) (hz : ¬ z < 0) :
    (tdiv18 lo hi).1
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cfloorDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  obtain ⟨hs1, _⟩ := quot_small hb
  rw [tdiv18_of_Rep r hb]
  unfold LeanCompCert.Ports.Section413Sweep.cfloorDiv
  rw [zfloorDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)]
  show (z.natAbs / 1000000000000000000 : Nat)
    = encodeZ ((z.natAbs / 1000000000000000000 : Nat) : Int)
  rw [encodeZ_ofNat _ hs1]

/-- **The lower endpoint**: floor division of the signed minimum by `10¹⁸`,
outward-rounded through the magnitude. -/
theorem divLo_spec {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) :
    roundLo s lo hi
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cfloorDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  unfold roundLo
  rw [r.sign]
  by_cases hz : z < 0
  · rw [bnat_true hz, if_pos (rfl : (1 : Nat) = 1)]
    exact divLo_neg r hb hz
  · rw [bnat_false hz, if_neg (by decide : ¬((0 : Nat) = 1))]
    exact divLo_nonneg r hb hz

/-- The upper endpoint, negative branch. -/
theorem divHi_neg {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) (hz : z < 0) :
    tsub 0 (tdiv18 lo hi).1
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cceilDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  obtain ⟨hs1, _⟩ := quot_small hb
  rw [tdiv18_of_Rep r hb]
  unfold LeanCompCert.Ports.Section413Sweep.cceilDiv
  rw [zceilDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz]
  show tsub 0 (z.natAbs / 1000000000000000000)
    = encodeZ (-((z.natAbs / 1000000000000000000 : Nat) : Int))
  rw [tsub_zero_encodeZ_neg _ hs1]

/-- The upper endpoint, nonnegative branch. -/
theorem divHi_nonneg {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) (hz : ¬ z < 0) :
    (tdiv18 lo hi).2
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cceilDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  obtain ⟨_, hs2⟩ := quot_small hb
  rw [tdiv18_of_Rep r hb]
  unfold LeanCompCert.Ports.Section413Sweep.cceilDiv
  rw [zceilDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)
      (by decide)]
  show ((z.natAbs + 999999999999999999) / 1000000000000000000 : Nat)
    = encodeZ (((z.natAbs + 999999999999999999) / 1000000000000000000
        : Nat) : Int)
  rw [encodeZ_ofNat _ hs2]

/-- **The upper endpoint**: ceiling division of the signed maximum. -/
theorem divHi_spec {s lo hi : Nat} {z : Int} (r : Rep s lo hi z)
    (hb : z.natAbs ≤ CAP * CAP) :
    roundHi s lo hi
      = encodeZ (LeanCompCert.Ports.Section413Sweep.cceilDiv z
          LeanCompCert.Ports.Section413Sweep.SCALE) := by
  unfold roundHi
  rw [r.sign]
  by_cases hz : z < 0
  · rw [bnat_true hz, if_pos (rfl : (1 : Nat) = 1)]
    exact divHi_neg r hb hz
  · rw [bnat_false hz, if_neg (by decide : ¬((0 : Nat) = 1))]
    exact divHi_nonneg r hb hz

/-! ## §12 The interval product

`cmulBack` is the back half of `cmulBody` — the two comparisons, the two
selections, the two 4-way reductions and the two divisions — transcribed
from `tcmul`, which it equals definitionally (`tcmul_eq_back`). -/

/-- The min/max/divide back half of the interval product. -/
def cmulBack (s1 l1 h1 s2 l2 h2 s3 l3 h3 s4 l4 h4 : Nat) : Nat × Nat :=
  let n1 := selMin s1 l1 h1 s2 l2 h2
  let x1 := selMax s1 l1 h1 s2 l2 h2
  let n2 := selMin s3 l3 h3 s4 l4 h4
  let x2 := selMax s3 l3 h3 s4 l4 h4
  let mn := selMin n1.1 n1.2.1 n1.2.2 n2.1 n2.2.1 n2.2.2
  let mx := selMax x1.1 x1.2.1 x1.2.2 x2.1 x2.2.1 x2.2.2
  (roundLo mn.1 mn.2.1 mn.2.2, roundHi mx.1 mx.2.1 mx.2.2)

set_option maxHeartbeats 1000000 in
/-- **`tcmul`'s two output words are exactly `cmulBack`** at the four
canonicalized partial products.

The eight `tmag`/`hl` results are taken as *abstract* hypotheses rather
than inlined: substituting them would duplicate `hl`'s body four times and
its two outputs a dozen times more, and the resulting term is far too
large for the elaborator to check.  With them abstract, unfolding the
whole block leaves a term whose atoms are variables. -/
theorem tcmul_eq_back (gate aLo aHi bLo bHi viol : Nat)
    {sa1 ma1 sa2 ma2 sb1 mb1 sb2 mb2 : Nat} {p1 p2 p3 p4 : Nat × Nat}
    (ha1 : tmag aLo = (sa1, ma1)) (ha2 : tmag aHi = (sa2, ma2))
    (hb1 : tmag bLo = (sb1, mb1)) (hb2 : tmag bHi = (sb2, mb2))
    (hq1 : Verified.MulWide.hl ma1 mb1 = p1)
    (hq2 : Verified.MulWide.hl ma1 mb2 = p2)
    (hq3 : Verified.MulWide.hl ma2 mb1 = p3)
    (hq4 : Verified.MulWide.hl ma2 mb2 = p4) :
    ((tcmul gate aLo aHi bLo bHi viol).1,
     (tcmul gate aLo aHi bLo bHi viol).2.1) =
      cmulBack (psign sa1 sb1 p1) p1.1 p1.2
               (psign sa1 sb2 p2) p2.1 p2.2
               (psign sa2 sb1 p3) p3.1 p3.2
               (psign sa2 sb2 p4) p4.1 p4.2 := by
  simp only [tcmul, cmulBack, selMin, selMax, roundLo, roundHi, psign, ha1, ha2, hb1, hb2, hq1, hq2, hq3, hq4]

/-- **The back half computes the outward-rounded interval product** of the
four partial products. -/
theorem cmulBack_spec {s1 l1 h1 s2 l2 h2 s3 l3 h3 s4 l4 h4 : Nat}
    {v1 v2 v3 v4 : Int}
    (r1 : Rep s1 l1 h1 v1) (r2 : Rep s2 l2 h2 v2)
    (r3 : Rep s3 l3 h3 v3) (r4 : Rep s4 l4 h4 v4)
    (b1 : v1.natAbs ≤ CAP * CAP) (b2 : v2.natAbs ≤ CAP * CAP)
    (b3 : v3.natAbs ≤ CAP * CAP) (b4 : v4.natAbs ≤ CAP * CAP) :
    cmulBack s1 l1 h1 s2 l2 h2 s3 l3 h3 s4 l4 h4 =
      (encodeZ (LeanCompCert.Ports.Section413Sweep.cfloorDiv
          (min (min v1 v2) (min v3 v4))
          LeanCompCert.Ports.Section413Sweep.SCALE),
       encodeZ (LeanCompCert.Ports.Section413Sweep.cceilDiv
          (max (max v1 v2) (max v3 v4))
          LeanCompCert.Ports.Section413Sweep.SCALE)) := by
  have rmn := Rep_min (Rep_min r1 r2) (Rep_min r3 r4)
  have rmx := Rep_max (Rep_max r1 r2) (Rep_max r3 r4)
  rw [CAP_sq] at b1 b2 b3 b4
  have bmn : (min (min v1 v2) (min v3 v4)).natAbs ≤ CAP * CAP := by
    rw [CAP_sq]; omega
  have bmx : (max (max v1 v2) (max v3 v4)).natAbs ≤ CAP * CAP := by
    rw [CAP_sq]; omega
  simp only [cmulBack, divLo_spec rmn bmn, divHi_spec rmx bmx]

/-! ## §13 **The cell transfer**: `tcmul` is `Section413Sweep.cmul` -/

/-- Each of the four partial products of two capped endpoints is a
canonical triple for the `Int` product. -/
theorem Rep_of_endpoints {x y : Int} (hx : x.natAbs ≤ CAP) (hy : y.natAbs ≤ CAP) :
    Rep (psign (bnat (x < 0)) (bnat (y < 0))
          (Verified.MulWide.hl x.natAbs y.natAbs))
        (Verified.MulWide.hl x.natAbs y.natAbs).1
        (Verified.MulWide.hl x.natAbs y.natAbs).2 (x * y) := by
  have hxb : x.natAbs < LeanCompCert.Verified.MulWide.B64 := by
    rw [B64_val]; simp only [CAP_val, M_val] at *; omega
  have hyb : y.natAbs < LeanCompCert.Verified.MulWide.B64 := by
    rw [B64_val]; simp only [CAP_val, M_val] at *; omega
  have h1 := (Verified.MulWide.hl_spec x.natAbs y.natAbs hxb hyb).1
  have h2 := (Verified.MulWide.hl_spec x.natAbs y.natAbs hxb hyb).2
  have h3 := Verified.MulWide.hl_hi_lt x.natAbs y.natAbs hxb hyb
  rw [B64_val] at h1 h2 h3
  exact Rep_mul rfl rfl h1 h2 h3

/-- Two capped endpoints have a product within the squared cap — the
regime `divP18q_spec` needs. -/
theorem mul_natAbs_le {x y : Int} (hx : x.natAbs ≤ CAP) (hy : y.natAbs ≤ CAP) :
    (x * y).natAbs ≤ CAP * CAP := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul hx hy

/-- **The interval product transfers.**  On a live gate, with the flag
still clean after the block, the machine's `cmulBody` computes the encoded
endpoints of `Section413Sweep.cmul` applied to the decoded input cells.

This is step 2 of the obligation's architecture: everything below the
model's `cmul` — the four 128-bit products, the branchless 4-way min and
max, the exact `10¹⁸` divider and its sign-directed outward rounding — is
now discharged in one lemma. -/
theorem tcmul_spec {gate aLo aHi bLo bHi viol : Nat} (hg : 0 < gate)
    (haLo : aLo < M) (haHi : aHi < M) (hbLo : bLo < M) (hbHi : bHi < M)
    (hclean : (tcmul gate aLo aHi bLo bHi viol).2.2 = 0) :
    ((tcmul gate aLo aHi bLo bHi viol).1,
     (tcmul gate aLo aHi bLo bHi viol).2.1) =
      (encodeZ (LeanCompCert.Ports.Section413Sweep.cmul
          ⟨decodeZ aLo, decodeZ aHi⟩ ⟨decodeZ bLo, decodeZ bHi⟩).lo,
       encodeZ (LeanCompCert.Ports.Section413Sweep.cmul
          ⟨decodeZ aLo, decodeZ aHi⟩ ⟨decodeZ bLo, decodeZ bHi⟩).hi) := by
  obtain ⟨-, hcap⟩ := tcmul_viol_eq_zero hclean
  obtain ⟨c1, c2, c3, c4⟩ := hcap hg
  rw [tmag_mag aLo haLo] at c1
  rw [tmag_mag aHi haHi] at c2
  rw [tmag_mag bLo hbLo] at c3
  rw [tmag_mag bHi hbHi] at c4
  have ha1 : tmag aLo = (bnat (decodeZ aLo < 0), (decodeZ aLo).natAbs) := by
    rw [← tmag_sign aLo haLo, ← tmag_mag aLo haLo]
  have ha2 : tmag aHi = (bnat (decodeZ aHi < 0), (decodeZ aHi).natAbs) := by
    rw [← tmag_sign aHi haHi, ← tmag_mag aHi haHi]
  have hb1 : tmag bLo = (bnat (decodeZ bLo < 0), (decodeZ bLo).natAbs) := by
    rw [← tmag_sign bLo hbLo, ← tmag_mag bLo hbLo]
  have hb2 : tmag bHi = (bnat (decodeZ bHi < 0), (decodeZ bHi).natAbs) := by
    rw [← tmag_sign bHi hbHi, ← tmag_mag bHi hbHi]
  rw [tcmul_eq_back gate aLo aHi bLo bHi viol ha1 ha2 hb1 hb2 rfl rfl rfl rfl,
    cmulBack_spec (Rep_of_endpoints c1 c3) (Rep_of_endpoints c1 c4)
      (Rep_of_endpoints c2 c3) (Rep_of_endpoints c2 c4)
      (mul_natAbs_le c1 c3) (mul_natAbs_le c1 c4)
      (mul_natAbs_le c2 c3) (mul_natAbs_le c2 c4)]
  rfl

/-! ## §14 Encoded arithmetic transfers

The wrapped `u64` operations of the transparent model are the reference
model's `Int` operations on the decoded endpoints.  Unconditionally the
machine computes `encodeZ` of the right value; the *capped* forms below add
that no wrap occurred, so `decodeZ` reads it back — that is exactly what
the runtime guards buy, since two capped endpoints sum to at most
`2·CAP = 2⁶¹`, comfortably inside the signed range `2⁶³`. -/

theorem encodeZ_zero : encodeZ 0 = 0 := rfl

/-- Machine addition of two encoded endpoints (`encodeZ_add`). -/
theorem add_transfer (a b : Nat) (ha : a < M) (hb : b < M) :
    (a + b) % M = encodeZ (decodeZ a + decodeZ b) := by
  have h := LeanCompCert.Ports.Section413Cells.encodeZ_add (decodeZ a) (decodeZ b)
  rw [encodeZ_decodeZ_self ha, encodeZ_decodeZ_self hb] at h
  rw [← h]
  rfl

/-- Machine doubling, which the touch block writes as `x + x`
(`encodeZ_double`). -/
theorem double_transfer (a : Nat) (ha : a < M) :
    (a + a) % M = encodeZ (2 * decodeZ a) := by
  have h := LeanCompCert.Ports.Section413Cells.encodeZ_double (decodeZ a)
  rw [encodeZ_decodeZ_self ha] at h
  rw [show a + a = 2 * a by omega, ← h]
  rfl

/-- A gated copy `g · x` with `g` a `0`/`1` gate. -/
theorem gate_transfer (g a : Nat) (hg : g ≤ 1) (ha : a < M) :
    (g * a) % M = encodeZ (if g = 1 then decodeZ a else 0) := by
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  · rw [if_neg (by decide : ¬((0 : Nat) = 1)), encodeZ_zero, Nat.zero_mul]
    exact Nat.zero_mod M
  · rw [if_pos rfl, encodeZ_decodeZ_self ha, Nat.one_mul]
    exact Nat.mod_eq_of_lt ha

/-- **Addition transfers exactly** when both operands are capped: the sum
is at most `2·CAP` in magnitude, so nothing wrapped. -/
theorem decodeZ_add {a b : Nat} (ha : a < M) (hb : b < M)
    (ca : Capped a) (cb : Capped b) :
    decodeZ ((a + b) % M) = decodeZ a + decodeZ b := by
  unfold Capped at ca cb
  rw [add_transfer a b ha hb]
  refine decodeZ_encodeZ _ ?_ ?_ <;>
    (simp only [cellsH63_val, CAP_val] at *; omega)

/-- **Doubling transfers exactly** on a capped operand. -/
theorem decodeZ_double {a : Nat} (ha : a < M) (ca : Capped a) :
    decodeZ ((a + a) % M) = 2 * decodeZ a := by
  unfold Capped at ca
  rw [double_transfer a ha]
  refine decodeZ_encodeZ _ ?_ ?_ <;>
    (simp only [cellsH63_val, CAP_val] at *; omega)

/-- **Negation transfers exactly** on a capped operand. -/
theorem decodeZ_tsub_zero {a : Nat} (ha : a < M) (ca : Capped a) :
    decodeZ (tsub 0 a) = -decodeZ a := by
  unfold Capped at ca
  rw [tsub_eq_encodeZ 0 a (by simp only [M_val]; omega) ha,
    LeanCompCert.Ports.Section413Cells.decodeZ_zero, Int.zero_sub]
  refine decodeZ_encodeZ _ ?_ ?_ <;>
    (simp only [cellsH63_val, CAP_val] at *; omega)

/-- **A gated copy transfers exactly** on a capped operand. -/
theorem decodeZ_gate {g a : Nat} (hg : g ≤ 1) (ha : a < M) :
    decodeZ ((g * a) % M) = if g = 1 then decodeZ a else 0 := by
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  · rw [if_neg (by decide : ¬((0 : Nat) = 1)), Nat.zero_mul, Nat.zero_mod]
    exact LeanCompCert.Ports.Section413Cells.decodeZ_zero
  · rw [if_pos rfl, Nat.one_mul, Nat.mod_eq_of_lt ha]

/-- The two outputs of `tcmul` are `u64`s (they are `encodeZ` images). -/
theorem tcmul_lt {gate aLo aHi bLo bHi viol : Nat} (hg : 0 < gate)
    (haLo : aLo < M) (haHi : aHi < M) (hbLo : bLo < M) (hbHi : bHi < M)
    (hclean : (tcmul gate aLo aHi bLo bHi viol).2.2 = 0) :
    (tcmul gate aLo aHi bLo bHi viol).1 < M ∧
    (tcmul gate aLo aHi bLo bHi viol).2.1 < M := by
  have h := tcmul_spec hg haLo haHi hbLo hbHi hclean
  rw [Prod.mk.injEq] at h
  refine ⟨?_, ?_⟩
  · rw [h.1]; exact encodeZ_lt_M _
  · rw [h.2]; exact encodeZ_lt_M _

/-! ## §15 The guard invariant

The predicate the forward induction of the remaining obligation carries.
It is a *definition*, not a claim; its preservation lemma is stated in the
`OPEN` section below and is not proved here.

Every persistent cell word and every live accumulator slot is `encodeZ` of
an `Int` of magnitude at most `CAP`, so no `% 2⁶⁴` in the transparent model
truncated anything; the μ plane holds only the codes `0/1/2`; and the flag
itself is a bit. -/

/-- The width part of the invariant on the register file. -/
def RegsCapped (t : TState) : Prop :=
  Capped t.wLo ∧ Capped t.wHi ∧ Capped t.wwLo ∧ Capped t.wwHi ∧
  Capped t.dLo ∧ Capped t.dHi ∧ Capped t.gLo ∧ Capped t.gHi

/-- The width part of the invariant on the two accumulator planes of a
configuration, together with the μ plane's alphabet. -/
def ArrCapped (c : Cfg) (t : TState) : Prop :=
  (∀ d, d ≤ c.cap → Capped (t.arr (d + c.plane1))) ∧
  (∀ d, d ≤ c.cap → Capped (t.arr (d + c.plane2))) ∧
  (∀ d, d ≤ c.cap → t.arr d = 0 ∨ t.arr d = 1 ∨ t.arr d = 2)

/-- **The guard invariant.**  Under it every word in flight decodes
exactly, so the machine's wrapped arithmetic is the reference model's `Int`
arithmetic. -/
def Inv (c : Cfg) (t : TState) : Prop :=
  t.viol ≤ 1 ∧ RegsCapped t ∧ ArrCapped c t

/-- The initial state satisfies the invariant: the zero-filled array is the
all-zero cell table, and `μ(1) = +1` is a legal μ code. -/
theorem Inv_tInit (c : Cfg) : Inv c tInit := by
  have hz : Capped 0 := by
    unfold Capped decodeZ
    simp only [cellsH63_val, CAP_val]
    split <;> omega
  refine ⟨by decide, ⟨hz, hz, hz, hz, hz, hz, hz, hz⟩, ?_, ?_, ?_⟩
  · intro d _
    show Capped (if d + c.plane1 = 1 then 1 else 0)
    split
    · unfold Capped decodeZ
      simp only [cellsH63_val, CAP_val]
      split <;> omega
    · exact hz
  · intro d _
    show Capped (if d + c.plane2 = 1 then 1 else 0)
    split
    · unfold Capped decodeZ
      simp only [cellsH63_val, CAP_val]
      split <;> omega
    · exact hz
  · intro d _
    show (if d = 1 then 1 else 0) = 0 ∨ (if d = 1 then 1 else 0) = 1 ∨
      (if d = 1 then 1 else 0) = 2
    split <;> simp

/-! ## OPEN: what remains of obligation (2)

Nothing below is proved; each item is stated exactly as it will have to be
proved, so that the next pass can pick any one of them up in isolation.
None of them is asserted anywhere in this file, as an axiom or otherwise.

**(O1) The invariant is preserved on the clean branch.**

```text
theorem Inv_tstep (c : Cfg) (hc : Admissible c) (idx : Nat) (t : TState)
    (hidx : idx < c.loopCount) (hI : Inv c t)
    (hclean : (c.tstep idx t).viol = 0) : Inv c (c.tstep idx t)
```

The route is the one the guards were placed for: `tstep_viol_le` and
`tcmul_viol_eq_zero`/`tguard_eq_zero` above turn `hclean` into the four
magnitude bounds of every product and the six accumulator bounds of every
touch; `capped_iff_guard_clean` turns each of those into `Capped`.

**(O2) The touch block computes `Section413Sweep.touch`.**

```text
theorem ttouch_spec (c : Cfg) (g d : Nat) (t : TState) (hg : g = 1)
    (hd : 0 < d) (hdc : d ≤ c.cap) (hI : Inv c t)
    (hclean : (c.ttouch g d t).viol = 0)
    (hmu : t.arr d = MertensCDEM.muCode d c.rounds) :
    ((c.ttouch g d t).arr (d + c.plane1),
     (c.ttouch g d t).arr (d + c.plane2),
     (c.ttouch g d t).dLo, (c.ttouch g d t).dHi)
      = (encodeZ (Section413Sweep.touch c.rounds W (A, D) d).1[d]!.lo, …)
```

where `A`, `W`, `D` are the decoded accumulator table, weight cell and
delta cell.  The `cmul A w` and `cmul w w` halves are `tcmul_spec` above;
what is left is the `csmul mu` case split on the μ code (three cases,
`+1/−1/0`, the negative one swapping the endpoints — that is
`Section413Sweep.csmul`'s own case split) and the two `cadd`s, each of
which is `Section413Cells.encodeZ_add` under `Inv`.  A gated-off touch
(`g = 0`) is the identity on the decoded state.

**(O3) Phase 1 computes `μ`.**

```text
theorem phase1_muCode (c : Cfg) (hc : Admissible c) (h : c.tFlag = 0)
    (n : Nat) (hn : 2 ≤ n) (hnc : n ≤ c.cap) :
    (tRunUpto c ((n - 1) * c.rounds)).arr n
      = MertensCDEM.muCode n c.rounds
```

The registers `res/sq/par` of `tstep` are literally
`MertensCDEM.trialStep` at the decoded divisor, so this is an induction
over the `c.rounds` rounds of the candidate-major block relating them to
`MertensCDEM.trialRun`, then the decode `code = 0/1/2`.  `μ(1) = +1` is
`tInit`.  `Admissible.cover` is what makes `muCode` correct for `n ≤ cap`.

**(O4) Pass A computes `sigmaPair`.**

```text
theorem passA_sigma (c : Cfg) (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s)).sigma
      = Section413Sweep.sigmaPair X
```

An induction over the `c.s` rounds of pass A; the gate
`X % r = 0 ∧ r² ≤ X` is the same divisor set as `sigmaPair`'s
`List.range (Nat.sqrt X)` filter, and the `X / r ≠ r` suppression is the
same.

**(O5) The weight round computes `weightV2`.**

```text
theorem weight_spec (c : Cfg) … :
    (decodeZ (…).wLo, decodeZ (…).wHi)
      = ((Section413Sweep.weightV2 c.rounds X).lo,
         (Section413Sweep.weightV2 c.rounds X).hi)
```

`⌊SCALE/σ⌋` and `⌈SCALE/σ⌉` against the μ code are `cratSMul (muZ X R)
(sigmaPair X) cone` outward-rounded; the parity gate `X % 2 = 1` is
`weightV2`'s.  Uses (O3) and (O4).

**(O6) Pass B is one `stepDivisors` block.**

```text
theorem passB_stepDivisors (c : Cfg) … :
    (decoded accumulator table, decoded delta) after the 2·s rounds
      = Section413Sweep.stepDivisors c.rounds X W (A, czero)
```

The two gated touches per round realize exactly one iteration of
`stepDivisors`' fold — divisor `r` and partner `X / r`, the partner
suppressed when equal — so this is (O2) plus an induction over `c.s`.

**(O7) Finalize is `cadd` and `g2Check`.**

```text
theorem fin_spec (c : Cfg) … (hclean : …) :
    c.checkLo ≤ X → Section413Sweep.g2Check X G' = true
```

`g += delta` is `cadd`; the two wide comparisons against the two-limb
literal `21·10¹⁸` are `g2Check` of the decoded `g` cell — via
`Verified.MulWide.hl_spec` on `|g.lo| · 10X` and `|g.hi| · 10X`, with the
sign registers `sLo`/`sHi` selecting which side of the two-sided test the
comparison discharges.

**(O8) The run.**

```text
theorem tFlag_zero_sound (c : Cfg) (hc : Admissible c) (h : c.tFlag = 0) :
    Section413Sweep.g2SweepOK c.rounds c.checkLo c.cap = true
```

One induction over `List.range c.loopCount` relating `tRunUpto c k` to the
prefix state of `Section413Sweep.g2Run`, using
`tRunUpto_viol_zero_of_tFlag` to keep the flag clean at every prefix and
(O1)–(O7) for the per-block steps; the Boolean is then read off the final
state.  This is the obligation itself.
-/

end LeanCompCert.Ports.Section413G2Sound
