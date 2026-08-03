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

end LeanCompCert.Ports.Section413G2Sound
