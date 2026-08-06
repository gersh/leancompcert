import LeanCompCert.Ports.Section413G2PassBGateDenote
import LeanCompCert.Verified.SqrtEquiv

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
   and `tcmul` is `Section413Sweep.cmul` of the decoded cells — the last
   of these, `tcmul_spec`, is the heaviest single block of the program
   (378 of its instructions, three uses per iteration).  The wrapped
   `+`, `2·` and `0−` of the surrounding blocks transfer likewise.
4. **Phase 1, phase 2, the run.**  `sweep_prefix` relates every candidate
   boundary to `g2Prefix`; `tFlag_zero_sound` reads the final Boolean.

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
  /-- The live range contains the first nontrivial candidate. -/
  cap_ge_two : 2 ≤ c.cap
  /-- Every candidate is covered by the trial division: `X ≤ N < (R+2)²`,
  so a leftover residual above `R+1` is prime. -/
  cover : c.cap < (c.rounds + 2) * (c.rounds + 2)
  /-- The three planes fit in the `u64` address space. -/
  arr_fits : 3 * (c.cap + 1) < M
  /-- A `√`-free upper bound for the loop length, hence `loopCount < 2⁶⁴`. -/
  loop_fits : (c.cap - 1) * c.rounds + c.cap * (2 * c.cap + 2) < M
  /-- The largest crude divisor sum plus the fixed-point scale does not wrap
  while forming the rounded weight numerator. -/
  weight_fits : c.cap * (2 * c.cap + 2) + SCALE < M
  /-- The first checked candidate is a real one. -/
  checkLo_pos : 0 < c.checkLo
  /-- The first checked candidate lies in the finite sweep. -/
  checkLo_le_cap : c.checkLo ≤ c.cap

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

/-- The finalizer's factor `10 * X` is an ordinary `u64` natural throughout
the configured sweep.  The large-cap case follows from `weight_fits`; the
three smaller admissible caps are discharged directly against `2^64`. -/
theorem Admissible.ten_cap_lt {c : Cfg} (h : Admissible c) :
    c.cap * 10 < M := by
  by_cases hlarge : 4 ≤ c.cap
  · have hten : 10 ≤ 2 * c.cap + 2 := by omega
    have hmul := Nat.mul_le_mul_left c.cap hten
    have hfit := h.weight_fits
    omega
  · have hsmall : c.cap * 10 ≤ 30 := by omega
    exact Nat.lt_of_le_of_lt hsmall (by decide)

theorem Admissible.ten_lt {c : Cfg} (h : Admissible c) {X : Nat}
    (hX : X ≤ c.cap) : X * 10 < M := by
  have := Nat.mul_le_mul_right 10 hX
  exact Nat.lt_of_le_of_lt this h.ten_cap_lt

/-- Forget the mathematical covering and fixed-point guards when invoking
the already-proved machine-stage range lemmas from the denotation layer. -/
theorem Admissible.toDenote {c : Cfg} (h : Admissible c) :
    LeanCompCert.Ports.Section413G2Denote.Admissible c where
  capPos := h.cap_ge_two
  roundsPos := Nat.lt_of_lt_of_le (by decide) h.rounds_ge
  arrayLt := by simpa only [Cfg.arrayLen] using h.arr_fits
  loopLt := h.loopCount_lt
  checkLoLt := by
    have hcapM : c.cap < M := by
      exact Nat.lt_trans (by omega : c.cap < 3 * (c.cap + 1)) h.arr_fits
    exact Nat.lt_of_le_of_lt h.checkLo_le_cap hcapM

/-- **The production configuration is admissible.** -/
theorem production_admissible : Admissible production :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- So is the smoke configuration. -/
theorem smoke_admissible : Admissible smoke :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## §1 The two moduli, and `bnat` -/

theorem M_val : M = 18446744073709551616 := rfl

theorem B64_val : LeanCompCert.Verified.MulWide.B64 = M := rfl

theorem CAP_val : CAP = 1152921504606846976 := rfl

theorem SCALE_eq_sweep : SCALE = LeanCompCert.Ports.Section413Sweep.SCALE := rfl

theorem H63_val : H63 = 9223372036854775808 := rfl

theorem KLO_val : KLO = 2553255926290448384 := rfl

theorem threshold_split : KLO + M = 21 * SCALE := by decide

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

theorem capped_of_range {w : Nat}
    (hlo : -(CAP : Int) ≤ decodeZ w) (hhi : decodeZ w ≤ (CAP : Int)) :
    Capped w := by
  unfold Capped decodeZ at *
  simp only [M_val, CAP_val, cellsH63_val, B64_val] at *
  split at * <;> omega

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

theorem ttouchTerm_viol_le (g pLo pHi wwLo wwHi viol : Nat) :
    viol ≤ (ttouchTerm g pLo pHi wwLo wwHi viol).2.2 := by
  refine Nat.le_trans (tguard_le _ _ _) (tguard_le _ _ _)

theorem ttouchProductViol_viol_le (g pLo pHi viol : Nat) :
    viol ≤ ttouchProductViol g pLo pHi viol := by
  refine Nat.le_trans (tguard_le _ _ _) (tguard_le _ _ _)

theorem ttouchDelta_viol_le (g mc tLo tHi dLo dHi viol : Nat) :
    viol ≤ (ttouchDelta g mc tLo tHi dLo dHi viol).2.2 := by
  refine Nat.le_trans (tguard_le _ _ _) (tguard_le _ _ _)

/-- The two post-product guards recover local caps on the product endpoints.
They are intentionally local: untouched accumulator cells need no global
width invariant. -/
theorem ttouchProductViol_eq_zero {g pLo pHi viol : Nat}
    (hg : 0 < g) (hpLo : pLo < M) (hpHi : pHi < M)
    (h : ttouchProductViol g pLo pHi viol = 0) :
    viol = 0 ∧ Capped pLo ∧ Capped pHi := by
  have hHi : Capped pHi := capped_of_tguard_eq_zero hpHi hg h
  have hInner : tguard g pLo viol = 0 := (tguard_eq_zero h).1
  exact ⟨(tguard_eq_zero hInner).1,
    capped_of_tguard_eq_zero hpLo hg hInner, hHi⟩

/-- A clean `2P + w²` stage caps both produced term endpoints and propagates
cleanliness back to the incoming flag. -/
theorem ttouchTerm_eq_zero {g pLo pHi wwLo wwHi viol : Nat}
    (hg : 0 < g) (h : (ttouchTerm g pLo pHi wwLo wwHi viol).2.2 = 0) :
    viol = 0 ∧ Capped (ttouchTerm g pLo pHi wwLo wwHi viol).1 ∧
      Capped (ttouchTerm g pLo pHi wwLo wwHi viol).2.1 := by
  let tLo := ((pLo + pLo) % M + wwLo) % M
  let tHi := ((pHi + pHi) % M + wwHi) % M
  have hMpos : 0 < M := by simp only [M_val]; omega
  have hLoLt : tLo < M := Nat.mod_lt _ hMpos
  have hHiLt : tHi < M := Nat.mod_lt _ hMpos
  change tguard g tHi (tguard g tLo viol) = 0 at h
  have hHi : Capped tHi := capped_of_tguard_eq_zero hHiLt hg h
  have hInner : tguard g tLo viol = 0 := (tguard_eq_zero h).1
  have hLo : Capped tLo := capped_of_tguard_eq_zero hLoLt hg hInner
  change viol = 0 ∧ Capped tLo ∧ Capped tHi
  exact ⟨(tguard_eq_zero hInner).1, hLo, hHi⟩

theorem ttouch_viol_le (c : Cfg) (g d : Nat) (t : TState) :
    t.viol ≤ (c.ttouch g d t).viol := by
  let r := tcmul g (t.arr (c.touchA1 g d)) (t.arr (c.touchA2 g d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol g r.1 r.2.1 r.2.2
  let term := ttouchTerm g r.1 r.2.1 t.wwLo t.wwHi pViol
  let delta := ttouchDelta g (t.arr (c.touchBase g d)) term.1 term.2.1
    t.dLo t.dHi term.2.2
  change t.viol ≤ delta.2.2
  exact Nat.le_trans (tcmul_viol_le _ _ _ _ _ _)
    (Nat.le_trans (ttouchProductViol_viol_le _ _ _ _)
      (Nat.le_trans (ttouchTerm_viol_le _ _ _ _ _ _)
        (ttouchDelta_viol_le _ _ _ _ _ _ _)))

/-- A clean full touch makes every internal guarded stage clean.  This is the
backwards dataflow used by the local transfer proof. -/
theorem ttouch_clean_parts (c : Cfg) (g d : Nat) (t : TState)
    (hclean : (c.ttouch g d t).viol = 0) :
    let r := tcmul g (t.arr (c.touchA1 g d)) (t.arr (c.touchA2 g d))
      t.wLo t.wHi t.viol
    let pViol := ttouchProductViol g r.1 r.2.1 r.2.2
    let term := ttouchTerm g r.1 r.2.1 t.wwLo t.wwHi pViol
    let delta := ttouchDelta g (t.arr (c.touchBase g d)) term.1 term.2.1
      t.dLo t.dHi term.2.2
    r.2.2 = 0 ∧ pViol = 0 ∧ term.2.2 = 0 ∧ delta.2.2 = 0 := by
  let r := tcmul g (t.arr (c.touchA1 g d)) (t.arr (c.touchA2 g d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol g r.1 r.2.1 r.2.2
  let term := ttouchTerm g r.1 r.2.1 t.wwLo t.wwHi pViol
  let delta := ttouchDelta g (t.arr (c.touchBase g d)) term.1 term.2.1
    t.dLo t.dHi term.2.2
  change delta.2.2 = 0 at hclean
  have hterm : term.2.2 = 0 := by
    have := ttouchDelta_viol_le g (t.arr (c.touchBase g d)) term.1 term.2.1
      t.dLo t.dHi term.2.2
    change term.2.2 ≤ delta.2.2 at this
    omega
  have hp : pViol = 0 := by
    have := ttouchTerm_viol_le g r.1 r.2.1 t.wwLo t.wwHi pViol
    change pViol ≤ term.2.2 at this
    omega
  have hr : r.2.2 = 0 := by
    have := ttouchProductViol_viol_le g r.1 r.2.1 r.2.2
    change r.2.2 ≤ pViol at this
    omega
  exact ⟨hr, hp, hterm, hclean⟩

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

/-- The flag produced by the weight multiplication is also below the flag of
the complete iteration.  This finer cut of `tstep_viol_le` lets a clean final
run discharge the square block without postulating a global invariant. -/
theorem tweight_viol_le_tstep (c : Cfg) (idx : Nat) (t : TState) :
    let z := c.tsel idx
    let u := tpassA z (ttrial z t)
    (tweight z u).viol ≤ (c.tstep idx t).viol := by
  let z := c.tsel idx
  let u := tpassA z (ttrial z t)
  let w := tweight z u
  have hpass : w.viol ≤ (c.tpassB z w).viol := by
    unfold Cfg.tpassB
    exact Nat.le_trans (ttouch_viol_le _ _ _ _)
      (ttouch_viol_le _ _ _ _)
  change w.viol ≤ (c.tfin z (c.tpassB z w)).viol
  unfold Cfg.tfin Cfg.tfinViol
  exact Nat.le_trans hpass
    (Nat.le_trans (tguard_le _ _ _)
      (Nat.le_trans (tguard_le _ _ _)
        (Nat.le_trans Nat.left_le_or Nat.left_le_or)))

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

/-! ## §8.1 Phase-1 trial state -/

/-- The three transparent registers that are exactly the shared trial
division state. -/
def trialOf (t : TState) : LeanCompCert.Ports.MertensCDEM.Trial :=
  ⟨t.res, t.sq, t.par⟩

/-- The shared three-valued Möbius code, factored over an already computed
trial state. -/
def trialCode (u : LeanCompCert.Ports.MertensCDEM.Trial) : Nat :=
  if u.sq = 1 then 0
  else if LeanCompCert.Ports.MertensCDEM.omegaPar u = 0 then 1 else 2

theorem trialCode_lt_M (u : LeanCompCert.Ports.MertensCDEM.Trial) :
    trialCode u < M := by
  unfold trialCode
  by_cases hs : u.sq = 1
  · simp [hs, M_val]
  · by_cases hp : LeanCompCert.Ports.MertensCDEM.omegaPar u = 0
    · simp [hs, hp, M_val]
    · simp [hs, hp, M_val]

theorem trialCode_trialRun (X R : Nat) :
    trialCode (LeanCompCert.Ports.MertensCDEM.trialRun X R) =
      LeanCompCert.Ports.MertensCDEM.muCode X R := rfl

/-- The branchless word formula written by `ttrial` is `trialCode`. -/
theorem machineTrialCode_eq (u : LeanCompCert.Ports.MertensCDEM.Trial)
    (hsq : u.sq ≤ 1) (hpar : u.par ≤ 1) :
    (((u.par ^^^ bnat (u.res ≠ 1)) + 1) % M) *
        (1 - u.sq) % M = trialCode u := by
  rcases (show u.sq = 0 ∨ u.sq = 1 by omega) with hs | hs <;>
    rcases (show u.par = 0 ∨ u.par = 1 by omega) with hp | hp <;>
    by_cases hr : u.res ≠ 1 <;>
    simp [trialCode, LeanCompCert.Ports.MertensCDEM.omegaPar, hs, hp, hr,
      M_val]

/-- On a phase-1 round, `ttrial` performs one shared `trialStep`, including
the candidate reset at the first round. -/
theorem trialOf_ttrial (z : TSel) (t : TState)
    (hP1 : z.inP1 = 1) (hD0 : z.isD0 ≤ 1) :
    trialOf (ttrial z t) =
      LeanCompCert.Ports.MertensCDEM.trialStep z.d1
        (if z.isD0 = 1 then ⟨z.n1, 0, 0⟩ else trialOf t) := by
  rcases (show z.isD0 = 0 ∨ z.isD0 = 1 by omega) with h0 | h1
  · simp [trialOf, ttrial, LeanCompCert.Ports.MertensCDEM.trialStep,
      hP1, h0, bnat]
    by_cases hdiv : t.res % z.d1 = 0 <;> simp [hdiv]
  · simp [trialOf, ttrial, LeanCompCert.Ports.MertensCDEM.trialStep,
      hP1, h1, bnat]
    by_cases hdiv : z.n1 % z.d1 = 0 <;> simp [hdiv]

/-- The last trial round writes the `trialCode` of its post-step state at the
candidate address. -/
theorem ttrial_last_write (z : TSel) (t : TState)
    (hDL : z.isDL = 1) (hn1 : z.n1 < M)
    (hsq : (trialOf (ttrial z t)).sq ≤ 1)
    (hpar : (trialOf (ttrial z t)).par ≤ 1) :
    (ttrial z t).arr z.n1 = trialCode (trialOf (ttrial z t)) := by
  have hc := machineTrialCode_eq (trialOf (ttrial z t)) hsq hpar
  simp only [trialOf] at hc
  unfold ttrial at hc ⊢
  simp only [hDL, Nat.one_mul, Nat.mod_eq_of_lt hn1, ↓reduceIte]
  simp only [trialOf]
  rw [← Nat.mod_eq_of_lt (trialCode_lt_M _)]
  exact congrArg (fun n => n % M) hc

/-- Selector decoding inside candidate `n` and trial round `r` of phase 1.
The modular word fields are ordinary naturals in this range. -/
theorem tsel_phase1_block (c : Cfg) (hc : Admissible c) (n r : Nat)
    (hn : n < c.cap - 1) (hr : r < c.rounds) :
    let z := c.tsel (n * c.rounds + r)
    z.inP1 = 1 ∧ z.inP2 = 0 ∧ z.q1 = n ∧ z.r1 = r ∧
      z.n1 = n + 2 ∧ z.d1 = r + 2 ∧
      z.isD0 = bnat (r = 0) ∧
      z.isDL = bnat (r = c.rounds - 1) ∧
      z.inA = 0 ∧ z.isW = 0 ∧ z.inB = 0 ∧ z.isF = 0 := by
  have hRpos : 0 < c.rounds := by omega
  have hcapm1 : 1 ≤ c.cap - 1 := by omega
  have hdecode :
      (n * c.rounds + r) / c.rounds = n ∧
        (n * c.rounds + r) % c.rounds = r := by
    constructor
    · rw [Nat.mul_comm, Nat.mul_add_div hRpos, Nat.div_eq_of_lt hr,
        Nat.add_zero]
    · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hphase : n * c.rounds + r < c.phase1 := by
    have hmul : (n + 1) * c.rounds ≤ (c.cap - 1) * c.rounds :=
      Nat.mul_le_mul_right c.rounds (by omega)
    rw [Nat.add_mul] at hmul
    unfold Cfg.phase1
    omega
  have hcapM : c.cap < M := by
    have := hc.arr_fits
    simp only [M_val] at this ⊢
    omega
  have hnM : n + 2 < M := by omega
  have hphaseM : c.phase1 + 1 < M := by
    have htail : 0 < c.cap * (2 * c.cap + 2) :=
      Nat.mul_pos hc.cap_pos (by omega)
    have hle : c.phase1 + 1 ≤ c.phase1 + c.cap * (2 * c.cap + 2) :=
      Nat.add_le_add_left htail c.phase1
    exact Nat.lt_of_le_of_lt hle hc.loop_fits
  have hRle : c.rounds ≤ c.phase1 := by
    unfold Cfg.phase1
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.rounds hcapm1
  have hdM : r + 2 < M := by omega
  simp [Cfg.tsel, hphase, hdecode.1, hdecode.2,
    Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hdM, bnat]

/-- The later four stages of a loop iteration do not modify the three trial
registers. -/
theorem trialOf_tstep (c : Cfg) (idx : Nat) (t : TState) :
    trialOf (c.tstep idx t) = trialOf (ttrial (c.tsel idx) t) := rfl

theorem trialPrefix_succ (X k : Nat) :
    LeanCompCert.Ports.MertensCDEM.trialPrefix X (k + 1) =
      LeanCompCert.Ports.MertensCDEM.trialStep (k + 2)
        (LeanCompCert.Ports.MertensCDEM.trialPrefix X k) := by
  unfold LeanCompCert.Ports.MertensCDEM.trialPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

/-- After `k+1` rounds of a phase-1 candidate block, the transparent trial
registers are the shared trial-division prefix of that length. -/
theorem phase1_trial_prefix (c : Cfg) (hc : Admissible c) (n : Nat)
    (hn : n < c.cap - 1) : ∀ k, k < c.rounds →
    trialOf (tRunUpto c (n * c.rounds + k + 1)) =
      LeanCompCert.Ports.MertensCDEM.trialPrefix (n + 2) (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hz := tsel_phase1_block c hc n 0 hn hk
      dsimp only at hz
      simp only [Nat.add_zero] at hz
      have hD0 : (c.tsel (n * c.rounds)).isD0 ≤ 1 := by
        rw [hz.2.2.2.2.2.2.1]
        exact bnat_le_one _
      rw [show n * c.rounds + 0 + 1 = n * c.rounds + 1 by omega,
        tRunUpto_succ, trialOf_tstep,
        trialOf_ttrial (c.tsel (n * c.rounds)) (tRunUpto c (n * c.rounds))
          hz.1 hD0,
        trialPrefix_succ, hz.2.2.2.2.1, hz.2.2.2.2.2.1,
        hz.2.2.2.2.2.2.1]
      rfl
  | succ k ih =>
      intro hk
      have hk0 : k < c.rounds := by omega
      have hz := tsel_phase1_block c hc n (k + 1) hn hk
      dsimp only at hz
      have hP1 : (c.tsel (n * c.rounds + k + 1)).inP1 = 1 := by
        simpa only [Nat.add_assoc] using hz.1
      have hD0 : (c.tsel (n * c.rounds + k + 1)).isD0 ≤ 1 := by
        have h : (c.tsel (n * c.rounds + k + 1)).isD0 =
            bnat (k + 1 = 0) := by
          simpa only [Nat.add_assoc] using hz.2.2.2.2.2.2.1
        rw [h]
        exact bnat_le_one _
      have hn1 : (c.tsel (n * c.rounds + k + 1)).n1 = n + 2 := by
        simpa only [Nat.add_assoc] using hz.2.2.2.2.1
      have hd1 : (c.tsel (n * c.rounds + k + 1)).d1 = k + 1 + 2 := by
        simpa only [Nat.add_assoc] using hz.2.2.2.2.2.1
      have hisD0 : (c.tsel (n * c.rounds + k + 1)).isD0 = 0 := by
        have h : (c.tsel (n * c.rounds + k + 1)).isD0 =
            bnat (k + 1 = 0) := by
          simpa only [Nat.add_assoc] using hz.2.2.2.2.2.2.1
        rw [h]
        simp [bnat]
      rw [show n * c.rounds + (k + 1) + 1 =
          (n * c.rounds + k + 1) + 1 by omega,
        tRunUpto_succ, trialOf_tstep,
        trialOf_ttrial (c.tsel (n * c.rounds + k + 1))
          (tRunUpto c (n * c.rounds + k + 1)) hP1 hD0,
        ih hk0, hn1, hd1, hisD0]
      exact (trialPrefix_succ (n + 2) (k + 1)).symm

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

theorem natAbs_decodeZ_lt (w : Nat) (hw : w < M) :
    (decodeZ w).natAbs < M := by
  rw [natAbs_decodeZ w hw]
  simp only [M_val] at *
  split <;> omega

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

/-- The rounded lower quotient of a capped product is in the signed `u64`
range, so decoding its `encodeZ` image is exact. -/
theorem cfloorDiv_signed_range {z : Int} (hb : z.natAbs ≤ CAP * CAP) :
    -(H63 : Int) ≤ LeanCompCert.Ports.Section413Sweep.cfloorDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ∧
      LeanCompCert.Ports.Section413Sweep.cfloorDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE < (H63 : Int) := by
  obtain ⟨hq, hc⟩ := quot_small hb
  unfold LeanCompCert.Ports.Section413Sweep.cfloorDiv
  by_cases hz : z < 0
  · rw [zfloorDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz (by decide)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, H63_val] at *
    omega
  · rw [zfloorDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, H63_val] at *
    omega

/-- The rounded upper quotient of a capped product is in the signed `u64`
range. -/
theorem cceilDiv_signed_range {z : Int} (hb : z.natAbs ≤ CAP * CAP) :
    -(H63 : Int) ≤ LeanCompCert.Ports.Section413Sweep.cceilDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ∧
      LeanCompCert.Ports.Section413Sweep.cceilDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE < (H63 : Int) := by
  obtain ⟨hq, hc⟩ := quot_small hb
  unfold LeanCompCert.Ports.Section413Sweep.cceilDiv
  by_cases hz : z < 0
  · rw [zceilDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, H63_val] at *
    omega
  · rw [zceilDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)
      (by decide)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, H63_val] at *
    omega

/-- Symbolic fixed-scale rounding bounds.  Keeping `SCALE` opaque here is
important: unfolding the 19-digit divisor makes kernel reduction enormous. -/
theorem scale_round_bounds (n : Nat) (h : n ≤ SCALE * SCALE) :
    n / SCALE ≤ SCALE ∧ (n + (SCALE - 1)) / SCALE ≤ SCALE := by
  constructor
  · exact Nat.div_le_of_le_mul h
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < SCALE)).2
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    have hpos : 0 < SCALE := by decide
    omega

theorem cfloorDiv_scale_range {z : Int} (h : z.natAbs ≤ SCALE * SCALE) :
    -(CAP : Int) ≤ LeanCompCert.Ports.Section413Sweep.cfloorDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ∧
      LeanCompCert.Ports.Section413Sweep.cfloorDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ≤ (CAP : Int) := by
  obtain ⟨hq, hc⟩ := scale_round_bounds z.natAbs h
  unfold LeanCompCert.Ports.Section413Sweep.cfloorDiv
  by_cases hz : z < 0
  · rw [zfloorDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz (by decide)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, SCALE, CAP_val] at *
    omega
  · rw [zfloorDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, SCALE, CAP_val] at *
    omega

theorem cceilDiv_scale_range {z : Int} (h : z.natAbs ≤ SCALE * SCALE) :
    -(CAP : Int) ≤ LeanCompCert.Ports.Section413Sweep.cceilDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ∧
      LeanCompCert.Ports.Section413Sweep.cceilDiv z
        LeanCompCert.Ports.Section413Sweep.SCALE ≤ (CAP : Int) := by
  obtain ⟨hq, hc⟩ := scale_round_bounds z.natAbs h
  unfold LeanCompCert.Ports.Section413Sweep.cceilDiv
  by_cases hz : z < 0
  · rw [zceilDiv_neg z LeanCompCert.Ports.Section413Sweep.SCALE hz]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, SCALE, CAP_val] at *
    omega
  · rw [zceilDiv_nonneg z LeanCompCert.Ports.Section413Sweep.SCALE (by omega)
      (by decide)]
    simp only [LeanCompCert.Ports.Section413Sweep.SCALE, SCALE, CAP_val] at *
    omega

theorem natAbs_min_le {a b : Int} {q : Nat}
    (ha : a.natAbs ≤ q) (hb : b.natAbs ≤ q) : (min a b).natAbs ≤ q := by
  rw [Int.min_def]
  split <;> assumption

theorem natAbs_max_le {a b : Int} {q : Nat}
    (ha : a.natAbs ≤ q) (hb : b.natAbs ≤ q) : (max a b).natAbs ≤ q := by
  rw [Int.max_def]
  split <;> assumption

/-- Scale-bounded input endpoints put both normalized product endpoints in
the machine cap interval. -/
theorem cmul_scale_range
    (A B : LeanCompCert.Ports.Section413Sweep.Cell)
    (haLo : A.lo.natAbs ≤ SCALE) (haHi : A.hi.natAbs ≤ SCALE)
    (hbLo : B.lo.natAbs ≤ SCALE) (hbHi : B.hi.natAbs ≤ SCALE) :
    (-(CAP : Int) ≤ (LeanCompCert.Ports.Section413Sweep.cmul A B).lo ∧
      (LeanCompCert.Ports.Section413Sweep.cmul A B).lo ≤ (CAP : Int)) ∧
    (-(CAP : Int) ≤ (LeanCompCert.Ports.Section413Sweep.cmul A B).hi ∧
      (LeanCompCert.Ports.Section413Sweep.cmul A B).hi ≤ (CAP : Int)) := by
  have b1 : (A.lo * B.lo).natAbs ≤ SCALE * SCALE := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haLo hbLo
  have b2 : (A.lo * B.hi).natAbs ≤ SCALE * SCALE := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haLo hbHi
  have b3 : (A.hi * B.lo).natAbs ≤ SCALE * SCALE := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haHi hbLo
  have b4 : (A.hi * B.hi).natAbs ≤ SCALE * SCALE := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul haHi hbHi
  have blo := natAbs_min_le (natAbs_min_le b1 b2) (natAbs_min_le b3 b4)
  have bhi := natAbs_max_le (natAbs_max_le b1 b2) (natAbs_max_le b3 b4)
  exact ⟨cfloorDiv_scale_range blo, cceilDiv_scale_range bhi⟩

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
  simp only [tcmul, tproduct, torderedLo, torderedHi, torder, troundLo,
    troundHi, cmulBack, selMin, selMax, roundLo, roundHi, psign,
    ha1, ha2, hb1, hb2, hq1, hq2, hq3, hq4]

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

/-- On a live clean gate, the encoded `tcmul` outputs decode to the reference
interval product.  `tcmul_spec` gives the encoded equality; the extra work
here proves the rounded reference endpoints are inside the signed range, so
the decode is not merely equality modulo `2^64`. -/
theorem tcmul_decode {gate aLo aHi bLo bHi viol : Nat} (hg : 0 < gate)
    (haLo : aLo < M) (haHi : aHi < M) (hbLo : bLo < M) (hbHi : bHi < M)
    (hclean : (tcmul gate aLo aHi bLo bHi viol).2.2 = 0) :
    (decodeZ (tcmul gate aLo aHi bLo bHi viol).1,
      decodeZ (tcmul gate aLo aHi bLo bHi viol).2.1) =
      let A : LeanCompCert.Ports.Section413Sweep.Cell :=
        ⟨decodeZ aLo, decodeZ aHi⟩
      let B : LeanCompCert.Ports.Section413Sweep.Cell :=
        ⟨decodeZ bLo, decodeZ bHi⟩
      ((LeanCompCert.Ports.Section413Sweep.cmul A B).lo,
       (LeanCompCert.Ports.Section413Sweep.cmul A B).hi) := by
  obtain ⟨_, hcap⟩ := tcmul_viol_eq_zero hclean
  obtain ⟨caLo, caHi, cbLo, cbHi⟩ := hcap hg
  rw [tmag_mag aLo haLo] at caLo
  rw [tmag_mag aHi haHi] at caHi
  rw [tmag_mag bLo hbLo] at cbLo
  rw [tmag_mag bHi hbHi] at cbHi
  let v1 := decodeZ aLo * decodeZ bLo
  let v2 := decodeZ aLo * decodeZ bHi
  let v3 := decodeZ aHi * decodeZ bLo
  let v4 := decodeZ aHi * decodeZ bHi
  have b1 : v1.natAbs ≤ CAP * CAP := mul_natAbs_le caLo cbLo
  have b2 : v2.natAbs ≤ CAP * CAP := mul_natAbs_le caLo cbHi
  have b3 : v3.natAbs ≤ CAP * CAP := mul_natAbs_le caHi cbLo
  have b4 : v4.natAbs ≤ CAP * CAP := mul_natAbs_le caHi cbHi
  have blo : (min (min v1 v2) (min v3 v4)).natAbs ≤ CAP * CAP := by
    rw [CAP_sq] at b1 b2 b3 b4 ⊢
    omega
  have bhi : (max (max v1 v2) (max v3 v4)).natAbs ≤ CAP * CAP := by
    rw [CAP_sq] at b1 b2 b3 b4 ⊢
    omega
  have hlo := cfloorDiv_signed_range blo
  have hhi := cceilDiv_signed_range bhi
  have hs := tcmul_spec hg haLo haHi hbLo hbHi hclean
  rw [Prod.mk.injEq] at hs
  rw [hs.1, hs.2]
  apply Prod.ext
  · change decodeZ (encodeZ (LeanCompCert.Ports.Section413Sweep.cfloorDiv
        (min (min v1 v2) (min v3 v4))
        LeanCompCert.Ports.Section413Sweep.SCALE)) =
      LeanCompCert.Ports.Section413Sweep.cfloorDiv
        (min (min v1 v2) (min v3 v4))
        LeanCompCert.Ports.Section413Sweep.SCALE
    exact decodeZ_encodeZ _ hlo.1 hlo.2
  · change decodeZ (encodeZ (LeanCompCert.Ports.Section413Sweep.cceilDiv
        (max (max v1 v2) (max v3 v4))
        LeanCompCert.Ports.Section413Sweep.SCALE)) =
      LeanCompCert.Ports.Section413Sweep.cceilDiv
        (max (max v1 v2) (max v3 v4))
        LeanCompCert.Ports.Section413Sweep.SCALE
    exact decodeZ_encodeZ _ hhi.1 hhi.2

/-- For a live clean touch, exactly the words used by that touch are capped:
the two loaded accumulator endpoints, the weight, the product, and `2P+w²`.
This replaces the former proposed invariant over every array cell. -/
theorem ttouch_live_caps (c : Cfg) (d : Nat) (t : TState)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (hclean : (c.ttouch 1 d t).viol = 0) :
    let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
      t.wLo t.wHi t.viol
    let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi
      (ttouchProductViol 1 r.1 r.2.1 r.2.2)
    Capped (t.arr (c.touchA1 1 d)) ∧ Capped (t.arr (c.touchA2 1 d)) ∧
      Capped t.wLo ∧ Capped t.wHi ∧ Capped r.1 ∧ Capped r.2.1 ∧
      Capped term.1 ∧ Capped term.2.1 := by
  let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol 1 r.1 r.2.1 r.2.2
  let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi pViol
  have hp := ttouch_clean_parts c 1 d t hclean
  change r.2.2 = 0 ∧ pViol = 0 ∧ term.2.2 = 0 ∧ _ at hp
  obtain ⟨hr0, hp0, ht0, _⟩ := hp
  have hinputs := (tcmul_viol_eq_zero hr0).2 (by decide)
  rw [tmag_mag _ haLo] at hinputs
  rw [tmag_mag _ haHi] at hinputs
  rw [tmag_mag _ hwLo] at hinputs
  rw [tmag_mag _ hwHi] at hinputs
  have hrLt := tcmul_lt (by decide : 0 < (1 : Nat)) haLo haHi hwLo hwHi hr0
  have hprod := ttouchProductViol_eq_zero (by decide) hrLt.1 hrLt.2 hp0
  have hterm := ttouchTerm_eq_zero (by decide) ht0
  change Capped (t.arr (c.touchA1 1 d)) ∧
    Capped (t.arr (c.touchA2 1 d)) ∧ Capped t.wLo ∧ Capped t.wHi ∧
    Capped r.1 ∧ Capped r.2.1 ∧ Capped term.1 ∧ Capped term.2.1
  exact ⟨hinputs.1, hinputs.2.1, hinputs.2.2.1, hinputs.2.2.2,
    hprod.2.1, hprod.2.2, hterm.2.1, hterm.2.2⟩

/-! The bound-form transfers.  The touch block adds `2·P` to `w²`, whose
sum can reach `3·CAP`, so the `Capped`-form lemmas above are too tight for
it; what actually matters is only that the sum stays inside the signed
range `2⁶³`. -/

/-- Addition transfers whenever the `Int` sum is in the signed range. -/
theorem decodeZ_add_of_range {a b : Nat} (ha : a < M) (hb : b < M)
    (h1 : -(H63 : Int) ≤ decodeZ a + decodeZ b)
    (h2 : decodeZ a + decodeZ b < (H63 : Int)) :
    decodeZ ((a + b) % M) = decodeZ a + decodeZ b := by
  rw [add_transfer a b ha hb]
  exact decodeZ_encodeZ _
    (by simp only [cellsH63_val, H63_val] at *; omega)
    (by simp only [cellsH63_val, H63_val] at *; omega)

/-- Doubling transfers whenever the doubled value is in the signed range. -/
theorem decodeZ_double_of_range {a : Nat} (ha : a < M)
    (h1 : -(H63 : Int) ≤ 2 * decodeZ a) (h2 : 2 * decodeZ a < (H63 : Int)) :
    decodeZ ((a + a) % M) = 2 * decodeZ a := by
  rw [double_transfer a ha]
  exact decodeZ_encodeZ _
    (by simp only [cellsH63_val, H63_val] at *; omega)
    (by simp only [cellsH63_val, H63_val] at *; omega)

/-- Negation transfers whenever the negated value is in the signed range. -/
theorem decodeZ_tsub_zero_of_range {a : Nat} (ha : a < M)
    (h1 : -(H63 : Int) ≤ -decodeZ a) (h2 : -decodeZ a < (H63 : Int)) :
    decodeZ (tsub 0 a) = -decodeZ a := by
  rw [tsub_eq_encodeZ 0 a (by simp only [M_val]; omega) ha,
    LeanCompCert.Ports.Section413Cells.decodeZ_zero, Int.zero_sub]
  exact decodeZ_encodeZ _
    (by simp only [cellsH63_val, H63_val] at *; omega)
    (by simp only [cellsH63_val, H63_val] at *; omega)

/-! The touch's `2P + w²` arithmetic can be decoded locally.  This is the
right proof seam for the verifier: the live product guards cap `P`, while the
weight theorem supplies the cap on `w²`; no global cap on every accumulator
cell is required. -/

theorem ttouchTerm_decode {g pLo pHi wwLo wwHi viol : Nat}
    (hpLo : pLo < M) (hpHi : pHi < M)
    (hwwLo : wwLo < M) (hwwHi : wwHi < M)
    (cpLo : Capped pLo) (cpHi : Capped pHi)
    (cwwLo : Capped wwLo) (cwwHi : Capped wwHi) :
    let term := ttouchTerm g pLo pHi wwLo wwHi viol
    decodeZ term.1 = 2 * decodeZ pLo + decodeZ wwLo ∧
      decodeZ term.2.1 = 2 * decodeZ pHi + decodeZ wwHi := by
  let dLo := (pLo + pLo) % M
  let dHi := (pHi + pHi) % M
  have hMpos : 0 < M := by simp only [M_val]; omega
  have hdLoLt : dLo < M := Nat.mod_lt _ hMpos
  have hdHiLt : dHi < M := Nat.mod_lt _ hMpos
  have hdLo := decodeZ_double hpLo cpLo
  have hdHi := decodeZ_double hpHi cpHi
  change decodeZ ((dLo + wwLo) % M) =
      2 * decodeZ pLo + decodeZ wwLo ∧
    decodeZ ((dHi + wwHi) % M) =
      2 * decodeZ pHi + decodeZ wwHi
  have cpLoR := capped_range hpLo cpLo
  have cpHiR := capped_range hpHi cpHi
  have cwwLoR := capped_range hwwLo cwwLo
  have cwwHiR := capped_range hwwHi cwwHi
  have hlo1 : -(H63 : Int) ≤ decodeZ dLo + decodeZ wwLo := by
    rw [show decodeZ dLo = 2 * decodeZ pLo from hdLo]
    simp only [H63_val, CAP_val] at *
    omega
  have hlo2 : decodeZ dLo + decodeZ wwLo < (H63 : Int) := by
    rw [show decodeZ dLo = 2 * decodeZ pLo from hdLo]
    simp only [H63_val, CAP_val] at *
    omega
  have hhi1 : -(H63 : Int) ≤ decodeZ dHi + decodeZ wwHi := by
    rw [show decodeZ dHi = 2 * decodeZ pHi from hdHi]
    simp only [H63_val, CAP_val] at *
    omega
  have hhi2 : decodeZ dHi + decodeZ wwHi < (H63 : Int) := by
    rw [show decodeZ dHi = 2 * decodeZ pHi from hdHi]
    simp only [H63_val, CAP_val] at *
    omega
  constructor
  · rw [decodeZ_add_of_range hdLoLt hwwLo hlo1 hlo2, hdLo]
  · rw [decodeZ_add_of_range hdHiLt hwwHi hhi1 hhi2, hdHi]

/-- Decode the signed Möbius contribution and its addition into the running
delta.  The proof is the three-value certificate alphabet (`0`, `+1`, `-1`)
rather than a pointwise triangle bound. -/
theorem ttouchDelta_decode {g mc tLo tHi dLo dHi viol : Nat}
    (hmc : mc = 0 ∨ mc = 1 ∨ mc = 2)
    (htLo : tLo < M) (htHi : tHi < M)
    (hdLo : dLo < M) (hdHi : dHi < M)
    (ctLo : Capped tLo) (ctHi : Capped tHi)
    (cdLo : Capped dLo) (cdHi : Capped dHi) :
    let delta := ttouchDelta g mc tLo tHi dLo dHi viol
    decodeZ delta.1 = decodeZ dLo +
        (if mc = 1 then decodeZ tLo else if mc = 2 then -decodeZ tHi else 0) ∧
      decodeZ delta.2.1 = decodeZ dHi +
        (if mc = 1 then decodeZ tHi else if mc = 2 then -decodeZ tLo else 0) := by
  have hMpos : 0 < M := by simp only [M_val]; omega
  rcases hmc with rfl | rfl | rfl
  · simp [ttouchDelta, bnat, Nat.mod_eq_of_lt hdLo, Nat.mod_eq_of_lt hdHi]
  · simpa [ttouchDelta, bnat, Nat.mod_eq_of_lt htLo,
      Nat.mod_eq_of_lt htHi] using
      And.intro (decodeZ_add hdLo htLo cdLo ctLo)
        (decodeZ_add hdHi htHi cdHi ctHi)
  · have hnHi := decodeZ_tsub_zero htHi ctHi
    have hnLo := decodeZ_tsub_zero htLo ctLo
    have hdLoR := capped_range hdLo cdLo
    have hdHiR := capped_range hdHi cdHi
    have htLoR := capped_range htLo ctLo
    have htHiR := capped_range htHi ctHi
    have hlo1 : -(H63 : Int) ≤ decodeZ dLo + decodeZ (tsub 0 tHi) := by
      rw [hnHi]
      simp only [H63_val, CAP_val] at *
      omega
    have hlo2 : decodeZ dLo + decodeZ (tsub 0 tHi) < (H63 : Int) := by
      rw [hnHi]
      simp only [H63_val, CAP_val] at *
      omega
    have hhi1 : -(H63 : Int) ≤ decodeZ dHi + decodeZ (tsub 0 tLo) := by
      rw [hnLo]
      simp only [H63_val, CAP_val] at *
      omega
    have hhi2 : decodeZ dHi + decodeZ (tsub 0 tLo) < (H63 : Int) := by
      rw [hnLo]
      simp only [H63_val, CAP_val] at *
      omega
    have hlo : decodeZ ((dLo + tsub 0 tHi) % M) =
        decodeZ dLo + -decodeZ tHi := by
      rw [decodeZ_add_of_range hdLo (tsub_lt 0 tHi) hlo1 hlo2, hnHi]
    have hhi : decodeZ ((dHi + tsub 0 tLo) % M) =
        decodeZ dHi + -decodeZ tLo := by
      rw [decodeZ_add_of_range hdHi (tsub_lt 0 tLo) hhi1 hhi2, hnLo]
    simpa [ttouchDelta, bnat, Nat.mod_eq_of_lt (tsub_lt 0 tHi),
      Nat.mod_eq_of_lt (tsub_lt 0 tLo)] using And.intro hlo hhi

/-- A live store is exactly cell addition after decoding. -/
theorem ttouchStore_decode {aLo aHi wLo wHi : Nat}
    (haLo : aLo < M) (haHi : aHi < M)
    (hwLo : wLo < M) (hwHi : wHi < M)
    (caLo : Capped aLo) (caHi : Capped aHi)
    (cwLo : Capped wLo) (cwHi : Capped wHi) :
    decodeZ (ttouchStore 1 aLo aHi wLo wHi).1 =
        decodeZ aLo + decodeZ wLo ∧
      decodeZ (ttouchStore 1 aLo aHi wLo wHi).2 =
        decodeZ aHi + decodeZ wHi := by
  simpa [ttouchStore, Nat.mod_eq_of_lt hwLo, Nat.mod_eq_of_lt hwHi] using
    And.intro (decodeZ_add haLo hwLo caLo cwLo)
      (decodeZ_add haHi hwHi caHi cwHi)

/-- The live touch term decodes to `2 * cmul A W + WW`.  The later weight
theorem will identify `WW` with `cmul W W`; keeping that premise separate
prevents the touch proof from depending on phase scheduling. -/
theorem ttouch_live_term_decode (c : Cfg) (d : Nat) (t : TState)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (hwwLo : t.wwLo < M) (hwwHi : t.wwHi < M)
    (cwwLo : Capped t.wwLo) (cwwHi : Capped t.wwHi)
    (hclean : (c.ttouch 1 d t).viol = 0) :
    let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
      t.wLo t.wHi t.viol
    let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi
      (ttouchProductViol 1 r.1 r.2.1 r.2.2)
    let P := LeanCompCert.Ports.Section413Sweep.cmul
      (⟨decodeZ (t.arr (c.touchA1 1 d)),
        decodeZ (t.arr (c.touchA2 1 d))⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell)
      (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell)
    decodeZ term.1 = 2 * P.lo + decodeZ t.wwLo ∧
      decodeZ term.2.1 = 2 * P.hi + decodeZ t.wwHi := by
  let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol 1 r.1 r.2.1 r.2.2
  let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi pViol
  let P := LeanCompCert.Ports.Section413Sweep.cmul
    (⟨decodeZ (t.arr (c.touchA1 1 d)),
      decodeZ (t.arr (c.touchA2 1 d))⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell)
    (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell)
  have hp := ttouch_clean_parts c 1 d t hclean
  change r.2.2 = 0 ∧ pViol = 0 ∧ term.2.2 = 0 ∧ _ at hp
  have hr0 := hp.1
  have hcaps := ttouch_live_caps c d t haLo haHi hwLo hwHi hclean
  change _ ∧ _ ∧ _ ∧ _ ∧ Capped r.1 ∧ Capped r.2.1 ∧ _ at hcaps
  have hrLt := tcmul_lt (by decide : 0 < (1 : Nat)) haLo haHi hwLo hwHi hr0
  have ht := ttouchTerm_decode (g := 1) (viol := pViol)
    hrLt.1 hrLt.2 hwwLo hwwHi
    hcaps.2.2.2.2.1 hcaps.2.2.2.2.2.1 cwwLo cwwHi
  change decodeZ term.1 = 2 * decodeZ r.1 + decodeZ t.wwLo ∧
    decodeZ term.2.1 = 2 * decodeZ r.2.1 + decodeZ t.wwHi at ht
  have hm := tcmul_decode (by decide : 0 < (1 : Nat)) haLo haHi hwLo hwHi hr0
  change (decodeZ r.1, decodeZ r.2.1) = (P.lo, P.hi) at hm
  rw [Prod.mk.injEq] at hm
  change decodeZ term.1 = 2 * P.lo + decodeZ t.wwLo ∧
    decodeZ term.2.1 = 2 * P.hi + decodeZ t.wwHi
  rw [← hm.1, ← hm.2]
  exact ht

/-- The live touch's delta registers decode to the signed Möbius update. -/
theorem ttouch_live_delta_decode (c : Cfg) (d mc : Nat) (t : TState)
    (hmc : mc = 0 ∨ mc = 1 ∨ mc = 2)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (hwwLo : t.wwLo < M) (hwwHi : t.wwHi < M)
    (hdLo : t.dLo < M) (hdHi : t.dHi < M)
    (cwwLo : Capped t.wwLo) (cwwHi : Capped t.wwHi)
    (cdLo : Capped t.dLo) (cdHi : Capped t.dHi)
    (hclean : (c.ttouch 1 d t).viol = 0) :
    let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
      t.wLo t.wHi t.viol
    let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi
      (ttouchProductViol 1 r.1 r.2.1 r.2.2)
    let delta := ttouchDelta 1 mc term.1 term.2.1 t.dLo t.dHi term.2.2
    let P := LeanCompCert.Ports.Section413Sweep.cmul
      (⟨decodeZ (t.arr (c.touchA1 1 d)),
        decodeZ (t.arr (c.touchA2 1 d))⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell)
      (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell)
    let tLo := 2 * P.lo + decodeZ t.wwLo
    let tHi := 2 * P.hi + decodeZ t.wwHi
    decodeZ delta.1 = decodeZ t.dLo +
        (if mc = 1 then tLo else if mc = 2 then -tHi else 0) ∧
      decodeZ delta.2.1 = decodeZ t.dHi +
        (if mc = 1 then tHi else if mc = 2 then -tLo else 0) := by
  let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol 1 r.1 r.2.1 r.2.2
  let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi pViol
  let delta := ttouchDelta 1 mc term.1 term.2.1 t.dLo t.dHi term.2.2
  let P := LeanCompCert.Ports.Section413Sweep.cmul
    (⟨decodeZ (t.arr (c.touchA1 1 d)),
      decodeZ (t.arr (c.touchA2 1 d))⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell)
    (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell)
  have hcaps := ttouch_live_caps c d t haLo haHi hwLo hwHi hclean
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ Capped term.1 ∧ Capped term.2.1 at hcaps
  have hMpos : 0 < M := by simp only [M_val]; omega
  have htLo : term.1 < M := by
    change (((r.1 + r.1) % M + t.wwLo) % M) < M
    exact Nat.mod_lt _ hMpos
  have htHi : term.2.1 < M := by
    change (((r.2.1 + r.2.1) % M + t.wwHi) % M) < M
    exact Nat.mod_lt _ hMpos
  have hd := ttouchDelta_decode (g := 1) (viol := term.2.2) hmc
    htLo htHi hdLo hdHi hcaps.2.2.2.2.2.2.1 hcaps.2.2.2.2.2.2.2
    cdLo cdHi
  change decodeZ delta.1 = decodeZ t.dLo +
      (if mc = 1 then decodeZ term.1 else if mc = 2 then -decodeZ term.2.1 else 0) ∧
    decodeZ delta.2.1 = decodeZ t.dHi +
      (if mc = 1 then decodeZ term.2.1 else if mc = 2 then -decodeZ term.1 else 0) at hd
  have ht := ttouch_live_term_decode c d t haLo haHi hwLo hwHi hwwLo hwwHi
    cwwLo cwwHi hclean
  change decodeZ term.1 = 2 * P.lo + decodeZ t.wwLo ∧
    decodeZ term.2.1 = 2 * P.hi + decodeZ t.wwHi at ht
  rw [ht.1, ht.2] at hd
  exact hd

/-! ## §15 Address arithmetic and the μ plane's alphabet -/

/-- Gated touch addresses do not wrap whenever the gated divisor product is
inside the configured slot range. -/
theorem touch_addr_of_product (c : Cfg) (hfit : 3 * (c.cap + 1) < M)
    {g d : Nat} (hgd : g * d ≤ c.cap) :
    c.touchBase g d = g * d ∧
      c.touchA1 g d = g * d + c.plane1 ∧
      c.touchA2 g d = g * d + c.plane2 := by
  have hbase : g * d < M := by
    simp only [M_val] at hfit ⊢
    omega
  have h1 : g * d + c.plane1 < M := by
    unfold Cfg.plane1
    simp only [M_val] at hfit ⊢
    omega
  have h2 : g * d + c.plane2 < M := by
    unfold Cfg.plane2
    simp only [M_val] at hfit ⊢
    omega
  have hbEq : c.touchBase g d = g * d := by
    unfold Cfg.touchBase
    exact Nat.mod_eq_of_lt hbase
  refine ⟨hbEq, ?_, ?_⟩
  · unfold Cfg.touchA1
    rw [hbEq, Nat.mod_eq_of_lt h1]
  · unfold Cfg.touchA2
    rw [hbEq, Nat.mod_eq_of_lt h2]

/-- A well-ranged touch cannot alter the μ plane (`0 .. cap`), because its
two stores land strictly above that plane. -/
theorem ttouch_mu_frame (c : Cfg) (g d : Nat) (t : TState) (i : Nat)
    (hc : Admissible c) (hgd : g * d ≤ c.cap) (hi : i ≤ c.cap) :
    (c.ttouch g d t).arr i = t.arr i := by
  have haddr := touch_addr_of_product c hc.arr_fits hgd
  have h2 : i ≠ c.touchA2 g d := by
    rw [haddr.2.2]
    unfold Cfg.plane2
    omega
  have h1 : i ≠ c.touchA1 g d := by
    rw [haddr.2.1]
    unfold Cfg.plane1
    omega
  change (if i = c.touchA2 g d then _
    else if i = c.touchA1 g d then _ else t.arr i) = t.arr i
  simp only [h2, h1, ↓reduceIte]

/-- The pair of touches used by pass B also leaves the μ plane unchanged. -/
theorem ttouch_pair_mu_frame (c : Cfg) (g₁ d₁ g₂ d₂ : Nat)
    (t : TState) (i : Nat) (hc : Admissible c)
    (hgd₁ : g₁ * d₁ ≤ c.cap) (hgd₂ : g₂ * d₂ ≤ c.cap)
    (hi : i ≤ c.cap) :
    (c.ttouch g₂ d₂ (c.ttouch g₁ d₁ t)).arr i = t.arr i := by
  rw [ttouch_mu_frame c g₂ d₂ _ i hc hgd₂ hi,
    ttouch_mu_frame c g₁ d₁ t i hc hgd₁ hi]

/-- During phase 1, the later stages cannot change a μ-plane cell; both
pass-B gates are zero. -/
theorem tstep_phase1_arr (c : Cfg) (idx : Nat) (t : TState) (i : Nat)
    (hc : Admissible c) (hi : i ≤ c.cap)
    (hB : (c.tsel idx).inB = 0) :
    (c.tstep idx t).arr i = (ttrial (c.tsel idx) t).arr i := by
  let z := c.tsel idx
  let u := tweight z (tpassA z (ttrial z t))
  let g₁ := bnat (z.X % z.rB = 0) * bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  have hg₁ : g₁ = 0 := by simp [g₁, z, hB]
  have hg₂ : g₂ = 0 := by simp [g₂, hg₁]
  change (c.ttouch g₂ q₂ (c.ttouch g₁ z.rB u)).arr i =
    (ttrial z t).arr i
  rw [hg₁, hg₂,
    ttouch_pair_mu_frame c 0 z.rB 0 q₂ u i hc
      (by simp) (by simp) hi]
  rfl

/-- Phase 1 writes the shared `MertensCDEM.muCode` for every completed
candidate.  No clean-flag hypothesis is needed: this part uses only exact
Nat trial division and the in-range μ-plane store. -/
theorem phase1_muCode (c : Cfg) (hc : Admissible c) (n : Nat)
    (hn : 2 ≤ n) (hnc : n ≤ c.cap) :
    (tRunUpto c ((n - 1) * c.rounds)).arr n =
      LeanCompCert.Ports.MertensCDEM.muCode n c.rounds := by
  let m := n - 2
  have hm : m < c.cap - 1 := by
    have hle : n - 2 ≤ c.cap - 2 := Nat.sub_le_sub_right hnc 2
    have hlt : c.cap - 2 < c.cap - 1 := by omega
    exact Nat.lt_of_le_of_lt hle hlt
  have hRpos : 0 < c.rounds := Nat.lt_of_lt_of_le (by decide) hc.rounds_ge
  have hk : c.rounds - 1 < c.rounds := Nat.sub_one_lt (Nat.ne_of_gt hRpos)
  have hp := phase1_trial_prefix c hc m hm (c.rounds - 1) hk
  have hm2 : m + 2 = n := by omega
  have hpost :
      trialOf (tRunUpto c (m * c.rounds + (c.rounds - 1) + 1)) =
        LeanCompCert.Ports.MertensCDEM.trialRun n c.rounds := by
    simpa only [hm2, show c.rounds - 1 + 1 = c.rounds by omega,
      LeanCompCert.Ports.MertensCDEM.trialPrefix_full] using hp
  let idx := m * c.rounds + (c.rounds - 1)
  have htime : (n - 1) * c.rounds = idx + 1 := by
    have hnm : n - 1 = m + 1 := by omega
    rw [hnm, Nat.add_mul]
    dsimp only [idx]
    omega
  have hz := tsel_phase1_block c hc m (c.rounds - 1) hm hk
  dsimp only at hz
  rcases hz with ⟨hP1, hP2, hq, hr, hn1, hd1, hD0, hDL,
    hA, hW, hB, hF⟩
  have hidx : idx = m * c.rounds + (c.rounds - 1) := rfl
  have hn1' : (c.tsel idx).n1 = n := by
    rw [hidx]
    exact hn1.trans hm2
  have hDL' : (c.tsel idx).isDL = 1 := by
    rw [hidx, hDL]
    simp [bnat]
  have hB' : (c.tsel idx).inB = 0 := by rw [hidx, hB]
  have hnM : (c.tsel idx).n1 < M := by
    rw [hn1']
    have := hc.arr_fits
    simp only [M_val] at this ⊢
    omega
  have htrialPost :
      trialOf (ttrial (c.tsel idx) (tRunUpto c idx)) =
        LeanCompCert.Ports.MertensCDEM.trialRun n c.rounds := by
    rw [← trialOf_tstep]
    rw [← tRunUpto_succ]
    simpa only [idx] using hpost
  have hbits := LeanCompCert.Ports.MertensCDEM.trialRun_bits n c.rounds
  have hsq : (trialOf (ttrial (c.tsel idx) (tRunUpto c idx))).sq ≤ 1 := by
    rw [htrialPost]
    exact hbits.1
  have hpar : (trialOf (ttrial (c.tsel idx) (tRunUpto c idx))).par ≤ 1 := by
    rw [htrialPost]
    exact hbits.2
  rw [htime, tRunUpto_succ,
    tstep_phase1_arr c idx (tRunUpto c idx) n hc hnc hB',
    ← hn1', ttrial_last_write _ _ hDL' hnM hsq hpar,
    htrialPost, trialCode_trialRun]
  rw [hn1']

/-- After candidate `n` has been written, every remaining phase-1 iteration
writes either address zero or a strictly later candidate, hence frames cell
`n`. -/
theorem tstep_phase1_arr_after (c : Cfg) (hc : Admissible c) (n idx : Nat)
    (hn : 1 ≤ n) (hstart : (n - 1) * c.rounds ≤ idx)
    (hidx : idx < c.phase1) :
    (c.tstep idx (tRunUpto c idx)).arr n = (tRunUpto c idx).arr n := by
  have hRpos : 0 < c.rounds := Nat.lt_of_lt_of_le (by decide) hc.rounds_ge
  let m := idx / c.rounds
  let r := idx % c.rounds
  have hr : r < c.rounds := Nat.mod_lt _ hRpos
  have hm : m < c.cap - 1 := by
    apply (Nat.div_lt_iff_lt_mul hRpos).2
    simpa only [Cfg.phase1] using hidx
  have hdecomp : idx = m * c.rounds + r := by
    symm
    simpa only [m, r, Nat.mul_comm] using Nat.div_add_mod idx c.rounds
  have hnm : n - 1 ≤ m := by
    apply (Nat.le_div_iff_mul_le hRpos).2
    exact hstart
  have hz := tsel_phase1_block c hc m r hm hr
  dsimp only at hz
  rcases hz with ⟨hP1, hP2, hq, hr1, hn1, hd1, hD0, hDL,
    hA, hW, hB, hF⟩
  rw [hdecomp, tstep_phase1_arr c (m * c.rounds + r)
    (tRunUpto c (m * c.rounds + r)) n hc (by omega) hB]
  unfold ttrial
  by_cases hlast : r = c.rounds - 1
  · have hDL' : (c.tsel (m * c.rounds + r)).isDL = 1 := by
      rw [hDL]
      simp [bnat, hlast]
    have hn1' : (c.tsel (m * c.rounds + r)).n1 = m + 2 := hn1
    have hm2M : m + 2 < M := by
      have hcapM : c.cap < M := by
        have := hc.arr_fits
        simp only [M_val] at this ⊢
        omega
      omega
    simp [hDL', hn1', Nat.mod_eq_of_lt hm2M]
    omega
  · have hDL' : (c.tsel (m * c.rounds + r)).isDL = 0 := by
      rw [hDL]
      simp [bnat, hlast]
    simp [hDL', Nat.ne_of_gt hn]

/-- At the phase boundary the whole live μ plane contains the shared trial
division codes, not merely the cell at its original write time. -/
theorem phase1_muCode_final (c : Cfg) (hc : Admissible c) (n : Nat)
    (hn : 2 ≤ n) (hnc : n ≤ c.cap) :
    (tRunUpto c c.phase1).arr n =
      LeanCompCert.Ports.MertensCDEM.muCode n c.rounds := by
  let start := (n - 1) * c.rounds
  have hstart : start ≤ c.phase1 := by
    unfold start Cfg.phase1
    exact Nat.mul_le_mul_right c.rounds (by omega)
  have aux : ∀ d, start + d ≤ c.phase1 →
      (tRunUpto c (start + d)).arr n =
        LeanCompCert.Ports.MertensCDEM.muCode n c.rounds := by
    intro d
    induction d with
    | zero =>
        intro _
        simpa only [start, Nat.add_zero] using phase1_muCode c hc n hn hnc
    | succ d ih =>
        intro hd
        rw [show start + (d + 1) = (start + d) + 1 by omega,
          tRunUpto_succ,
          tstep_phase1_arr_after c hc n (start + d) (by omega)]
        · exact ih (by omega)
        · dsimp only [start]
          omega
        · omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hstart
  rw [hd]
  exact aux d (by omega)

theorem trialStep_one (d : Nat) (hd : 1 < d) :
    LeanCompCert.Ports.MertensCDEM.trialStep d ⟨1, 0, 0⟩ = ⟨1, 0, 0⟩ := by
  have hmod : 1 % d = 1 := Nat.mod_eq_of_lt hd
  simp [LeanCompCert.Ports.MertensCDEM.trialStep, hmod]

theorem trialRun_one (R : Nat) :
    LeanCompCert.Ports.MertensCDEM.trialRun 1 R = ⟨1, 0, 0⟩ := by
  unfold LeanCompCert.Ports.MertensCDEM.trialRun
  induction R with
  | zero => rfl
  | succ R ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil]
      exact trialStep_one (R + 2) (by omega)

theorem muCode_one (R : Nat) : LeanCompCert.Ports.MertensCDEM.muCode 1 R = 1 := by
  simp [LeanCompCert.Ports.MertensCDEM.muCode, trialRun_one,
    LeanCompCert.Ports.MertensCDEM.omegaPar]

theorem phase1_muCode_final_one (c : Cfg) (hc : Admissible c) :
    (tRunUpto c c.phase1).arr 1 =
      LeanCompCert.Ports.MertensCDEM.muCode 1 c.rounds := by
  have aux : ∀ k, k ≤ c.phase1 → (tRunUpto c k).arr 1 = 1 := by
    intro k
    induction k with
    | zero => simp [tRunUpto, tInit]
    | succ k ih =>
        intro hk
        rw [tRunUpto_succ,
          tstep_phase1_arr_after c hc 1 k (by decide) (by simp)]
        · exact ih (by omega)
        · omega
  rw [muCode_one]
  exact aux c.phase1 (Nat.le_refl _)

theorem phase1_muCode_final_ge_one (c : Cfg) (hc : Admissible c) (n : Nat)
    (hn : 1 ≤ n) (hnc : n ≤ c.cap) :
    (tRunUpto c c.phase1).arr n =
      LeanCompCert.Ports.MertensCDEM.muCode n c.rounds := by
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · exact phase1_muCode_final_one c hc
  · exact phase1_muCode_final c hc n hn2 hnc

/-- **No address wraps.**  Under `Admissible.arr_fits` the three plane
addresses of a live slot are computed exactly, with no `% 2⁶⁴`. -/
theorem touch_addr (c : Cfg) (hfit : 3 * (c.cap + 1) < M) {d : Nat}
    (hd : d ≤ c.cap) :
    1 * d % M = d ∧
    (1 * d % M + c.plane1) % M = d + c.plane1 ∧
    (1 * d % M + c.plane2) % M = d + c.plane2 := by
  unfold Cfg.plane1 Cfg.plane2 at *
  simp only [M_val] at *
  exact ⟨by omega, by omega, by omega⟩

/-- **The μ plane's codes decode to the reference model's `muZ`.**  This is
the join between the shared trial division (`Ports/MertensCDEM`) and the
sweep's signed weights. -/
theorem muZ_eq (X R : Nat) :
    LeanCompCert.Ports.Section413Sweep.muZ X R =
      if LeanCompCert.Ports.MertensCDEM.muCode X R = 1 then 1
      else if LeanCompCert.Ports.MertensCDEM.muCode X R = 2 then -1 else 0 := by
  unfold LeanCompCert.Ports.Section413Sweep.muZ
  generalize LeanCompCert.Ports.MertensCDEM.muCode X R = n
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (_ + 3) => rfl

theorem muCode_cases (X R : Nat) :
    LeanCompCert.Ports.MertensCDEM.muCode X R = 0 ∨
      LeanCompCert.Ports.MertensCDEM.muCode X R = 1 ∨
      LeanCompCert.Ports.MertensCDEM.muCode X R = 2 := by
  let t := LeanCompCert.Ports.MertensCDEM.trialRun X R
  change (if t.sq = 1 then 0 else
      if LeanCompCert.Ports.MertensCDEM.omegaPar t = 0 then 1 else 2) = 0 ∨
    (if t.sq = 1 then 0 else
      if LeanCompCert.Ports.MertensCDEM.omegaPar t = 0 then 1 else 2) = 1 ∨
    (if t.sq = 1 then 0 else
      if LeanCompCert.Ports.MertensCDEM.omegaPar t = 0 then 1 else 2) = 2
  by_cases hs : t.sq = 1
  · simp [hs]
  · by_cases hp : LeanCompCert.Ports.MertensCDEM.omegaPar t = 0
    · simp [hs, hp]
    · simp [hs, hp]

/-- The `0`/`1` selectors the touch block reads off the μ plane pick out
exactly the three cases of `Section413Sweep.csmul`'s scalar. -/
theorem muZ_of_code {X R mc : Nat}
    (h : mc = LeanCompCert.Ports.MertensCDEM.muCode X R) :
    (if mc = 1 then (1 : Int) else if mc = 2 then -1 else 0)
      = LeanCompCert.Ports.Section413Sweep.muZ X R := by
  rw [muZ_eq, h]

/-- The two endpoint selectors used by `ttouchDelta` are exactly scalar
multiplication by the decoded three-value Möbius code. -/
theorem csmul_of_code {mc : Nat} (hmc : mc = 0 ∨ mc = 1 ∨ mc = 2)
    (lo hi : Int) :
    (⟨if mc = 1 then lo else if mc = 2 then -hi else 0,
       if mc = 1 then hi else if mc = 2 then -lo else 0⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.csmul
        (if mc = 1 then 1 else if mc = 2 then -1 else 0) ⟨lo, hi⟩ := by
  rcases hmc with rfl | rfl | rfl <;>
    simp [LeanCompCert.Ports.Section413Sweep.csmul]

/-- The delta-register part of a live touch is the reference sweep's
`deltaTerm`, once the weight round has supplied the independently computed
square `ww = cmul w w`.  This is the arithmetic core of `ttouch_spec`; it
uses only the guards exercised by this touch. -/
theorem ttouch_live_deltaTerm (c : Cfg) (d : Nat) (t : TState)
    (hc : Admissible c)
    (hd : d ≤ c.cap)
    (hmu : t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (hwwLo : t.wwLo < M) (hwwHi : t.wwHi < M)
    (hdLo : t.dLo < M) (hdHi : t.dHi < M)
    (cwwLo : Capped t.wwLo) (cwwHi : Capped t.wwHi)
    (cdLo : Capped t.dLo) (cdHi : Capped t.dHi)
    (hclean : (c.ttouch 1 d t).viol = 0)
    (hww :
      (⟨decodeZ t.wwLo, decodeZ t.wwHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)) :
    (⟨decodeZ (c.ttouch 1 d t).dLo, decodeZ (c.ttouch 1 d t).dHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
    LeanCompCert.Ports.Section413Sweep.cadd
      ⟨decodeZ t.dLo, decodeZ t.dHi⟩
      (LeanCompCert.Ports.Section413Sweep.deltaTerm
        (LeanCompCert.Ports.Section413Sweep.muZ d c.rounds)
        ⟨decodeZ (t.arr (c.touchA1 1 d)),
          decodeZ (t.arr (c.touchA2 1 d))⟩
        ⟨decodeZ t.wLo, decodeZ t.wHi⟩) := by
  let A : LeanCompCert.Ports.Section413Sweep.Cell :=
    ⟨decodeZ (t.arr (c.touchA1 1 d)), decodeZ (t.arr (c.touchA2 1 d))⟩
  let W : LeanCompCert.Ports.Section413Sweep.Cell :=
    ⟨decodeZ t.wLo, decodeZ t.wHi⟩
  let D : LeanCompCert.Ports.Section413Sweep.Cell :=
    ⟨decodeZ t.dLo, decodeZ t.dHi⟩
  let P := LeanCompCert.Ports.Section413Sweep.cmul A W
  let mc := t.arr (c.touchBase 1 d)
  have hbase : c.touchBase 1 d = d := (touch_addr c hc.arr_fits hd).1
  have hmcEq : mc = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds := by
    simp only [mc, hbase, hmu]
  have hmcCases : mc = 0 ∨ mc = 1 ∨ mc = 2 := by
    rw [hmcEq]
    exact muCode_cases d c.rounds
  have hdelta := ttouch_live_delta_decode c d mc t hmcCases
    haLo haHi hwLo hwHi hwwLo hwwHi hdLo hdHi cwwLo cwwHi cdLo cdHi hclean
  change decodeZ (c.ttouch 1 d t).dLo = D.lo +
      (if mc = 1 then 2 * P.lo + decodeZ t.wwLo
       else if mc = 2 then -(2 * P.hi + decodeZ t.wwHi) else 0) ∧
    decodeZ (c.ttouch 1 d t).dHi = D.hi +
      (if mc = 1 then 2 * P.hi + decodeZ t.wwHi
       else if mc = 2 then -(2 * P.lo + decodeZ t.wwLo) else 0) at hdelta
  let T : LeanCompCert.Ports.Section413Sweep.Cell :=
    ⟨2 * P.lo + decodeZ t.wwLo, 2 * P.hi + decodeZ t.wwHi⟩
  have hdeltaCell :
      (⟨decodeZ (c.ttouch 1 d t).dLo, decodeZ (c.ttouch 1 d t).dHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cadd D
        ⟨if mc = 1 then T.lo else if mc = 2 then -T.hi else 0,
         if mc = 1 then T.hi else if mc = 2 then -T.lo else 0⟩ := by
    congr 1
    · simpa [LeanCompCert.Ports.Section413Sweep.cadd, T] using hdelta.1
    · simpa [LeanCompCert.Ports.Section413Sweep.cadd, T] using hdelta.2
  have hterm : T = LeanCompCert.Ports.Section413Sweep.cadd
      (LeanCompCert.Ports.Section413Sweep.csmul 2 P)
      (LeanCompCert.Ports.Section413Sweep.cmul W W) := by
    change (⟨2 * P.lo + decodeZ t.wwLo, 2 * P.hi + decodeZ t.wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) = _
    change (⟨decodeZ t.wwLo, decodeZ t.wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul W W at hww
    rw [← hww]
    simp [LeanCompCert.Ports.Section413Sweep.cadd,
      LeanCompCert.Ports.Section413Sweep.csmul]
  rw [hdeltaCell, csmul_of_code hmcCases, muZ_of_code hmcEq, hterm]
  rfl

/-! The inactive-touch transfers used between the live divisor events. -/

@[simp] theorem tguard_gate_zero (w viol : Nat) : tguard 0 w viol = viol := by
  simp [tguard]

theorem tcmul_gate_zero_viol (aLo aHi bLo bHi viol : Nat) :
    (tcmul 0 aLo aHi bLo bHi viol).2.2 = viol := by
  rw [tcmul_viol_eq]
  simp

theorem ttouchProductViol_gate_zero (pLo pHi viol : Nat) :
    ttouchProductViol 0 pLo pHi viol = viol := by
  simp [ttouchProductViol]

theorem ttouchTerm_gate_zero (pLo pHi wwLo wwHi viol : Nat) :
    (ttouchTerm 0 pLo pHi wwLo wwHi viol).2.2 = viol := by
  simp [ttouchTerm]

theorem ttouchDelta_gate_zero (tLo tHi dLo dHi viol : Nat)
    (hdLo : dLo < M) (hdHi : dHi < M) :
    ttouchDelta 0 0 tLo tHi dLo dHi viol = (dLo, dHi, viol) := by
  simp [ttouchDelta, bnat, Nat.mod_eq_of_lt hdLo, Nat.mod_eq_of_lt hdHi]

theorem ttouchStore_gate_zero (aLo aHi wLo wHi : Nat)
    (haLo : aLo < M) (haHi : aHi < M) :
    ttouchStore 0 aLo aHi wLo wHi = (aLo, aHi) := by
  simp [ttouchStore, Nat.mod_eq_of_lt haLo, Nat.mod_eq_of_lt haHi]

/-- The two accumulator-plane stores of a live touch are the reference
cell addition.  The address proof also shows that the low store cannot be
shadowed by the high store. -/
theorem ttouch_live_store (c : Cfg) (d : Nat) (t : TState)
    (hc : Admissible c) (hd : d ≤ c.cap)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (caLo : Capped (t.arr (c.touchA1 1 d)))
    (caHi : Capped (t.arr (c.touchA2 1 d)))
    (cwLo : Capped t.wLo) (cwHi : Capped t.wHi) :
    (⟨decodeZ ((c.ttouch 1 d t).arr (d + c.plane1)),
       decodeZ ((c.ttouch 1 d t).arr (d + c.plane2))⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
    LeanCompCert.Ports.Section413Sweep.cadd
      ⟨decodeZ (t.arr (c.touchA1 1 d)),
        decodeZ (t.arr (c.touchA2 1 d))⟩
      ⟨decodeZ t.wLo, decodeZ t.wHi⟩ := by
  have haddr := touch_addr c hc.arr_fits hd
  have ha1 : c.touchA1 1 d = d + c.plane1 := haddr.2.1
  have ha2 : c.touchA2 1 d = d + c.plane2 := haddr.2.2
  have hne : d + c.plane1 ≠ d + c.plane2 := by
    unfold Cfg.plane1 Cfg.plane2
    omega
  have hs := ttouchStore_decode haLo haHi hwLo hwHi caLo caHi cwLo cwHi
  change decodeZ (ttouchStore 1 (t.arr (c.touchA1 1 d))
      (t.arr (c.touchA2 1 d)) t.wLo t.wHi).1 =
        decodeZ (t.arr (c.touchA1 1 d)) + decodeZ t.wLo ∧
    decodeZ (ttouchStore 1 (t.arr (c.touchA1 1 d))
      (t.arr (c.touchA2 1 d)) t.wLo t.wHi).2 =
        decodeZ (t.arr (c.touchA2 1 d)) + decodeZ t.wHi at hs
  congr 1
  · change decodeZ (if d + c.plane1 = c.touchA2 1 d then _
      else if d + c.plane1 = c.touchA1 1 d then _ else _) = _
    rw [ha1, ha2]
    simp only [hne, ↓reduceIte]
    simpa only [ha1, ha2] using hs.1
  · change decodeZ (if d + c.plane2 = c.touchA2 1 d then _
      else if d + c.plane2 = c.touchA1 1 d then _ else _) = _
    rw [ha1, ha2]
    simp only [↓reduceIte]
    simpa only [ha1, ha2] using hs.2

/-- A touch changes no array word outside its two accumulator-plane
addresses.  This frame fact is independent of the gate and of arithmetic
soundness. -/
theorem ttouch_arr_frame (c : Cfg) (g d : Nat) (t : TState) (i : Nat)
    (h2 : i ≠ c.touchA2 g d) (h1 : i ≠ c.touchA1 g d) :
    (c.ttouch g d t).arr i = t.arr i := by
  change (if i = c.touchA2 g d then _
    else if i = c.touchA1 g d then _ else t.arr i) = t.arr i
  simp only [h2, h1, ↓reduceIte]

/-- The raw `u64` bounds needed by pass B.  These are deliberately weaker
than `Capped`: inactive or not-yet-used cells need only be machine words. -/
def PassU64 (t : TState) : Prop :=
  t.wLo < M ∧ t.wHi < M ∧ t.wwLo < M ∧ t.wwHi < M ∧
    t.dLo < M ∧ t.dHi < M ∧ ∀ i, t.arr i < M

/-- The raw words inherited by a weight round. -/
def CoreU64 (t : TState) : Prop :=
  t.dLo < M ∧ t.dHi < M ∧ ∀ i, t.arr i < M

/-- A touch preserves raw machine-word bounds independently of its gate and
independently of whether its arithmetic guards remain clean. -/
theorem ttouch_passU64 (c : Cfg) (g d : Nat) (t : TState)
    (h : PassU64 t) : PassU64 (c.ttouch g d t) := by
  rcases h with ⟨hwLo, hwHi, hwwLo, hwwHi, hdLo, hdHi, harr⟩
  have hMpos : 0 < M := by simp only [M_val]; omega
  refine ⟨hwLo, hwHi, hwwLo, hwwHi, ?_, ?_, ?_⟩
  · simp only [Cfg.ttouch, ttouchDelta]
    exact Nat.mod_lt _ hMpos
  · simp only [Cfg.ttouch, ttouchDelta]
    exact Nat.mod_lt _ hMpos
  · intro i
    change (if i = c.touchA2 g d then
        (ttouchStore g (t.arr (c.touchA1 g d))
          (t.arr (c.touchA2 g d)) t.wLo t.wHi).2
      else if i = c.touchA1 g d then
        (ttouchStore g (t.arr (c.touchA1 g d))
          (t.arr (c.touchA2 g d)) t.wLo t.wHi).1
      else t.arr i) < M
    split
    · unfold ttouchStore
      exact Nat.mod_lt _ hMpos
    · split
      · unfold ttouchStore
        exact Nat.mod_lt _ hMpos
      · exact harr i

theorem tpassB_passU64 (c : Cfg) (z : TSel) (t : TState)
    (h : PassU64 t) : PassU64 (c.tpassB z t) := by
  unfold Cfg.tpassB
  exact ttouch_passU64 c _ _ _ (ttouch_passU64 c _ _ _ h)

theorem ttouch_coreU64 (c : Cfg) (g d : Nat) (t : TState)
    (h : CoreU64 t) : CoreU64 (c.ttouch g d t) := by
  rcases h with ⟨hdLo, hdHi, harr⟩
  have hMpos : 0 < M := by simp only [M_val]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cfg.ttouch, ttouchDelta]
    exact Nat.mod_lt _ hMpos
  · simp only [Cfg.ttouch, ttouchDelta]
    exact Nat.mod_lt _ hMpos
  · intro i
    change (if i = c.touchA2 g d then
        (ttouchStore g (t.arr (c.touchA1 g d))
          (t.arr (c.touchA2 g d)) t.wLo t.wHi).2
      else if i = c.touchA1 g d then
        (ttouchStore g (t.arr (c.touchA1 g d))
          (t.arr (c.touchA2 g d)) t.wLo t.wHi).1
      else t.arr i) < M
    split
    · unfold ttouchStore
      exact Nat.mod_lt _ hMpos
    · split
      · unfold ttouchStore
        exact Nat.mod_lt _ hMpos
      · exact harr i

theorem ttrial_coreU64 (z : TSel) (t : TState) (h : CoreU64 t) :
    CoreU64 (ttrial z t) := by
  rcases h with ⟨hdLo, hdHi, harr⟩
  have hMpos : 0 < M := by simp only [M_val]; omega
  refine ⟨hdLo, hdHi, ?_⟩
  intro i
  simp only [ttrial]
  split
  · exact Nat.mod_lt _ hMpos
  · exact harr i

theorem tpassA_coreU64 (z : TSel) (t : TState) (h : CoreU64 t) :
    CoreU64 (tpassA z t) := by
  simpa only [CoreU64, tpassA] using h

theorem tweight_coreU64 (z : TSel) (t : TState) (h : CoreU64 t) :
    CoreU64 (tweight z t) := by
  simpa only [CoreU64, tweight] using h

theorem tpassB_coreU64 (c : Cfg) (z : TSel) (t : TState)
    (h : CoreU64 t) : CoreU64 (c.tpassB z t) := by
  unfold Cfg.tpassB
  exact ttouch_coreU64 c _ _ _ (ttouch_coreU64 c _ _ _ h)

theorem tfin_coreU64 (c : Cfg) (z : TSel) (t : TState)
    (h : CoreU64 t) : CoreU64 (c.tfin z t) := by
  rcases h with ⟨_hdLo, _hdHi, harr⟩
  have hMpos : 0 < M := by simp only [M_val]; omega
  refine ⟨?_, ?_, ?_⟩
  · change tfinDLo z t < M
    unfold tfinDLo
    exact Nat.mod_lt _ hMpos
  · change tfinDHi z t < M
    unfold tfinDHi
    exact Nat.mod_lt _ hMpos
  · exact harr

theorem tfin_passU64 (c : Cfg) (z : TSel) (t : TState)
    (h : PassU64 t) : PassU64 (c.tfin z t) := by
  rcases h with ⟨hwLo, hwHi, hwwLo, hwwHi, _hdLo, _hdHi, harr⟩
  have hMpos : 0 < M := by simp only [M_val]; omega
  refine ⟨hwLo, hwHi, hwwLo, hwwHi, ?_, ?_, harr⟩
  · change tfinDLo z t < M
    unfold tfinDLo
    exact Nat.mod_lt _ hMpos
  · change tfinDHi z t < M
    unfold tfinDHi
    exact Nat.mod_lt _ hMpos

theorem tstep_coreU64 (c : Cfg) (idx : Nat) (t : TState)
    (h : CoreU64 t) : CoreU64 (c.tstep idx t) := by
  let z := c.tsel idx
  exact tfin_coreU64 c z _
    (tpassB_coreU64 c z _
      (tweight_coreU64 z _ (tpassA_coreU64 z _ (ttrial_coreU64 z t h))))

theorem tInit_coreU64 : CoreU64 tInit := by
  refine ⟨by simp [tInit, M_val], by simp [tInit, M_val], ?_⟩
  intro i
  by_cases hi : i = 1 <;> simp [tInit, M_val, hi]

theorem tRunUpto_coreU64 (c : Cfg) (k : Nat) : CoreU64 (tRunUpto c k) := by
  induction k with
  | zero => simpa only [tRunUpto_zero] using tInit_coreU64
  | succ k ih =>
      rw [show k + 1 = k + 1 by rfl, tRunUpto_succ]
      exact tstep_coreU64 c k _ ih

/-- With μ-plane cell zero, an inactive touch leaves every persistent
quantity unchanged.  The hypotheses are only the generic machine-word
bounds needed to remove the final `% M` from the no-op additions/stores. -/
theorem ttouch_gate_zero (c : Cfg) (d : Nat) (t : TState)
    (hmu0 : t.arr 0 = 0)
    (haLo : t.arr (c.touchA1 0 d) < M)
    (haHi : t.arr (c.touchA2 0 d) < M)
    (hdLo : t.dLo < M) (hdHi : t.dHi < M) :
    (c.ttouch 0 d t).viol = t.viol ∧
      (c.ttouch 0 d t).dLo = t.dLo ∧
      (c.ttouch 0 d t).dHi = t.dHi ∧
      (c.ttouch 0 d t).arr = t.arr := by
  let aLo := t.arr (c.touchA1 0 d)
  let aHi := t.arr (c.touchA2 0 d)
  let r := tcmul 0 aLo aHi t.wLo t.wHi t.viol
  let pViol := ttouchProductViol 0 r.1 r.2.1 r.2.2
  let term := ttouchTerm 0 r.1 r.2.1 t.wwLo t.wwHi pViol
  let delta := ttouchDelta 0 0 term.1 term.2.1 t.dLo t.dHi term.2.2
  let stored := ttouchStore 0 aLo aHi t.wLo t.wHi
  have hr : r.2.2 = t.viol := tcmul_gate_zero_viol _ _ _ _ _
  have hp : pViol = t.viol := by
    change ttouchProductViol 0 r.1 r.2.1 r.2.2 = t.viol
    rw [ttouchProductViol_gate_zero, hr]
  have ht : term.2.2 = t.viol := by
    change (ttouchTerm 0 r.1 r.2.1 t.wwLo t.wwHi pViol).2.2 = t.viol
    rw [ttouchTerm_gate_zero, hp]
  have hdelta : delta = (t.dLo, t.dHi, t.viol) := by
    change ttouchDelta 0 0 term.1 term.2.1 t.dLo t.dHi term.2.2 = _
    rw [ttouchDelta_gate_zero _ _ _ _ _ hdLo hdHi, ht]
  have hstored : stored = (aLo, aHi) :=
    ttouchStore_gate_zero _ _ _ _ haLo haHi
  change ttouchDelta 0 0 term.1 term.2.1 t.dLo t.dHi term.2.2 =
    (t.dLo, t.dHi, t.viol) at hdelta
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (ttouchDelta 0 (t.arr (c.touchBase 0 d)) term.1 term.2.1
      t.dLo t.dHi term.2.2).2.2 = t.viol
    simp only [Cfg.touchBase, Nat.zero_mul, Nat.zero_mod, hmu0]
    rw [hdelta]
  · change (ttouchDelta 0 (t.arr (c.touchBase 0 d)) term.1 term.2.1
      t.dLo t.dHi term.2.2).1 = t.dLo
    simp only [Cfg.touchBase, Nat.zero_mul, Nat.zero_mod, hmu0]
    rw [hdelta]
  · change (ttouchDelta 0 (t.arr (c.touchBase 0 d)) term.1 term.2.1
      t.dLo t.dHi term.2.2).2.1 = t.dHi
    simp only [Cfg.touchBase, Nat.zero_mul, Nat.zero_mod, hmu0]
    rw [hdelta]
  · funext i
    change (if i = c.touchA2 0 d then stored.2
      else if i = c.touchA1 0 d then stored.1 else t.arr i) = t.arr i
    rw [hstored]
    by_cases h2 : i = c.touchA2 0 d
    · simp [h2, aHi]
    · by_cases h1 : i = c.touchA1 0 d
      · subst i
        simp [h2, aLo]
      · simp [h2, h1]

/-- With the permanent `arr[0]=0` seed and raw word bounds, an inactive
touch is the identity on the entire transparent state. -/
theorem ttouch_gate_zero_eq (c : Cfg) (d : Nat) (t : TState)
    (hzero : t.arr 0 = 0) (hu64 : PassU64 t) : c.ttouch 0 d t = t := by
  have h := ttouch_gate_zero c d t hzero
    (hu64.2.2.2.2.2.2 (c.touchA1 0 d))
    (hu64.2.2.2.2.2.2 (c.touchA2 0 d))
    hu64.2.2.2.2.1 hu64.2.2.2.2.2.1
  rw [TState.mk.injEq]
  exact ⟨h.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    h.2.1, h.2.2.1, rfl, rfl, h.2.2.2⟩

/-- One live touch simultaneously has the reference accumulator update and
the reference delta update.  Only the scheduling facts `hmu` and `hww`, the
incoming delta caps, and the current touch's clean guards remain as premises;
the accumulator and weight caps are recovered from those guards locally. -/
theorem ttouch_live_spec (c : Cfg) (d : Nat) (t : TState)
    (hc : Admissible c) (hd : d ≤ c.cap)
    (hmu : t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (haLo : t.arr (c.touchA1 1 d) < M)
    (haHi : t.arr (c.touchA2 1 d) < M)
    (hwLo : t.wLo < M) (hwHi : t.wHi < M)
    (hwwLo : t.wwLo < M) (hwwHi : t.wwHi < M)
    (hdLo : t.dLo < M) (hdHi : t.dHi < M)
    (cwwLo : Capped t.wwLo) (cwwHi : Capped t.wwHi)
    (cdLo : Capped t.dLo) (cdHi : Capped t.dHi)
    (hclean : (c.ttouch 1 d t).viol = 0)
    (hww :
      (⟨decodeZ t.wwLo, decodeZ t.wwHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ t.wLo, decodeZ t.wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)) :
    (⟨decodeZ ((c.ttouch 1 d t).arr (d + c.plane1)),
       decodeZ ((c.ttouch 1 d t).arr (d + c.plane2))⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cadd
        ⟨decodeZ (t.arr (c.touchA1 1 d)),
          decodeZ (t.arr (c.touchA2 1 d))⟩
        ⟨decodeZ t.wLo, decodeZ t.wHi⟩ ∧
    (⟨decodeZ (c.ttouch 1 d t).dLo, decodeZ (c.ttouch 1 d t).dHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cadd
        ⟨decodeZ t.dLo, decodeZ t.dHi⟩
        (LeanCompCert.Ports.Section413Sweep.deltaTerm
          (LeanCompCert.Ports.Section413Sweep.muZ d c.rounds)
          ⟨decodeZ (t.arr (c.touchA1 1 d)),
            decodeZ (t.arr (c.touchA2 1 d))⟩
          ⟨decodeZ t.wLo, decodeZ t.wHi⟩) := by
  have hcaps := ttouch_live_caps c d t haLo haHi hwLo hwHi hclean
  change Capped (t.arr (c.touchA1 1 d)) ∧
    Capped (t.arr (c.touchA2 1 d)) ∧ Capped t.wLo ∧ Capped t.wHi ∧ _ at hcaps
  exact ⟨
    ttouch_live_store c d t hc hd haLo haHi hwLo hwHi
      hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2.1,
    ttouch_live_deltaTerm c d t hc hd hmu haLo haHi hwLo hwHi
      hwwLo hwwHi hdLo hdHi cwwLo cwwHi cdLo cdHi hclean hww⟩

/-- The two persistent cells represented by a transparent state. -/
def accAt (c : Cfg) (t : TState) (d : Nat) :
    LeanCompCert.Ports.Section413Sweep.Cell :=
  ⟨decodeZ (t.arr (d + c.plane1)), decodeZ (t.arr (d + c.plane2))⟩

def deltaAt (t : TState) : LeanCompCert.Ports.Section413Sweep.Cell :=
  ⟨decodeZ t.dLo, decodeZ t.dHi⟩

def weightAt (t : TState) : LeanCompCert.Ports.Section413Sweep.Cell :=
  ⟨decodeZ t.wLo, decodeZ t.wHi⟩

def squareAt (t : TState) : LeanCompCert.Ports.Section413Sweep.Cell :=
  ⟨decodeZ t.wwLo, decodeZ t.wwHi⟩

def AccRel (c : Cfg) (t : TState)
    (A : Array LeanCompCert.Ports.Section413Sweep.Cell) : Prop :=
  A.size = c.cap + 1 ∧ ∀ d, d ≤ c.cap → accAt c t d = A[d]!

/-- The exact invariant carried between pass-B touches. -/
structure PassInv (c : Cfg) (W : LeanCompCert.Ports.Section413Sweep.Cell)
    (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell) : Prop where
  u64 : PassU64 t
  arr_zero : t.arr 0 = 0
  wwLo_cap : Capped t.wwLo
  wwHi_cap : Capped t.wwHi
  dLo_cap : Capped t.dLo
  dHi_cap : Capped t.dHi
  weight_eq : weightAt t = W
  square_eq : squareAt t = LeanCompCert.Ports.Section413Sweep.cmul W W
  acc_rel : AccRel c t p.1
  delta_eq : deltaAt t = p.2

/-- Equality of precisely the state fields observed by `PassInv`. -/
structure PassFrame (a b : TState) : Prop where
  wLo : a.wLo = b.wLo
  wHi : a.wHi = b.wHi
  wwLo : a.wwLo = b.wwLo
  wwHi : a.wwHi = b.wwHi
  dLo : a.dLo = b.dLo
  dHi : a.dHi = b.dHi
  arr : a.arr = b.arr

structure DAFrame (a b : TState) : Prop where
  dLo : a.dLo = b.dLo
  dHi : a.dHi = b.dHi
  arr : a.arr = b.arr

theorem DAFrame.trans {a b d : TState} (hab : DAFrame a b)
    (hbd : DAFrame b d) : DAFrame a d :=
  ⟨hab.dLo.trans hbd.dLo, hab.dHi.trans hbd.dHi, hab.arr.trans hbd.arr⟩

theorem PassFrame.trans {a b d : TState} (hab : PassFrame a b)
    (hbd : PassFrame b d) : PassFrame a d := by
  exact ⟨hab.wLo.trans hbd.wLo, hab.wHi.trans hbd.wHi,
    hab.wwLo.trans hbd.wwLo, hab.wwHi.trans hbd.wwHi,
    hab.dLo.trans hbd.dLo, hab.dHi.trans hbd.dHi, hab.arr.trans hbd.arr⟩

theorem ttrial_pass_frame (z : TSel) (t : TState)
    (harr : (ttrial z t).arr = t.arr) : PassFrame (ttrial z t) t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, harr⟩

theorem tpassA_pass_frame (z : TSel) (t : TState) :
    PassFrame (tpassA z t) t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tweight_pass_frame (z : TSel) (t : TState) (hW : z.isW = 0) :
    PassFrame (tweight z t) t := by
  have hWne : z.isW ≠ 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [tweight, hWne, if_false]
  · simp only [tweight, hWne, if_false]
  · simp only [tweight, hWne, if_false]
  · simp only [tweight, hWne, if_false]

theorem PassInv.of_frame {c : Cfg}
    {W : LeanCompCert.Ports.Section413Sweep.Cell} {a b : TState}
    {p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell}
    (h : PassInv c W b p) (hf : PassFrame a b) : PassInv c W a p := by
  rcases hf with ⟨hwLo, hwHi, hwwLo, hwwHi, hdLo, hdHi, harr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [PassU64, hwLo, hwHi, hwwLo, hwwHi, hdLo, hdHi, harr]
      using h.u64
  · simpa only [harr] using h.arr_zero
  · simpa only [hwwLo] using h.wwLo_cap
  · simpa only [hwwHi] using h.wwHi_cap
  · simpa only [hdLo] using h.dLo_cap
  · simpa only [hdHi] using h.dHi_cap
  · simpa only [weightAt, hwLo, hwHi] using h.weight_eq
  · simpa only [squareAt, hwwLo, hwwHi] using h.square_eq
  · rcases h.acc_rel with ⟨hsize, hcells⟩
    refine ⟨hsize, ?_⟩
    intro d hd
    simpa only [accAt, harr] using hcells d hd
  · simpa only [deltaAt, hdLo, hdHi] using h.delta_eq

theorem getElem_bang_set_bang {α : Type} [Inhabited α]
    (A : Array α) (d e : Nat) (v : α) (hd : d < A.size) (he : e < A.size) :
    (A.set! d v)[e]! = if d = e then v else A[e]! := by
  rw [Array.set!_eq_setIfInBounds]
  have he' : e < (A.setIfInBounds d v).size := by
    simpa only [Array.size_setIfInBounds] using he
  rw [getElem!_pos (A.setIfInBounds d v) e he', Array.getElem_setIfInBounds he,
    getElem!_pos A e he]

/-- A live touch frames every other accumulator slot. -/
theorem ttouch_live_acc_frame (c : Cfg) (d e : Nat) (t : TState)
    (hc : Admissible c) (hd : d ≤ c.cap) (he : e ≤ c.cap) (hne : e ≠ d) :
    accAt c (c.ttouch 1 d t) e = accAt c t e := by
  have haddr := touch_addr c hc.arr_fits hd
  have hp : 0 < c.plane1 := by unfold Cfg.plane1; omega
  have hp12 : c.plane1 < c.plane2 := by
    unfold Cfg.plane1 Cfg.plane2
    omega
  have ha1 : c.touchA1 1 d = d + c.plane1 := by
    unfold Cfg.touchA1
    exact haddr.2.1
  have ha2 : c.touchA2 1 d = d + c.plane2 := by
    unfold Cfg.touchA2
    exact haddr.2.2
  unfold accAt
  congr 1
  · rw [ttouch_arr_frame]
    · rw [ha2]
      unfold Cfg.plane1 Cfg.plane2
      omega
    · rw [ha1]
      omega
  · rw [ttouch_arr_frame]
    · rw [ha2]
      omega
    · rw [ha1]
      unfold Cfg.plane1 Cfg.plane2
      omega

/-- A clean live touch caps the delta registers it emits, providing the
inductive cap premise for the next divisor touch. -/
theorem ttouch_live_delta_capped (c : Cfg) (d : Nat) (t : TState)
    (hclean : (c.ttouch 1 d t).viol = 0) :
    Capped (c.ttouch 1 d t).dLo ∧ Capped (c.ttouch 1 d t).dHi := by
  let r := tcmul 1 (t.arr (c.touchA1 1 d)) (t.arr (c.touchA2 1 d))
    t.wLo t.wHi t.viol
  let pViol := ttouchProductViol 1 r.1 r.2.1 r.2.2
  let term := ttouchTerm 1 r.1 r.2.1 t.wwLo t.wwHi pViol
  let delta := ttouchDelta 1 (t.arr (c.touchBase 1 d)) term.1 term.2.1
    t.dLo t.dHi term.2.2
  have hparts := ttouch_clean_parts c 1 d t hclean
  have hdelta : delta.2.2 = 0 := hparts.2.2.2
  have hMpos : 0 < M := by simp only [M_val]; omega
  have hlo : delta.1 < M := by
    dsimp only [delta]
    unfold ttouchDelta
    exact Nat.mod_lt _ hMpos
  have hhi : delta.2.1 < M := by
    dsimp only [delta]
    unfold ttouchDelta
    exact Nat.mod_lt _ hMpos
  have chi : Capped delta.2.1 := capped_of_tguard_eq_zero hhi (by decide) hdelta
  have hinner : tguard 1 delta.1 term.2.2 = 0 := (tguard_eq_zero hdelta).1
  have clo : Capped delta.1 := capped_of_tguard_eq_zero hlo (by decide) hinner
  exact ⟨clo, chi⟩

/-- `ttouch_live_spec` in the compact persistent-cell vocabulary used by the
pass-B induction. -/
theorem ttouch_live_decoded (c : Cfg) (d : Nat) (t : TState)
    (hc : Admissible c) (hd : d ≤ c.cap)
    (hmu : t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (hu64 : PassU64 t) (cwwLo : Capped t.wwLo) (cwwHi : Capped t.wwHi)
    (cdLo : Capped t.dLo) (cdHi : Capped t.dHi)
    (hclean : (c.ttouch 1 d t).viol = 0)
    (hww : squareAt t = LeanCompCert.Ports.Section413Sweep.cmul
      (weightAt t) (weightAt t)) :
    accAt c (c.ttouch 1 d t) d =
      LeanCompCert.Ports.Section413Sweep.cadd (accAt c t d) (weightAt t) ∧
    deltaAt (c.ttouch 1 d t) =
      LeanCompCert.Ports.Section413Sweep.cadd (deltaAt t)
        (LeanCompCert.Ports.Section413Sweep.deltaTerm
          (LeanCompCert.Ports.Section413Sweep.muZ d c.rounds)
          (accAt c t d) (weightAt t)) := by
  rcases hu64 with ⟨hwLo, hwHi, hwwLo, hwwHi, hdLo, hdHi, harr⟩
  have haddr := touch_addr c hc.arr_fits hd
  have ha1 : c.touchA1 1 d = d + c.plane1 := by
    unfold Cfg.touchA1
    exact haddr.2.1
  have ha2 : c.touchA2 1 d = d + c.plane2 := by
    unfold Cfg.touchA2
    exact haddr.2.2
  have hs := ttouch_live_spec c d t hc hd hmu
    (harr _) (harr _) hwLo hwHi hwwLo hwwHi hdLo hdHi
    cwwLo cwwHi cdLo cdHi hclean hww
  simpa only [accAt, deltaAt, weightAt, squareAt, ha1, ha2] using hs

theorem AccRel_live_store (c : Cfg) (d : Nat) (t : TState)
    (A : Array LeanCompCert.Ports.Section413Sweep.Cell)
    (hc : Admissible c) (hd : d ≤ c.cap) (hrel : AccRel c t A)
    (hupdate : accAt c (c.ttouch 1 d t) d =
      LeanCompCert.Ports.Section413Sweep.cadd (accAt c t d) (weightAt t)) :
    AccRel c (c.ttouch 1 d t)
      (A.set! d (LeanCompCert.Ports.Section413Sweep.cadd A[d]! (weightAt t))) := by
  constructor
  · rw [Array.size_set!, hrel.1]
  · intro e he
    have hdA : d < A.size := by rw [hrel.1]; omega
    have heA : e < A.size := by rw [hrel.1]; omega
    rw [getElem_bang_set_bang A d e _ hdA heA]
    by_cases hde : d = e
    · subst e
      rw [if_pos rfl, hupdate, hrel.2 d hd]
    · rw [if_neg hde]
      exact (ttouch_live_acc_frame c d e t hc hd he (Ne.symm hde)).trans
        (hrel.2 e he)

/-- One live machine touch advances exactly one reference `touch` while
preserving every premise required by the next live touch. -/
theorem PassInv.touch_live (c : Cfg)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (d : Nat) (hc : Admissible c) (hd : d ≤ c.cap)
    (hmu : t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (hinv : PassInv c W t p) (hclean : (c.ttouch 1 d t).viol = 0) :
    PassInv c W (c.ttouch 1 d t)
      (LeanCompCert.Ports.Section413Sweep.touch c.rounds W p d) := by
  have hww : squareAt t = LeanCompCert.Ports.Section413Sweep.cmul
      (weightAt t) (weightAt t) := by
    rw [hinv.weight_eq]
    exact hinv.square_eq
  have hdec := ttouch_live_decoded c d t hc hd hmu hinv.u64
    hinv.wwLo_cap hinv.wwHi_cap hinv.dLo_cap hinv.dHi_cap hclean hww
  have hacc := AccRel_live_store c d t p.1 hc hd hinv.acc_rel hdec.1
  have hzero : (c.ttouch 1 d t).arr 0 = 0 := by
    rw [ttouch_mu_frame c 1 d t 0 hc (by simpa using hd) (by omega),
      hinv.arr_zero]
  refine ⟨ttouch_passU64 c 1 d t hinv.u64, hzero,
    hinv.wwLo_cap, hinv.wwHi_cap,
    (ttouch_live_delta_capped c d t hclean).1,
    (ttouch_live_delta_capped c d t hclean).2,
    hinv.weight_eq, hinv.square_eq, ?_, ?_⟩
  · simpa only [LeanCompCert.Ports.Section413Sweep.touch, hinv.weight_eq]
      using hacc
  · simpa only [LeanCompCert.Ports.Section413Sweep.touch, hinv.delta_eq,
      hinv.weight_eq, hinv.acc_rel.2 d hd] using hdec.2

theorem PassInv.touch_zero (c : Cfg)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (d : Nat) (hinv : PassInv c W t p) :
    PassInv c W (c.ttouch 0 d t) p := by
  rw [ttouch_gate_zero_eq c d t hinv.arr_zero hinv.u64]
  exact hinv

/-! ## §16 A legacy global guard invariant

These definitions record the first proof route considered for obligation
(2).  They remain useful descriptions of the initial state, but they are not
the invariant used by the soundness proof: accumulator-plane stores are not
guarded immediately, so `ArrCapped` is not preserved after every `tstep`.

The selected route instead obtains bounds exactly where the machine checks
them.  `ttouch_clean_parts` and `ttouch_live_caps` extract the local guards;
`tcmul_decode`, `ttouch_live_term_decode`, `ttouch_live_delta_decode`, and
`ttouchStore_decode` then transfer one live touch without asserting a global
cap on every accumulator slot. -/

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

/-! ## §16 The divisor-pair sum used by pass A -/

/-- One mathematical divisor-pair accumulator step. -/
def sigmaStep (X r acc : Nat) : Nat :=
  if X % r = 0 then
    if r * r ≤ X then
      acc + r + (if X / r ≠ r then X / r else 0)
    else acc
  else acc

/-- The pass-A sum with the machine's explicit square guard.  Unlike the
reference `sigmaPair`, this may be run past `Nat.sqrt X`; those extra rounds
are identities. -/
def sigmaScan (X k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => sigmaStep X (i + 1) acc) 0

/-- The square guard at zero-based index `i` is exactly membership in the
reference scan range. -/
theorem sq_le_iff_lt_sqrt (X i : Nat) :
    (i + 1) * (i + 1) ≤ X ↔ i < Nat.sqrt X := by
  constructor
  · intro h
    have := LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le h
    omega
  · intro h
    exact LeanCompCert.Verified.SqrtEquiv.sq_le_of_le_sqrt (by omega)

/-- Up to the square root, `sigmaScan` is definitionally the reference
divisor-pair fold: its extra guard is true at every visited index. -/
theorem sigmaScan_le_sqrt (X k : Nat) (hk : k ≤ Nat.sqrt X) :
    sigmaScan X k =
      (List.range k).foldl
        (fun acc i =>
          let r := i + 1
          if X % r = 0 then
            acc + r + (if X / r ≠ r then X / r else 0)
          else acc) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ Nat.sqrt X := by omega
      have hsquare : (k + 1) * (k + 1) ≤ X :=
        (sq_le_iff_lt_sqrt X k).2 (by omega)
      unfold sigmaScan sigmaStep at ih ⊢
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hk']
      simp only [hsquare, ↓reduceIte]

theorem sigmaScan_sqrt (X : Nat) :
    sigmaScan X (Nat.sqrt X) =
      LeanCompCert.Ports.Section413Sweep.sigmaPair X := by
  unfold LeanCompCert.Ports.Section413Sweep.sigmaPair
  exact sigmaScan_le_sqrt X (Nat.sqrt X) (Nat.le_refl _)

/-- Once the square-root boundary has been reached, every later guarded
round is an identity. -/
theorem sigmaScan_add_sqrt (X d : Nat) :
    sigmaScan X (Nat.sqrt X + d) =
      LeanCompCert.Ports.Section413Sweep.sigmaPair X := by
  induction d with
  | zero => simpa using sigmaScan_sqrt X
  | succ d ih =>
      have hroot :
          X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
      have hle : Nat.sqrt X + 1 ≤ Nat.sqrt X + d + 1 := by omega
      have hsq :
          (Nat.sqrt X + 1) * (Nat.sqrt X + 1) ≤
            (Nat.sqrt X + d + 1) * (Nat.sqrt X + d + 1) :=
        Nat.mul_le_mul hle hle
      have hoff : ¬ ((Nat.sqrt X + d + 1) * (Nat.sqrt X + d + 1) ≤ X) := by
        omega
      unfold sigmaScan sigmaStep at ih ⊢
      rw [show Nat.sqrt X + (d + 1) = (Nat.sqrt X + d) + 1 by omega,
        List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp [hoff]

/-- The configured pass-A length covers the square root of every candidate. -/
theorem sqrt_le_cfg_s (c : Cfg) {X : Nat} (hXc : X ≤ c.cap) :
    Nat.sqrt X ≤ c.s := by
  unfold Cfg.s
  apply LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le
  exact Nat.le_trans (Nat.sqrt_le X) hXc

/-- Therefore the full configured guarded scan is exactly `sigmaPair`. -/
theorem sigmaScan_cfg_s (c : Cfg) (X : Nat) (hXc : X ≤ c.cap) :
    sigmaScan X c.s = LeanCompCert.Ports.Section413Sweep.sigmaPair X := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (sqrt_le_cfg_s c hXc)
  rw [hd]
  exact sigmaScan_add_sqrt X d

theorem sigmaScan_succ (X k : Nat) :
    sigmaScan X (k + 1) = sigmaStep X (k + 1) (sigmaScan X k) := by
  unfold sigmaScan
  rw [List.range_succ, List.foldl_append]
  rfl

/-- A live divisor-pair contribution is at most `2X`. -/
theorem sigmaStep_le (X r acc : Nat) (hr : 0 < r) :
    sigmaStep X r acc ≤ acc + 2 * X := by
  unfold sigmaStep
  split
  · split
    · have hrX : r ≤ X := by
        have hrr : r ≤ r * r := by
          calc
            r = r * 1 := by simp
            _ ≤ r * r := Nat.mul_le_mul_left r hr
        exact Nat.le_trans hrr ‹r * r ≤ X›
      have hq : X / r ≤ X := Nat.div_le_self X r
      split
      · have hadd : acc + r + X / r ≤ acc + X + X :=
          Nat.add_le_add (Nat.add_le_add_left hrX acc) hq
        calc
          acc + r + X / r ≤ acc + X + X := hadd
          _ = acc + 2 * X := by omega
      · have hadd : acc + r ≤ acc + X := Nat.add_le_add_left hrX acc
        have hX2 : X ≤ 2 * X := by omega
        exact Nat.le_trans hadd (Nat.add_le_add_left hX2 acc)
    · exact Nat.le_add_right acc (2 * X)
  · exact Nat.le_add_right acc (2 * X)

theorem sigmaScan_le (X k : Nat) : sigmaScan X k ≤ k * (2 * X) := by
  induction k with
  | zero => simp [sigmaScan]
  | succ k ih =>
      rw [sigmaScan_succ]
      have hs := sigmaStep_le X (k + 1) (sigmaScan X k) (by omega)
      calc
        sigmaStep X (k + 1) (sigmaScan X k)
            ≤ sigmaScan X k + 2 * X := hs
        _ ≤ k * (2 * X) + 2 * X := Nat.add_le_add_right ih _
        _ = (k + 1) * (2 * X) := by rw [Nat.add_mul]; simp

theorem sigmaStep_acc_le (X r acc : Nat) : acc ≤ sigmaStep X r acc := by
  unfold sigmaStep
  split
  · split <;> omega
  · exact Nat.le_refl _

theorem sigmaScan_add_mono (X k d : Nat) :
    sigmaScan X k ≤ sigmaScan X (k + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show k + (d + 1) = (k + d) + 1 by omega, sigmaScan_succ]
      exact Nat.le_trans ih (sigmaStep_acc_le _ _ _)

theorem sigmaPair_pos (X : Nat) (hX : 1 ≤ X) :
    0 < LeanCompCert.Ports.Section413Sweep.sigmaPair X := by
  have hroot : 1 ≤ Nat.sqrt X := by
    apply LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le
    simpa using hX
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hroot
  have hfirst : 0 < sigmaScan X 1 := by
    simp [sigmaScan, sigmaStep, Nat.mod_one]
    split <;> omega
  have hmono := sigmaScan_add_mono X 1 d
  rw [← hd, sigmaScan_sqrt] at hmono
  exact Nat.lt_of_lt_of_le hfirst hmono

/-- The reference rational weight for one of the three machine Möbius codes.
This isolates the signed floor/ceiling rounding identity used by `tweight`. -/
theorem cratSMul_of_code {mc sig : Nat}
    (hmc : mc = 0 ∨ mc = 1 ∨ mc = 2) (hsig : 0 < sig) :
    LeanCompCert.Ports.Section413Sweep.cratSMul
        (if mc = 1 then 1 else if mc = 2 then -1 else 0) sig
        LeanCompCert.Ports.Section413Sweep.cone =
      (⟨if mc = 1 then (LeanCompCert.Ports.Section413Sweep.SCALE / sig : Nat)
          else if mc = 2 then -(((LeanCompCert.Ports.Section413Sweep.SCALE +
            (sig - 1)) / sig : Nat) : Int)
          else 0,
        if mc = 1 then (((LeanCompCert.Ports.Section413Sweep.SCALE +
            (sig - 1)) / sig : Nat) : Int)
          else if mc = 2 then
            -((LeanCompCert.Ports.Section413Sweep.SCALE / sig : Nat) : Int)
          else 0⟩ : LeanCompCert.Ports.Section413Sweep.Cell) := by
  rcases hmc with rfl | rfl | rfl
  · simp [LeanCompCert.Ports.Section413Sweep.cratSMul,
      LeanCompCert.Ports.Section413Sweep.cdivNat,
      LeanCompCert.Ports.Section413Sweep.csmul,
      LeanCompCert.Ports.Section413Sweep.cone,
      LeanCompCert.Ports.Section413Sweep.cfloorDiv,
      LeanCompCert.Ports.Section413Sweep.cceilDiv]
  · simp only [LeanCompCert.Ports.Section413Sweep.cratSMul,
      LeanCompCert.Ports.Section413Sweep.cdivNat,
      LeanCompCert.Ports.Section413Sweep.csmul,
      LeanCompCert.Ports.Section413Sweep.cone,
      LeanCompCert.Ports.Section413Sweep.cfloorDiv,
      LeanCompCert.Ports.Section413Sweep.cceilDiv, if_pos, Int.reduceLE,
      Int.one_mul]
    rw [LeanCompCert.Ports.Section413Cells.natCast_ediv,
      LeanCompCert.Ports.Section413Cells.neg_natCast_ediv
        LeanCompCert.Ports.Section413Sweep.SCALE sig hsig]
    simp
  · simp only [LeanCompCert.Ports.Section413Sweep.cratSMul,
      LeanCompCert.Ports.Section413Sweep.cdivNat,
      LeanCompCert.Ports.Section413Sweep.csmul,
      LeanCompCert.Ports.Section413Sweep.cone,
      LeanCompCert.Ports.Section413Sweep.cfloorDiv,
      LeanCompCert.Ports.Section413Sweep.cceilDiv, Nat.reduceEqDiff,
      ↓reduceIte, Int.reduceLE, Int.reduceNeg, Int.neg_mul, Int.one_mul]
    rw [LeanCompCert.Ports.Section413Cells.neg_natCast_ediv
        LeanCompCert.Ports.Section413Sweep.SCALE sig hsig]
    simp only [Int.neg_neg]
    rw [LeanCompCert.Ports.Section413Cells.natCast_ediv]

theorem decodeZ_ofNat_small (n : Nat) (hn : n < H63) : decodeZ n = (n : Int) := by
  unfold decodeZ
  rw [if_pos]
  simpa only [cellsH63_val, H63_val] using hn

theorem decodeZ_tsub_small (n : Nat) (hn : n < H63) :
    decodeZ (tsub 0 n) = -(n : Int) := by
  rw [tsub_zero_encodeZ_neg n (by simpa only [H63_val] using hn)]
  apply LeanCompCert.Ports.Section413Cells.decodeZ_encodeZ
  · change -(LeanCompCert.Ports.Section413Cells.H63 : Int) ≤ -(n : Int)
    simp only [cellsH63_val, H63_val] at *
    omega
  · change -(n : Int) < (LeanCompCert.Ports.Section413Cells.H63 : Int)
    simp only [cellsH63_val]
    omega

/-- The two rounded magnitudes used by the weight block lie below the fixed
scale, independently of the positive denominator. -/
theorem weight_quotients_le (sig : Nat) (hsig : 0 < sig) :
    SCALE / sig ≤ SCALE ∧ (SCALE + (sig - 1)) / sig ≤ SCALE := by
  constructor
  · exact Nat.div_le_self SCALE sig
  · apply Nat.div_le_of_le_mul
    have hm : sig - 1 ≤ (sig - 1) * SCALE := by
      have := Nat.mul_le_mul_right (sig - 1) (by decide : 1 ≤ SCALE)
      calc
        sig - 1 = 1 * (sig - 1) := by simp
        _ ≤ SCALE * (sig - 1) := this
        _ = (sig - 1) * SCALE := Nat.mul_comm ..
    have hsigEq : sig * SCALE = SCALE + (sig - 1) * SCALE := by
      have hs : sig = 1 + (sig - 1) := by omega
      calc
        sig * SCALE = (1 + (sig - 1)) * SCALE := congrArg (fun n => n * SCALE) hs
        _ = SCALE + (sig - 1) * SCALE := by rw [Nat.add_mul, Nat.one_mul]
    calc
      SCALE + (sig - 1) ≤ SCALE + (sig - 1) * SCALE :=
        Nat.add_le_add_left hm SCALE
      _ = sig * SCALE := hsigEq.symm

/-- Every endpoint of the reference weight has magnitude at most one fixed
scale unit. -/
theorem weightV2_natAbs_le_scale (R X : Nat) (hX : 1 ≤ X) :
    (LeanCompCert.Ports.Section413Sweep.weightV2 R X).lo.natAbs ≤ SCALE ∧
      (LeanCompCert.Ports.Section413Sweep.weightV2 R X).hi.natAbs ≤ SCALE := by
  let mc := LeanCompCert.Ports.MertensCDEM.muCode X R
  let sig := LeanCompCert.Ports.Section413Sweep.sigmaPair X
  have hmc := muCode_cases X R
  have hsig : 0 < sig := sigmaPair_pos X hX
  have hq := weight_quotients_le sig hsig
  have hrat := cratSMul_of_code hmc hsig
  have hmuz :
      (if mc = 1 then (1 : Int) else if mc = 2 then -1 else 0) =
        LeanCompCert.Ports.Section413Sweep.muZ X R :=
    muZ_of_code (X := X) (R := R) (mc := mc) rfl
  rw [hmuz, ← SCALE_eq_sweep] at hrat
  by_cases hodd : X % 2 = 1
  · rw [LeanCompCert.Ports.Section413Sweep.weightV2, if_pos hodd, hrat]
    rcases hmc with h0 | h1 | h2
    · simp [h0]
    · simp only [h1, if_pos, Int.natAbs_natCast]
      exact hq
    · simp only [h2, Nat.reduceEqDiff, ↓reduceIte, Int.natAbs_neg,
        Int.natAbs_natCast]
      exact ⟨hq.2, hq.1⟩
  · rw [LeanCompCert.Ports.Section413Sweep.weightV2, if_neg hodd]
    simp [LeanCompCert.Ports.Section413Sweep.czero]

/-- At a live weight selector, the transparent word block decodes to the
reference `weightV2` cell. -/
theorem tweight_live_weight (R X sig mc : Nat) (z : TSel) (t : TState)
    (hW : z.isW = 1) (hX : z.X = X) (hXM : X < M)
    (harr : t.arr X = mc)
    (hcode : mc = LeanCompCert.Ports.MertensCDEM.muCode X R)
    (hsigma : t.sigma = sig)
    (hsigRef : sig = LeanCompCert.Ports.Section413Sweep.sigmaPair X)
    (hsig : 0 < sig)
    (hsigAddM : sig + SCALE < M) :
    (⟨decodeZ (tweight z t).wLo, decodeZ (tweight z t).wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.weightV2 R X := by
  have hmc := muCode_cases X R
  rw [← hcode] at hmc
  have hsigM : sig < M := by omega
  have hnumM : sig + (SCALE - 1) < M := by omega
  have hq := weight_quotients_le sig hsig
  have hfH : SCALE / sig < H63 :=
    Nat.lt_of_le_of_lt hq.1 (by decide)
  have hcH : (SCALE + (sig - 1)) / sig < H63 :=
    Nat.lt_of_le_of_lt hq.2 (by decide)
  have hmu := muZ_of_code hcode
  have hrat := cratSMul_of_code hmc hsig
  rw [hmu] at hrat
  have hsigNe : sig ≠ 0 := Nat.ne_of_gt hsig
  have hceilWord : (sig + (SCALE - 1)) % M / sig =
      (SCALE + (sig - 1)) / sig := by
    rw [Nat.mod_eq_of_lt hnumM]
    have hScalePos : 1 ≤ SCALE := by decide
    have hnumEq : sig + (SCALE - 1) = SCALE + (sig - 1) := by omega
    rw [hnumEq]
  have hfM : SCALE / sig < M := Nat.lt_trans hfH (by
    simp only [H63_val, M_val]
    omega)
  have hcM : (SCALE + (sig - 1)) / sig < M := Nat.lt_trans hcH (by
    simp only [H63_val, M_val]
    omega)
  have hnegFmod : tsub 0 (SCALE / sig) % M = tsub 0 (SCALE / sig) :=
    Nat.mod_eq_of_lt (tsub_lt _ _)
  have hnegCmod : tsub 0 ((SCALE + (sig - 1)) / sig) % M =
      tsub 0 ((SCALE + (sig - 1)) / sig) :=
    Nat.mod_eq_of_lt (tsub_lt _ _)
  have hfH' : LeanCompCert.Ports.Section413Sweep.SCALE / sig < H63 := by
    rw [← SCALE_eq_sweep]
    exact hfH
  have hcH' : (LeanCompCert.Ports.Section413Sweep.SCALE + (sig - 1)) / sig < H63 := by
    rw [← SCALE_eq_sweep]
    exact hcH
  have hfM' : LeanCompCert.Ports.Section413Sweep.SCALE / sig < M := by
    rw [← SCALE_eq_sweep]
    exact hfM
  have hcM' : (LeanCompCert.Ports.Section413Sweep.SCALE + (sig - 1)) / sig < M := by
    rw [← SCALE_eq_sweep]
    exact hcM
  have hceilWord' :
      (sig + (LeanCompCert.Ports.Section413Sweep.SCALE - 1)) % M / sig =
        (LeanCompCert.Ports.Section413Sweep.SCALE + (sig - 1)) / sig := by
    rw [← SCALE_eq_sweep]
    exact hceilWord
  have hnegFmod' :
      tsub 0 (LeanCompCert.Ports.Section413Sweep.SCALE / sig) % M =
        tsub 0 (LeanCompCert.Ports.Section413Sweep.SCALE / sig) := by
    rw [← SCALE_eq_sweep]
    exact hnegFmod
  have hnegCmod' :
      tsub 0 ((LeanCompCert.Ports.Section413Sweep.SCALE + (sig - 1)) / sig) % M =
        tsub 0 ((LeanCompCert.Ports.Section413Sweep.SCALE + (sig - 1)) / sig) := by
    rw [← SCALE_eq_sweep]
    exact hnegCmod
  have hXmod : X % M = X := Nat.mod_eq_of_lt hXM
  by_cases hodd : X % 2 = 1
  · rw [LeanCompCert.Ports.Section413Sweep.weightV2, if_pos hodd,
      ← hsigRef, hrat]
    rcases hmc with rfl | rfl | rfl
    · simp [tweight, hW, hX, hXmod, harr, hsigma, hsigNe,
        Nat.mod_eq_of_lt hsigM,
          bnat, hodd, SCALE_eq_sweep,
        LeanCompCert.Ports.Section413Cells.decodeZ_zero]
    · simp [tweight, hW, hX, hXmod, harr, hsigma, hsigNe,
        Nat.mod_eq_of_lt hsigM,
        bnat, hodd,
        SCALE_eq_sweep]
      constructor
      · rw [Nat.mod_eq_of_lt hfM', decodeZ_ofNat_small _ hfH']
        exact (LeanCompCert.Ports.Section413Cells.natCast_ediv _ _).symm
      · rw [hceilWord', Nat.mod_eq_of_lt hcM', decodeZ_ofNat_small _ hcH']
        exact (LeanCompCert.Ports.Section413Cells.natCast_ediv _ _).symm
    · simp [tweight, hW, hX, hXmod, harr, hsigma, hsigNe,
        Nat.mod_eq_of_lt hsigM,
        bnat, hodd,
        SCALE_eq_sweep]
      constructor
      · rw [hceilWord', hnegCmod', decodeZ_tsub_small _ hcH']
        congr 1
      · rw [hnegFmod', decodeZ_tsub_small _ hfH']
        congr 1
  · rw [LeanCompCert.Ports.Section413Sweep.weightV2, if_neg hodd]
    simp [tweight, hW, hX, hXmod, harr, hsigma, hsigNe,
      Nat.mod_eq_of_lt hsigM, hceilWord,
      bnat, hodd, LeanCompCert.Ports.Section413Sweep.czero,
      LeanCompCert.Ports.Section413Cells.decodeZ_zero]

/-- A clean live weight block also records the exact interval square of the
weight it just wrote.  This is the relation consumed by every pass-B touch;
keeping it local avoids a global register invariant. -/
theorem tweight_live_square (z : TSel) (t : TState)
    (hW : z.isW = 1) (hclean : (tweight z t).viol = 0) :
    (⟨decodeZ (tweight z t).wwLo, decodeZ (tweight z t).wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ (tweight z t).wLo, decodeZ (tweight z t).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ (tweight z t).wLo, decodeZ (tweight z t).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell) := by
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
  let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  let wLo := (isP * magF + isM * tsub 0 magC) % M * live % M
  let wHi := (isP * magC + isM * tsub 0 magF) % M * live % M
  let ww := tcmul z.isW wLo wHi wLo wHi t.viol
  have hMpos : 0 < M := by simp only [M_val]; omega
  have hwLo : wLo < M := Nat.mod_lt _ hMpos
  have hwHi : wHi < M := Nat.mod_lt _ hMpos
  have hww : ww.2.2 = 0 := by
    simpa only [ww, tweight, hW, if_pos, muX, isP, isM, live, sig1,
      magF, magC, wLo, wHi] using hclean
  have hmul := tcmul_decode (gate := z.isW) (aLo := wLo) (aHi := wHi)
    (bLo := wLo) (bHi := wHi) (viol := t.viol)
    (by omega) hwLo hwHi hwLo hwHi hww
  have hcell := congrArg
    (fun p : Int × Int =>
      (⟨p.1, p.2⟩ : LeanCompCert.Ports.Section413Sweep.Cell)) hmul
  simpa only [ww, tweight, hW, if_pos, muX, isP, isM, live, sig1,
    magF, magC, wLo, wHi] using hcell

/-- A clean live weight round establishes all raw bounds required by pass B,
provided the inherited delta registers and array were already words. -/
theorem tweight_passU64 (z : TSel) (t : TState) (hW : z.isW = 1)
    (hdLo : t.dLo < M) (hdHi : t.dHi < M)
    (harr : ∀ i, t.arr i < M) (hclean : (tweight z t).viol = 0) :
    PassU64 (tweight z t) := by
  let muX := t.arr (z.isW * z.X % M)
  let isP := bnat (muX = 1)
  let isM := bnat (muX = 2)
  let live := (isP + isM) * bnat (z.X % 2 = 1) * z.isW
  let sig1 := (t.sigma + bnat (t.sigma = 0)) % M
  let magF := SCALE / sig1
  let magC := ((sig1 + (SCALE - 1)) % M) / sig1
  let wLo := (isP * magF + isM * tsub 0 magC) % M * live % M
  let wHi := (isP * magC + isM * tsub 0 magF) % M * live % M
  let ww := tcmul z.isW wLo wHi wLo wHi t.viol
  have hMpos : 0 < M := by simp only [M_val]; omega
  have hwLo : wLo < M := Nat.mod_lt _ hMpos
  have hwHi : wHi < M := Nat.mod_lt _ hMpos
  have hwwClean : ww.2.2 = 0 := by
    simpa only [ww, tweight, hW, if_pos, muX, isP, isM, live, sig1,
      magF, magC, wLo, wHi] using hclean
  have hww := tcmul_lt (gate := z.isW) (aLo := wLo) (aHi := wHi)
    (bLo := wLo) (bHi := wHi) (viol := t.viol)
    (by omega) hwLo hwHi hwLo hwHi hwwClean
  have hout : wLo < M ∧ wHi < M ∧ ww.1 < M ∧ ww.2.1 < M ∧
      t.dLo < M ∧ t.dHi < M ∧ ∀ i, t.arr i < M :=
    ⟨hwLo, hwHi, hww.1, hww.2, hdLo, hdHi, harr⟩
  simpa only [PassU64, tweight, hW, if_pos, muX, isP, isM, live, sig1,
    magF, magC, wLo, wHi, ww] using hout

/-- Selector decoding inside candidate `x+1` and phase-2 position `pos`.
All word-valued fields are ordinary naturals in the live range. -/
theorem tsel_phase2_block (c : Cfg) (hc : Admissible c) (x pos : Nat)
    (hx : x < c.cap) (hpos : pos < c.p) :
    let z := c.tsel (c.phase1 + x * c.p + pos)
    z.inP1 = 0 ∧ z.inP2 = 1 ∧ z.b2 = x * c.p + pos ∧
      z.x0 = x ∧ z.pX = pos ∧ z.X = x + 1 ∧
      z.inA = bnat (pos < c.s) ∧ z.isW = bnat (pos = c.s) ∧
      z.rA = pos + 1 := by
  have hp : 0 < c.p := by simp [Cfg.p]
  have htail : x * c.p + pos < c.cap * c.p := by
    have hmul : (x + 1) * c.p ≤ c.cap * c.p :=
      Nat.mul_le_mul_right c.p (by omega)
    rw [Nat.add_mul] at hmul
    omega
  have hcp : c.cap * c.p ≤ c.cap * (2 * c.cap + 2) :=
    Nat.mul_le_mul_left c.cap hc.p_le
  have hidxM : c.phase1 + x * c.p + pos < M := by
    have := hc.loop_fits
    unfold Cfg.phase1 at this ⊢
    omega
  have hphaseM : c.phase1 ≤ M := by omega
  have hb2M : x * c.p + pos < M := by omega
  have hsub : tsub (c.phase1 + x * c.p + pos) c.phase1 = x * c.p + pos := by
    unfold tsub
    have heq : c.phase1 + x * c.p + pos + (M - c.phase1) =
        (x * c.p + pos) + M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hb2M]
  have hdecode :
      (x * c.p + pos) / c.p = x ∧ (x * c.p + pos) % c.p = pos := by
    constructor
    · rw [Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt hpos,
        Nat.add_zero]
    · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hpos]
  have hcapM : c.cap < M := by
    have := hc.arr_fits
    simp only [M_val] at this ⊢
    omega
  have hxM : x + 1 < M := by omega
  have hpM : c.p < M := by
    have hcap1 : 1 ≤ c.cap := hc.cap_pos
    have hle : c.p ≤ c.cap * c.p := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.p hcap1
    have hcpm : c.cap * c.p < M := by
      have := hc.loop_fits
      exact Nat.lt_of_le_of_lt hcp (by omega)
    exact Nat.lt_of_le_of_lt hle hcpm
  have hposM : pos + 1 < M := by omega
  have hphase : ¬ (c.phase1 + x * c.p + pos < c.phase1) := by omega
  simp [Cfg.tsel, hphase, hsub, hdecode.1, hdecode.2, Nat.mod_eq_of_lt hxM,
    Nat.mod_eq_of_lt hposM, bnat]

/-- Selector specialization for pass B.  Position `s+r` is the live divisor
slot `r`, for every `1 ≤ r ≤ s`; in particular no modular subtraction is
hidden in the scheduled divisor. -/
theorem tsel_passB_block (c : Cfg) (hc : Admissible c) (x r : Nat)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s) :
    let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
    z.inP1 = 0 ∧ z.inP2 = 1 ∧ z.X = x + 1 ∧
      z.inB = 1 ∧ z.rBr = r ∧ z.rB = r := by
  have hpos : c.s + r < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x (c.s + r) hx hpos
  rcases hz with ⟨hP1, hP2, _hb2, _hx0, hpX, hX, _hA, _hW, _hrA⟩
  let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
  have hInB : z.inB = 1 := by
    change bnat (c.s + 1 ≤ z.pX) * bnat (z.pX ≤ 2 * c.s) * z.inP2 = 1
    rw [hpX, hP2]
    have hlo : c.s + 1 ≤ c.s + r := by omega
    have hhi : c.s + r ≤ 2 * c.s := by omega
    simp [bnat, hlo, hhi]
  have hsCap : c.s ≤ c.cap := sqrt_le_self c.cap
  have hposM : c.s + r < M := by
    have := hc.arr_fits
    simp only [M_val] at this ⊢
    omega
  have hsM : c.s ≤ M := by omega
  have hrM : r < M := by omega
  have hsub : tsub (c.s + r) c.s = r := by
    unfold tsub
    have heq : c.s + r + (M - c.s) = r + M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hrM]
  have hrBr : z.rBr = r := by
    change tsub z.pX c.s = r
    rw [hpX, hsub]
  have hrB : z.rB = r := by
    change (bnat (z.rBr = 0) + z.rBr) % M = r
    rw [hrBr]
    simp [bnat, Nat.ne_of_gt hr, Nat.mod_eq_of_lt hrM]
  exact ⟨hP1, hP2, hX, hInB, hrBr, hrB⟩

/-- Every scheduled pass-B square test is an ordinary natural square test:
the product is below `2^64`, so the machine's `% M` is inert. -/
theorem passB_square_no_wrap (c : Cfg) (hc : Admissible c) (r : Nat)
    (hrs : r ≤ c.s) : r * r < M := by
  have hsCap : c.s ≤ c.cap := sqrt_le_self c.cap
  have hrCap : r ≤ c.cap := Nat.le_trans hrs hsCap
  have hrr : r * r ≤ c.cap * c.cap := Nat.mul_le_mul hrCap hrCap
  have hcap : c.cap * c.cap ≤ c.cap * (2 * c.cap + 2) :=
    Nat.mul_le_mul_left c.cap (by omega)
  have hlarge : c.cap * (2 * c.cap + 2) < M := by
    have := hc.loop_fits
    omega
  exact Nat.lt_of_le_of_lt (Nat.le_trans hrr hcap) hlarge

/-- On a reference divisor round `r ≤ √X`, the two machine gates are exactly
the divisor gate and its unequal-partner gate. -/
theorem passB_gates_live (c : Cfg) (hc : Admissible c) (x r : Nat)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : r ≤ Nat.sqrt (x + 1)) :
    let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
    let g₁ := bnat (z.X % z.rB = 0) *
      bnat (z.rB * z.rB % M ≤ z.X) * z.inB
    let q₂ := z.X / z.rB
    let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
    g₁ = bnat ((x + 1) % r = 0) ∧ q₂ = (x + 1) / r ∧
      g₂ = bnat ((x + 1) % r = 0) *
        (1 - bnat ((x + 1) / r = r)) := by
  have hz := tsel_passB_block c hc x r hx hr hrs
  rcases hz with ⟨_hP1, _hP2, hX, hInB, _hrBr, hrB⟩
  have hrrM := passB_square_no_wrap c hc r hrs
  have hsq : r * r ≤ x + 1 :=
    LeanCompCert.Verified.SqrtEquiv.sq_le_of_le_sqrt hrX
  simp [hX, hrB, hInB, Nat.mod_eq_of_lt hrrM, hsq, bnat]

/-- Rounds beyond `√X` are genuine no-ops: the explicit square gate turns
both touches off. -/
theorem passB_gates_past_sqrt (c : Cfg) (hc : Admissible c) (x r : Nat)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : Nat.sqrt (x + 1) < r) :
    let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
    let g₁ := bnat (z.X % z.rB = 0) *
      bnat (z.rB * z.rB % M ≤ z.X) * z.inB
    let q₂ := z.X / z.rB
    let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
    g₁ = 0 ∧ g₂ = 0 := by
  have hz := tsel_passB_block c hc x r hx hr hrs
  rcases hz with ⟨_hP1, _hP2, hX, hInB, _hrBr, hrB⟩
  have hrrM := passB_square_no_wrap c hc r hrs
  have hsq : ¬ r * r ≤ x + 1 := by
    intro h
    have := LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le h
    omega
  simp [hX, hrB, hInB, Nat.mod_eq_of_lt hrrM, hsq, bnat]

/-- One scheduled pass-B round is exactly one iteration of the reference
divisor-pair fold. -/
theorem PassInv.passB_round (c : Cfg) (hc : Admissible c) (x r : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : r ≤ Nat.sqrt (x + 1))
    (hmu : ∀ d, 1 ≤ d → d ≤ c.cap →
      t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (hinv : PassInv c W t p)
    (hclean : (c.tpassB
      (c.tsel (c.phase1 + x * c.p + (c.s + r))) t).viol = 0) :
    let X := x + 1
    let q := X / r
    let p' := if X % r = 0 then
        let p1 := LeanCompCert.Ports.Section413Sweep.touch c.rounds W p r
        if q ≠ r then
          LeanCompCert.Ports.Section413Sweep.touch c.rounds W p1 q
        else p1
      else p
    PassInv c W
      (c.tpassB (c.tsel (c.phase1 + x * c.p + (c.s + r))) t) p' := by
  let X := x + 1
  let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  let q := X / r
  have hz := tsel_passB_block c hc x r hx hr hrs
  have hg := passB_gates_live c hc x r hx hr hrs hrX
  dsimp only at hz hg
  rcases hz with ⟨_hP1, _hP2, _hX, _hInB, _hrBr, hrB⟩
  rcases hg with ⟨hg₁, _hq₂, _hg₂⟩
  change (c.ttouch g₂ q₂ (c.ttouch g₁ z.rB t)).viol = 0 at hclean
  dsimp only [g₁, q₂, g₂, z] at hclean
  rw [hg₁] at hclean
  simp only [_hX, hrB] at hclean
  change PassInv c W (c.ttouch g₂ q₂ (c.ttouch g₁ z.rB t)) _
  dsimp only [g₁, q₂, g₂, z]
  rw [hg₁]
  simp only [_hX, hrB]
  have hrCap : r ≤ c.cap :=
    Nat.le_trans hrs (Nat.le_trans (sqrt_le_self c.cap) (Nat.le_refl _))
  have hXCap : X ≤ c.cap := by dsimp only [X]; omega
  have hqCap : q ≤ c.cap := by
    dsimp only [q]
    exact Nat.le_trans (Nat.div_le_self X r) hXCap
  have hqPos : 1 ≤ q := by
    apply Nat.div_pos (Nat.le_trans hrX (sqrt_le_self (x + 1))) hr
  by_cases hdiv : X % r = 0
  · have hg1one : bnat (X % r = 0) = 1 := bnat_true hdiv
    rw [hg1one, Nat.one_mul] at hclean ⊢
    by_cases heq : q = r
    · have hg2zero : 1 - bnat (q = r) = 0 := by simp [heq, bnat]
      have hg2zero' : 1 - bnat ((x + 1) / r = r) = 0 := by
        simpa only [q, X] using hg2zero
      rw [hg2zero'] at hclean ⊢
      change (c.ttouch 0 q (c.ttouch 1 r t)).viol = 0 at hclean
      have hclean1 : (c.ttouch 1 r t).viol = 0 := by
        have hle := ttouch_viol_le c 0 q (c.ttouch 1 r t)
        omega
      have hi1 := PassInv.touch_live c W t p r hc hrCap (hmu r hr hrCap)
        hinv hclean1
      have hi2 := PassInv.touch_zero c W (c.ttouch 1 r t)
        (LeanCompCert.Ports.Section413Sweep.touch c.rounds W p r) q hi1
      simpa only [X, q, hdiv, if_pos, heq, ne_eq, not_true_eq_false,
        if_false] using hi2
    · have hg2one : 1 - bnat (q = r) = 1 := by simp [heq, bnat]
      have hg2one' : 1 - bnat ((x + 1) / r = r) = 1 := by
        simpa only [q, X] using hg2one
      rw [hg2one'] at hclean ⊢
      change (c.ttouch 1 q (c.ttouch 1 r t)).viol = 0 at hclean
      have hclean1 : (c.ttouch 1 r t).viol = 0 := by
        have hle := ttouch_viol_le c 1 q (c.ttouch 1 r t)
        omega
      have hi1 := PassInv.touch_live c W t p r hc hrCap (hmu r hr hrCap)
        hinv hclean1
      have hmuq : (c.ttouch 1 r t).arr q =
          LeanCompCert.Ports.MertensCDEM.muCode q c.rounds := by
        rw [ttouch_mu_frame c 1 r t q hc (by simpa using hrCap) hqCap]
        exact hmu q hqPos hqCap
      have hi2 := PassInv.touch_live c W (c.ttouch 1 r t)
        (LeanCompCert.Ports.Section413Sweep.touch c.rounds W p r)
        q hc hqCap hmuq hi1 hclean
      simpa only [X, q, hdiv, if_pos, heq, ne_eq, not_false_eq_true]
        using hi2
  · have hg1zero : bnat (X % r = 0) = 0 := bnat_false hdiv
    rw [hg1zero, Nat.zero_mul] at hclean ⊢
    have hi1 := PassInv.touch_zero c W t p r hinv
    have hi2 := PassInv.touch_zero c W (c.ttouch 0 r t) p q hi1
    simpa only [X, q, hdiv, if_false] using hi2

theorem PassInv.passB_round_past_sqrt (c : Cfg) (hc : Admissible c)
    (x r : Nat) (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : Nat.sqrt (x + 1) < r) (hinv : PassInv c W t p) :
    PassInv c W
      (c.tpassB (c.tsel (c.phase1 + x * c.p + (c.s + r))) t) p := by
  let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  have hz := tsel_passB_block c hc x r hx hr hrs
  have hg := passB_gates_past_sqrt c hc x r hx hr hrs hrX
  dsimp only at hz hg
  rcases hz with ⟨_hP1, _hP2, _hX, _hInB, _hrBr, hrB⟩
  rcases hg with ⟨hg₁, _hg₂⟩
  change PassInv c W (c.ttouch g₂ q₂ (c.ttouch g₁ z.rB t)) p
  dsimp only [g₁, q₂, g₂, z]
  rw [hg₁, Nat.zero_mul, hrB]
  exact PassInv.touch_zero c W (c.ttouch 0 r t) p _
    (PassInv.touch_zero c W t p r hinv)

/-- Trial, pass A, and weight are frames on the pass-B persistent fields. -/
theorem passB_pre_frame (c : Cfg) (hc : Admissible c) (x r : Nat)
    (t : TState) (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hzero : t.arr 0 = 0) :
    let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
    let pre := tweight z (tpassA z (ttrial z t))
    PassFrame pre t := by
  let z := c.tsel (c.phase1 + x * c.p + (c.s + r))
  let pre := tweight z (tpassA z (ttrial z t))
  have hpos : c.s + r < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x (c.s + r) hx hpos
  rcases hz with ⟨hP1, _hP2, _hb2, _hx0, _hpX, _hX, _hA, hW, _hrA⟩
  have hW0 : z.isW = 0 := by
    dsimp only [z]
    rw [hW]
    simp [bnat]
    omega
  have hDL : z.isDL = 0 := by
    change bnat (z.r1 = c.rounds - 1) * z.inP1 = 0
    dsimp only [z]
    rw [hP1]
    simp
  have htrialArr : (ttrial z t).arr = t.arr := by
    funext i
    simp only [ttrial, hDL, Nat.zero_mul, Nat.zero_mod]
    by_cases hi : i = 0
    · simp [hi, hzero]
    · simp [hi]
  exact PassFrame.trans (tweight_pass_frame z _ hW0)
    (PassFrame.trans (tpassA_pass_frame z _)
      (ttrial_pass_frame z t htrialArr))

/-- An inactive finalizer frames the pass-B persistent fields. -/
theorem tfin_pass_frame (c : Cfg) (z : TSel) (t : TState)
    (hF : z.isF = 0) (hu64 : PassU64 t) : PassFrame (c.tfin z t) t := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · change tfinDLo z t = t.dLo
    simp [tfinDLo, hF, Nat.mod_eq_of_lt hu64.2.2.2.2.1]
  · change tfinDHi z t = t.dHi
    simp [tfinDHi, hF, Nat.mod_eq_of_lt hu64.2.2.2.2.2.1]

theorem tfin_viol_le (c : Cfg) (z : TSel) (t : TState) :
    t.viol ≤ (c.tfin z t).viol := by
  unfold Cfg.tfin Cfg.tfinViol
  exact Nat.le_trans (tguard_le _ _ _)
    (Nat.le_trans (tguard_le _ _ _)
      (Nat.le_trans Nat.left_le_or Nat.left_le_or))

theorem tfin_DA_frame (c : Cfg) (z : TSel) (t : TState)
    (hF : z.isF = 0) (hcore : CoreU64 t) : DAFrame (c.tfin z t) t := by
  refine ⟨?_, ?_, rfl⟩
  · change tfinDLo z t = t.dLo
    unfold tfinDLo
    simp only [hF, Nat.sub_zero, Nat.mul_one,
      Nat.mod_eq_of_lt hcore.1]
  · change tfinDHi z t = t.dHi
    unfold tfinDHi
    simp only [hF, Nat.sub_zero, Nat.mul_one,
      Nat.mod_eq_of_lt hcore.2.1]

/-- Positions `0 … s` of a candidate (pass A plus the weight round) frame
the accumulator array and delta registers. -/
theorem prePass_step_DA_frame (c : Cfg) (hc : Admissible c) (x pos : Nat)
    (t : TState) (hx : x < c.cap) (hpos : pos ≤ c.s)
    (hzero : t.arr 0 = 0) (hcore : CoreU64 t) :
    DAFrame (c.tstep (c.phase1 + x * c.p + pos) t) t := by
  let idx := c.phase1 + x * c.p + pos
  let z := c.tsel idx
  let trial := ttrial z t
  let pre := tweight z (tpassA z trial)
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  let first := c.ttouch g₁ z.rB pre
  let pb := c.ttouch g₂ q₂ first
  have hposp : pos < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x pos hx hposp
  rcases hz with ⟨hP1, hP2, _hb2, _hx0, hpX, _hX, _hA, _hW, _hrA⟩
  have hDL : z.isDL = 0 := by
    change bnat (z.r1 = c.rounds - 1) * z.inP1 = 0
    dsimp only [z, idx]
    rw [hP1]
    simp
  have hB : z.inB = 0 := by
    change bnat (c.s + 1 ≤ z.pX) * bnat (z.pX ≤ 2 * c.s) * z.inP2 = 0
    dsimp only [z, idx]
    rw [hpX, hP2]
    have hn : ¬ c.s + 1 ≤ pos := by omega
    simp [bnat, hn]
  have hF : z.isF = 0 := by
    change bnat (z.pX = 2 * c.s + 1) * z.inP2 = 0
    dsimp only [z, idx]
    rw [hpX, hP2]
    have hn : pos ≠ 2 * c.s + 1 := by omega
    simp [bnat, hn]
  have htrialArr : trial.arr = t.arr := by
    dsimp only [trial]
    funext i
    simp only [ttrial, hDL, Nat.zero_mul, Nat.zero_mod]
    by_cases hi : i = 0
    · simp [hi, hzero]
    · simp [hi]
  have htrialCore : CoreU64 trial := ttrial_coreU64 z t hcore
  have hpreCore : CoreU64 pre :=
    tweight_coreU64 z _ (tpassA_coreU64 z _ htrialCore)
  have hpreDLo : pre.dLo = t.dLo := rfl
  have hpreDHi : pre.dHi = t.dHi := rfl
  have hpreArr : pre.arr = trial.arr := rfl
  have hpreZero : pre.arr 0 = 0 := by
    change trial.arr 0 = 0
    rw [htrialArr, hzero]
  have hg₁ : g₁ = 0 := by simp [g₁, hB]
  have hg₂ : g₂ = 0 := by simp [g₂, hg₁]
  have hfirst := ttouch_gate_zero c z.rB pre hpreZero
    (hpreCore.2.2 (c.touchA1 0 z.rB))
    (hpreCore.2.2 (c.touchA2 0 z.rB)) hpreCore.1 hpreCore.2.1
  have hfirstCore : CoreU64 first := by
    dsimp only [first]
    exact ttouch_coreU64 c g₁ z.rB pre hpreCore
  have hfirstZero : first.arr 0 = 0 := by
    dsimp only [first]
    rw [hg₁, hfirst.2.2.2, hpreZero]
  have hpb := ttouch_gate_zero c q₂ first hfirstZero
    (hfirstCore.2.2 (c.touchA1 0 q₂))
    (hfirstCore.2.2 (c.touchA2 0 q₂)) hfirstCore.1 hfirstCore.2.1
  have hpbCore : CoreU64 pb := by
    dsimp only [pb]
    exact ttouch_coreU64 c g₂ q₂ first hfirstCore
  have hpbdLo : pb.dLo = t.dLo := by
    dsimp only [pb]
    rw [hg₂, hpb.2.1]
    dsimp only [first]
    rw [hg₁, hfirst.2.1, hpreDLo]
  have hpbdHi : pb.dHi = t.dHi := by
    dsimp only [pb]
    rw [hg₂, hpb.2.2.1]
    dsimp only [first]
    rw [hg₁, hfirst.2.2.1, hpreDHi]
  have hpbArr : pb.arr = t.arr := by
    dsimp only [pb]
    rw [hg₂, hpb.2.2.2]
    dsimp only [first]
    rw [hg₁, hfirst.2.2.2]
    exact hpreArr.trans htrialArr
  exact DAFrame.trans (tfin_DA_frame c z pb hF hpbCore)
    ⟨hpbdLo, hpbdHi, hpbArr⟩

theorem prePass_DA_prefix (c : Cfg) (hc : Admissible c) (x : Nat)
    (hx : x < c.cap)
    (hzero : (tRunUpto c (c.phase1 + x * c.p)).arr 0 = 0) :
    ∀ k, k ≤ c.s + 1 →
      DAFrame (tRunUpto c (c.phase1 + x * c.p + k))
        (tRunUpto c (c.phase1 + x * c.p)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [Nat.add_zero] using
        (show DAFrame (tRunUpto c (c.phase1 + x * c.p))
          (tRunUpto c (c.phase1 + x * c.p)) from ⟨rfl, rfl, rfl⟩)
  | succ k ih =>
      intro hk
      have hkpos : k ≤ c.s := by omega
      have hprev := ih (by omega)
      let start := c.phase1 + x * c.p
      let cur := tRunUpto c (start + k)
      have hcurZero : cur.arr 0 = 0 := by
        have := congrArg (fun a => a 0) hprev.arr
        simpa only [cur, start] using this.trans hzero
      have hstep := prePass_step_DA_frame c hc x k cur hx hkpos hcurZero
        (tRunUpto_coreU64 c (start + k))
      rw [show start + (k + 1) = (start + k) + 1 by omega, tRunUpto_succ]
      have hidx : start + k = c.phase1 + x * c.p + k := by
        dsimp only [start]
      rw [hidx]
      exact DAFrame.trans hstep hprev

/-- The full scheduled transition at `s+r` realizes one reference divisor
round; the surrounding transparent stages and inactive finalizer are frames. -/
theorem PassInv.tstep_passB_round (c : Cfg) (hc : Admissible c) (x r : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : r ≤ Nat.sqrt (x + 1))
    (hmu : ∀ d, 1 ≤ d → d ≤ c.cap →
      t.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds)
    (hinv : PassInv c W t p)
    (hclean : (c.tstep (c.phase1 + x * c.p + (c.s + r)) t).viol = 0) :
    let X := x + 1
    let q := X / r
    let p' := if X % r = 0 then
        let p1 := LeanCompCert.Ports.Section413Sweep.touch c.rounds W p r
        if q ≠ r then
          LeanCompCert.Ports.Section413Sweep.touch c.rounds W p1 q
        else p1
      else p
    PassInv c W (c.tstep (c.phase1 + x * c.p + (c.s + r)) t) p' := by
  let idx := c.phase1 + x * c.p + (c.s + r)
  let z := c.tsel idx
  let pre := tweight z (tpassA z (ttrial z t))
  let pb := c.tpassB z pre
  have hfpre : PassFrame pre t := by
    simpa only [idx, z, pre] using passB_pre_frame c hc x r t hx hr hrs hinv.arr_zero
  have hipre : PassInv c W pre p := PassInv.of_frame hinv hfpre
  have hmupre : ∀ d, 1 ≤ d → d ≤ c.cap →
      pre.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds := by
    intro d hdpos hd
    rw [hfpre.arr]
    exact hmu d hdpos hd
  have hpbclean : pb.viol = 0 := by
    change (c.tfin z pb).viol = 0 at hclean
    have hle := tfin_viol_le c z pb
    omega
  have hipb :
      let X := x + 1
      let q := X / r
      let p' := if X % r = 0 then
          let p1 := LeanCompCert.Ports.Section413Sweep.touch c.rounds W p r
          if q ≠ r then
            LeanCompCert.Ports.Section413Sweep.touch c.rounds W p1 q
          else p1
        else p
      PassInv c W pb p' := by
    simpa only [idx, z, pre, pb] using
      PassInv.passB_round c hc x r W pre p hx hr hrs hrX hmupre hipre hpbclean
  have hpos : c.s + r < c.p := by unfold Cfg.p; omega
  have hzsel := tsel_phase2_block c hc x (c.s + r) hx hpos
  have hF : z.isF = 0 := by
    rcases hzsel with ⟨_hP1, hP2, _hb2, _hx0, hpX, _hX, _hA, _hW, _hrA⟩
    change bnat (z.pX = 2 * c.s + 1) * z.inP2 = 0
    dsimp only [z, idx]
    rw [hpX, hP2]
    simp [bnat]
    omega
  have hfpost : PassFrame (c.tfin z pb) pb := tfin_pass_frame c z pb hF hipb.u64
  change PassInv c W (c.tfin z pb) _
  exact PassInv.of_frame hipb hfpost

theorem PassInv.tstep_passB_past_sqrt (c : Cfg) (hc : Admissible c)
    (x r : Nat) (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hx : x < c.cap) (hr : 1 ≤ r) (hrs : r ≤ c.s)
    (hrX : Nat.sqrt (x + 1) < r) (hinv : PassInv c W t p) :
    PassInv c W (c.tstep (c.phase1 + x * c.p + (c.s + r)) t) p := by
  let idx := c.phase1 + x * c.p + (c.s + r)
  let z := c.tsel idx
  let pre := tweight z (tpassA z (ttrial z t))
  let pb := c.tpassB z pre
  have hfpre : PassFrame pre t := by
    simpa only [idx, z, pre] using passB_pre_frame c hc x r t hx hr hrs hinv.arr_zero
  have hipre : PassInv c W pre p := PassInv.of_frame hinv hfpre
  have hipb : PassInv c W pb p := by
    simpa only [idx, z, pre, pb] using
      PassInv.passB_round_past_sqrt c hc x r W pre p hx hr hrs hrX hipre
  have hpos : c.s + r < c.p := by unfold Cfg.p; omega
  have hzsel := tsel_phase2_block c hc x (c.s + r) hx hpos
  have hF : z.isF = 0 := by
    rcases hzsel with ⟨_hP1, hP2, _hb2, _hx0, hpX, _hX, _hA, _hW, _hrA⟩
    change bnat (z.pX = 2 * c.s + 1) * z.inP2 = 0
    dsimp only [z, idx]
    rw [hpX, hP2]
    simp [bnat]
    omega
  have hfpost : PassFrame (c.tfin z pb) pb := tfin_pass_frame c z pb hF hipb.u64
  change PassInv c W (c.tfin z pb) p
  exact PassInv.of_frame hipb hfpost

/-- The reference divisor-pair fold truncated to its first `k` rounds. -/
def divisorPrefix (R X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (k : Nat)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell) :
    Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell :=
  (List.range k).foldl
    (fun p i =>
      let r := i + 1
      if X % r = 0 then
        let p1 := LeanCompCert.Ports.Section413Sweep.touch R W p r
        if X / r ≠ r then
          LeanCompCert.Ports.Section413Sweep.touch R W p1 (X / r)
        else p1
      else p) p

theorem divisorPrefix_zero (R X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell) :
    divisorPrefix R X W 0 p = p := rfl

theorem divisorPrefix_succ (R X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (k : Nat)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell) :
    divisorPrefix R X W (k + 1) p =
      let q := X / (k + 1)
      let p0 := divisorPrefix R X W k p
      if X % (k + 1) = 0 then
        let p1 := LeanCompCert.Ports.Section413Sweep.touch R W p0 (k + 1)
        if q ≠ k + 1 then
          LeanCompCert.Ports.Section413Sweep.touch R W p1 q
        else p1
      else p0 := by
  unfold divisorPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem divisorPrefix_sqrt (R X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell) :
    divisorPrefix R X W (Nat.sqrt X) p =
      LeanCompCert.Ports.Section413Sweep.stepDivisors R X W p := rfl

/-- Every phase-2 transition frames the μ plane.  The pass-B address bounds
come from the already-proved selector/gate range theorem used by machine
denotation; `ttouch_pair_mu_frame` then discharges both array writes. -/
theorem tstep_phase2_mu_frame (c : Cfg) (hc : Admissible c) (idx : Nat)
    (t : TState) (n : Nat) (hn : 1 ≤ n) (hnc : n ≤ c.cap)
    (hphase : c.phase1 ≤ idx) (hidx : idx < c.loopCount) :
    (c.tstep idx t).arr n = t.arr n := by
  let z := c.tsel idx
  let u := tweight z (tpassA z (ttrial z t))
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  have hP1 : z.inP1 = 0 := by
    simp [z, Cfg.tsel, bnat, Nat.not_lt_of_ge hphase]
  have hDL : z.isDL = 0 := by
    change bnat (z.r1 = c.rounds - 1) * z.inP1 = 0
    rw [hP1]
    simp
  have htrial : (ttrial z t).arr n = t.arr n := by
    unfold ttrial
    simp [hDL, Nat.ne_of_gt hn]
  have hp := LeanCompCert.Ports.Section413G2Denote.Admissible.passBProducts
    c hc.toDenote idx hidx
  dsimp only at hp
  change (c.ttouch g₂ q₂ (c.ttouch g₁ z.rB u)).arr n = t.arr n
  rw [ttouch_pair_mu_frame c g₁ z.rB g₂ q₂ u n hc hp.1 hp.2 hnc]
  exact htrial

/-- The phase-boundary μ plane remains intact throughout phase 2. -/
theorem phase2_muCode (c : Cfg) (hc : Admissible c) (n : Nat)
    (hn : 1 ≤ n) (hnc : n ≤ c.cap) : ∀ k, k ≤ c.cap * c.p →
    (tRunUpto c (c.phase1 + k)).arr n =
      LeanCompCert.Ports.MertensCDEM.muCode n c.rounds := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [Nat.add_zero] using phase1_muCode_final_ge_one c hc n hn hnc
  | succ k ih =>
      intro hk
      have hklt : k < c.cap * c.p := by omega
      have hidx : c.phase1 + k < c.loopCount := by
        unfold Cfg.loopCount
        omega
      rw [show c.phase1 + (k + 1) = (c.phase1 + k) + 1 by omega,
        tRunUpto_succ,
        tstep_phase2_mu_frame c hc (c.phase1 + k) (tRunUpto c (c.phase1 + k))
          n (by omega) hnc (by omega) hidx]
      exact ih (by omega)

/-- The scheduled machine prefixes simulate every prefix of the reference
divisor fold. -/
theorem passB_prefix (c : Cfg) (hc : Admissible c) (X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hbase : PassInv c W
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)) p) :
    ∀ k, k ≤ Nat.sqrt X →
      PassInv c W
        (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1 + k))
        (divisorPrefix c.rounds X W k p) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [Nat.add_zero, divisorPrefix_zero] using hbase
  | succ k ih =>
      intro hk
      have hkroot : k + 1 ≤ Nat.sqrt X := by simpa using hk
      have hkprev : k ≤ Nat.sqrt X := by omega
      have hprev := ih hkprev
      let base := c.phase1 + (X - 1) * c.p + c.s + 1
      let off := (X - 1) * c.p + c.s + 1 + k
      let idx := c.phase1 + off
      let cur := tRunUpto c (base + k)
      have hsCover : Nat.sqrt X ≤ c.s := sqrt_le_cfg_s c hXc
      have hwithin : c.s + 1 + k < c.p := by
        unfold Cfg.p
        omega
      have hXp : X * c.p ≤ c.cap * c.p := Nat.mul_le_mul_right c.p hXc
      have hsplit : (X - 1) * c.p + c.p = X * c.p := by
        have hsucc : X - 1 + 1 = X := by omega
        calc
          (X - 1) * c.p + c.p = ((X - 1) + 1) * c.p := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = X * c.p := by rw [hsucc]
      have hoff : off < c.cap * c.p := by
        dsimp only [off]
        omega
      have hidx : idx < c.loopCount := by
        dsimp only [idx]
        unfold Cfg.loopCount
        omega
      have htime : idx = base + k := by
        dsimp only [idx, off, base]
        omega
      have htime' : c.phase1 + off = base + k := by
        simpa only [idx] using htime
      have hmu : ∀ d, 1 ≤ d → d ≤ c.cap →
          cur.arr d = LeanCompCert.Ports.MertensCDEM.muCode d c.rounds := by
        intro d hdpos hdc
        have hm := phase2_muCode c hc d hdpos hdc off (Nat.le_of_lt hoff)
        rw [htime'] at hm
        exact hm
      have hclean := (tstep_clean_of_tFlag c hflag hidx).2
      have hsched :
          c.phase1 + (X - 1) * c.p + (c.s + (k + 1)) = idx := by
        dsimp only [idx, off]
        omega
      have hclean' :
          (c.tstep (c.phase1 + (X - 1) * c.p + (c.s + (k + 1))) cur).viol = 0 := by
        rw [hsched]
        simpa only [cur, htime] using hclean
      have hxone : X - 1 + 1 = X := by omega
      have hroot' : k + 1 ≤ Nat.sqrt (X - 1 + 1) := by
        rw [hxone]
        exact hkroot
      have hround := PassInv.tstep_passB_round c hc (X - 1) (k + 1)
        W cur (divisorPrefix c.rounds X W k p)
        (by omega) (by omega) (by omega) hroot'
        hmu (by simpa only [cur, base, Nat.add_assoc] using hprev) hclean'
      have hstepIndex :
          c.phase1 + (X - 1) * c.p + (c.s + (k + 1)) =
            c.phase1 + (X - 1) * c.p + (c.s + (1 + k)) := by omega
      rw [hstepIndex] at hround
      rw [show base + (k + 1) = (base + k) + 1 by omega, tRunUpto_succ,
        divisorPrefix_succ]
      simpa only [cur, base, Nat.add_assoc, hxone] using hround

theorem passB_tail (c : Cfg) (hc : Admissible c) (X : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hstart : PassInv c W
      (tRunUpto c
        (c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X)) p) :
    ∀ d, Nat.sqrt X + d ≤ c.s →
      PassInv c W
        (tRunUpto c
          (c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X + d)) p := by
  intro d
  induction d with
  | zero =>
      intro _
      simpa only [Nat.add_zero] using hstart
  | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      let base := c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X
      let cur := tRunUpto c (base + d)
      let r := Nat.sqrt X + d + 1
      have hr : 1 ≤ r := by dsimp only [r]; omega
      have hrs : r ≤ c.s := by dsimp only [r]; omega
      have hrX : Nat.sqrt (X - 1 + 1) < r := by
        have hxone : X - 1 + 1 = X := by omega
        rw [hxone]
        dsimp only [r]
        omega
      have hstep := PassInv.tstep_passB_past_sqrt c hc (X - 1) r W cur p
        (by omega) hr hrs hrX
        (by simpa only [cur, base, Nat.add_assoc] using hprev)
      have hidx :
          c.phase1 + (X - 1) * c.p + (c.s + r) = base + d := by
        dsimp only [r, base]
        omega
      change PassInv c W (tRunUpto c (base + (d + 1))) p
      have hrun : tRunUpto c (base + (d + 1)) =
          c.tstep (c.phase1 + (X - 1) * c.p + (c.s + r)) cur := by
        rw [show base + (d + 1) = (base + d) + 1 by omega, tRunUpto_succ]
        rw [hidx]
      rw [hrun]
      exact hstep

theorem tstep_sigma (c : Cfg) (idx : Nat) (t : TState) :
    (c.tstep idx t).sigma =
      (tpassA (c.tsel idx) (ttrial (c.tsel idx) t)).sigma := rfl

theorem tstep_sigma_of_inP2_zero (c : Cfg) (idx : Nat) (t : TState)
    (hP2 : (c.tsel idx).inP2 = 0) (ht : t.sigma < M) :
    (c.tstep idx t).sigma = t.sigma := by
  have hA : (c.tsel idx).inA = 0 := by
    change bnat ((c.tsel idx).pX < c.s) * (c.tsel idx).inP2 = 0
    rw [hP2]
    simp
  rw [tstep_sigma]
  unfold tpassA ttrial
  simp [hP2, hA, Nat.mod_eq_of_lt ht]

theorem tstep_sigma_lt (c : Cfg) (idx : Nat) (t : TState) :
    (c.tstep idx t).sigma < M := by
  rw [tstep_sigma]
  unfold tpassA
  exact Nat.mod_lt _ (by decide)

theorem tRunUpto_sigma_lt (c : Cfg) (k : Nat) :
    (tRunUpto c k).sigma < M := by
  cases k with
  | zero => simp [tRunUpto, tInit, M_val]
  | succ k =>
      rw [tRunUpto_succ]
      exact tstep_sigma_lt c k _

/-- Phase 1 never touches the sigma register. -/
theorem phase1_sigma_zero (c : Cfg) : ∀ k, k ≤ c.phase1 →
    (tRunUpto c k).sigma = 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hlt : k < c.phase1 := by omega
      rw [show k + 1 = Nat.succ k by rfl, tRunUpto_succ,
        tstep_sigma_of_inP2_zero]
      · exact ih (by omega)
      · simp [Cfg.tsel, hlt, bnat]
      · exact tRunUpto_sigma_lt c k

/-- A live pass-A machine round is one exact `sigmaStep`.  The hypothesis is
phrased after the candidate-start reset, so it also covers position zero. -/
theorem tpassA_phase2_sigma (c : Cfg) (hc : Admissible c) (x pos : Nat)
    (t : TState) (hx : x < c.cap) (hpos : pos < c.s)
    (hsigma : (if pos = 0 then 0 else t.sigma) = sigmaScan (x + 1) pos) :
    (tpassA (c.tsel (c.phase1 + x * c.p + pos)) t).sigma =
      sigmaScan (x + 1) (pos + 1) := by
  have hsp : c.s < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x pos hx (Nat.lt_trans hpos hsp)
  dsimp only at hz
  rcases hz with ⟨hP1, hP2, hb2, hx0, hpX, hX, hA, hW, hrA⟩
  have hXc : x + 1 ≤ c.cap := by omega
  have hsCap : c.s ≤ c.cap := sqrt_le_self c.cap
  have hrCap : pos + 1 ≤ c.cap := by omega
  have hcapTermM : c.cap * (2 * c.cap + 2) < M := by
    have := hc.loop_fits
    omega
  have hcapSqM : c.cap * c.cap < M := by
    have hle : c.cap * c.cap ≤ c.cap * (2 * c.cap + 2) :=
      Nat.mul_le_mul_left c.cap (by omega)
    exact Nat.lt_of_le_of_lt hle hcapTermM
  have hsqM : (pos + 1) * (pos + 1) < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hrCap hrCap) hcapSqM
  have hq : (x + 1) / (pos + 1) ≤ x + 1 :=
    Nat.div_le_self (x + 1) (pos + 1)
  have hpairM : pos + 1 + (x + 1) / (pos + 1) < M := by
    have htwoCap : 2 * c.cap + 2 ≤ c.cap * (2 * c.cap + 2) := by
      have hcap1 : 1 ≤ c.cap := hc.cap_pos
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (2 * c.cap + 2) hcap1
    have hsmall : pos + 1 + (x + 1) / (pos + 1) ≤ 2 * c.cap := by omega
    exact Nat.lt_of_le_of_lt hsmall
      (Nat.lt_of_le_of_lt (by omega) hcapTermM)
  have hcurM : sigmaScan (x + 1) pos < M := by
    have hb := sigmaScan_le (x + 1) pos
    have hmul : pos * (2 * (x + 1)) ≤ c.cap * (2 * c.cap + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hb hmul) hcapTermM
  have hnextM : sigmaScan (x + 1) (pos + 1) < M := by
    have hb := sigmaScan_le (x + 1) (pos + 1)
    have hmul : (pos + 1) * (2 * (x + 1)) ≤
        c.cap * (2 * c.cap + 2) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hb hmul) hcapTermM
  have hstepM : sigmaStep (x + 1) (pos + 1) (sigmaScan (x + 1) pos) < M := by
    rw [← sigmaScan_succ]
    exact hnextM
  rw [sigmaScan_succ]
  unfold tpassA
  simp only [hpX, hP2, hX, hA, hrA, Nat.mul_one]
  have hreset : (if bnat (pos = 0) = 1 then 0 else t.sigma) =
      sigmaScan (x + 1) pos := by
    by_cases hp0 : pos = 0 <;> simp [bnat, hp0] at hsigma ⊢ <;> exact hsigma
  rw [hreset]
  simp only [bnat_true hpos, Nat.mul_one]
  have hsqMod : (pos + 1) * (pos + 1) % M = (pos + 1) * (pos + 1) :=
    Nat.mod_eq_of_lt hsqM
  rw [hsqMod]
  by_cases hdiv : (x + 1) % (pos + 1) = 0
  · by_cases hsquare : (pos + 1) * (pos + 1) ≤ x + 1
    · by_cases hdiag : (x + 1) / (pos + 1) = pos + 1
      · have hm := hstepM
        simp [sigmaStep, hdiv, hsquare, hdiag] at hm
        simp [sigmaStep, bnat, hdiv, hsquare, hdiag,
          Nat.mod_eq_of_lt (by omega : pos + 1 < M), Nat.mod_eq_of_lt hm]
      · have hm := hstepM
        simp [sigmaStep, hdiv, hsquare, hdiag] at hm
        have hm' : sigmaScan (x + 1) pos +
            (pos + 1 + (x + 1) / (pos + 1)) < M := by omega
        simp [sigmaStep, bnat, hdiv, hsquare, hdiag,
          Nat.mod_eq_of_lt hpairM, Nat.mod_eq_of_lt hm']
        omega
    · simp [sigmaStep, bnat, hdiv, hsquare, Nat.mod_eq_of_lt hcurM]
  · simp [sigmaStep, bnat, hdiv, Nat.mod_eq_of_lt hcurM]

/-- After `k>0` pass-A rounds for candidate `x+1`, the sigma register is
the corresponding guarded mathematical prefix.  Position zero needs no
incoming invariant because the machine resets sigma there. -/
theorem phase2_sigma_prefix (c : Cfg) (hc : Admissible c) (x : Nat)
    (hx : x < c.cap) : ∀ k, 0 < k → k ≤ c.s →
    (tRunUpto c (c.phase1 + x * c.p + k)).sigma = sigmaScan (x + 1) k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ pos ih =>
      intro _ hks
      have hpos : pos < c.s := by omega
      let idx := c.phase1 + x * c.p + pos
      have htime : c.phase1 + x * c.p + (pos + 1) = idx + 1 := by
        dsimp only [idx]
        omega
      rw [htime, tRunUpto_succ, tstep_sigma]
      apply tpassA_phase2_sigma c hc x pos
        (ttrial (c.tsel idx) (tRunUpto c idx)) hx hpos
      by_cases hp0 : pos = 0
      · simp [hp0, sigmaScan]
      · simp only [hp0, ↓reduceIte]
        change (tRunUpto c idx).sigma = sigmaScan (x + 1) pos
        simpa only [idx] using ih (Nat.pos_of_ne_zero hp0) (by omega)

/-- Pass A computes the reference divisor-pair sum for every live
candidate. -/
theorem passA_sigma (c : Cfg) (hc : Admissible c) (X : Nat)
    (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s)).sigma =
      LeanCompCert.Ports.Section413Sweep.sigmaPair X := by
  have hsPos : 0 < c.s := by
    unfold Cfg.s
    apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
    apply LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le
    simpa using Nat.le_trans hX hXc
  have hx : X - 1 < c.cap := by omega
  have hp := phase2_sigma_prefix c hc (X - 1) hx c.s hsPos (Nat.le_refl _)
  have hXeq : X - 1 + 1 = X := by omega
  rw [hXeq] at hp
  exact hp.trans (sigmaScan_cfg_s c X hXc)

/-- The complete loop transition at phase-2 position `s` writes the reference
weight endpoints.  The μ-plane and sigma premises are the two preceding
simulation components, kept explicit for composition. -/
theorem tstep_weight_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (t : TState) (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hmu : t.arr X = LeanCompCert.Ports.MertensCDEM.muCode X c.rounds)
    (hsigma : t.sigma = LeanCompCert.Ports.Section413Sweep.sigmaPair X) :
    let idx := c.phase1 + (X - 1) * c.p + c.s
    (⟨decodeZ (c.tstep idx t).wLo, decodeZ (c.tstep idx t).wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X := by
  let x := X - 1
  let idx := c.phase1 + x * c.p + c.s
  let z := c.tsel idx
  let u := tpassA z (ttrial z t)
  have hx : x < c.cap := by dsimp only [x]; omega
  have hsp : c.s < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x c.s hx hsp
  dsimp only at hz
  rcases hz with ⟨hP1, hP2, hb2, hx0, hpX, hzX, hA, hW, hrA⟩
  have hxX : x + 1 = X := by dsimp only [x]; omega
  have hzX' : z.X = X := hzX.trans hxX
  have hW' : z.isW = 1 := by simpa [bnat] using hW
  have hA' : z.inA = 0 := by simpa [bnat] using hA
  have hpX' : z.pX = c.s := hpX
  have hP2' : z.inP2 = 1 := hP2
  have hDL : z.isDL = 0 := by
    change bnat ((idx % c.rounds) = c.rounds - 1) * z.inP1 = 0
    rw [hP1]
    simp
  have huArr : u.arr X = t.arr X := by
    unfold u tpassA ttrial
    simp [hDL, Nat.ne_of_gt hX]
  have hcapM : c.cap < M := by
    have := hc.arr_fits
    simp only [M_val] at this ⊢
    omega
  have hXM : X < M := Nat.lt_of_le_of_lt hXc hcapM
  have hsigPos := sigmaPair_pos X hX
  have hsigBound :
      LeanCompCert.Ports.Section413Sweep.sigmaPair X ≤
        c.cap * (2 * c.cap + 2) := by
    rw [← sigmaScan_cfg_s c X hXc]
    have hb := sigmaScan_le X c.s
    have hsCap := sqrt_le_self c.cap
    exact Nat.le_trans hb (Nat.mul_le_mul hsCap (by omega))
  have hsigAddM :
      LeanCompCert.Ports.Section413Sweep.sigmaPair X + SCALE < M :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right hsigBound SCALE) hc.weight_fits
  have htSigmaM : t.sigma < M := by rw [hsigma]; omega
  have hsPos : 0 < c.s := by
    unfold Cfg.s
    apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
    apply LeanCompCert.Verified.SqrtEquiv.le_sqrt_of_sq_le
    simpa using Nat.le_trans hX hXc
  have huSigma : u.sigma = t.sigma := by
    unfold u tpassA ttrial
    simp [hA', hP2', hpX', Nat.ne_of_gt hsPos, bnat,
      Nat.mod_eq_of_lt htSigmaM]
  change (⟨decodeZ (tweight z u).wLo, decodeZ (tweight z u).wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) = _
  apply tweight_live_weight c.rounds X
    (LeanCompCert.Ports.Section413Sweep.sigmaPair X)
    (LeanCompCert.Ports.MertensCDEM.muCode X c.rounds) z u
    hW' hzX' hXM
  · exact huArr.trans hmu
  · rfl
  · exact huSigma.trans hsigma
  · rfl
  · exact hsigPos
  · exact hsigAddM

/-- At a live weight position, a clean complete iteration frames the exact
square written by `tweight` through the two pass-B touches and finalizer. -/
theorem tstep_weight_square (c : Cfg) (idx : Nat) (t : TState)
    (hW : (c.tsel idx).isW = 1) (hclean : (c.tstep idx t).viol = 0) :
    (⟨decodeZ (c.tstep idx t).wwLo, decodeZ (c.tstep idx t).wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ (c.tstep idx t).wLo, decodeZ (c.tstep idx t).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ (c.tstep idx t).wLo, decodeZ (c.tstep idx t).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell) := by
  let z := c.tsel idx
  let u := tpassA z (ttrial z t)
  have hwClean : (tweight z u).viol = 0 := by
    have hle : (tweight z u).viol ≤ (c.tstep idx t).viol := by
      simpa only [z, u] using tweight_viol_le_tstep c idx t
    rw [hclean] at hle
    omega
  have hsquare := tweight_live_square z u (by simpa only [z] using hW) hwClean
  change
    (⟨decodeZ (tweight z u).wwLo, decodeZ (tweight z u).wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ (tweight z u).wLo, decodeZ (tweight z u).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ (tweight z u).wLo, decodeZ (tweight z u).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
  exact hsquare

/-- A clean live weight iteration establishes and preserves the raw pass-B
word invariant through its inactive touches and finalizer. -/
theorem tstep_weight_passU64 (c : Cfg) (idx : Nat) (t : TState)
    (hW : (c.tsel idx).isW = 1) (hcore : CoreU64 t)
    (hclean : (c.tstep idx t).viol = 0) : PassU64 (c.tstep idx t) := by
  let z := c.tsel idx
  let u := tpassA z (ttrial z t)
  have huCore : CoreU64 u :=
    tpassA_coreU64 z _ (ttrial_coreU64 z t hcore)
  have hwClean : (tweight z u).viol = 0 := by
    have hle : (tweight z u).viol ≤ (c.tstep idx t).viol := by
      simpa only [z, u] using tweight_viol_le_tstep c idx t
    rw [hclean] at hle
    omega
  have hw := tweight_passU64 z u (by simpa only [z] using hW)
    huCore.1 huCore.2.1 huCore.2.2 hwClean
  change PassU64 (c.tfin z (c.tpassB z (tweight z u)))
  exact tfin_passU64 c z _ (tpassB_passU64 c z _ hw)

/-- The scheduled weight round in the transparent run computes `weightV2`.
The preceding μ and sigma theorems supply the two explicit premises of
`tstep_weight_spec`. -/
theorem weight_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    let idx := c.phase1 + (X - 1) * c.p + c.s
    (⟨decodeZ (tRunUpto c (idx + 1)).wLo,
      decodeZ (tRunUpto c (idx + 1)).wHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X := by
  let k := (X - 1) * c.p + c.s
  let idx := c.phase1 + (X - 1) * c.p + c.s
  have hsp : c.s < c.p := by unfold Cfg.p; omega
  have hk : k ≤ c.cap * c.p := by
    have hXp : X * c.p ≤ c.cap * c.p := Nat.mul_le_mul_right c.p hXc
    dsimp only [k]
    have hsplit : (X - 1) * c.p + c.p = X * c.p := by
      have : X - 1 + 1 = X := by omega
      calc
        (X - 1) * c.p + c.p = ((X - 1) + 1) * c.p := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = X * c.p := by rw [this]
    omega
  have hmu := phase2_muCode c hc X hX hXc k hk
  have hsigma := passA_sigma c hc X hX hXc
  dsimp only
  rw [tRunUpto_succ]
  apply tstep_weight_spec c hc X (tRunUpto c idx) hX hXc
  · simpa only [idx, k, Nat.add_assoc] using hmu
  · simpa only [idx, Nat.add_assoc] using hsigma

/-- The scheduled weight round records the exact square throughout a clean
run.  This is the pass-B invariant at its induction base. -/
theorem weight_square_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    let idx := c.phase1 + (X - 1) * c.p + c.s
    (⟨decodeZ (tRunUpto c (idx + 1)).wwLo,
      decodeZ (tRunUpto c (idx + 1)).wwHi⟩ :
      LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul
        (⟨decodeZ (tRunUpto c (idx + 1)).wLo,
          decodeZ (tRunUpto c (idx + 1)).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell)
        (⟨decodeZ (tRunUpto c (idx + 1)).wLo,
          decodeZ (tRunUpto c (idx + 1)).wHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell) := by
  let x := X - 1
  let idx := c.phase1 + x * c.p + c.s
  have hx : x < c.cap := by dsimp only [x]; omega
  have hsp : c.s < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x c.s hx hsp
  have hW : (c.tsel idx).isW = 1 := by
    dsimp only [idx]
    simpa only [bnat_true] using hz.2.2.2.2.2.2.2.1
  have hidx : idx < c.loopCount := by
    have hx1 : x + 1 ≤ c.cap := by omega
    have hmul := Nat.mul_le_mul_right c.p hx1
    rw [Nat.add_mul, Nat.one_mul] at hmul
    have htail : x * c.p + c.s < c.cap * c.p := by omega
    simpa only [idx, Cfg.loopCount, Nat.add_assoc] using
      Nat.add_lt_add_left htail c.phase1
  have hclean := (tstep_clean_of_tFlag c hflag hidx).2
  dsimp only
  rw [tRunUpto_succ]
  exact tstep_weight_square c idx (tRunUpto c idx) hW hclean

/-- Raw word bounds at the scheduled pass-B entry. -/
theorem weight_passU64_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    let idx := c.phase1 + (X - 1) * c.p + c.s
    PassU64 (tRunUpto c (idx + 1)) := by
  let x := X - 1
  let idx := c.phase1 + x * c.p + c.s
  have hx : x < c.cap := by dsimp only [x]; omega
  have hsp : c.s < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x c.s hx hsp
  have hW : (c.tsel idx).isW = 1 := by
    dsimp only [idx]
    simpa only [bnat_true] using hz.2.2.2.2.2.2.2.1
  have hx1 : x + 1 ≤ c.cap := by omega
  have hmul := Nat.mul_le_mul_right c.p hx1
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have htail : x * c.p + c.s < c.cap * c.p := by omega
  have hidx : idx < c.loopCount := by
    simpa only [idx, Cfg.loopCount, Nat.add_assoc] using
      Nat.add_lt_add_left htail c.phase1
  have hclean := (tstep_clean_of_tFlag c hflag hidx).2
  dsimp only
  rw [tRunUpto_succ]
  exact tstep_weight_passU64 c idx (tRunUpto c idx) hW
    (tRunUpto_coreU64 c idx) hclean

/-- The exact scheduled square is capped.  This is the last arithmetic
component needed by `ttouch_live_spec` at the first divisor round. -/
theorem weight_square_capped_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    let idx := c.phase1 + (X - 1) * c.p + c.s
    Capped (tRunUpto c (idx + 1)).wwLo ∧
      Capped (tRunUpto c (idx + 1)).wwHi := by
  let idx := c.phase1 + (X - 1) * c.p + c.s
  let st := tRunUpto c (idx + 1)
  let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
  have hw :
      (⟨decodeZ st.wLo, decodeZ st.wHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) = W := by
    simpa only [idx, st, W] using weight_spec c hc X hX hXc
  have hsquare :
      (⟨decodeZ st.wwLo, decodeZ st.wwHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) =
      LeanCompCert.Ports.Section413Sweep.cmul W W := by
    have hs := weight_square_spec c hc X hflag hX hXc
    dsimp only at hs
    rw [hw] at hs
    simpa only [idx, st, W] using hs
  have hWcap := weightV2_natAbs_le_scale c.rounds X hX
  have hrange := cmul_scale_range W W hWcap.1 hWcap.2 hWcap.1 hWcap.2
  have hlo := congrArg (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.lo)
    hsquare
  have hhi := congrArg (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.hi)
    hsquare
  change decodeZ st.wwLo = (LeanCompCert.Ports.Section413Sweep.cmul W W).lo at hlo
  change decodeZ st.wwHi = (LeanCompCert.Ports.Section413Sweep.cmul W W).hi at hhi
  change Capped st.wwLo ∧ Capped st.wwHi
  constructor
  · apply capped_of_range
    · rw [hlo]
      exact hrange.1.1
    · rw [hlo]
      exact hrange.1.2
  · apply capped_of_range
    · rw [hhi]
      exact hrange.2.1
    · rw [hhi]
      exact hrange.2.2

/-- **Pass B is one `stepDivisors` block**, under the explicit incoming
accumulator relation and zero-delta reset supplied by the outer sweep
induction. -/
theorem passB_stepDivisors (c : Cfg) (hc : Admissible c) (X : Nat)
    (A : Array LeanCompCert.Ports.Section413Sweep.Cell)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hzero :
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)).arr 0 = 0)
    (hacc : AccRel c
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)) A)
    (hdelta : deltaAt
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)) =
        LeanCompCert.Ports.Section413Sweep.czero) :
    let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
    PassInv c W
      (tRunUpto c
        (c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X))
      (LeanCompCert.Ports.Section413Sweep.stepDivisors c.rounds X W
        (A, LeanCompCert.Ports.Section413Sweep.czero)) := by
  let base := c.phase1 + (X - 1) * c.p + c.s + 1
  let st := tRunUpto c base
  let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
  have hu64 : PassU64 st := by
    simpa only [base, st, Nat.add_assoc] using
      weight_passU64_spec c hc X hflag hX hXc
  have hww := weight_square_capped_spec c hc X hflag hX hXc
  dsimp only at hww
  have hw : weightAt st = W := by
    simpa only [weightAt, base, st, W, Nat.add_assoc] using
      weight_spec c hc X hX hXc
  have hsquare : squareAt st =
      LeanCompCert.Ports.Section413Sweep.cmul W W := by
    have hs := weight_square_spec c hc X hflag hX hXc
    dsimp only at hs
    have hs' : squareAt st = LeanCompCert.Ports.Section413Sweep.cmul
        (weightAt st) (weightAt st) := by
      simpa only [squareAt, weightAt, base, st, Nat.add_assoc] using hs
    rw [hw] at hs'
    exact hs'
  have hdLo0 : decodeZ st.dLo = 0 := by
    have hd := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.lo) hdelta
    simpa only [deltaAt, base, st,
      LeanCompCert.Ports.Section413Sweep.czero] using hd
  have hdHi0 : decodeZ st.dHi = 0 := by
    have hd := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.hi) hdelta
    simpa only [deltaAt, base, st,
      LeanCompCert.Ports.Section413Sweep.czero] using hd
  have cdLo : Capped st.dLo := by
    unfold Capped
    rw [hdLo0]
    simp
  have cdHi : Capped st.dHi := by
    unfold Capped
    rw [hdHi0]
    simp
  have hbase : PassInv c W st
      (A, LeanCompCert.Ports.Section413Sweep.czero) :=
    ⟨hu64, by simpa only [base, st] using hzero,
      by simpa only [base, st] using hww.1,
      by simpa only [base, st] using hww.2,
      cdLo, cdHi, hw, hsquare,
      by simpa only [base, st] using hacc,
      by simpa only [base, st] using hdelta⟩
  have hp := passB_prefix c hc X W
    (A, LeanCompCert.Ports.Section413Sweep.czero)
    hflag hX hXc hbase (Nat.sqrt X) (Nat.le_refl _)
  rw [divisorPrefix_sqrt] at hp
  simpa only [base, st, W, Nat.add_assoc] using hp

/-- The remaining configured slots past `√X` are no-ops, so the state just
before finalization still denotes the same `stepDivisors` result. -/
theorem passB_full (c : Cfg) (hc : Admissible c) (X : Nat)
    (A : Array LeanCompCert.Ports.Section413Sweep.Cell)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hzero :
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)).arr 0 = 0)
    (hacc : AccRel c
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)) A)
    (hdelta : deltaAt
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1)) =
        LeanCompCert.Ports.Section413Sweep.czero) :
    let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
    PassInv c W
      (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s + 1 + c.s))
      (LeanCompCert.Ports.Section413Sweep.stepDivisors c.rounds X W
        (A, LeanCompCert.Ports.Section413Sweep.czero)) := by
  let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
  let p := LeanCompCert.Ports.Section413Sweep.stepDivisors c.rounds X W
    (A, LeanCompCert.Ports.Section413Sweep.czero)
  have hp : PassInv c W
      (tRunUpto c
        (c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X)) p := by
    simpa only [W, p] using
      passB_stepDivisors c hc X A hflag hX hXc hzero hacc hdelta
  have hs : Nat.sqrt X ≤ c.s := sqrt_le_cfg_s c hXc
  have ht := passB_tail c hc X W p hX hXc hp (c.s - Nat.sqrt X) (by omega)
  have hadd : Nat.sqrt X + (c.s - Nat.sqrt X) = c.s := by omega
  have htime :
      c.phase1 + (X - 1) * c.p + c.s + 1 + Nat.sqrt X +
          (c.s - Nat.sqrt X) =
        c.phase1 + (X - 1) * c.p + c.s + 1 + c.s := by omega
  rw [htime] at ht
  simpa only [W, p] using ht

/-- The two-limb finalizer comparison is exactly comparison with
`21 * SCALE`. -/
theorem tfinBadCore_eq_zero_iff (w tenX : Nat) (hw : w < M) (ht : tenX < M) :
    tfinBadCore w tenX = 0 ↔ w * tenX ≤ 21 * SCALE := by
  let p := LeanCompCert.Verified.MulWide.hl w tenX
  have hs := LeanCompCert.Verified.MulWide.hl_spec w tenX
    (by rw [B64_val]; exact hw) (by rw [B64_val]; exact ht)
  have heq : p.1 + M * p.2 = w * tenX := by
    simpa only [p, B64_val] using hs.1
  have hlo : p.1 < M := by simpa only [p, B64_val] using hs.2
  unfold tfinBadCore
  change bnat (1 < p.2) + bnat (p.2 = 1) * bnat (KLO < p.1) = 0 ↔ _
  by_cases hhi : 1 < p.2
  · rw [bnat_true hhi]
    have hm : 2 * M ≤ M * p.2 := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left M (show 2 ≤ p.2 by omega)
    have h2 : 21 * SCALE < 2 * M := by decide
    constructor
    · omega
    · intro hle
      omega
  · have hhile : p.2 ≤ 1 := by omega
    by_cases hhi1 : p.2 = 1
    · rw [bnat_false hhi, bnat_true hhi1, Nat.zero_add, Nat.one_mul]
      rw [hhi1, Nat.mul_one] at heq
      rw [bnat_eq_zero_iff]
      constructor <;> intro h
      · have hthr := threshold_split
        omega
      · have hthr := threshold_split
        omega
    · have hhi0 : p.2 = 0 := by omega
      rw [bnat_false hhi, bnat_false hhi1, Nat.zero_add, Nat.zero_mul]
      rw [hhi0, Nat.mul_zero, Nat.add_zero] at heq
      constructor
      · intro _
        have hthr := threshold_split
        omega
      · intro _
        rfl

/-- A vanished lower-endpoint bad bit is precisely the lower half of
`g2Check`.  The signed-negative branch is converted to the natural
sign-magnitude product tested by `tfinBadCore`; the nonnegative branch is
automatic. -/
theorem tfinBadLo_zero_sound (c : Cfg) (hc : Admissible c) (z : TSel)
    (t : TState) (hF : z.isF = 1) (hX : z.X ≤ c.cap)
    (hcheck : c.checkLo ≤ z.X) (hbad : c.tfinBadLo z t = 0) :
    -21 * (SCALE : Int) ≤
      decodeZ (tfinGLo z t) * ((10 * z.X : Nat) : Int) := by
  let g := tfinGLo z t
  let tenX := z.X * 10 % M
  have hg : g < M := by
    dsimp only [g, tfinGLo]
    exact Nat.mod_lt _ (by decide)
  have htenRaw : z.X * 10 < M := hc.ten_lt hX
  have htenMod : z.X * 10 % M = z.X * 10 := Nat.mod_eq_of_lt htenRaw
  change -21 * (SCALE : Int) ≤
    decodeZ g * ((10 * z.X : Nat) : Int)
  rw [Nat.mul_comm 10 z.X]
  by_cases hneg : decodeZ g < 0
  · have hH : H63 ≤ g := by
      have hh := (decodeZ_lt_zero_iff g hg).mp hneg
      simpa only [H63_val] using hh
    have hsign : bnat (H63 ≤ g) = 1 := bnat_true hH
    have hmag : tsub 0 g = (decodeZ g).natAbs := by
      have hm := tmag_mag g hg
      simpa only [tmag, if_pos hH] using hm
    have hcore : tfinBadCore (decodeZ g).natAbs (z.X * 10) = 0 := by
      change bnat (H63 ≤ g) *
        tfinBadCore (if bnat (H63 ≤ g) = 1 then tsub 0 g else g)
          (z.X * 10 % M) *
        (z.isF * bnat (c.checkLo ≤ z.X)) = 0 at hbad
      simpa only [hsign, if_pos, hF, bnat_true hcheck, hmag, htenMod,
        Nat.one_mul, Nat.mul_one] using hbad
    have hprod := (tfinBadCore_eq_zero_iff _ _
      (natAbs_decodeZ_lt g hg) htenRaw).mp hcore
    have hcast :
        ((decodeZ g).natAbs * (z.X * 10) : Nat) ≤ 21 * SCALE := hprod
    have hmagEq : decodeZ g = -((decodeZ g).natAbs : Int) := by
      rcases Int.natAbs_eq (decodeZ g) with hp | hn
      · have hp0 : 0 ≤ decodeZ g := by
          rw [hp]
          exact Int.natCast_nonneg _
        omega
      · exact hn
    have hcast' :
        (((decodeZ g).natAbs : Int) * ((z.X * 10 : Nat) : Int)) ≤
          21 * (SCALE : Int) := by
      exact_mod_cast hcast
    rw [hmagEq]
    simpa only [Int.neg_mul] using Int.neg_le_neg hcast'
  · have hg0 : 0 ≤ decodeZ g := by omega
    have hten0 : 0 ≤ ((z.X * 10 : Nat) : Int) := Int.natCast_nonneg _
    have hprod0 : 0 ≤ decodeZ g * ((z.X * 10 : Nat) : Int) :=
      Int.mul_nonneg hg0 hten0
    have hleft : -21 * (SCALE : Int) ≤ 0 := by
      have := Int.natCast_nonneg SCALE
      omega
    exact Int.le_trans hleft hprod0

/-- A vanished upper-endpoint bad bit is the upper half of `g2Check`. -/
theorem tfinBadHi_zero_sound (c : Cfg) (hc : Admissible c) (z : TSel)
    (t : TState) (hF : z.isF = 1) (hX : z.X ≤ c.cap)
    (hcheck : c.checkLo ≤ z.X) (hbad : c.tfinBadHi z t = 0) :
    decodeZ (tfinGHi z t) * ((10 * z.X : Nat) : Int) ≤
      21 * (SCALE : Int) := by
  let g := tfinGHi z t
  let tenX := z.X * 10 % M
  have hg : g < M := by
    dsimp only [g, tfinGHi]
    exact Nat.mod_lt _ (by decide)
  have htenRaw : z.X * 10 < M := hc.ten_lt hX
  have htenMod : z.X * 10 % M = z.X * 10 := Nat.mod_eq_of_lt htenRaw
  change decodeZ g * ((10 * z.X : Nat) : Int) ≤ 21 * (SCALE : Int)
  by_cases hneg : decodeZ g < 0
  · have hten0 : 0 ≤ ((10 * z.X : Nat) : Int) := Int.natCast_nonneg _
    have hprod0 : decodeZ g * ((10 * z.X : Nat) : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hten0
    have hright : 0 ≤ 21 * (SCALE : Int) :=
      Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
    exact Int.le_trans hprod0 hright
  · have hg0 : 0 ≤ decodeZ g := by omega
    have hH : ¬ H63 ≤ g := by
      intro hh
      apply hneg
      apply (decodeZ_lt_zero_iff g hg).mpr
      simpa only [H63_val] using hh
    have hsign : bnat (H63 ≤ g) = 0 := bnat_false hH
    have hmag : g = (decodeZ g).natAbs := by
      have hm := tmag_mag g hg
      simpa only [tmag, if_neg hH] using hm
    have hcore : tfinBadCore (decodeZ g).natAbs (z.X * 10) = 0 := by
      change (1 - bnat (H63 ≤ g)) *
        tfinBadCore (if bnat (H63 ≤ g) = 1 then tsub 0 g else g)
          (z.X * 10 % M) *
        (z.isF * bnat (c.checkLo ≤ z.X)) = 0 at hbad
      rw [hsign] at hbad
      simp only [Nat.sub_zero, Nat.zero_ne_one, if_false, hF,
        bnat_true hcheck, Nat.one_mul, Nat.mul_one] at hbad
      rw [hmag, htenMod] at hbad
      exact hbad
    have hmagLt : (decodeZ g).natAbs < M := by
      rw [← hmag]
      exact hg
    have hprod := (tfinBadCore_eq_zero_iff _ _ hmagLt htenRaw).mp hcore
    have hcast :
        (((decodeZ g).natAbs : Int) * ((z.X * 10 : Nat) : Int)) ≤
          21 * (SCALE : Int) := by
      exact_mod_cast hprod
    rw [Int.natAbs_of_nonneg hg0] at hcast
    simpa only [Int.natCast_mul, Nat.mul_comm] using hcast

/-- The active finalizer adds the completed divisor delta to `G`, resets the
delta registers, preserves the accumulator table, and turns a clean pair of
wide comparison bits into the reference `g2Check`. -/
theorem tfin_spec (c : Cfg) (hc : Admissible c) (X : Nat) (z : TSel)
    (t : TState) (W G : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hinv : PassInv c W t p)
    (hgLo : t.gLo < M) (hgHi : t.gHi < M)
    (cgLo : Capped t.gLo) (cgHi : Capped t.gHi)
    (hG : ⟨decodeZ t.gLo, decodeZ t.gHi⟩ = G)
    (hF : z.isF = 1) (hZX : z.X = X) (hXc : X ≤ c.cap)
    (hclean : (c.tfin z t).viol = 0) :
    AccRel c (c.tfin z t) p.1 ∧
      (c.tfin z t).arr 0 = 0 ∧
      deltaAt (c.tfin z t) = LeanCompCert.Ports.Section413Sweep.czero ∧
      (c.tfin z t).gLo < M ∧ (c.tfin z t).gHi < M ∧
      Capped (c.tfin z t).gLo ∧ Capped (c.tfin z t).gHi ∧
      (⟨decodeZ (c.tfin z t).gLo, decodeZ (c.tfin z t).gHi⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell) =
        LeanCompCert.Ports.Section413Sweep.cadd G p.2 ∧
      (c.checkLo ≤ X →
        LeanCompCert.Ports.Section413Sweep.g2Check X
          (LeanCompCert.Ports.Section413Sweep.cadd G p.2) = true) := by
  have hMpos : 0 < M := by decide
  have hgLo' : tfinGLo z t < M := by
    unfold tfinGLo
    exact Nat.mod_lt _ hMpos
  have hgHi' : tfinGHi z t < M := by
    unfold tfinGHi
    exact Nat.mod_lt _ hMpos
  have hor2 := or_eq_zero hclean
  have hor1 := or_eq_zero hor2.1
  have hguards :
      tguard z.isF (tfinGHi z t)
        (tguard z.isF (tfinGLo z t) t.viol) = 0 := hor1.1
  have hbadLo : c.tfinBadLo z t = 0 := hor1.2
  have hbadHi : c.tfinBadHi z t = 0 := hor2.2
  have cHi : Capped (tfinGHi z t) :=
    capped_of_tguard_eq_zero hgHi' (by omega) hguards
  have hinner : tguard z.isF (tfinGLo z t) t.viol = 0 :=
    (tguard_eq_zero hguards).1
  have cLo : Capped (tfinGLo z t) :=
    capped_of_tguard_eq_zero hgLo' (by omega) hinner
  have haddLo : decodeZ (tfinGLo z t) = decodeZ t.gLo + decodeZ t.dLo := by
    simp only [tfinGLo, hF, Nat.one_mul]
    rw [Nat.mod_eq_of_lt hinv.u64.2.2.2.2.1]
    exact decodeZ_add hgLo hinv.u64.2.2.2.2.1 cgLo hinv.dLo_cap
  have haddHi : decodeZ (tfinGHi z t) = decodeZ t.gHi + decodeZ t.dHi := by
    simp only [tfinGHi, hF, Nat.one_mul]
    rw [Nat.mod_eq_of_lt hinv.u64.2.2.2.2.2.1]
    exact decodeZ_add hgHi hinv.u64.2.2.2.2.2.1 cgHi hinv.dHi_cap
  have hgEq :
      (⟨decodeZ (tfinGLo z t), decodeZ (tfinGHi z t)⟩ :
          LeanCompCert.Ports.Section413Sweep.Cell) =
        LeanCompCert.Ports.Section413Sweep.cadd G p.2 := by
    have hdLo := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.lo) hinv.delta_eq
    have hdHi := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.hi) hinv.delta_eq
    have hGLo := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.lo) hG
    have hGHi := congrArg
      (fun I : LeanCompCert.Ports.Section413Sweep.Cell => I.hi) hG
    change decodeZ t.dLo = p.2.lo at hdLo
    change decodeZ t.dHi = p.2.hi at hdHi
    change decodeZ t.gLo = G.lo at hGLo
    change decodeZ t.gHi = G.hi at hGHi
    rw [LeanCompCert.Ports.Section413Sweep.Cell.mk.injEq]
    constructor
    · change decodeZ (tfinGLo z t) = G.lo + p.2.lo
      rw [haddLo, hGLo]
      rw [hdLo]
    · change decodeZ (tfinGHi z t) = G.hi + p.2.hi
      rw [haddHi, hGHi]
      rw [hdHi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hgEq, ?_⟩
  · rcases hinv.acc_rel with ⟨hsize, hcells⟩
    refine ⟨hsize, ?_⟩
    intro d hd
    simpa only [accAt, Cfg.tfin] using hcells d hd
  · simpa only [Cfg.tfin] using hinv.arr_zero
  · simp only [deltaAt, Cfg.tfin, tfinDLo, tfinDHi, hF, Nat.sub_self,
      Nat.mul_zero, Nat.zero_mod,
      LeanCompCert.Ports.Section413Cells.decodeZ_zero,
      LeanCompCert.Ports.Section413Sweep.czero]
  · simpa only [Cfg.tfin] using hgLo'
  · simpa only [Cfg.tfin] using hgHi'
  · simpa only [Cfg.tfin] using cLo
  · simpa only [Cfg.tfin] using cHi
  · intro hcheck
    have hlo := tfinBadLo_zero_sound c hc z t hF
      (by rw [hZX]; exact hXc) (by rw [hZX]; exact hcheck) hbadLo
    have hhi := tfinBadHi_zero_sound c hc z t hF
      (by rw [hZX]; exact hXc) (by rw [hZX]; exact hcheck) hbadHi
    rw [← hgEq]
    unfold LeanCompCert.Ports.Section413Sweep.g2Check
    apply decide_eq_true
    simpa only [hZX, ← SCALE_eq_sweep] using And.intro hlo hhi

/-- Selector specialization for the last slot of a candidate block. -/
theorem tsel_final_block (c : Cfg) (hc : Admissible c) (x : Nat)
    (hx : x < c.cap) :
    let z := c.tsel (c.phase1 + x * c.p + (2 * c.s + 1))
    z.inP1 = 0 ∧ z.inP2 = 1 ∧ z.X = x + 1 ∧ z.isF = 1 ∧
      z.inB = 0 ∧ z.isW = 0 := by
  have hpos : 2 * c.s + 1 < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x (2 * c.s + 1) hx hpos
  rcases hz with ⟨hP1, hP2, _hb2, _hx0, hpX, hX, _hA, hW, _hrA⟩
  let z := c.tsel (c.phase1 + x * c.p + (2 * c.s + 1))
  have hF : z.isF = 1 := by
    change bnat (z.pX = 2 * c.s + 1) * z.inP2 = 1
    dsimp only [z]
    rw [hpX, hP2]
    simp [bnat]
  have hB : z.inB = 0 := by
    change bnat (c.s + 1 ≤ z.pX) * bnat (z.pX ≤ 2 * c.s) * z.inP2 = 0
    dsimp only [z]
    rw [hpX, hP2]
    have hn : ¬ 2 * c.s + 1 ≤ 2 * c.s := by omega
    simp [bnat, hn]
  have hW0 : z.isW = 0 := by
    dsimp only [z]
    rw [hW]
    simp [bnat]
    omega
  exact ⟨hP1, hP2, hX, hF, hB, hW0⟩

/-- All stages before `tfin` in the final slot are persistent-state no-ops.
This isolates the finalizer from the phase-1, pass-A, weight, and pass-B
instruction blocks that share the same compiled loop body. -/
theorem final_pre_inv (c : Cfg) (hc : Admissible c) (x : Nat)
    (W : LeanCompCert.Ports.Section413Sweep.Cell) (t : TState)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hx : x < c.cap) (hinv : PassInv c W t p) :
    let idx := c.phase1 + x * c.p + (2 * c.s + 1)
    let z := c.tsel idx
    let pre := tweight z (tpassA z (ttrial z t))
    let pb := c.tpassB z pre
    PassInv c W pb p ∧ pb.gLo = t.gLo ∧ pb.gHi = t.gHi := by
  let idx := c.phase1 + x * c.p + (2 * c.s + 1)
  let z := c.tsel idx
  let trial := ttrial z t
  let pre := tweight z (tpassA z trial)
  let pb := c.tpassB z pre
  have hz := tsel_final_block c hc x hx
  have hP1 : z.inP1 = 0 := by simpa only [idx, z] using hz.1
  have hP2 : z.inP2 = 1 := by simpa only [idx, z] using hz.2.1
  have hF : z.isF = 1 := by simpa only [idx, z] using hz.2.2.2.1
  have hB : z.inB = 0 := by simpa only [idx, z] using hz.2.2.2.2.1
  have hW : z.isW = 0 := by simpa only [idx, z] using hz.2.2.2.2.2
  have hDL : z.isDL = 0 := by
    change bnat (z.r1 = c.rounds - 1) * z.inP1 = 0
    rw [hP1]
    simp
  have htrialArr : trial.arr = t.arr := by
    dsimp only [trial]
    funext i
    simp only [ttrial, hDL, Nat.zero_mul, Nat.zero_mod]
    by_cases hi : i = 0
    · simp [hi, hinv.arr_zero]
    · simp [hi]
  have hfpre : PassFrame pre t := by
    exact PassFrame.trans (tweight_pass_frame z _ hW)
      (PassFrame.trans (tpassA_pass_frame z _)
        (ttrial_pass_frame z t htrialArr))
  have hipre : PassInv c W pre p := PassInv.of_frame hinv hfpre
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  have hg₁ : g₁ = 0 := by simp [g₁, hB]
  have hg₂ : g₂ = 0 := by simp [g₂, hg₁]
  have hfirst : c.ttouch g₁ z.rB pre = pre := by
    rw [hg₁]
    exact ttouch_gate_zero_eq c z.rB pre hipre.arr_zero hipre.u64
  have hpb : pb = pre := by
    change c.ttouch g₂ q₂ (c.ttouch g₁ z.rB pre) = pre
    rw [hg₂, hfirst]
    exact ttouch_gate_zero_eq c q₂ pre hipre.arr_zero hipre.u64
  refine ⟨?_, ?_, ?_⟩
  · change PassInv c W pb p
    rw [hpb]
    exact hipre
  · change pb.gLo = t.gLo
    rw [hpb]
    rfl
  · change pb.gHi = t.gHi
    rw [hpb]
    rfl

/-- The scheduled last slot of candidate `X` realizes the reference
finalization and lands exactly at the next candidate boundary. -/
theorem final_step_spec (c : Cfg) (hc : Admissible c) (X : Nat)
    (W G : LeanCompCert.Ports.Section413Sweep.Cell)
    (p : Array LeanCompCert.Ports.Section413Sweep.Cell ×
      LeanCompCert.Ports.Section413Sweep.Cell)
    (hflag : c.tFlag = 0) (hX : 1 ≤ X) (hXc : X ≤ c.cap)
    (hinv : PassInv c W
      (tRunUpto c (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))) p)
    (hgLo : (tRunUpto c
      (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gLo < M)
    (hgHi : (tRunUpto c
      (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gHi < M)
    (cgLo : Capped (tRunUpto c
      (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gLo)
    (cgHi : Capped (tRunUpto c
      (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gHi)
    (hG :
      (⟨decodeZ (tRunUpto c
          (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gLo,
        decodeZ (tRunUpto c
          (c.phase1 + (X - 1) * c.p + (2 * c.s + 1))).gHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) = G) :
    AccRel c (tRunUpto c (c.phase1 + X * c.p)) p.1 ∧
      (tRunUpto c (c.phase1 + X * c.p)).arr 0 = 0 ∧
      deltaAt (tRunUpto c (c.phase1 + X * c.p)) =
        LeanCompCert.Ports.Section413Sweep.czero ∧
      (tRunUpto c (c.phase1 + X * c.p)).gLo < M ∧
      (tRunUpto c (c.phase1 + X * c.p)).gHi < M ∧
      Capped (tRunUpto c (c.phase1 + X * c.p)).gLo ∧
      Capped (tRunUpto c (c.phase1 + X * c.p)).gHi ∧
      (⟨decodeZ (tRunUpto c (c.phase1 + X * c.p)).gLo,
        decodeZ (tRunUpto c (c.phase1 + X * c.p)).gHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) =
          LeanCompCert.Ports.Section413Sweep.cadd G p.2 ∧
      (c.checkLo ≤ X →
        LeanCompCert.Ports.Section413Sweep.g2Check X
          (LeanCompCert.Ports.Section413Sweep.cadd G p.2) = true) := by
  let x := X - 1
  let idx := c.phase1 + x * c.p + (2 * c.s + 1)
  let t := tRunUpto c idx
  let z := c.tsel idx
  let pre := tweight z (tpassA z (ttrial z t))
  let pb := c.tpassB z pre
  have hx : x < c.cap := by dsimp only [x]; omega
  have hz := tsel_final_block c hc x hx
  have hF : z.isF = 1 := by simpa only [idx, z] using hz.2.2.2.1
  have hxEq : x + 1 = X := by dsimp only [x]; omega
  have hZX : z.X = X := by
    have hzX : z.X = x + 1 := by simpa only [idx, z] using hz.2.2.1
    exact hzX.trans hxEq
  have hinv' : PassInv c W t p := by
    simpa only [t, idx, x] using hinv
  have hpre := final_pre_inv c hc x W t p hx hinv'
  have hipb : PassInv c W pb p := by
    simpa only [idx, z, pre, pb] using hpre.1
  have hpbgLo : pb.gLo = t.gLo := by
    simpa only [idx, z, pre, pb] using hpre.2.1
  have hpbgHi : pb.gHi = t.gHi := by
    simpa only [idx, z, pre, pb] using hpre.2.2
  have hidx : idx < c.loopCount := by
    have hXp : X * c.p ≤ c.cap * c.p := Nat.mul_le_mul_right c.p hXc
    have htail : x * c.p + (2 * c.s + 1) < X * c.p := by
      calc
        x * c.p + (2 * c.s + 1) < x * c.p + c.p := by
          unfold Cfg.p
          omega
        _ = (x + 1) * c.p := by simp only [Nat.add_mul, Nat.one_mul]
        _ = X * c.p := by rw [hxEq]
    simpa only [idx, Cfg.loopCount, Nat.add_assoc] using
      Nat.add_lt_add_left (Nat.lt_of_lt_of_le htail hXp) c.phase1
  have hcleanStep := (tstep_clean_of_tFlag c hflag hidx).2
  have hclean : (c.tfin z pb).viol = 0 := by
    simpa only [Cfg.tstep, idx, t, z, pre, pb] using hcleanStep
  have hfin := tfin_spec c hc X z pb W G p hipb
    (by rw [hpbgLo]; simpa only [t, idx, x] using hgLo)
    (by rw [hpbgHi]; simpa only [t, idx, x] using hgHi)
    (by rw [hpbgLo]; simpa only [t, idx, x] using cgLo)
    (by rw [hpbgHi]; simpa only [t, idx, x] using cgHi)
    (by rw [hpbgLo, hpbgHi]; simpa only [t, idx, x] using hG)
    hF hZX hXc hclean
  have htime : idx + 1 = c.phase1 + X * c.p := by
    calc
      idx + 1 = c.phase1 + x * c.p + c.p := by
        dsimp only [idx]
        unfold Cfg.p
        omega
      _ = c.phase1 + (x + 1) * c.p := by rw [Nat.add_mul]; omega
      _ = c.phase1 + X * c.p := by rw [hxEq]
  rw [← htime, tRunUpto_succ]
  simpa only [Cfg.tstep, idx, t, z, pre, pb] using hfin

/-- Persistent zero state carried through the trial-division phase.  The
μ-plane may change, but all cells above it (including both accumulator
planes) and every sweep register remain zero. -/
structure Phase1Persist (c : Cfg) (t : TState) : Prop where
  wLo : t.wLo = 0
  wHi : t.wHi = 0
  wwLo : t.wwLo = 0
  wwHi : t.wwHi = 0
  dLo : t.dLo = 0
  dHi : t.dHi = 0
  gLo : t.gLo = 0
  gHi : t.gHi = 0
  arr_zero : t.arr 0 = 0
  arr_above : ∀ i, c.cap < i → t.arr i = 0

theorem tInit_phase1Persist (c : Cfg) (hc : Admissible c) :
    Phase1Persist c tInit := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [tInit]
  · intro i hi
    have hcap := hc.cap_ge_two
    have hi1 : i ≠ 1 := by omega
    simp [tInit, hi1]

theorem Phase1Persist.step (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.phase1) (h : Phase1Persist c (tRunUpto c idx)) :
    Phase1Persist c (c.tstep idx (tRunUpto c idx)) := by
  let t := tRunUpto c idx
  let m := idx / c.rounds
  let r := idx % c.rounds
  have hR : 0 < c.rounds := Nat.lt_of_lt_of_le (by decide) hc.rounds_ge
  have hr : r < c.rounds := Nat.mod_lt _ hR
  have hm : m < c.cap - 1 := by
    apply (Nat.div_lt_iff_lt_mul hR).2
    simpa only [Cfg.phase1] using hidx
  have hdecomp : idx = m * c.rounds + r := by
    symm
    simpa only [m, r, Nat.mul_comm] using Nat.div_add_mod idx c.rounds
  have hz0 := tsel_phase1_block c hc m r hm hr
  rcases hz0 with ⟨hP1', hP2', _hq, _hr1, hn1', _hd1, _hD0,
    hDL', _hA, hW', hB', hF'⟩
  let z := c.tsel idx
  have hP1 : z.inP1 = 1 := by simpa only [z, hdecomp] using hP1'
  have hP2 : z.inP2 = 0 := by simpa only [z, hdecomp] using hP2'
  have hn1 : z.n1 = m + 2 := by simpa only [z, hdecomp] using hn1'
  have hDL : z.isDL = bnat (r = c.rounds - 1) := by
    simpa only [z, hdecomp] using hDL'
  have hB : z.inB = 0 := by simpa only [z, hdecomp] using hB'
  have hF : z.isF = 0 := by simpa only [z, hdecomp] using hF'
  have hW : z.isW = 0 := by simpa only [z, hdecomp] using hW'
  have hncap : z.n1 ≤ c.cap := by rw [hn1]; omega
  have hcapM : c.cap < M := Nat.lt_trans (by omega) hc.arr_fits
  have hnM : z.n1 < M := Nat.lt_of_le_of_lt hncap hcapM
  have hDLle : z.isDL ≤ 1 := by rw [hDL]; exact bnat_le_one _
  have hwrRaw : z.isDL * z.n1 < M := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.mul_le_mul_right z.n1 hDLle) (by simp)) hnM
  have hwr : z.isDL * z.n1 % M = z.isDL * z.n1 :=
    Nat.mod_eq_of_lt hwrRaw
  let trial := ttrial z t
  have htrialZero : trial.arr 0 = 0 := by
    dsimp only [trial]
    change (if 0 = z.isDL * z.n1 % M then z.isDL * _ % M else t.arr 0) = 0
    rw [hwr]
    by_cases hw0 : z.isDL * z.n1 = 0
    · have hd0 : z.isDL = 0 := by
        rcases Nat.mul_eq_zero.mp hw0 with hd | hn
        · exact hd
        · rw [hn1] at hn
          omega
      rw [if_pos hw0.symm, hd0]
      simp
    · rw [if_neg (Ne.symm hw0)]
      exact h.arr_zero
  have htrialAbove : ∀ i, c.cap < i → trial.arr i = 0 := by
    intro i hi
    dsimp only [trial]
    change (if i = z.isDL * z.n1 % M then _ else t.arr i) = 0
    rw [hwr]
    have haddr : z.isDL * z.n1 ≤ c.cap := by
      exact Nat.le_trans (Nat.mul_le_mul_right z.n1 hDLle) (by simpa using hncap)
    rw [if_neg (show i ≠ z.isDL * z.n1 by omega)]
    exact h.arr_above i hi
  let pre := tweight z (tpassA z trial)
  have hWne : z.isW ≠ 1 := by omega
  have hpreFields : pre.wLo = 0 ∧ pre.wHi = 0 ∧ pre.wwLo = 0 ∧
      pre.wwHi = 0 ∧ pre.dLo = 0 ∧ pre.dHi = 0 ∧
      pre.gLo = 0 ∧ pre.gHi = 0 ∧ pre.arr = trial.arr := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simpa only [pre, tweight, hWne, if_false, tpassA, trial, ttrial, t]
        using h.wLo
    · simpa only [pre, tweight, hWne, if_false, tpassA, trial, ttrial, t]
        using h.wHi
    · simpa only [pre, tweight, hWne, if_false, tpassA, trial, ttrial, t]
        using h.wwLo
    · simpa only [pre, tweight, hWne, if_false, tpassA, trial, ttrial, t]
        using h.wwHi
    · exact h.dLo
    · exact h.dHi
    · exact h.gLo
    · exact h.gHi
  have hpreU64 : PassU64 pre := by
    have hcore := tweight_coreU64 z _
      (tpassA_coreU64 z _ (ttrial_coreU64 z t (tRunUpto_coreU64 c idx)))
    exact ⟨by rw [hpreFields.1]; decide,
      by rw [hpreFields.2.1]; decide,
      by rw [hpreFields.2.2.1]; decide,
      by rw [hpreFields.2.2.2.1]; decide,
      hcore.1, hcore.2.1, hcore.2.2⟩
  let g₁ := bnat (z.X % z.rB = 0) *
    bnat (z.rB * z.rB % M ≤ z.X) * z.inB
  let q₂ := z.X / z.rB
  let g₂ := g₁ * (1 - bnat (q₂ = z.rB))
  have hg₁ : g₁ = 0 := by simp [g₁, hB]
  have hg₂ : g₂ = 0 := by simp [g₂, hg₁]
  let pb := c.tpassB z pre
  have hpb : pb = pre := by
    change c.ttouch g₂ q₂ (c.ttouch g₁ z.rB pre) = pre
    rw [hg₂, hg₁, ttouch_gate_zero_eq c z.rB pre
      (by rw [hpreFields.2.2.2.2.2.2.2.2, htrialZero]) hpreU64]
    exact ttouch_gate_zero_eq c q₂ pre
      (by rw [hpreFields.2.2.2.2.2.2.2.2, htrialZero]) hpreU64
  change Phase1Persist c (c.tfin z pb)
  rw [hpb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpreFields.1
  · exact hpreFields.2.1
  · exact hpreFields.2.2.1
  · exact hpreFields.2.2.2.1
  · simp [Cfg.tfin, tfinDLo, hF, hpreFields.2.2.2.2.1]
  · simp [Cfg.tfin, tfinDHi, hF, hpreFields.2.2.2.2.2.1]
  · simp [Cfg.tfin, tfinGLo, hF, hpreFields.2.2.2.2.2.2.1]
  · simp [Cfg.tfin, tfinGHi, hF, hpreFields.2.2.2.2.2.2.2.1]
  · simpa only [Cfg.tfin, hpreFields.2.2.2.2.2.2.2.2] using htrialZero
  · intro i hi
    simpa only [Cfg.tfin, hpreFields.2.2.2.2.2.2.2.2] using htrialAbove i hi

theorem phase1_persist (c : Cfg) (hc : Admissible c) : ∀ k, k ≤ c.phase1 →
    Phase1Persist c (tRunUpto c k) := by
  intro k
  induction k with
  | zero => intro _; simpa only [tRunUpto_zero] using tInit_phase1Persist c hc
  | succ k ih =>
      intro hk
      rw [tRunUpto_succ]
      exact Phase1Persist.step c hc k (by omega) (ih (by omega))

/-- Before the last slot of a candidate, the finalizer gate is inactive, so
the global `G` registers are framed exactly. -/
theorem tstep_g_frame (c : Cfg) (hc : Admissible c) (x pos : Nat)
    (t : TState) (hx : x < c.cap) (hpos : pos ≤ 2 * c.s)
    (hgLo : t.gLo < M) (hgHi : t.gHi < M) :
    (c.tstep (c.phase1 + x * c.p + pos) t).gLo = t.gLo ∧
      (c.tstep (c.phase1 + x * c.p + pos) t).gHi = t.gHi := by
  let idx := c.phase1 + x * c.p + pos
  let z := c.tsel idx
  have hposp : pos < c.p := by unfold Cfg.p; omega
  have hz := tsel_phase2_block c hc x pos hx hposp
  have hF : z.isF = 0 := by
    rcases hz with ⟨_hP1, hP2, _hb2, _hx0, hpX, _hX, _hA, _hW, _hrA⟩
    change bnat (z.pX = 2 * c.s + 1) * z.inP2 = 0
    dsimp only [z, idx]
    rw [hpX, hP2]
    have hn : pos ≠ 2 * c.s + 1 := by omega
    simp [bnat, hn]
  let pb := c.tpassB z (tweight z (tpassA z (ttrial z t)))
  have hpbLo : pb.gLo = t.gLo := rfl
  have hpbHi : pb.gHi = t.gHi := rfl
  change (c.tfin z pb).gLo = t.gLo ∧ (c.tfin z pb).gHi = t.gHi
  constructor
  · simp only [Cfg.tfin, tfinGLo, hF, Nat.zero_mul, Nat.zero_mod,
      Nat.add_zero]
    rw [hpbLo, Nat.mod_eq_of_lt hgLo]
  · simp only [Cfg.tfin, tfinGHi, hF, Nat.zero_mul, Nat.zero_mod,
      Nat.add_zero]
    rw [hpbHi, Nat.mod_eq_of_lt hgHi]

theorem candidate_g_prefix (c : Cfg) (hc : Admissible c) (x : Nat)
    (hx : x < c.cap)
    (hgLo : (tRunUpto c (c.phase1 + x * c.p)).gLo < M)
    (hgHi : (tRunUpto c (c.phase1 + x * c.p)).gHi < M) :
    ∀ k, k ≤ 2 * c.s + 1 →
      (tRunUpto c (c.phase1 + x * c.p + k)).gLo =
          (tRunUpto c (c.phase1 + x * c.p)).gLo ∧
        (tRunUpto c (c.phase1 + x * c.p + k)).gHi =
          (tRunUpto c (c.phase1 + x * c.p)).gHi := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let start := c.phase1 + x * c.p
      let cur := tRunUpto c (start + k)
      have hcurLo : cur.gLo < M := by
        rw [show cur.gLo = (tRunUpto c start).gLo by
          simpa only [cur, start] using hprev.1]
        simpa only [start] using hgLo
      have hcurHi : cur.gHi < M := by
        rw [show cur.gHi = (tRunUpto c start).gHi by
          simpa only [cur, start] using hprev.2]
        simpa only [start] using hgHi
      have hs := tstep_g_frame c hc x k cur hx (by omega) hcurLo hcurHi
      rw [show start + (k + 1) = (start + k) + 1 by omega,
        tRunUpto_succ]
      constructor
      · exact hs.1.trans (by simpa only [cur, start] using hprev.1)
      · exact hs.2.trans (by simpa only [cur, start] using hprev.2)

/-- Reference sweep after exactly `k` candidates, retaining the production
array size `N+1` in every prefix. -/
def g2Prefix (R checkLo N k : Nat) :
    LeanCompCert.Ports.Section413Sweep.G2State :=
  (List.range k).foldl
    (fun s i => LeanCompCert.Ports.Section413Sweep.g2Step R checkLo s (i + 1))
    ⟨Array.replicate (N + 1) LeanCompCert.Ports.Section413Sweep.czero,
      LeanCompCert.Ports.Section413Sweep.czero, true⟩

theorem g2Prefix_zero (R checkLo N : Nat) :
    g2Prefix R checkLo N 0 =
      ⟨Array.replicate (N + 1) LeanCompCert.Ports.Section413Sweep.czero,
        LeanCompCert.Ports.Section413Sweep.czero, true⟩ := rfl

theorem g2Prefix_succ (R checkLo N k : Nat) :
    g2Prefix R checkLo N (k + 1) =
      LeanCompCert.Ports.Section413Sweep.g2Step R checkLo
        (g2Prefix R checkLo N k) (k + 1) := by
  unfold g2Prefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem g2Prefix_full (R checkLo N : Nat) :
    g2Prefix R checkLo N N =
      LeanCompCert.Ports.Section413Sweep.g2Run R checkLo N := rfl

/-- Boundary invariant between candidate blocks of the machine loop and the
corresponding reference sweep prefix. -/
structure SweepRel (c : Cfg) (t : TState)
    (s : LeanCompCert.Ports.Section413Sweep.G2State) : Prop where
  acc_rel : AccRel c t s.acc
  arr_zero : t.arr 0 = 0
  delta_zero : deltaAt t = LeanCompCert.Ports.Section413Sweep.czero
  gLo_u64 : t.gLo < M
  gHi_u64 : t.gHi < M
  gLo_cap : Capped t.gLo
  gHi_cap : Capped t.gHi
  g_eq : (⟨decodeZ t.gLo, decodeZ t.gHi⟩ :
    LeanCompCert.Ports.Section413Sweep.Cell) = s.g
  ok_true : s.ok = true

theorem phase1_sweepRel (c : Cfg) (hc : Admissible c) :
    SweepRel c (tRunUpto c c.phase1) (g2Prefix c.rounds c.checkLo c.cap 0) := by
  have hp := phase1_persist c hc c.phase1 (Nat.le_refl _)
  have hzeroDecode := LeanCompCert.Ports.Section413Cells.decodeZ_zero
  refine ⟨?_, hp.arr_zero, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨by simp [g2Prefix], ?_⟩
    intro d hd
    have h1 : c.cap < d + c.plane1 := by unfold Cfg.plane1; omega
    have h2 : c.cap < d + c.plane2 := by unfold Cfg.plane2; omega
    have hdsize : d < (Array.replicate (c.cap + 1)
        LeanCompCert.Ports.Section413Sweep.czero).size := by
      simp only [Array.size_replicate]
      omega
    unfold accAt
    rw [hp.arr_above _ h1, hp.arr_above _ h2,
      hzeroDecode]
    simp only [g2Prefix, List.range_zero, List.foldl_nil]
    rw [getElem!_pos
      (Array.replicate (c.cap + 1) LeanCompCert.Ports.Section413Sweep.czero)
      d hdsize, Array.getElem_replicate]
    rfl
  · simp only [deltaAt, hp.dLo, hp.dHi, hzeroDecode,
      LeanCompCert.Ports.Section413Sweep.czero]
  · rw [hp.gLo]; decide
  · rw [hp.gHi]; decide
  · unfold Capped
    rw [hp.gLo, hzeroDecode]
    simp
  · unfold Capped
    rw [hp.gHi, hzeroDecode]
    simp
  · simp only [g2Prefix, List.range_zero, List.foldl_nil, hp.gLo, hp.gHi,
      hzeroDecode, LeanCompCert.Ports.Section413Sweep.czero]

theorem SweepRel.step (c : Cfg) (hc : Admissible c) (hflag : c.tFlag = 0)
    (k : Nat) (hk : k < c.cap)
    (hrel : SweepRel c (tRunUpto c (c.phase1 + k * c.p))
      (g2Prefix c.rounds c.checkLo c.cap k)) :
    SweepRel c (tRunUpto c (c.phase1 + (k + 1) * c.p))
      (g2Prefix c.rounds c.checkLo c.cap (k + 1)) := by
  let X := k + 1
  let s := g2Prefix c.rounds c.checkLo c.cap k
  let W := LeanCompCert.Ports.Section413Sweep.weightV2 c.rounds X
  let ad := LeanCompCert.Ports.Section413Sweep.stepDivisors c.rounds X W
    (s.acc, LeanCompCert.Ports.Section413Sweep.czero)
  let base := c.phase1 + k * c.p
  let wbase := base + c.s + 1
  have hX : 1 ≤ X := by dsimp only [X]; omega
  have hXc : X ≤ c.cap := by dsimp only [X]; omega
  have hXsub : X - 1 = k := by dsimp only [X]; omega
  have hpre := prePass_DA_prefix c hc k hk hrel.arr_zero (c.s + 1)
    (Nat.le_refl _)
  have hpre' : DAFrame (tRunUpto c wbase) (tRunUpto c base) := by
    simpa only [wbase, base, Nat.add_assoc] using hpre
  have hzeroW : (tRunUpto c wbase).arr 0 = 0 := by
    have hz := congrArg (fun a => a 0) hpre'.arr
    exact hz.trans (by simpa only [base] using hrel.arr_zero)
  have haccW : AccRel c (tRunUpto c wbase) s.acc := by
    rcases hrel.acc_rel with ⟨hsize, hcells⟩
    refine ⟨hsize, ?_⟩
    intro d hd
    simpa only [accAt, hpre'.arr, base, s] using hcells d hd
  have hdeltaW : deltaAt (tRunUpto c wbase) =
      LeanCompCert.Ports.Section413Sweep.czero := by
    unfold deltaAt
    rw [hpre'.dLo, hpre'.dHi]
    simpa only [deltaAt, base] using hrel.delta_zero
  have hp0 := passB_full c hc X s.acc hflag hX hXc
    (by simpa only [wbase, base, hXsub] using hzeroW)
    (by simpa only [wbase, base, hXsub, s] using haccW)
    (by simpa only [wbase, base, hXsub] using hdeltaW)
  have htimeB :
      c.phase1 + (X - 1) * c.p + c.s + 1 + c.s =
        c.phase1 + k * c.p + (2 * c.s + 1) := by
    rw [hXsub]
    omega
  have hp : PassInv c W
      (tRunUpto c (c.phase1 + k * c.p + (2 * c.s + 1))) ad := by
    simpa only [W, ad, s, htimeB] using hp0
  have hgprefix := candidate_g_prefix c hc k hk hrel.gLo_u64 hrel.gHi_u64
    (2 * c.s + 1) (Nat.le_refl _)
  have hgLo : (tRunUpto c
      (c.phase1 + k * c.p + (2 * c.s + 1))).gLo < M := by
    rw [hgprefix.1]
    exact hrel.gLo_u64
  have hgHi : (tRunUpto c
      (c.phase1 + k * c.p + (2 * c.s + 1))).gHi < M := by
    rw [hgprefix.2]
    exact hrel.gHi_u64
  have cgLo : Capped (tRunUpto c
      (c.phase1 + k * c.p + (2 * c.s + 1))).gLo := by
    rw [hgprefix.1]
    exact hrel.gLo_cap
  have cgHi : Capped (tRunUpto c
      (c.phase1 + k * c.p + (2 * c.s + 1))).gHi := by
    rw [hgprefix.2]
    exact hrel.gHi_cap
  have hG :
      (⟨decodeZ (tRunUpto c
          (c.phase1 + k * c.p + (2 * c.s + 1))).gLo,
        decodeZ (tRunUpto c
          (c.phase1 + k * c.p + (2 * c.s + 1))).gHi⟩ :
        LeanCompCert.Ports.Section413Sweep.Cell) = s.g := by
    rw [hgprefix.1, hgprefix.2]
    simpa only [s] using hrel.g_eq
  have hfin := final_step_spec c hc X W s.g ad hflag hX hXc hp hgLo hgHi
    cgLo cgHi hG
  have hnext : c.phase1 + X * c.p = c.phase1 + (k + 1) * c.p := by
    rfl
  rw [← hnext]
  rw [g2Prefix_succ]
  change SweepRel c (tRunUpto c (c.phase1 + X * c.p))
    (LeanCompCert.Ports.Section413Sweep.g2Step c.rounds c.checkLo s X)
  have hok :
      (LeanCompCert.Ports.Section413Sweep.g2Step c.rounds c.checkLo s X).ok =
        true := by
    unfold LeanCompCert.Ports.Section413Sweep.g2Step
    dsimp only [W, ad]
    rw [hrel.ok_true]
    by_cases hcheck : c.checkLo ≤ X
    · rw [if_pos hcheck, hfin.2.2.2.2.2.2.2.2 hcheck]
      decide
    · rw [if_neg hcheck]
      decide
  refine ⟨?_, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
    hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1, ?_, hok⟩
  · simpa only [LeanCompCert.Ports.Section413Sweep.g2Step, W, ad] using hfin.1
  · simpa only [LeanCompCert.Ports.Section413Sweep.g2Step, W, ad] using
      hfin.2.2.2.2.2.2.2.1

theorem sweep_prefix (c : Cfg) (hc : Admissible c) (hflag : c.tFlag = 0) :
    ∀ k, k ≤ c.cap →
      SweepRel c (tRunUpto c (c.phase1 + k * c.p))
        (g2Prefix c.rounds c.checkLo c.cap k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [Nat.zero_mul, Nat.add_zero] using phase1_sweepRel c hc
  | succ k ih =>
      intro hk
      exact SweepRel.step c hc hflag k (by omega) (ih (by omega))

/-- **Transparent-model source soundness.**  A clean compiled sweep implies
the independently defined reference Boolean.  Together with
`Section413G2FinalDenote.g2Program_denote`, this closes both directions of
the production LeanCompCert route. -/
theorem tFlag_zero_sound (c : Cfg) (hc : Admissible c) (h : c.tFlag = 0) :
    LeanCompCert.Ports.Section413Sweep.g2SweepOK
      c.rounds c.checkLo c.cap = true := by
  have hr := sweep_prefix c hc h c.cap (Nat.le_refl _)
  unfold LeanCompCert.Ports.Section413Sweep.g2SweepOK
  rw [← g2Prefix_full]
  exact hr.ok_true

theorem production_tFlag_zero_sound (h : production.tFlag = 0) :
    LeanCompCert.Ports.Section413Sweep.g2SweepOK
      production.rounds production.checkLo production.cap = true :=
  tFlag_zero_sound production production_admissible h

/-! ## Obligation (2): closed

`passB_full` proves the scheduled divisor fold, `final_step_spec` proves the
active finalizer and wide `g2Check`, and `sweep_prefix` carries their joint
invariant from the phase-1 zero state through all `cap` candidates.
`tFlag_zero_sound` is the resulting model-to-reference theorem.  The separate
module `Section413G2Verified` joins it to `g2Program_denote` and the verified
compiler theorem without introducing an import cycle.
-/

end LeanCompCert.Ports.Section413G2Sound
