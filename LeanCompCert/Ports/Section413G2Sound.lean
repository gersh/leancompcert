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

/-! ## OPEN: what remains of obligation (2)

Nothing below is proved; each item is stated exactly as it will have to be
proved, so that the next pass can pick any one of them up in isolation.
None of them is asserted anywhere in this file, as an axiom or otherwise.

**(O1, retired) A global `Inv_tstep`.**

This is deliberately no longer an obligation.  Accumulator-plane stores are
unguarded until their next live use, so preservation of `ArrCapped` is too
strong.  The local clean-guard lemmas named above replace it and match the
actual program.

**(O2, arithmetic proved) The touch block computes
`Section413Sweep.touch`.**

```text
theorem ttouch_spec (c : Cfg) (g d : Nat) (t : TState) (hg : g = 1)
    (hd : 0 < d) (hdc : d ≤ c.cap)
    (hclean : (c.ttouch g d t).viol = 0)
    (hmu : t.arr d = MertensCDEM.muCode d c.rounds) :
    ((c.ttouch g d t).arr (d + c.plane1),
     (c.ttouch g d t).arr (d + c.plane2),
     (c.ttouch g d t).dLo, (c.ttouch g d t).dHi)
      = (encodeZ (Section413Sweep.touch c.rounds W (A, D) d).1[d]!.lo, …)
```

where `A`, `W`, `D` are the decoded accumulator table, weight cell and
delta cell.  `ttouch_live_spec` now proves both updated accumulator endpoints
and both delta endpoints in exactly the reference `cadd`/`deltaTerm` form;
`ttouch_arr_frame`, `ttouch_mu_frame`, and `ttouch_pair_mu_frame` prove the
needed array frames, while `ttouch_gate_zero` proves the gated-off identity.
What remains is only the scheduling layer: provide the weight-square and
incoming-delta premises and package the pointwise cells as the reference
`Array`.

**(O3, proved) Phase 1 computes `μ`.**

```text
theorem phase1_muCode (c : Cfg) (hc : Admissible c) (h : c.tFlag = 0)
    (n : Nat) (hn : 2 ≤ n) (hnc : n ≤ c.cap) :
    (tRunUpto c ((n - 1) * c.rounds)).arr n
      = MertensCDEM.muCode n c.rounds
```

The theorem `phase1_muCode` above now has this conclusion without even the
clean-flag premise.  `phase1_trial_prefix` proves the full per-round fold
against `MertensCDEM.trialPrefix`; `ttrial_last_write` proves the branchless
last-round code and its in-range store.  The later phase-1 stages are proved
to frame the μ plane.  `μ(1) = +1` remains the `tInit` seed.

**(O4, proved) Pass A computes `sigmaPair`.**

```text
theorem passA_sigma (c : Cfg) (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    (tRunUpto c (c.phase1 + (X - 1) * c.p + c.s)).sigma
      = Section413Sweep.sigmaPair X
```

The theorem `passA_sigma` above proves this exact statement.  The local
`sigmaScan` model includes the machine's explicit square guard;
`sigmaScan_cfg_s` proves that its `c.s = Nat.sqrt c.cap` rounds equal the
reference `sigmaPair` fold for every `X ≤ c.cap`.  `phase2_sigma_prefix`
then lifts the exact machine transition through the pass, including its
position-zero reset and all `% M` non-wrapping obligations.

**(O5, endpoint computation proved) The weight round computes `weightV2`.**

```text
theorem weight_spec (c : Cfg) … :
    (decodeZ (…).wLo, decodeZ (…).wHi)
      = ((Section413Sweep.weightV2 c.rounds X).lo,
         (Section413Sweep.weightV2 c.rounds X).hi)
```

The theorem `weight_spec` above proves this scheduled endpoint equality.
`cratSMul_of_code` handles the exact signed floor/ceiling identities for the
three μ codes; `phase1_muCode_final_ge_one` and `phase2_muCode` prove that the
μ plane remains live through the weight round; and (O4) supplies the
positive `sigmaPair` denominator.  The rounded numerator's non-wrapping bound
is now an explicit `Admissible.weight_fits` field.  The separate `ww = w²`
relation needed by pass B remains part of (O6)'s incoming invariant.

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
