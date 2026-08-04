import LeanCompCert.Ports.CeDyadicBlock
import LeanCompCert.Ports.CeDyadicClaim

/-!
# Source specification of the dyadic cE fold

This file closes the mathematical side of `CeDyadicFold`: the flattened
machine state is identified with the candidate-wise trial-division sum used
by the consumer.  It contains no run admission.
-/

namespace LeanCompCert.Ports.CeDyadicSpec

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Ports.CeDyadicFold
open LeanCompCert.Ports.CeDyadicBlock
open LeanCompCert.Ports.CeDyadicClaim

private theorem bit_or_eq_zero_iff {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) :
    (x ||| y = 0) ↔ x = 0 ∧ y = 0 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
    rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

private theorem trialBit_le (n r : Nat) :
    (if n % (2 * r + 1) = 0 then 1 else 0) ≤ 1 := by
  split <;> omega

/-- The composite flag is a bit whenever its seed is a bit. -/
theorem cfRun_le_one (n : Nat) : ∀ a m x, x ≤ 1 → cfRun n a m x ≤ 1 := by
  intro a m x hx
  induction m generalizing a x with
  | zero => exact hx
  | succ m ih =>
      exact ih (a := a + 1) (x := x |||
        (if n % (2 * a + 1) = 0 then 1 else 0))
        (bit_bor hx (trialBit_le n a))

/-- Peel the last trial round, matching `List.range_succ`. -/
theorem cfRun_succ_right (n a m x : Nat) :
    cfRun n a (m + 1) x =
      cfRun n a m x |||
        (if n % (2 * (a + m) + 1) = 0 then 1 else 0) := by
  induction m generalizing a x with
  | zero => rfl
  | succ m ih =>
      rw [show cfRun n a (m + 1 + 1) x =
        cfRun n (a + 1) (m + 1)
          (x ||| (if n % (2 * a + 1) = 0 then 1 else 0)) from rfl,
        ih,
        show cfRun n a (m + 1) x =
          cfRun n (a + 1) m
            (x ||| (if n % (2 * a + 1) = 0 then 1 else 0)) from rfl]
      have hidx : a + 1 + m = a + (m + 1) := by omega
      rw [hidx]

/-- Consecutive quiet runs compose without evaluating either segment. -/
theorem cfRun_append (n a m k x : Nat) :
    cfRun n a (m + k) x = cfRun n (a + m) k (cfRun n a m x) := by
  induction m generalizing a x with
  | zero => simp [cfRun]
  | succ m ih =>
      have hlen : m + 1 + k = (m + k) + 1 := by omega
      rw [hlen]
      change cfRun n (a + 1) (m + k)
          (x ||| (if n % (2 * a + 1) = 0 then 1 else 0)) =
        cfRun n (a + (m + 1)) k (cfRun n a (m + 1) x)
      rw [ih]
      change cfRun n (a + 1 + m) k
          (cfRun n (a + 1) m
            (x ||| (if n % (2 * a + 1) = 0 then 1 else 0))) =
        cfRun n (a + (m + 1)) k
          (cfRun n (a + 1) m
            (x ||| (if n % (2 * a + 1) = 0 then 1 else 0)))
      have ha : a + 1 + m = a + (m + 1) := by omega
      rw [ha]

/-- A quiet trial-division run leaves zero precisely when its seed is zero
and every odd trial divisor in its half-open round interval misses `n`. -/
theorem cfRun_eq_zero_iff (n : Nat) : ∀ a m x, x ≤ 1 →
    (cfRun n a m x = 0 ↔
      x = 0 ∧ ∀ r, a ≤ r → r < a + m → n % (2 * r + 1) ≠ 0) := by
  intro a m x
  intro hx
  induction m generalizing a x with
  | zero =>
      constructor
      · intro hx0
        refine ⟨hx0, ?_⟩
        intro r har hr
        omega
      · rintro ⟨hx0, _⟩
        exact hx0
  | succ m ih =>
      let b := if n % (2 * a + 1) = 0 then 1 else 0
      have hb : b ≤ 1 := trialBit_le n a
      have hor : (x ||| b = 0) ↔ x = 0 ∧ b = 0 :=
        bit_or_eq_zero_iff hx hb
      rw [show cfRun n a (m + 1) x = cfRun n (a + 1) m (x ||| b) from rfl,
        ih (a := a + 1) (x := x ||| b) (bit_bor hx hb), hor]
      have hb0 : b = 0 ↔ n % (2 * a + 1) ≠ 0 := by
        simp [b]
      constructor
      · rintro ⟨⟨hx0, hbzero⟩, hrest⟩
        refine ⟨hx0, ?_⟩
        intro r har hr
        by_cases hra : r = a
        · subst r
          exact hb0.mp hbzero
        · exact hrest r (by omega) (by omega)
      · rintro ⟨hx0, hall⟩
        refine ⟨⟨hx0, hb0.mpr (hall a (Nat.le_refl _) (by omega))⟩, ?_⟩
        intro r har hr
        exact hall r (by omega) (by omega)

/-- The exact flag produced by all trial-division rounds of one candidate. -/
def candidateFlag (n R : Nat) : Nat :=
  cfRun n 1 (R - 1) (if n % 2 = 0 then 1 else 0)

/-- The machine flag is zero exactly when all of its configured trial
divisors miss the candidate. -/
theorem candidateFlag_eq_zero_iff {n R : Nat} (hR : 0 < R) :
    candidateFlag n R = 0 ↔ ∀ r < R, ¬ tdiv r ∣ n := by
  have hseed : (if n % 2 = 0 then 1 else 0) ≤ 1 := by split <;> omega
  rw [candidateFlag, cfRun_eq_zero_iff n 1 (R - 1)
    (if n % 2 = 0 then 1 else 0) hseed]
  constructor
  · rintro ⟨heven, hodd⟩ r hr hdvd
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · have hm : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      simp [hm] at heven
    · have hm : n % (2 * r + 1) = 0 := by
        rw [tdiv, if_neg (by omega)] at hdvd
        exact Nat.dvd_iff_mod_eq_zero.mp hdvd
      exact hodd r hrpos (by omega) hm
  · intro hall
    constructor
    · have hnd : ¬ 2 ∣ n := hall 0 hR
      have hm : n % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hnd
      simp [hm]
    · intro r hr1 hrR hm
      have hd : tdiv r ∣ n := by
        rw [tdiv, if_neg (by omega)]
        exact Nat.dvd_iff_mod_eq_zero.mpr hm
      exact hall r (by omega) hd

/-! ## The eight byte-wide long-division rounds -/

/-- State after `i` long-division rounds of candidate `j`. -/
def sdState (c : Params) (j : Nat) (v : Vals) (i : Nat) : Vals :=
  let n := c.lo + j
  let A := sdRun (denAOf c n v.pk) i (v.qA, v.rA)
  let B := sdRun (denBOf c n v.pk) i (v.qB, v.rB)
  { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
    cf := cfRun n 1 i v.cf,
    qA := A.1, rA := A.2, qB := B.1, rB := B.2,
    q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB }

/-- Rounds `1 ... i` are exactly `i` applications of each byte-wide
shift-and-divide recurrence. -/
theorem sd_fold (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) : ∀ i, i ≤ 8 →
    (List.range i).foldl
      (fun w r => ceRound c (j * c.R + (r + 1)) w) v = sdState c j v i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
      have hi8 : i ≤ 8 := by omega
      have hir : i + 1 < c.R := by omega
      obtain ⟨hdiv, hmod⟩ := split_idx (R := c.R) (j := j) (a := i + 1)
        (by omega) hir
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hi8,
        ceRound_sd c (j * c.R + (i + 1)) j (i + 1) (sdState c j v i)
          hdiv hmod (by omega) (by omega) hR]
      · simp [sdState, sdRun_succ, cfRun_succ_right, sdStep, Nat.add_comm]
      · exact hacc

/-! ## Structural decomposition of one candidate block -/

def phase0 (c : Params) (j : Nat) (v : Vals) : Vals :=
  ceRound c (j * c.R) v

def phase8 (c : Params) (j : Nat) (v : Vals) : Vals :=
  (List.range 8).foldl
    (fun w r => ceRound c (j * c.R + (r + 1)) w) (phase0 c j v)

def phase9 (c : Params) (j : Nat) (v : Vals) : Vals :=
  ceRound c (j * c.R + 9) (phase8 c j v)

def phase10 (c : Params) (j : Nat) (v : Vals) : Vals :=
  ceRound c (j * c.R + 10) (phase9 c j v)

def phaseQuiet (c : Params) (j : Nat) (v : Vals) : Vals :=
  (List.range' (j * c.R + 11) (c.R - 12)).foldl
    (fun w k => ceRound c k w) (phase10 c j v)

def phaseLast (c : Params) (j : Nat) (v : Vals) : Vals :=
  ceRound c (j * c.R + (c.R - 1)) (phaseQuiet c j v)

/-- The 2,501-round block has six semantic phases: reset, eight long-division
bytes, quotient, finalisation, quiet trial division, and accumulation. -/
theorem block_eq_phases (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals) :
    BlockedFold.block c.R (fun w k => ceRound c k w) v j = phaseLast c j v := by
  unfold BlockedFold.block phaseLast phaseQuiet phase10 phase9 phase8 phase0
  let s := j * c.R
  have hs0 : List.range' s c.R =
      List.range' s 1 ++ List.range' (s + 1) (c.R - 1) := by
    calc
      List.range' s c.R = List.range' s (1 + (c.R - 1)) := by congr 1 <;> omega
      _ = _ := LeanCompCert.Verified.Segment.range'_split s 1 (c.R - 1)
  have hs1 : List.range' (s + 1) (c.R - 1) =
      List.range' (s + 1) 8 ++ List.range' (s + 9) (c.R - 9) := by
    calc
      List.range' (s + 1) (c.R - 1) =
          List.range' (s + 1) (8 + (c.R - 9)) := by congr 1 <;> omega
      _ = List.range' (s + 1) 8 ++ List.range' (s + 1 + 8) (c.R - 9) :=
        LeanCompCert.Verified.Segment.range'_split (s + 1) 8 (c.R - 9)
      _ = _ := by congr 2 <;> omega
  have hs2 : List.range' (s + 9) (c.R - 9) =
      List.range' (s + 9) 1 ++ List.range' (s + 10) (c.R - 10) := by
    calc
      List.range' (s + 9) (c.R - 9) =
          List.range' (s + 9) (1 + (c.R - 10)) := by congr 1 <;> omega
      _ = List.range' (s + 9) 1 ++ List.range' (s + 9 + 1) (c.R - 10) :=
        LeanCompCert.Verified.Segment.range'_split (s + 9) 1 (c.R - 10)
      _ = _ := by congr 2 <;> omega
  have hs3 : List.range' (s + 10) (c.R - 10) =
      List.range' (s + 10) 1 ++ List.range' (s + 11) (c.R - 11) := by
    calc
      List.range' (s + 10) (c.R - 10) =
          List.range' (s + 10) (1 + (c.R - 11)) := by congr 1 <;> omega
      _ = List.range' (s + 10) 1 ++ List.range' (s + 10 + 1) (c.R - 11) :=
        LeanCompCert.Verified.Segment.range'_split (s + 10) 1 (c.R - 11)
      _ = _ := by congr 2 <;> omega
  have hs4 : List.range' (s + 11) (c.R - 11) =
      List.range' (s + 11) (c.R - 12) ++ List.range' (s + c.R - 1) 1 := by
    calc
      List.range' (s + 11) (c.R - 11) =
          List.range' (s + 11) ((c.R - 12) + 1) := by congr 1 <;> omega
      _ = List.range' (s + 11) (c.R - 12) ++
          List.range' (s + 11 + (c.R - 12)) 1 :=
        LeanCompCert.Verified.Segment.range'_split (s + 11) (c.R - 12) 1
      _ = _ := by congr 2 <;> omega
  change List.foldl (fun w k => ceRound c k w) v (List.range' s c.R) = _
  rw [hs0, hs1, hs2, hs3, hs4]
  simp only [List.foldl_append, List.range'_one, List.foldl_cons, List.foldl_nil]
  rw [BlockedFold.foldl_range'_shift
    (g := fun w k => ceRound c k w) (n := 8) (s := s + 1)]
  congr 1
  · simp [s]
    omega

/-! ## Closed forms of the six phases -/

def bumpPk (c : Params) (j : Nat) (v : Vals) : Nat :=
  if v.pk * 2 ≤ c.lo + j then v.pk * 2 else v.pk

def bumpK (c : Params) (j : Nat) (v : Vals) : Nat :=
  if v.pk * 2 ≤ c.lo + j then v.kk + 1 else v.kk

/-- The dyadic bump preserves `pk = 2^kk`. -/
theorem bumpPk_eq_pow (c : Params) (j : Nat) (v : Vals)
    (hpow : v.pk = 2 ^ v.kk) : bumpPk c j v = 2 ^ bumpK c j v := by
  unfold bumpPk bumpK
  by_cases h : v.pk * 2 ≤ c.lo + j
  · rw [if_pos h, if_pos h, hpow, Nat.pow_succ]
  · rw [if_neg h, if_neg h, hpow]

def zeroState (c : Params) (j : Nat) (v : Vals) : Vals :=
  let n := c.lo + j
  let pk := bumpPk c j v
  let kk := bumpK c j v
  { acc := v.acc, ok := v.ok, pk := pk, kk := kk,
    cf := if n % 2 = 0 then 1 else 0,
    qA := 0, rA := (if c.up = 1 then n * n - pk * pk
                    else 3 * (n * n - pk * pk)),
    qB := 0, rB := (if c.up = 1 then 3 * (4 * pk * pk - n * n)
                    else 4 * pk * pk - n * n),
    q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB }

theorem phase0_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) : phase0 c j v = zeroState c j v := by
  obtain ⟨hdiv, hmod⟩ := split_idx (R := c.R) (j := j) (a := 0)
    (by omega) (by omega)
  unfold phase0
  rw [ceRound_zero c (j * c.R) j v hdiv hmod hR hacc]
  simp [zeroState, bumpPk, bumpK, Nat.mul_assoc]

theorem phase8_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    phase8 c j v = sdState c j (zeroState c j v) 8 := by
  unfold phase8
  rw [phase0_eq c hR j v hacc]
  exact sd_fold c hR j (zeroState c j v) (by simpa [zeroState] using hacc) 8
    (by decide)

def q0State (c : Params) (j : Nat) (v : Vals) : Vals :=
  let n := c.lo + j
  let C := n * (n - 1)
  { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
    cf := v.cf ||| (if n % 19 = 0 then 1 else 0),
    qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
    q0 := c.lfx / C, r0 := c.lfx % C, fA := v.fA, fB := v.fB }

theorem phase9_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    phase9 c j v = q0State c j (sdState c j (zeroState c j v) 8) := by
  obtain ⟨hdiv, hmod⟩ := split_idx (R := c.R) (j := j) (a := 9)
    (by omega) (by omega)
  unfold phase9
  rw [phase8_eq c hR j v hacc,
    ceRound_q0 c (j * c.R + 9) j _ hdiv hmod hR]
  · rfl
  · simpa [sdState, zeroState] using hacc

def quotientB (up C a FB : Nat) : Nat :=
  let ge := if a ≤ FB then 1 else 0
  let cb := ge ^^^ up
  ((if ge = 1 then FB - a else a - FB) + cb * (C - 1)) / C

theorem quotientB_zero (C a FB : Nat) (hC : 0 < C) :
    quotientB 0 C a FB =
      if a ≤ FB then (FB - a + C - 1) / C else (a - FB) / C := by
  by_cases h : a ≤ FB <;> simp [quotientB, h] <;> congr 1 <;> omega

theorem quotientB_one (C a FB : Nat) (hC : 0 < C) :
    quotientB 1 C a FB =
      if a ≤ FB then (FB - a) / C else (a - FB + C - 1) / C := by
  by_cases h : a ≤ FB <;> simp [quotientB, h] <;> congr 1 <;> omega

def finState (c : Params) (j : Nat) (v : Vals) : Vals :=
  let n := c.lo + j
  let C := n * (n - 1)
  let FA := v.qA + c.up * (if v.rA = 0 then 0 else 1)
  let FB := v.qB + (1 - c.up) * (if v.rB = 0 then 0 else 1)
  let a1 := (v.kk + 1) * v.r0
  { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
    cf := v.cf ||| (if n % 21 = 0 then 1 else 0),
    qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
    q0 := v.q0, r0 := v.r0,
    fA := (v.kk * v.r0 + FA + c.up * (C - 1)) / C,
    fB := quotientB c.up C a1 FB }

theorem phase10_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    phase10 c j v = finState c j
      (q0State c j (sdState c j (zeroState c j v) 8)) := by
  obtain ⟨hdiv, hmod⟩ := split_idx (R := c.R) (j := j) (a := 10)
    (by omega) (by omega)
  unfold phase10
  rw [phase9_eq c hR j v hacc,
    ceRound_fin c (j * c.R + 10) j _ hdiv hmod hR]
  · rfl
  · simpa [q0State, sdState, zeroState] using hacc

def quietState (c : Params) (j : Nat) (v : Vals) : Vals :=
  { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
    cf := cfRun (c.lo + j) 11 (c.R - 12) v.cf,
    qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
    q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB }

theorem phaseQuiet_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    phaseQuiet c j v = quietState c j (finState c j
      (q0State c j (sdState c j (zeroState c j v) 8))) := by
  unfold phaseQuiet
  rw [phase10_eq c hR j v hacc]
  exact quiet_fold c hR j (c.R - 12) 11 _ (by omega) (by omega)
    (by simpa [finState, q0State, sdState, zeroState] using hacc)

def lastCf (c : Params) (j : Nat) (v : Vals) : Nat :=
  v.cf ||| (if (c.lo + j) % (2 * (c.R - 1) + 1) = 0 then 1 else 0)

def lastTerm (c : Params) (v : Vals) : Nat :=
  let FB2 := v.qB + (1 - c.up) * (if v.rB = 0 then 0 else 1)
  let a1b := (v.kk + 1) * v.r0
  let tA := v.kk * v.q0 + v.fA
  let base := (v.kk + 1) * v.q0
  let tB := if (if a1b ≤ FB2 then 1 else 0) = 1 then
      (if v.fB ≤ base then base - v.fB else tA) else base + v.fB
  if c.up = 1 then min tA tB else max tA tB

def lastContribution (c : Params) (j : Nat) (v : Vals) : Nat :=
  (if lastCf c j v = 0 then 1 else 0) * lastTerm c v

def lastState (c : Params) (j : Nat) (v : Vals) : Vals :=
  let cf := lastCf c j v
  let ct := lastContribution c j v
  { acc := (v.acc + ct) % M,
    ok := if v.acc + ct < M then v.ok else 0,
    pk := v.pk, kk := v.kk, cf := cf,
    qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
    q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB }

theorem phaseLast_eq (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    phaseLast c j v = lastState c j (quietState c j (finState c j
      (q0State c j (sdState c j (zeroState c j v) 8)))) := by
  obtain ⟨hdiv, hmod⟩ := split_idx (R := c.R) (j := j) (a := c.R - 1)
    (by omega) (by omega)
  unfold phaseLast
  rw [phaseQuiet_eq c hR j v hacc,
    ceRound_acc c (j * c.R + (c.R - 1)) j (c.R - 1) _ hdiv hmod rfl (by omega)]
  unfold lastState lastCf lastContribution lastTerm
  rfl

def preLast (c : Params) (j : Nat) (v : Vals) : Vals :=
  quietState c j (finState c j
    (q0State c j (sdState c j (zeroState c j v) 8)))

/-- All round-specific divisibility bits in the composed state are exactly the
single configured candidate flag. -/
theorem lastState_cf (c : Params) (hR : 12 ≤ c.R) (j : Nat) (v : Vals) :
    (lastState c j (preLast c j v)).cf = candidateFlag (c.lo + j) c.R := by
  let n := c.lo + j
  let seed := if n % 2 = 0 then 1 else 0
  have h9 := cfRun_succ_right n 1 8 seed
  have h10 := cfRun_succ_right n 1 9 seed
  have happ := cfRun_append n 1 10 (c.R - 12) seed
  have hlast := cfRun_succ_right n 1 (c.R - 2) seed
  simp only [lastState, lastCf, preLast, quietState, finState, q0State, sdState,
    zeroState]
  change (cfRun n 11 (c.R - 12)
      ((cfRun n 1 8 seed ||| (if n % 19 = 0 then 1 else 0)) |||
        (if n % 21 = 0 then 1 else 0)) |||
      (if n % (2 * (c.R - 1) + 1) = 0 then 1 else 0)) =
    candidateFlag n c.R
  have h9' : cfRun n 1 8 seed ||| (if n % 19 = 0 then 1 else 0) =
      cfRun n 1 9 seed := by simpa using h9.symm
  have h10' : cfRun n 1 9 seed ||| (if n % 21 = 0 then 1 else 0) =
      cfRun n 1 10 seed := by simpa using h10.symm
  rw [h9', h10']
  have happ' : cfRun n 11 (c.R - 12) (cfRun n 1 10 seed) =
      cfRun n 1 (c.R - 2) seed := by
    rw [← happ]
    congr 3 <;> omega
  rw [happ']
  have hlast' : cfRun n 1 (c.R - 2) seed |||
        (if n % (2 * (c.R - 1) + 1) = 0 then 1 else 0) =
      cfRun n 1 (c.R - 1) seed := by
    have hd : 2 * (c.R - 1) + 1 = 2 * (1 + (c.R - 2)) + 1 := by omega
    have hl : c.R - 2 + 1 = c.R - 1 := by omega
    rw [hd, ← hlast, hl]
  rw [hlast']
  rfl

/-- The arithmetic selected at the accumulation round is exactly the source
`ceTerm` for the carried dyadic exponent. -/
theorem lastTerm_preLast (c : Params) (j : Nat) (v : Vals)
    (hup : c.up ≤ 1) (hpow : v.pk = 2 ^ v.kk) (hn : 2 ≤ c.lo + j) :
    lastTerm c (preLast c j v) = ceTerm c (c.lo + j) (bumpK c j v) := by
  rcases c with ⟨lo, len, R, k0, up, lfx, bound⟩
  dsimp only [Params.up] at hup
  dsimp only [Params.lo] at hn
  rcases (show up = 0 ∨ up = 1 by omega) with rfl | rfl
  · let c0 : Params := ⟨lo, len, R, k0, 0, lfx, bound⟩
    have hpk : bumpPk c0 j v = 2 ^ bumpK c0 j v := bumpPk_eq_pow c0 j v hpow
    have hC : 0 < (lo + j) * (lo + j - 1) :=
      Nat.mul_pos (by omega) (by omega)
    have hceil (x : Nat) : x + ((lo + j) * (lo + j - 1) - 1) =
        x + (lo + j) * (lo + j - 1) - 1 := by omega
    change lastTerm c0 (preLast c0 j v) = ceTerm c0 (lo + j) (bumpK c0 j v)
    simp [c0, lastTerm, preLast, quietState, finState, q0State, sdState,
      zeroState, ceTerm, sd, denAOf, denBOf, hpk, quotientB_zero _ _ _ hC,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    simp_all [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · let c1 : Params := ⟨lo, len, R, k0, 1, lfx, bound⟩
    have hpk : bumpPk c1 j v = 2 ^ bumpK c1 j v := bumpPk_eq_pow c1 j v hpow
    have hC : 0 < (lo + j) * (lo + j - 1) :=
      Nat.mul_pos (by omega) (by omega)
    have hceil (x : Nat) : x + ((lo + j) * (lo + j - 1) - 1) =
        x + (lo + j) * (lo + j - 1) - 1 := by omega
    change lastTerm c1 (preLast c1 j v) = ceTerm c1 (lo + j) (bumpK c1 j v)
    simp [c1, lastTerm, preLast, quietState, finState, q0State, sdState,
      zeroState, ceTerm, sd, denAOf, denBOf, hpk, quotientB_one _ _ _ hC,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    simp_all [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-! ## One block is one source candidate -/

/-- The exact source-level contribution of candidate `j`, still expressed in
terms of the incoming state's carried dyadic exponent. -/
def candidateContribution (c : Params) (j : Nat) (v : Vals) : Nat :=
  if candidateFlag (c.lo + j) c.R = 0 then
    ceTerm c (c.lo + j) (bumpK c j v)
  else 0

theorem lastContribution_preLast (c : Params) (hR : 12 ≤ c.R)
    (j : Nat) (v : Vals) (hpow : v.pk = 2 ^ v.kk) (hup : c.up ≤ 1)
    (hn : 2 ≤ c.lo + j) :
    lastContribution c j (preLast c j v) = candidateContribution c j v := by
  have hcf : lastCf c j (preLast c j v) = candidateFlag (c.lo + j) c.R := by
    simpa only [lastState] using lastState_cf c hR j v
  rw [lastContribution, candidateContribution, hcf,
    lastTerm_preLast c j v hup hpow hn]
  by_cases h : candidateFlag (c.lo + j) c.R = 0 <;> simp [h]

/-- One machine block updates the accumulator by exactly the source
candidate contribution, modulo the machine word modulus. -/
theorem block_acc_eq (c : Params) (hP : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) (hpow : v.pk = 2 ^ v.kk) :
    (BlockedFold.block c.R (fun w k => ceRound c k w) v j).acc =
      (v.acc + candidateContribution c j v) % M := by
  rw [block_eq_phases c hP.RBig j v, phaseLast_eq c hP.RBig j v hacc]
  change (v.acc + lastContribution c j (preLast c j v)) % M = _
  rw [lastContribution_preLast c hP.RBig j v hpow hP.upBit
    (by have := hP.loBig; omega)]

/-- The no-wrap bit records precisely whether this candidate addition stayed
inside one machine word. -/
theorem block_ok_eq (c : Params) (hP : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) (hpow : v.pk = 2 ^ v.kk) :
    (BlockedFold.block c.R (fun w k => ceRound c k w) v j).ok =
      if v.acc + candidateContribution c j v < M then v.ok else 0 := by
  rw [block_eq_phases c hP.RBig j v, phaseLast_eq c hP.RBig j v hacc]
  change (if v.acc + lastContribution c j (preLast c j v) < M
    then v.ok else 0) = _
  rw [lastContribution_preLast c hP.RBig j v hpow hP.upBit
    (by have := hP.loBig; omega)]

/-- One block preserves the power/exponent relation and advances it by the
single dyadic bump belonging to its candidate. -/
theorem block_pk_eq (c : Params) (hP : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    (BlockedFold.block c.R (fun w k => ceRound c k w) v j).pk = bumpPk c j v := by
  rw [block_eq_phases c hP.RBig j v, phaseLast_eq c hP.RBig j v hacc]
  rfl

theorem block_kk_eq (c : Params) (hP : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    (BlockedFold.block c.R (fun w k => ceRound c k w) v j).kk = bumpK c j v := by
  rw [block_eq_phases c hP.RBig j v, phaseLast_eq c hP.RBig j v hacc]
  rfl

/-! ## The outer candidate fold -/

def blockFold (c : Params) (j : Nat) : Vals :=
  (List.range j).foldl
    (BlockedFold.block c.R (fun v k => ceRound c k v)) (initVals c)

theorem blockFold_succ (c : Params) (j : Nat) :
    blockFold c (j + 1) =
      BlockedFold.block c.R (fun v k => ceRound c k v) (blockFold c j) j := by
  unfold blockFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- At every block boundary, the abstract fold inherits the proved machine
invariant: it is a word, carries an exact power of two, and brackets the next
candidate within one dyadic interval. -/
theorem blockFold_facts (c : Params) (hP : c.Sane) (j : Nat) (hj : j ≤ c.len) :
    (blockFold c j).acc < M ∧
    (blockFold c j).ok ≤ 1 ∧
    (blockFold c j).pk = 2 ^ (blockFold c j).kk ∧
    (blockFold c j).pk ≤ c.lo + j ∧
    c.lo + j ≤ 2 * (blockFold c j).pk := by
  let u := (List.range (j * c.R)).foldl
    (fun w i => ceStep c i w) (ceInitState c)
  obtain ⟨hvals, hInv⟩ := ceFold_spec c hP (j * c.R)
    (Nat.mul_le_mul_right c.R hj)
  have hflat :
      (List.range (j * c.R)).foldl (fun v k => ceRound c k v) (initVals c) =
        blockFold c j := by
    exact (BlockedFold.foldl_range_mul j c.R
      (fun v k => ceRound c k v) (initVals c)).trans rfl
  have hv : valsOf u = blockFold c j := hvals.trans hflat
  have eacc := congrArg Vals.acc hv
  have eok := congrArg Vals.ok hv
  have epk := congrArg Vals.pk hv
  have ekk := congrArg Vals.kk hv
  dsimp only [valsOf, Vals.acc] at eacc
  dsimp only [valsOf, Vals.ok] at eok
  dsimp only [valsOf, Vals.pk] at epk
  dsimp only [valsOf, Vals.kk] at ekk
  have hR : 0 < c.R := by have := hP.RBig; omega
  obtain ⟨hdiv, _⟩ := split_idx (R := c.R) (j := j) (a := 0) hR (by omega)
  have hcand : cand c (j * c.R) = c.lo + j := by
    simp only [cand]
    rw [show j * c.R = j * c.R + 0 by omega, hdiv]
  have hacc := hInv.word 0
  have hok := hInv.okLe
  have hpow := hInv.pkPow
  have hle := hInv.pkLe
  have hge := hInv.candLe
  change u 0 < M at hacc
  change u 1 ≤ 1 at hok
  change u 2 = 2 ^ u 3 at hpow
  change u 2 ≤ cand c (j * c.R) at hle
  change cand c (j * c.R) ≤ 2 * u 2 at hge
  rw [eacc] at hacc
  rw [eok] at hok
  rw [epk, ekk] at hpow
  rw [epk, hcand] at hle
  rw [epk, hcand] at hge
  exact ⟨hacc, hok, hpow, hle, hge⟩

private theorem log2_eq_of_pow_le_lt {n k : Nat} (hn : n ≠ 0)
    (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) : Nat.log2 n = k := by
  have h1 : k ≤ Nat.log2 n := (Nat.le_log2 hn).mpr hlo
  have h2 : Nat.log2 n < k + 1 := (Nat.log2_lt hn).mpr hhi
  omega

/-- The single bump at the start of block `j` turns the carried exponent into
exactly `Nat.log2 (lo + j)`. -/
theorem bumpK_blockFold_eq_log2 (c : Params) (hP : c.Sane)
    (j : Nat) (hj : j ≤ c.len) :
    bumpK c j (blockFold c j) = Nat.log2 (c.lo + j) := by
  obtain ⟨_, _, hpow, hlo, hhi⟩ := blockFold_facts c hP j hj
  have hn : c.lo + j ≠ 0 := by have := hP.loBig; omega
  unfold bumpK
  by_cases hb : (blockFold c j).pk * 2 ≤ c.lo + j
  · rw [if_pos hb]
    have heq : c.lo + j = (blockFold c j).pk * 2 := by omega
    rw [heq, hpow, ← Nat.pow_succ, Nat.log2_two_pow]
  · rw [if_neg hb]
    have hlo' : 2 ^ (blockFold c j).kk ≤ c.lo + j := by
      rw [← hpow]
      exact hlo
    have hhi' : c.lo + j < 2 ^ ((blockFold c j).kk + 1) := by
      rw [Nat.pow_succ, ← hpow]
      omega
    exact (log2_eq_of_pow_le_lt hn hlo' hhi').symm

/-- Source contribution with the dyadic exponent stated independently of the
machine's carried state. -/
def sourceContribution (c : Params) (j : Nat) : Nat :=
  if candidateFlag (c.lo + j) c.R = 0 then
    ceTerm c (c.lo + j) (Nat.log2 (c.lo + j))
  else 0

theorem candidateContribution_blockFold (c : Params) (hP : c.Sane)
    (j : Nat) (hj : j ≤ c.len) :
    candidateContribution c j (blockFold c j) = sourceContribution c j := by
  simp only [candidateContribution, sourceContribution,
    bumpK_blockFold_eq_log2 c hP j hj]

def sourceSum (c : Params) (j : Nat) : Nat :=
  (List.range j).foldl (fun a i => a + sourceContribution c i) 0

theorem sourceSum_succ (c : Params) (j : Nat) :
    sourceSum c (j + 1) = sourceSum c j + sourceContribution c j := by
  unfold sourceSum
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem blockFold_acc_succ (c : Params) (hP : c.Sane)
    (j : Nat) (hj : j < c.len) :
    (blockFold c (j + 1)).acc =
      ((blockFold c j).acc + sourceContribution c j) % M := by
  obtain ⟨hacc, _, hpow, _, _⟩ := blockFold_facts c hP j (by omega)
  rw [blockFold_succ, block_acc_eq c hP j (blockFold c j) hacc hpow,
    candidateContribution_blockFold c hP j (by omega)]

theorem blockFold_ok_succ (c : Params) (hP : c.Sane)
    (j : Nat) (hj : j < c.len) :
    (blockFold c (j + 1)).ok =
      if (blockFold c j).acc + sourceContribution c j < M then
        (blockFold c j).ok else 0 := by
  obtain ⟨hacc, _, hpow, _, _⟩ := blockFold_facts c hP j (by omega)
  rw [blockFold_succ, block_ok_eq c hP j (blockFold c j) hacc hpow,
    candidateContribution_blockFold c hP j (by omega)]

theorem blockFold_ok_succ_le (c : Params) (hP : c.Sane)
    (j : Nat) (hj : j < c.len) :
    (blockFold c (j + 1)).ok ≤ (blockFold c j).ok := by
  rw [blockFold_ok_succ c hP j hj]
  split <;> omega

/-- Once the no-wrap bit falls to zero it never recovers. -/
theorem blockFold_ok_anti (c : Params) (hP : c.Sane) :
    ∀ d j, j + d ≤ c.len →
      (blockFold c (j + d)).ok ≤ (blockFold c j).ok := by
  intro d
  induction d with
  | zero => intro j _; exact Nat.le_refl _
  | succ d ih =>
      intro j hj
      have hs := blockFold_ok_succ_le c hP (j + d) (by omega)
      have hi := ih j (by omega)
      exact Nat.le_trans (by simpa [Nat.add_assoc] using hs) hi

/-- If the final no-wrap bit accepts, every modular accumulator update was a
no-op and the final word is the exact unbounded source sum. -/
theorem blockFold_acc_eq_sourceSum_of_ok (c : Params) (hP : c.Sane)
    (hok : (blockFold c c.len).ok = 1) :
    ∀ j, j ≤ c.len → (blockFold c j).acc = sourceSum c j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hmono := blockFold_ok_anti c hP (c.len - (j + 1)) (j + 1) (by omega)
      rw [show j + 1 + (c.len - (j + 1)) = c.len by omega, hok] at hmono
      have hokLe := (blockFold_facts c hP (j + 1) hj).2
      have hjok : (blockFold c (j + 1)).ok = 1 := by omega
      have hs := blockFold_ok_succ c hP j (by omega)
      by_cases hadd : (blockFold c j).acc + sourceContribution c j < M
      · rw [blockFold_acc_succ c hP j (by omega), Nat.mod_eq_of_lt hadd,
          ih (by omega), sourceSum_succ]
      · rw [if_neg hadd] at hs
        omega

theorem ceFinal_eq_blockFold (c : Params) : ceFinal c = blockFold c c.len := by
  unfold ceFinal blockFold
  exact ceFold_blocked c

/-- The source-shaped statement certified by the external program. -/
def sourceAccepts (c : Params) : Prop :=
  if c.up = 1 then sourceSum c c.len ≤ c.bound
  else c.bound ≤ sourceSum c c.len

theorem sourceAccepts_of_ceAccepts (c : Params) (hP : c.Sane)
    (h : ceAccepts c) : sourceAccepts c := by
  obtain ⟨hok, hbound⟩ := h
  rw [ceFinal_eq_blockFold] at hok hbound
  have hsum := blockFold_acc_eq_sourceSum_of_ok c hP hok c.len (Nat.le_refl _)
  unfold sourceAccepts
  rw [hsum] at hbound
  exact hbound

/-- End-to-end source theorem: a proved-program return certificate establishes
the exact candidate-wise sum used by the consumer. -/
theorem sourceAccepts_of_denote (c : Params) (hP : c.Sane)
    (hrun : (ceProgram c).denote = some 1) : sourceAccepts c :=
  sourceAccepts_of_ceAccepts c hP (ceAccepts_of_denote c hP hrun)

/-- Program claim whose proposition is the source sum, not an internal
machine-state predicate. -/
def ceSourceClaim (c : Params) (hP : c.Sane) :
    LeanCompCert.Verified.Algorithm.ProgramClaim (sourceAccepts c) := {
  program := ceProgram c
  wellFormed := ceProgram_wf c
  acceptingValue := 1
  sound := sourceAccepts_of_denote c hP
}

end LeanCompCert.Ports.CeDyadicSpec
