import LeanCompCert.Ports.CDEMAbelMarkTermination

/-!
# Arithmetic meaning of the finite CDEM marking plane

The compiled cursor starts divisor `d` at `(d - w % d) % d` and advances by
`d`.  This file identifies that executable progression with divisibility of
the represented integer `w + j`, then identifies the corresponding finite
plane fold with the independent `Ref.deltaF` computation.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkPlane

open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMarkReady
open LeanCompCert.Verified.Reflect

/-- The first cell marked by a nonzero divisor row. -/
def firstCell (w d : Nat) : Nat := (d - w % d) % d

/-- A cell belongs to the literal arithmetic progression traversed by row
`d`. -/
def MarksCell (w d j : Nat) : Prop :=
  j % d = firstCell w d

instance (w d j : Nat) : Decidable (MarksCell w d j) := by
  unfold MarksCell
  infer_instance

theorem firstCell_lt (w d : Nat) (hd : 0 < d) : firstCell w d < d := by
  exact Nat.mod_lt _ hd

private theorem primeTrialFold_one (ps : List Nat)
    (hps : ∀ p ∈ ps, 2 ≤ p) :
    ps.foldl Ref.primeTrialStep ⟨1, 0, 1⟩ = ⟨1, 0, 1⟩ := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hpTwo : 2 ≤ p := hps p (by simp)
      have htail : ∀ q ∈ ps, 2 ≤ q := by
        intro q hq
        exact hps q (by simp [hq])
      simp only [List.foldl_cons]
      have hpOne : 1 < p := by omega
      have hp : 1 % p ≠ 0 := by rw [Nat.mod_eq_of_lt hpOne]; decide
      have hM : 1 % M = 1 := by decide
      simp [Ref.primeTrialStep, hp, hM, ih htail]

theorem muCodeFor_one (kBound : Nat) : Ref.muCodeFor kBound 1 = 1 := by
  have hps : ∀ p ∈ Ref.muPrimes kBound, 2 ≤ p := by
    intro p hp
    exact (LeanCompCert.Verified.PackedSieve.PrimeBase.prime hp).two_le
  simp [Ref.muCodeFor, Ref.muCodeWith, primeTrialFold_one _ hps,
    Ref.decodePrimeTrial, show 1 % M = 1 by decide]

theorem mod_eq_firstCell_iff (w d j : Nat) (hd : 0 < d) :
    j % d = firstCell w d ↔ d ∣ w + j := by
  let r := w % d
  have hr : r < d := Nat.mod_lt _ hd
  have hj : j % d < d := Nat.mod_lt _ hd
  have hwmod : w % d = r := rfl
  constructor
  · intro heq
    by_cases hr0 : r = 0
    · have hfirst : firstCell w d = 0 := by
        simp [firstCell, hwmod, hr0]
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hwmod, heq, hfirst]
      simpa [hr0]
    · have hsubPos : 0 < d - r := by omega
      have hsubLt : d - r < d := by omega
      have hfirst : firstCell w d = d - r := by
        unfold firstCell
        rw [hwmod, Nat.mod_eq_of_lt hsubLt]
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hwmod, heq, hfirst]
      rw [show r + (d - r) = d by omega, Nat.mod_self]
  · intro hdvd
    have hmod : (r + j % d) % d = 0 := by
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      simpa [Nat.add_mod, hwmod] using hdvd
    by_cases hr0 : r = 0
    · have hj0 : j % d = 0 := by
        rw [hr0, Nat.zero_add, Nat.mod_eq_of_lt hj] at hmod
        exact hmod
      have hfirst : firstCell w d = 0 := by
        simp [firstCell, hwmod, hr0]
      simpa [hfirst] using hj0
    · have hdiv : d ∣ r + j % d :=
        (Nat.dvd_iff_mod_eq_zero).2 hmod
      rcases hdiv with ⟨q, hq⟩
      have hsumPos : 0 < r + j % d := by omega
      have hsumLt : r + j % d < 2 * d := by omega
      have hqPos : 0 < q := by
        by_cases hq0 : q = 0
        · simp [hq0] at hq
          omega
        · exact Nat.zero_lt_of_ne_zero hq0
      have hqLt : q < 2 := by
        apply (Nat.mul_lt_mul_left hd).mp
        calc
          d * q = r + j % d := hq.symm
          _ < 2 * d := hsumLt
          _ = d * 2 := Nat.mul_comm _ _
      have hqOne : q = 1 := by omega
      have hsum : r + j % d = d := by simpa [hqOne] using hq
      have hsubLt : d - r < d := by omega
      have hfirst : firstCell w d = d - r := by
        unfold firstCell
        rw [hwmod, Nat.mod_eq_of_lt hsubLt]
      rw [hfirst]
      omega

theorem marksCell_progression_iff (w d j : Nat) (hd : 0 < d) :
    MarksCell w d j ↔ ∃ n, j = firstCell w d + n * d := by
  constructor
  · intro hmod
    refine ⟨j / d, ?_⟩
    calc
      j = j % d + d * (j / d) := (Nat.mod_add_div j d).symm
      _ = firstCell w d + (j / d) * d := by rw [hmod, Nat.mul_comm]
  · rintro ⟨n, rfl⟩
    have hfirst := firstCell_lt w d hd
    simp [MarksCell, Nat.add_mod, Nat.mod_eq_of_lt hfirst]

theorem marksCell_iff_dvd (w d j : Nat) (hd : 0 < d) :
    MarksCell w d j ↔ d ∣ w + j :=
  mod_eq_firstCell_iff w d j hd

/-! ## Cursor-local attachment

The following invariant is deliberately local: whenever the cursor is about
to perform a resident write, its sign is the decoded Möbius coefficient and
its cell lies in the divisor progression.  This is the induction needed to
attach the terminal array telescope to `planeValue` without replaying a
production-size trace.
-/

structure ArithmeticInv (c : Cfg) (w : Nat) (s : MarkState) : Prop where
  table : ∀ d, 1 ≤ d → d ≤ c.kBound →
    s.arr (d + c.muBase) = Ref.muCodeFor c.kBound d
  divisorPos : 0 < s.divisor
  divisorBound : s.divisor ≤ c.kBound
  sign_active : s.multiple < c.segLen →
    s.sign = markSignOfCode (Ref.muCodeFor c.kBound s.divisor)
  progression_active : s.multiple < c.segLen →
    MarksCell w s.divisor s.multiple

theorem first_arithmeticInv (c : Cfg) (w : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hkPos : 0 < c.kBound) : ArithmeticInv c w (MarkState.first c st) := by
  refine
    { table := ?_
      divisorPos := by simp [MarkState.first]
      divisorBound := by simp [MarkState.first]; omega
      sign_active := ?_
      progression_active := ?_ }
  · intro d hd hdK
    simp only [MarkState.first]
    rw [if_neg (by unfold Cfg.winBase Cfg.k1; omega)]
    exact htable d hd hdK
  · intro _
    simp [MarkState.first, markSignOfCode, muCodeFor_one]
  · intro _
    simp [MarkState.first, MarksCell, firstCell, Nat.mod_one]

theorem ArithmeticInv.step (c : Cfg) (w : Nat) (s : MarkState)
    (h : ArithmeticInv c w s) : ArithmeticInv c w (s.step c w) := by
  by_cases hm : s.multiple < c.segLen
  · refine
      { table := ?_
        divisorPos := by simpa [MarkState.step, hm] using h.divisorPos
        divisorBound := by simpa [MarkState.step, hm] using h.divisorBound
        sign_active := ?_
        progression_active := ?_ }
    · intro d hd hdK
      simp only [MarkState.step, hm, ↓reduceIte]
      rw [if_neg (by unfold Cfg.winBase Cfg.k1; omega)]
      exact h.table d hd hdK
    · intro hnext
      simpa [MarkState.step, hm] using h.sign_active hm
    · intro hnext
      have hmod := h.progression_active hm
      unfold MarksCell at hmod ⊢
      simpa [MarkState.step, hm, Nat.add_mod] using hmod
  · have hmout : c.segLen ≤ s.multiple := Nat.not_lt.mp hm
    by_cases hdK : s.divisor < c.kBound
    · let d := s.divisor + 1
      have hdPos : 0 < d := by omega
      have hdBound : d ≤ c.kBound := by omega
      have hcode : s.arr (d + c.muBase) = Ref.muCodeFor c.kBound d :=
        h.table d (by omega) hdBound
      refine
        { table := by simpa [MarkState.step, hm, hdK] using h.table
          divisorPos := by simp [MarkState.step, hm, hdK]
          divisorBound := by
            simp only [MarkState.step, hm, hdK, ↓reduceIte]
            omega
          sign_active := ?_
          progression_active := ?_ }
      · intro hactive
        simp only [MarkState.step, hm, hdK, ↓reduceIte]
        rw [hcode]
      · intro hactive
        simp only [MarkState.step, hm, hdK, ↓reduceIte] at hactive ⊢
        have hcode' : s.arr (s.divisor + 1 + c.muBase) =
            Ref.muCodeFor c.kBound (s.divisor + 1) := by
          simpa [d] using hcode
        have hnonzero : Ref.muCodeFor c.kBound d ≠ 0 := by
          intro hz
          rw [hcode, markCellOfCode, if_pos hz] at hactive
          exact (Nat.lt_irrefl _ hactive)
        have hnonzero' : Ref.muCodeFor c.kBound (s.divisor + 1) ≠ 0 := by
          simpa [d] using hnonzero
        have hfirstLt := firstCell_lt w (s.divisor + 1) (by omega)
        simp [MarksCell, markCellOfCode, hcode', hnonzero', firstCell,
          Nat.mod_eq_of_lt hfirstLt]
    · have hd : s.divisor = c.kBound :=
        Nat.le_antisymm h.divisorBound (Nat.le_of_not_gt hdK)
      exact
        { table := by simpa [MarkState.step, hm, hdK] using h.table
          divisorPos := by simpa [MarkState.step, hm, hdK, hd] using
            h.divisorPos
          divisorBound := by simp [MarkState.step, hm, hdK]
          sign_active := by simp [MarkState.step, hm, hdK]
          progression_active := by simp [MarkState.step, hm, hdK] }

theorem ArithmeticInv.iter (c : Cfg) (w n : Nat) (s : MarkState)
    (h : ArithmeticInv c w s) : ArithmeticInv c w (s.iter c w n) := by
  induction n with
  | zero => simpa [MarkState.iter] using h
  | succ n ih =>
      simpa [MarkState.iter] using ih.step c w

theorem active_write_has_mobius_sign_and_divides (c : Cfg) (w : Nat)
    (s : MarkState) (h : ArithmeticInv c w s)
    (hm : s.multiple < c.segLen) :
    s.sign = markSignOfCode (Ref.muCodeFor c.kBound s.divisor) ∧
      s.divisor ∣ w + s.multiple := by
  exact ⟨h.sign_active hm,
    (marksCell_iff_dvd w s.divisor s.multiple h.divisorPos).1
      (h.progression_active hm)⟩

/-- Pointwise declarative value of the plane produced by all divisor rows.
This fold is finite and executable; unlike `Ref.deltaF`, its membership test
is stated in the same first-cell/progression language as the compiled cursor.
-/
def applyMuCode (acc code : Nat) : Nat :=
  if code = 1 then (acc + 1) % M
  else if code = 2 then (acc + (M - 1)) % M else acc

def rowStep (kBound w j acc d : Nat) : Nat :=
  if MarksCell w d j then applyMuCode acc (Ref.muCodeFor kBound d) else acc

def planeValue (kBound w j : Nat) : Nat :=
  ((List.range (kBound + 1)).drop 1).foldl
    (rowStep kBound w j) 0

/-- The same divisor fold indexed by the number of completed rows.  This
recursive presentation makes the cursor's divisor-advance step symbolic: the
`n+1` equation adds exactly row `n+1`. -/
def rowsValue (kBound w j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rowStep kBound w j (rowsValue kBound w j n) (n + 1)

theorem rowsValue_eq_fold_range' (kBound w j n : Nat) :
    rowsValue kBound w j n =
      (List.range' 1 n).foldl (rowStep kBound w j) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range'_1_concat, List.foldl_append]
      simp [rowsValue, ih, Nat.add_comm]

private theorem drop_one_range_succ (n : Nat) :
    (List.range (n + 1)).drop 1 = List.range' 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        List.range_succ, List.drop_append_of_le_length]
      · rw [ih, List.range'_1_concat]
        simp [Nat.add_comm]
      · simp

theorem planeValue_eq_rowsValue (kBound w j : Nat) :
    planeValue kBound w j = rowsValue kBound w j kBound := by
  rw [planeValue, drop_one_range_succ, ← rowsValue_eq_fold_range']

/-- Rows strictly before `divisor`, plus the already-written prefix of the
current row.  This is the ghost value maintained by the executable marking
cursor; `multiple` is its next resident write. -/
def partialPlaneValue (kBound w j divisor multiple : Nat) : Nat :=
  let acc := rowsValue kBound w j (divisor - 1)
  if j < multiple then rowStep kBound w j acc divisor else acc

theorem partialPlaneValue_terminal (kBound w j multiple : Nat)
    (hkPos : 0 < kBound) (hj : j < multiple) :
    partialPlaneValue kBound w j kBound multiple = planeValue kBound w j := by
  rw [partialPlaneValue, if_pos hj, planeValue_eq_rowsValue]
  have hk : kBound - 1 + 1 = kBound := by omega
  rw [← hk]
  rfl

/-- Arithmetic cursor invariant together with the exact pointwise value of
the writes already performed.  `origin` is the window plane before the first
marking iteration. -/
structure PlaneInv (c : Cfg) (w : Nat) (origin : Nat → Nat)
    (s : MarkState) : Prop where
  arithmetic : ArithmeticInv c w s
  originWord : ∀ j, j < c.segLen → origin j < M
  window : ∀ j, j < c.segLen →
    s.arr (j + c.winBase) =
      (origin j + partialPlaneValue c.kBound w j s.divisor s.multiple) % M

theorem first_planeInv (c : Cfg) (w : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hword : ∀ j, j < c.segLen → st.arr (j + c.winBase) < M)
    (hkPos : 0 < c.kBound) :
    PlaneInv c w (fun j => st.arr (j + c.winBase))
      (MarkState.first c st) := by
  refine
    { arithmetic := first_arithmeticInv c w st htable hkPos
      originWord := hword
      window := ?_ }
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [MarkState.first, partialPlaneValue, rowsValue, rowStep,
      MarksCell, firstCell, applyMuCode, muCodeFor_one, Nat.mod_one]
  · have haddr : j + c.winBase ≠ c.winBase := by omega
    have hjOne : ¬j < 1 := by omega
    simp [MarkState.first, partialPlaneValue, rowsValue, hjOne, haddr, hj0,
      Nat.mod_eq_of_lt (hword j hj)]

/-- Once the cursor is parked at the terminal divisor and outside the
window, its pointwise ghost value is the complete declarative plane. -/
theorem PlaneInv.window_eq_planeValue_of_terminal (c : Cfg) (w : Nat)
    (origin : Nat → Nat) (s : MarkState) (h : PlaneInv c w origin s)
    (hd : s.divisor = c.kBound) (hm : c.segLen ≤ s.multiple)
    (j : Nat) (hj : j < c.segLen) :
    s.arr (j + c.winBase) =
      (origin j + planeValue c.kBound w j) % M := by
  rw [h.window j hj, hd,
    partialPlaneValue_terminal c.kBound w j s.multiple (by
      rw [← hd]
      exact h.arithmetic.divisorPos) (by omega)]

private theorem marksCell_eq_of_between (w d m j : Nat) (hd : 0 < d)
    (hm : MarksCell w d m) (hj : MarksCell w d j)
    (hmj : m ≤ j) (hjm : j < m + d) : j = m := by
  have hdm := (marksCell_iff_dvd w d m hd).1 hm
  have hdj := (marksCell_iff_dvd w d j hd).1 hj
  have hdsub : d ∣ j - m := by
    have := Nat.dvd_sub hdj hdm
    simpa [Nat.add_sub_add_left, hmj] using this
  by_cases heq : j = m
  · exact heq
  · have hpos : 0 < j - m := by omega
    have hle := Nat.le_of_dvd hpos hdsub
    omega

private theorem not_marksCell_of_lt_first (w d j : Nat) (hd : 0 < d)
    (hj : j < firstCell w d) : ¬ MarksCell w d j := by
  intro hm
  have hjd : j < d := Nat.lt_trans hj (firstCell_lt w d hd)
  unfold MarksCell at hm
  rw [Nat.mod_eq_of_lt hjd] at hm
  omega

private theorem applyMuCode_eq_add_sign (acc code : Nat) (hacc : acc < M)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    applyMuCode acc code = (acc + markSignOfCode code) % M := by
  rcases hcode with rfl | rfl | rfl <;>
    simp [applyMuCode, markSignOfCode, Nat.mod_eq_of_lt hacc]

private theorem rowsValue_lt (kBound w j n : Nat) :
    rowsValue kBound w j n < M := by
  induction n with
  | zero => simp [rowsValue]; decide
  | succ n ih =>
      simp only [rowsValue, rowStep]
      split
      · rw [applyMuCode_eq_add_sign _ _ ih
          (CDEMAbelMarkReady.muCode_cases kBound _)]
        exact Nat.mod_lt _ (by decide)
      · exact ih

private theorem partialPlaneValue_lt (kBound w j d m : Nat) :
    partialPlaneValue kBound w j d m < M := by
  simp only [partialPlaneValue]
  split
  · simp only [rowStep]
    split
    · rw [applyMuCode_eq_add_sign _ _ (rowsValue_lt _ _ _ _)
          (CDEMAbelMarkReady.muCode_cases kBound d)]
      exact Nat.mod_lt _ (by decide)
    · exact rowsValue_lt _ _ _ _
  · exact rowsValue_lt _ _ _ _

private theorem partialPlaneValue_of_row_complete (kBound w j d m : Nat)
    (hd : 0 < d) (hj : j < m) :
    partialPlaneValue kBound w j d m = rowsValue kBound w j d := by
  rw [partialPlaneValue, if_pos hj]
  have hdPred : d - 1 + 1 = d := by omega
  rw [← hdPred]
  rfl

private theorem partialPlaneValue_at_row_start (c : Cfg) (w j d : Nat)
    (hd : 0 < d) (hj : j < c.segLen) :
    partialPlaneValue c.kBound w j d
        (markCellOfCode c w d (Ref.muCodeFor c.kBound d)) =
      rowsValue c.kBound w j (d - 1) := by
  rcases CDEMAbelMarkReady.muCode_cases c.kBound d with hcode | hcode | hcode
  · simp [partialPlaneValue, markCellOfCode, hcode, hj, rowStep, applyMuCode]
  · by_cases hfirst : j < firstCell w d
    · have hnmark := not_marksCell_of_lt_first w d j hd hfirst
      simp [partialPlaneValue, markCellOfCode, firstCell, hcode, hfirst,
        rowStep, hnmark]
    · have hnot : ¬ j < (d - w % d) % d := by
        simpa [firstCell] using hfirst
      simp [partialPlaneValue, markCellOfCode, hcode, hnot]
  · by_cases hfirst : j < firstCell w d
    · have hnmark := not_marksCell_of_lt_first w d j hd hfirst
      simp [partialPlaneValue, markCellOfCode, firstCell, hcode, hfirst,
        rowStep, hnmark]
    · have hnot : ¬ j < (d - w % d) % d := by
        simpa [firstCell] using hfirst
      simp [partialPlaneValue, markCellOfCode, hcode, hnot]

theorem PlaneInv.step (c : Cfg) (w : Nat) (origin : Nat → Nat)
    (s : MarkState) (h : PlaneInv c w origin s) :
    PlaneInv c w origin (s.step c w) := by
  refine
    { arithmetic := h.arithmetic.step c w
      originWord := h.originWord
      window := ?_ }
  intro j hj
  by_cases hm : s.multiple < c.segLen
  · by_cases hjm : j = s.multiple
    · subst j
      have hmark := h.arithmetic.progression_active hm
      have hsign := h.arithmetic.sign_active hm
      have hcode := CDEMAbelMarkReady.muCode_cases c.kBound s.divisor
      simp only [MarkState.step, hm, ↓reduceIte]
      rw [h.window s.multiple hm]
      simp only [partialPlaneValue, Nat.lt_irrefl, if_false,
        show s.multiple < s.multiple + s.divisor by
          exact Nat.lt_add_of_pos_right h.arithmetic.divisorPos,
        if_true, rowStep, hmark]
      rw [applyMuCode_eq_add_sign _ _ (rowsValue_lt _ _ _ _) hcode,
        ← hsign]
      rw [Nat.mod_add_mod, Nat.add_mod_mod]
      simp [Nat.add_assoc]
    · have haddr : j + c.winBase ≠ s.multiple + c.winBase := by omega
      simp only [MarkState.step, hm, ↓reduceIte]
      rw [if_neg haddr, h.window j hj]
      by_cases hjmark : MarksCell w s.divisor j
      · have hcut : j < s.multiple ↔ j < s.multiple + s.divisor := by
          constructor
          · omega
          · intro hnew
            by_cases hold : j < s.multiple
            · exact hold
            · exact False.elim (hjm (marksCell_eq_of_between w s.divisor
                s.multiple j h.arithmetic.divisorPos
                (h.arithmetic.progression_active hm) hjmark
                (Nat.not_lt.mp hold) hnew))
        simp [partialPlaneValue, rowStep, hjmark, hcut]
      · simp [partialPlaneValue, rowStep, hjmark]
  · have hmout : c.segLen ≤ s.multiple := Nat.not_lt.mp hm
    by_cases hdK : s.divisor < c.kBound
    · have htable : s.arr (s.divisor + 1 + c.muBase) =
          Ref.muCodeFor c.kBound (s.divisor + 1) :=
        h.arithmetic.table (s.divisor + 1) (by omega) (by omega)
      simp only [MarkState.step, hm, hdK, ↓reduceIte]
      rw [h.window j hj,
        partialPlaneValue_of_row_complete c.kBound w j s.divisor
          s.multiple h.arithmetic.divisorPos (by omega)]
      rw [htable]
      have hstart := partialPlaneValue_at_row_start c w j
        (s.divisor + 1) (by omega) hj
      have hpred : s.divisor + 1 - 1 = s.divisor := by omega
      rw [hstart, hpred]
    · have hd : s.divisor = c.kBound :=
        Nat.le_antisymm h.arithmetic.divisorBound (Nat.le_of_not_gt hdK)
      simp only [MarkState.step, hm, hdK, ↓reduceIte]
      rw [h.window j hj]
      unfold partialPlaneValue
      rw [if_pos (by omega), if_pos hj, hd]

theorem PlaneInv.iter (c : Cfg) (w : Nat) (origin : Nat → Nat)
    (s : MarkState) (h : PlaneInv c w origin s) (n : Nat) :
    PlaneInv c w origin (s.iter c w n) := by
  induction n with
  | zero => simpa [MarkState.iter] using h
  | succ n ih =>
      simpa [MarkState.iter] using ih.step c w origin

private theorem fold_marks_eq_delta (kBound w j : Nat) (xs : List Nat)
    (hpos : ∀ d ∈ xs, 0 < d) (acc : Nat) :
    xs.foldl
        (fun a d =>
          if MarksCell w d j then
            let code := Ref.muCodeFor kBound d
            if code = 1 then (a + 1) % M
            else if code = 2 then (a + (M - 1)) % M else a
          else a) acc =
      xs.foldl
        (fun a d =>
          if (w + j) % d ≠ 0 then a
          else
            let code := Ref.muCodeFor kBound d
            if code = 1 then (a + 1) % M
            else if code = 2 then (a + (M - 1)) % M else a) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons d ds ih =>
      have hd : 0 < d := hpos d (by simp)
      have htail : ∀ e ∈ ds, 0 < e := by
        intro e he
        exact hpos e (by simp [he])
      simp only [List.foldl_cons]
      by_cases hm : MarksCell w d j
      · have hz : (w + j) % d = 0 :=
          (Nat.dvd_iff_mod_eq_zero).1 ((marksCell_iff_dvd w d j hd).1 hm)
        simp only [if_pos hm, if_neg (fun hn : (w + j) % d ≠ 0 => hn hz)]
        exact ih htail _
      · have hnz : (w + j) % d ≠ 0 := by
          intro hz
          apply hm
          exact (marksCell_iff_dvd w d j hd).2
            ((Nat.dvd_iff_mod_eq_zero).2 hz)
        simp only [if_neg hm, if_pos hnz]
        exact ih htail _

theorem planeValue_eq_deltaF (kBound w j : Nat) :
    planeValue kBound w j = Ref.deltaF kBound (w + j) := by
  unfold planeValue rowStep applyMuCode Ref.deltaF
  apply fold_marks_eq_delta
  intro d hd
  have hdRange : d ∈ List.range (kBound + 1) :=
    List.mem_of_mem_drop hd
  have hdNotZero : d ≠ 0 := by
    intro hz
    subst d
    simpa using hd
  omega

/-- The exact remaining-work execution of the pure cursor leaves every
resident cell equal to the original window plus `Ref.deltaF`.  This is the
terminal array attachment; it is proved by induction and does not evaluate a
production-sized trace. -/
theorem first_iter_remaining_window_eq_deltaF (c : Cfg) (w : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hword : ∀ j, j < c.segLen → st.arr (j + c.winBase) < M)
    (hkPos : 0 < c.kBound) :
    let cinv := first_cursorInv c st htable hkPos
    let n := remaining c w (MarkState.first c st) cinv.divisorPos
    let out := (MarkState.first c st).iter c w n
    ∀ j, j < c.segLen →
      out.arr (j + c.winBase) =
        (st.arr (j + c.winBase) + Ref.deltaF c.kBound (w + j)) % M := by
  let cinv := first_cursorInv c st htable hkPos
  let n := remaining c w (MarkState.first c st) cinv.divisorPos
  have hp := PlaneInv.iter c w (fun j => st.arr (j + c.winBase))
    (MarkState.first c st) (first_planeInv c w st htable hword hkPos) n
  have ht := iter_remaining_terminal c w (MarkState.first c st) cinv
  dsimp only at ht ⊢
  intro j hj
  rw [hp.window_eq_planeValue_of_terminal c w _ _ ht.1 ht.2 j hj,
    planeValue_eq_deltaF]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The literal scheduled machine loop has the same terminal marking array as
the pure cursor.  Thus the executable CompCert path computes the finite
`Ref.deltaF` contribution pointwise, provided its certified finite budget
covers the symbolic remaining-work count. -/
theorem bodyIter_from_start_window_eq_deltaF_of_budget (c : Cfg) (idx : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState) (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (LeanCompCert.Verified.ArrayFoldBridge.arun idx st c.body))
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hword : ∀ j, j < c.segLen → st.arr (j + c.winBase) < M)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hsegPos : 0 < c.segLen) (hsegM : c.segLen < M)
    (hkPos : 0 < c.kBound) (hkM : c.kBound < M)
    (hbudget : 1 + remaining c w (MarkState.first c st)
      (first_cursorInv c st htable hkPos).divisorPos ≤ c.markSteps)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M) (hwM : w < M) :
    let cinv := first_cursorInv c st htable hkPos
    let n := remaining c w (MarkState.first c st) cinv.divisorPos
    let out := bodyIter c idx (n + 1) st
    ∀ j, j < c.segLen →
      out.arr (j + c.winBase) =
        (st.arr (j + c.winBase) + Ref.deltaF c.kBound (w + j)) % M := by
  let cinv := first_cursorInv c st htable hkPos
  let n := remaining c w (MarkState.first c st) cinv.divisorPos
  have hrep := bodyIter_markState_from_start_ready c idx n st w hfirst
    htable hbudget hidxM hsieveM hsieve hmarkM hsegPos hsegM hkPos hkM
    hkNextM hsumM hsinkM hperiodM hwM
  have hp := PlaneInv.iter c w (fun j => st.arr (j + c.winBase))
    (MarkState.first c st) (first_planeInv c w st htable hword hkPos) n
  have ht := iter_remaining_terminal c w (MarkState.first c st) cinv
  dsimp only at ht ⊢
  intro j hj
  have haddr : j + c.winBase ≠ c.sink := by
    unfold Cfg.sink
    omega
  rw [hrep.live _ haddr,
    hp.window_eq_planeValue_of_terminal c w _ _ ht.1 ht.2 j hj,
    planeValue_eq_deltaF]

end LeanCompCert.Ports.CDEMAbelMarkPlane
