import LeanCompCert.Ports.CDEMAbelMarkReady

/-!
# Finite termination measure for the CDEM Abel marking cursor

The literal marking loop performs one resident write or one divisor advance
per iteration.  This file gives that loop an executable source-level cost.
Unlike reducing `MarkState.iter` for the production budget, the cost has only
one recursive node per resident write and is used symbolically below; the
production numeral will be checked by a separate compiled computation.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkTermination

open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Ports.CDEMAbelMarkTelescope

/-- Number of resident writes still required by divisor `d` from cell `m`.
The positivity argument is proof-irrelevant and only justifies termination. -/
def residentSteps (segLen d m : Nat) (hd : 0 < d) : Nat :=
  if h : m < segLen then
    1 + residentSteps segLen d (m + d) hd
  else 0
termination_by segLen - m
decreasing_by omega

@[simp] theorem residentSteps_of_lt (segLen d m : Nat) (hd : 0 < d)
    (hm : m < segLen) :
    residentSteps segLen d m hd =
      1 + residentSteps segLen d (m + d) hd := by
  rw [residentSteps]
  simp [hm]

@[simp] theorem residentSteps_of_le (segLen d m : Nat) (hd : 0 < d)
    (hm : segLen ≤ m) : residentSteps segLen d m hd = 0 := by
  rw [residentSteps]
  simp [Nat.not_lt.mpr hm]

def ceilDivNat (n d : Nat) : Nat := (n + d - 1) / d

theorem ceilDivNat_sub_step (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    ceilDivNat (n - d) d + 1 = ceilDivNat n d := by
  by_cases hnd : n ≤ d
  · have hnPred : n - 1 < d := by omega
    have hdPred : d - 1 < d := by omega
    have hsum : n + d - 1 = (n - 1) + d := by omega
    simp only [ceilDivNat, Nat.sub_eq_zero_of_le hnd, Nat.zero_add]
    rw [Nat.div_eq_of_lt hdPred, Nat.zero_add, hsum,
      Nat.add_div_right _ hd, Nat.div_eq_of_lt hnPred, Nat.zero_add]
  · have hsub : n - d + d - 1 = n - 1 := by omega
    have hsum : n + d - 1 = (n - 1) + d := by omega
    simp only [ceilDivNat, hsub, hsum]
    rw [Nat.add_div_right _ hd]

theorem residentSteps_le_ceilDiv (segLen d m : Nat) (hd : 0 < d) :
    residentSteps segLen d m hd ≤ ceilDivNat (segLen - m) d := by
  generalize hn : segLen - m = n
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
      by_cases hm : m < segLen
      · rw [residentSteps_of_lt _ _ _ hd hm]
        have hmeasure : segLen - (m + d) < n := by omega
        have hrec := ih _ hmeasure (m + d) rfl
        have hpos : 0 < n := by omega
        have hsub : segLen - (m + d) = n - d := by omega
        rw [hsub] at hrec
        have hle : 1 + residentSteps segLen d (m + d) hd ≤
            ceilDivNat n d := calc
          1 + residentSteps segLen d (m + d) hd ≤
              1 + ceilDivNat (n - d) d := Nat.add_le_add_left hrec 1
          _ = ceilDivNat (n - d) d + 1 := Nat.add_comm _ _
          _ = ceilDivNat n d := ceilDivNat_sub_step n d hpos hd
        simpa [hn] using hle
      · rw [residentSteps_of_le _ _ _ hd (Nat.not_lt.mp hm)]
        exact Nat.zero_le _

theorem ceilDivNat_le_div_succ (n d : Nat) (hd : 0 < d) :
    ceilDivNat n d ≤ n / d + 1 := by
  unfold ceilDivNat
  have hle : n + d - 1 ≤ n + d := Nat.sub_le _ _
  exact Nat.le_trans (Nat.div_le_div_right hle) (Nat.le_of_eq
    (Nat.add_div_right n hd))

theorem residentSteps_le_div_succ (segLen d m : Nat) (hd : 0 < d) :
    residentSteps segLen d m hd ≤ segLen / d + 1 := by
  have hresident := residentSteps_le_ceilDiv segLen d m hd
  have hceil := ceilDivNat_le_div_succ (segLen - m) d hd
  have hdiv : (segLen - m) / d ≤ segLen / d :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  omega

/-- Per-divisor allowance used by the finite production budget check. -/
def divisorAllowance (c : Cfg) (d : Nat) : Nat :=
  if Ref.muCodeFor c.kBound d = 0 then 0 else c.segLen / d + 1

/-- A compact, executable upper bound for a cursor beginning at divisor `d`.
It has one recursion node per divisor, not one per resident write. -/
def allowanceAux (c : Cfg) : Nat → Nat → Nat
  | 0, d => divisorAllowance c d
  | fuel + 1, d => divisorAllowance c d + 1 + allowanceAux c fuel (d + 1)

/-- Compact finite check consumed by the production certificate.  It has
`kBound - 1` divisor nodes and no resident-write recursion. -/
def compactMarkBudget (c : Cfg) : Nat :=
  c.segLen + 2 + allowanceAux c (c.kBound - 2) 2

/-- Tail-recursive evaluator for the same allowance.  Production tools use
this form so the host stack is independent of `kBound`. -/
def allowanceTail (c : Cfg) : Nat → Nat → Nat → Nat
  | 0, d, acc => acc + divisorAllowance c d
  | fuel + 1, d, acc =>
      allowanceTail c fuel (d + 1) (acc + divisorAllowance c d + 1)

theorem allowanceTail_eq (c : Cfg) (fuel d acc : Nat) :
    allowanceTail c fuel d acc = acc + allowanceAux c fuel d := by
  induction fuel generalizing d acc with
  | zero => simp [allowanceTail, allowanceAux]
  | succ fuel ih =>
      rw [allowanceTail, ih]
      simp [allowanceAux, Nat.add_assoc]

def compactMarkBudgetRun (c : Cfg) : Nat :=
  c.segLen + 2 + allowanceTail c (c.kBound - 2) 2 0

theorem compactMarkBudgetRun_eq (c : Cfg) :
    compactMarkBudgetRun c = compactMarkBudget c := by
  simp [compactMarkBudgetRun, compactMarkBudget, allowanceTail_eq]

/-- Runtime form with the verified prime base hoisted out of the divisor
loop.  The production configuration stores this exact list. -/
def divisorAllowanceWith (c : Cfg) (primes : List Nat) (d : Nat) : Nat :=
  if Ref.muCodeWith primes d = 0 then 0 else c.segLen / d + 1

def allowanceTailWith (c : Cfg) (primes : List Nat) :
    Nat → Nat → Nat → Nat
  | 0, d, acc => acc + divisorAllowanceWith c primes d
  | fuel + 1, d, acc =>
      allowanceTailWith c primes fuel (d + 1)
        (acc + divisorAllowanceWith c primes d + 1)

def compactMarkBudgetRunWith (c : Cfg) (primes : List Nat) : Nat :=
  c.segLen + 2 + allowanceTailWith c primes (c.kBound - 2) 2 0

/-- Process exactly `rows` non-final divisor rows.  Unlike
`allowanceTailWith`, every row includes its following divisor-advance step;
this makes long production checks composable into independently compiled
shards. -/
def allowancePrefixWith (c : Cfg) (primes : List Nat) :
    Nat → Nat → Nat → Nat
  | 0, _d, acc => acc
  | rows + 1, d, acc =>
      allowancePrefixWith c primes rows (d + 1)
        (acc + divisorAllowanceWith c primes d + 1)

theorem allowancePrefixWith_acc_add (c : Cfg) (primes : List Nat)
    (rows d base acc : Nat) :
    allowancePrefixWith c primes rows d (base + acc) =
      base + allowancePrefixWith c primes rows d acc := by
  induction rows generalizing d acc with
  | zero => simp [allowancePrefixWith]
  | succ rows ih =>
      rw [allowancePrefixWith, allowancePrefixWith,
        show base + acc + divisorAllowanceWith c primes d + 1 =
            base + (acc + divisorAllowanceWith c primes d + 1) by omega,
        ih]

theorem allowanceTailWith_acc_add (c : Cfg) (primes : List Nat)
    (fuel d base acc : Nat) :
    allowanceTailWith c primes fuel d (base + acc) =
      base + allowanceTailWith c primes fuel d acc := by
  induction fuel generalizing d acc with
  | zero => simp [allowanceTailWith, Nat.add_assoc]
  | succ fuel ih =>
      rw [allowanceTailWith, allowanceTailWith,
        show base + acc + divisorAllowanceWith c primes d + 1 =
            base + (acc + divisorAllowanceWith c primes d + 1) by omega,
        ih]

theorem allowancePrefixWith_add (c : Cfg) (primes : List Nat)
    (left right d acc : Nat) :
    allowancePrefixWith c primes (left + right) d acc =
      allowancePrefixWith c primes right (d + left)
        (allowancePrefixWith c primes left d acc) := by
  induction left generalizing d acc with
  | zero => simp [allowancePrefixWith]
  | succ left ih =>
      rw [Nat.succ_add, allowancePrefixWith, ih]
      simp [allowancePrefixWith, Nat.add_comm, Nat.add_left_comm]

theorem allowanceTailWith_split (c : Cfg) (primes : List Nat)
    (rows fuel d acc : Nat) :
    allowanceTailWith c primes (rows + fuel) d acc =
      allowanceTailWith c primes fuel (d + rows)
        (allowancePrefixWith c primes rows d acc) := by
  induction rows generalizing d acc with
  | zero => simp [allowancePrefixWith]
  | succ rows ih =>
      rw [Nat.succ_add, allowanceTailWith, allowancePrefixWith, ih]
      congr 1 <;> omega

/-- A finite tail is its non-final row prefix followed by the last divisor.
This opaque symbolic form prevents consumers from normalising a large
concrete `allowanceTailWith` recursion merely to expose its final shape. -/
theorem allowanceTailWith_eq_prefix_last (c : Cfg) (primes : List Nat)
    (rows d acc : Nat) :
    allowanceTailWith c primes rows d acc =
      allowancePrefixWith c primes rows d acc +
        divisorAllowanceWith c primes (d + rows) := by
  have h := allowanceTailWith_split c primes rows 0 d acc
  simp only [Nat.add_zero] at h
  rw [h]
  simp [allowanceTailWith]

theorem compactMarkBudgetRunWith_eq_tail (c : Cfg) (primes : List Nat) :
    compactMarkBudgetRunWith c primes =
      c.segLen + 2 + allowanceTailWith c primes (c.kBound - 2) 2 0 := rfl

theorem compactMarkBudgetRunWith_muPrimes (c : Cfg) :
    compactMarkBudgetRunWith c (Ref.muPrimes c.kBound) =
      compactMarkBudgetRun c := by
  have hallow : ∀ fuel d acc,
      allowanceTailWith c (Ref.muPrimes c.kBound) fuel d acc =
        allowanceTail c fuel d acc := by
    intro fuel
    induction fuel with
    | zero =>
        intro d acc
        simp [allowanceTailWith, allowanceTail, divisorAllowanceWith,
          divisorAllowance, Ref.muCodeFor]
    | succ fuel ih =>
        intro d acc
        simp only [allowanceTailWith, allowanceTail]
        rw [show divisorAllowanceWith c (Ref.muPrimes c.kBound) d =
            divisorAllowance c d by
          simp [divisorAllowanceWith, divisorAllowance, Ref.muCodeFor],
          ih]
  simp [compactMarkBudgetRunWith, compactMarkBudgetRun, hallow]

theorem residentSteps_markCell_le_allowance (c : Cfg) (w d : Nat)
    (hd : 0 < d) :
    residentSteps c.segLen d
        (markCellOfCode c w d (Ref.muCodeFor c.kBound d)) hd ≤
      divisorAllowance c d := by
  by_cases hzero : Ref.muCodeFor c.kBound d = 0
  · simp [divisorAllowance, markCellOfCode, hzero]
  · simp only [divisorAllowance, hzero, if_false]
    exact residentSteps_le_div_succ c.segLen d _ hd

/-- Exact remaining scheduled work.  `fuel` is the number of divisor
advances still possible, so the production cursor uses `kBound - divisor`.
-/
def remainingAux (c : Cfg) (w : Nat) :
    (fuel d m : Nat) → 0 < d → Nat
  | 0, d, m, hd => residentSteps c.segLen d m hd
  | fuel + 1, d, m, hd =>
      residentSteps c.segLen d m hd + 1 +
        remainingAux c w fuel (d + 1)
          (markCellOfCode c w (d + 1)
            (Ref.muCodeFor c.kBound (d + 1))) (by omega)

theorem remainingAux_from_markCell_le_allowance (c : Cfg) (w fuel d : Nat)
    (hd : 0 < d) :
    remainingAux c w fuel d
        (markCellOfCode c w d (Ref.muCodeFor c.kBound d)) hd ≤
      allowanceAux c fuel d := by
  induction fuel generalizing d with
  | zero =>
      simpa [remainingAux, allowanceAux] using
        residentSteps_markCell_le_allowance c w d hd
  | succ fuel ih =>
      simp only [remainingAux, allowanceAux]
      have hhead := residentSteps_markCell_le_allowance c w d hd
      have htail := ih (d + 1) (by omega)
      omega

theorem remainingAux_start_le_compactMarkBudget (c : Cfg) (w : Nat)
    (hkTwo : 2 ≤ c.kBound) :
    remainingAux c w (c.kBound - 1) 1 1 (by omega) ≤
      compactMarkBudget c := by
  have hkSplit : c.kBound - 1 = (c.kBound - 2) + 1 := by omega
  rw [hkSplit]
  simp only [remainingAux, compactMarkBudget]
  have hhead := residentSteps_le_div_succ c.segLen 1 1 (by omega)
  have htail := remainingAux_from_markCell_le_allowance c w
    (c.kBound - 2) 2 (by omega)
  have hhead' : residentSteps c.segLen 1 1 (by omega) ≤ c.segLen + 1 := by
    simpa using hhead
  have htail' : remainingAux c w (c.kBound - 2) 2
      (markCellOfCode c w 2 (Ref.muCodeFor c.kBound 2)) (by omega) ≤
      allowanceAux c (c.kBound - 2) 2 := by
    simpa using htail
  change residentSteps c.segLen 1 1 _ + 1 +
      remainingAux c w (c.kBound - 2) 2
        (markCellOfCode c w 2 (Ref.muCodeFor c.kBound 2)) _ ≤
    c.segLen + 2 + allowanceAux c (c.kBound - 2) 2
  omega

theorem remainingAux_resident (c : Cfg) (w fuel d m : Nat)
    (hd : 0 < d) (hm : m < c.segLen) :
    remainingAux c w fuel d m hd =
      1 + remainingAux c w fuel d (m + d) hd := by
  cases fuel <;> simp [remainingAux, residentSteps_of_lt _ _ _ hd hm,
    Nat.add_assoc]

theorem remainingAux_advance (c : Cfg) (w fuel d m : Nat)
    (hd : 0 < d) (hm : c.segLen ≤ m) :
    remainingAux c w (fuel + 1) d m hd =
      1 + remainingAux c w fuel (d + 1)
        (markCellOfCode c w (d + 1)
          (Ref.muCodeFor c.kBound (d + 1))) (by omega) := by
  simp [remainingAux, residentSteps_of_le _ _ _ hd hm]

theorem remainingAux_congr_multiple (c : Cfg) (w fuel d m₁ m₂ : Nat)
    (hd₁ hd₂ : 0 < d) (hm : m₁ = m₂) :
    remainingAux c w fuel d m₁ hd₁ =
      remainingAux c w fuel d m₂ hd₂ := by
  subst m₂
  rfl

/-- Source-level number of nonterminal steps remaining in a valid cursor. -/
def remaining (c : Cfg) (w : Nat) (s : MarkState) (hd : 0 < s.divisor) : Nat :=
  remainingAux c w (c.kBound - s.divisor) s.divisor s.multiple hd

structure CursorInv (c : Cfg) (s : MarkState) : Prop where
  table : ∀ d, 1 ≤ d → d ≤ c.kBound →
    s.arr (d + c.muBase) = Ref.muCodeFor c.kBound d
  divisorPos : 0 < s.divisor
  divisorBound : s.divisor ≤ c.kBound

theorem CursorInv.step (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) : CursorInv c (s.step c w) := by
  by_cases hm : s.multiple < c.segLen
  · exact
      { table := by
          intro d hd hdK
          simp only [MarkState.step, hm, ↓reduceIte]
          rw [if_neg (by
            unfold Cfg.winBase Cfg.k1
            omega)]
          exact h.table d hd hdK
        divisorPos := by simpa [MarkState.step, hm] using h.divisorPos
        divisorBound := by simpa [MarkState.step, hm] using h.divisorBound }
  · by_cases hdK : s.divisor < c.kBound
    · exact
        { table := by simpa [MarkState.step, hm, hdK] using h.table
          divisorPos := by simp [MarkState.step, hm, hdK]
          divisorBound := by
            simp only [MarkState.step, hm, hdK, ↓reduceIte]
            omega }
    · have hbound := h.divisorBound
      have hd : s.divisor = c.kBound := by omega
      exact
        { table := by simpa [MarkState.step, hm, hdK] using h.table
          divisorPos := by simpa [MarkState.step, hm, hdK, hd] using
            h.divisorPos
          divisorBound := by simp [MarkState.step, hm, hdK] }

theorem remaining_step_of_resident (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) (hm : s.multiple < c.segLen) :
    remaining c w s h.divisorPos =
      1 + remaining c w (s.step c w) (h.step c w).divisorPos := by
  simp only [remaining, MarkState.step, hm, ↓reduceIte]
  exact remainingAux_resident c w _ _ _ h.divisorPos hm

theorem remaining_step_of_advance (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) (hm : c.segLen ≤ s.multiple)
    (hdK : s.divisor < c.kBound) :
    remaining c w s h.divisorPos =
      1 + remaining c w (s.step c w) (h.step c w).divisorPos := by
  have hsub : c.kBound - s.divisor =
      (c.kBound - (s.divisor + 1)) + 1 := by omega
  simp only [remaining, MarkState.step, Nat.not_lt.mpr hm, hdK, ↓reduceIte]
  rw [hsub]
  rw [remainingAux_advance c w _ _ _ h.divisorPos hm]
  apply congrArg (fun n => 1 + n)
  apply remainingAux_congr_multiple
  exact congrArg (markCellOfCode c w (s.divisor + 1))
    (h.table (s.divisor + 1) (by omega) (by omega)).symm

theorem remaining_eq_zero_of_terminal (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) (hm : c.segLen ≤ s.multiple)
    (hd : s.divisor = c.kBound) :
    remaining c w s h.divisorPos = 0 := by
  unfold remaining
  simp only [hd, Nat.sub_self]
  change residentSteps c.segLen c.kBound s.multiple _ = 0
  exact residentSteps_of_le _ _ _ _ hm

theorem MarkState.iter_succ_start (c : Cfg) (w n : Nat) (s : MarkState) :
    (s.step c w).iter c w n = s.iter c w (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [MarkState.iter]
      exact congrArg (fun t => t.step c w) ih

/-- Running for the exact executable remaining-work count reaches the parked
terminal cursor.  The proof is a measure induction; it never evaluates a
production-size trace in the kernel. -/
theorem iter_remaining_terminal (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) :
    let out := s.iter c w (remaining c w s h.divisorPos)
    out.divisor = c.kBound ∧ c.segLen ≤ out.multiple := by
  generalize hn : remaining c w s h.divisorPos = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
      by_cases hm : s.multiple < c.segLen
      · have hstep := remaining_step_of_resident c w s h hm
        have hnstep : remaining c w (s.step c w) (h.step c w).divisorPos < n := by
          omega
        have hout := ih _ hnstep (s.step c w) (h.step c w) rfl
        have hn' : n =
            remaining c w (s.step c w) (h.step c w).divisorPos + 1 := by
          omega
        dsimp only at hout ⊢
        rw [hn', ← MarkState.iter_succ_start]
        exact hout
      · have hm' : c.segLen ≤ s.multiple := Nat.not_lt.mp hm
        by_cases hdK : s.divisor < c.kBound
        · have hstep := remaining_step_of_advance c w s h hm' hdK
          have hnstep : remaining c w (s.step c w) (h.step c w).divisorPos < n := by
            omega
          have hout := ih _ hnstep (s.step c w) (h.step c w) rfl
          have hn' : n =
              remaining c w (s.step c w) (h.step c w).divisorPos + 1 := by
            omega
          dsimp only at hout ⊢
          rw [hn', ← MarkState.iter_succ_start]
          exact hout
        · have hd : s.divisor = c.kBound := by
            have := h.divisorBound
            omega
          have hz := remaining_eq_zero_of_terminal c w s h hm' hd
          have hn0 : n = 0 := by omega
          dsimp only
          rw [hn0]
          simpa [MarkState.iter] using And.intro hd hm'

theorem MarkState.iter_add (c : Cfg) (w a b : Nat) (s : MarkState) :
    s.iter c w (a + b) = (s.iter c w a).iter c w b := by
  induction b with
  | zero => simp [MarkState.iter]
  | succ b ih =>
      rw [Nat.add_succ]
      simp only [MarkState.iter, ih]

/-- Once outside the final row, further scheduled marking iterations preserve
the array and remain terminal. -/
theorem MarkState.iter_terminal (c : Cfg) (w n : Nat) (s : MarkState)
    (hd : s.divisor = c.kBound) (hm : c.segLen ≤ s.multiple) :
    let out := s.iter c w n
    out.arr = s.arr ∧ out.divisor = c.kBound ∧ c.segLen ≤ out.multiple := by
  induction n with
  | zero =>
      change s.arr = s.arr ∧ s.divisor = c.kBound ∧ c.segLen ≤ s.multiple
      exact ⟨rfl, hd, hm⟩
  | succ n ih =>
      dsimp only at ih ⊢
      simp only [MarkState.iter]
      have hnot : ¬(s.iter c w n).multiple < c.segLen :=
        Nat.not_lt.mpr ih.2.2
      have hdnot : ¬(s.iter c w n).divisor < c.kBound := by
        rw [ih.2.1]
        exact Nat.lt_irrefl _
      simp only [MarkState.step, hnot, hdnot, ↓reduceIte]
      exact ⟨ih.1, trivial, Nat.le_refl _⟩

/-- Any budget at least the exact remaining-work count has the same completed
array as that exact countdown and is terminal. -/
theorem iter_of_remaining_le_terminal (c : Cfg) (w : Nat) (s : MarkState)
    (h : CursorInv c s) (n : Nat)
    (hle : remaining c w s h.divisorPos ≤ n) :
    let rem := remaining c w s h.divisorPos
    let exact := s.iter c w rem
    let out := s.iter c w n
    out.arr = exact.arr ∧ out.divisor = c.kBound ∧
      c.segLen ≤ out.multiple := by
  let rem := remaining c w s h.divisorPos
  obtain ⟨extra, hn⟩ := Nat.exists_eq_add_of_le hle
  have ht := iter_remaining_terminal c w s h
  have hp := MarkState.iter_terminal c w extra (s.iter c w rem) ht.1 ht.2
  dsimp only at ht hp ⊢
  rw [hn, MarkState.iter_add]
  exact hp

/-- The first scheduled state has the required resident table invariant. -/
theorem first_cursorInv (c : Cfg) (st : LeanCompCert.Verified.ArrayState.AState)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hkPos : 0 < c.kBound) : CursorInv c (MarkState.first c st) := by
  exact
    { table := by
        intro d hd hdK
        simp only [MarkState.first]
        rw [if_neg (by
          unfold Cfg.winBase Cfg.k1
          omega)]
        exact htable d hd hdK
      divisorPos := by simp [MarkState.first]
      divisorBound := by simp [MarkState.first]; omega }

theorem first_remaining_le_compactMarkBudget (c : Cfg)
    (st : LeanCompCert.Verified.ArrayState.AState) (w : Nat)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hkTwo : 2 ≤ c.kBound) :
    remaining c w (MarkState.first c st)
        (first_cursorInv c st htable (by omega)).divisorPos ≤
      compactMarkBudget c := by
  unfold remaining
  simpa [MarkState.first] using
    remainingAux_start_le_compactMarkBudget c w hkTwo

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMarkReady

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The symbolic countdown connects directly to the literal scheduled body.
Only the explicit finite budget inequality remains to instantiate for a
concrete configuration; no production-size `bodyIter` is reduced by Lean. -/
theorem bodyIter_from_start_terminal_of_budget (c : Cfg) (idx : Nat)
    (st : AState) (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (arun idx st c.body))
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
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
    out.regs rD = c.kBound ∧ c.segLen ≤ out.regs rJ := by
  let cinv := first_cursorInv c st htable hkPos
  let n := remaining c w (MarkState.first c st) cinv.divisorPos
  have hrep := bodyIter_markState_from_start_ready c idx n st w hfirst
    htable hbudget hidxM hsieveM hsieve hmarkM hsegPos hsegM hkPos hkM
    hkNextM hsumM hsinkM hperiodM hwM
  have hterminal := iter_remaining_terminal c w (MarkState.first c st) cinv
  dsimp only at hterminal ⊢
  constructor
  · exact hrep.divisor.trans hterminal.1
  · rw [hrep.multiple]
    exact hterminal.2

end LeanCompCert.Ports.CDEMAbelMarkTermination
