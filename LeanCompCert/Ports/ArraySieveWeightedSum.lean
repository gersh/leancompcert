import LeanCompCert.Ports.ArraySieveCount

/-!
# A proved array sieve with a weighted prime sum

This is the finite-computation companion to `ArraySieveCount`.  It uses the
same proved smallest-factor sieve, but its final pass accumulates

`weight / p + bonus`

for every prime `p < len`.  The division is executed through an explicit
nonzero clamp even on inactive rows, so the source and emitted C program have
no division-by-zero escape hatch.
-/

namespace LeanCompCert.Ports.ArraySieveWeightedSum

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySieveCount

def regCount : Nat := 14

/-- The count sieve with a final weighted accumulation pass.  Register `12`
holds the explicitly positive divisor clamp; register `13` holds the row
weight before it is gated by primality. -/
def sieveWeightedBody (bound len weight bonus : Nat) : List AInstr :=
  [ .scalar (.binop 1 .urem .idx (.lit len))
  , .scalar (.binop 2 .udiv .idx (.lit len))
  , .scalar (.binop 3 .lt (.reg 2) (.lit bound))
  , .scalar (.binop 4 .add (.reg 2) (.lit 2))
  , .load 5 1
  , .scalar (.binop 6 .mul (.reg 4) (.reg 4))
  , .scalar (.binop 6 .le (.reg 6) (.reg 1))
  , .scalar (.binop 7 .urem (.reg 1) (.reg 4))
  , .scalar (.binop 7 .eq (.reg 7) (.lit 0))
  , .scalar (.binop 8 .eq (.reg 5) (.lit 0))
  , .scalar (.binop 9 .mul (.reg 3) (.reg 8))
  , .scalar (.binop 9 .mul (.reg 9) (.reg 6))
  , .scalar (.binop 9 .mul (.reg 9) (.reg 7))
  , .scalar (.binop 10 .mul (.reg 9) (.reg 4))
  , .scalar (.binop 11 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 5))
  , .scalar (.binop 10 .add (.reg 10) (.reg 11))
  , .store 1 10
  , .scalar (.binop 11 .sub (.lit 1) (.reg 3))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 8))
  , .scalar (.binop 10 .ge (.reg 1) (.lit 2))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 10))
    -- safe divisor: `n` on active rows and `n+1` at `n=0,1`
  , .scalar (.binop 12 .sub (.lit 1) (.reg 10))
  , .scalar (.binop 12 .add (.reg 1) (.reg 12))
  , .scalar (.binop 13 .udiv (.lit weight) (.reg 12))
  , .scalar (.binop 13 .add (.reg 13) (.lit bonus))
  , .scalar (.binop 13 .mul (.reg 11) (.reg 13))
  , .scalar (.binop 0 .add (.reg 0) (.reg 13))
  ]

def sieveWeightedProgram (bound len weight bonus : Nat) : AProgram :=
  { regCount := regCount
  , arrayLen := len
  , loopCount := (bound + 1) * len
  , init := []
  , body := sieveWeightedBody bound len weight bonus
  , epilogue := []
  , output := 0 }

/-- The same proved weighted sieve followed by a one-word budget verdict.
The emitted result is `0` exactly when the complete weighted prime sum fits
`budget`; no prime predicate or large list is reduced by the Lean kernel. -/
def sieveWeightedBudgetProgram (bound len weight bonus budget : Nat) : AProgram :=
  { sieveWeightedProgram bound len weight bonus with
    epilogue := [.scalar (.binop 0 .gt (.reg 0) (.lit budget))] }

abbrev Abs := (Nat → Nat) × Nat

def obs (s : AState) : Abs := (s.arr, s.regs 0)

def rowWeight (weight bonus n : Nat) : Nat := weight / n + bonus

def gstep (bound len weight bonus t : Nat) (a : Abs) : Abs :=
  ( fun c =>
      if c = t % len then
        (if t / len < bound then
            Sieve.spfStep (t % len) (a.1 (t % len)) (t / len)
          else a.1 (t % len))
      else a.1 c
  , (a.2 +
      (if (¬ t / len < bound ∧ a.1 (t % len) = 0) ∧ 2 ≤ t % len then
          rowWeight weight bonus (t % len)
        else 0)) % M )

private theorem sel_eq (q bound n v : Nat) :
    (if ((q < bound ∧ v = 0) ∧ (q + 2) * (q + 2) ≤ n) ∧ n % (q + 2) = 0 then
        q + 2 else v)
      = (if q < bound then Sieve.spfStep n v q else v) := by
  unfold Sieve.spfStep
  by_cases h1 : q < bound
  · rw [if_pos h1]
    by_cases h2 : v = 0
    · by_cases h3 : (q + 2) * (q + 2) ≤ n
      · by_cases h4 : n % (q + 2) = 0
        · rw [if_pos ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, if_pos ⟨h2, h3, h4⟩]
        · rw [if_neg (fun h => h4 h.2), if_neg (fun h => h4 h.2.2)]
      · rw [if_neg (fun h => h3 h.1.2), if_neg (fun h => h3 h.2.1)]
    · rw [if_neg (fun h => h2 h.1.1.2), if_neg (fun h => h2 h.1)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.1.1)]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
theorem body_spec (bound len weight bonus t : Nat) (s : AState)
    (h0 : 0 < len) (hlm : len < M) (ht : t < M) (hq : t / len ≤ bound)
    (hB : (bound + 2) * (bound + 2) < M) (hw : weight < M)
    (hb : bonus < M) (hP : ∀ c, s.arr c < M) :
    AllDefined len t s (sieveWeightedBody bound len weight bonus) ∧
      (arun t s (sieveWeightedBody bound len weight bonus)).arr =
        (gstep bound len weight bonus t (obs s)).1 ∧
      (arun t s (sieveWeightedBody bound len weight bonus)).regs 0 =
        (gstep bound len weight bonus t (obs s)).2 := by
  have hva : s.arr (t % len) < M := hP _
  have htM : t % M = t := Nat.mod_eq_of_lt ht
  have hlmm : len % M = len := Nat.mod_eq_of_lt hlm
  have hlne : ¬ (len = 0) := by omega
  have hnlt : t % len < len := Nat.mod_lt _ h0
  have hb2 : bound + 2 ≤ (bound + 2) * (bound + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hdlt : t / len + 2 < M := by omega
  have hnltM : t % len < M := by omega
  have hqltM : t / len < M := by omega
  have hnM : t % len % M = t % len := Nat.mod_eq_of_lt hnltM
  have hqM : t / len % M = t / len := Nat.mod_eq_of_lt hqltM
  have hboundM : bound % M = bound := Nat.mod_eq_of_lt (by omega)
  have hweightM : weight % M = weight := Nat.mod_eq_of_lt hw
  have hbonusM : bonus % M = bonus := Nat.mod_eq_of_lt hb
  have h2M : (2:Nat) % M = 2 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hzeroM : (0:Nat) % M = 0 := by decide
  have hdM : (t / len + 2) % M = t / len + 2 := Nat.mod_eq_of_lt hdlt
  have hddlt : (t / len + 2) * (t / len + 2) < M := by
    have h : (t / len + 2) * (t / len + 2) ≤ (bound + 2) * (bound + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hddM : ((t / len + 2) * (t / len + 2)) % M =
      (t / len + 2) * (t / len + 2) := Nat.mod_eq_of_lt hddlt
  have hremlt : t % len % (t / len + 2) < M := by
    have h : t % len % (t / len + 2) < t / len + 2 := Nat.mod_lt _ (by omega)
    omega
  have hremM : (t % len % (t / len + 2)) % M = t % len % (t / len + 2) :=
    Nat.mod_eq_of_lt hremlt
  have hvaM : s.arr (t % len) % M = s.arr (t % len) := Nat.mod_eq_of_lt hva
  have hsafePos : 0 < t % len + (1 - if 2 ≤ t % len then 1 else 0) := by
    split <;> omega
  have hsafeLt : t % len + (1 - if 2 ≤ t % len then 1 else 0) < M := by
    split <;> omega
  have hsafeM : (t % len + (1 - if 2 ≤ t % len then 1 else 0)) % M =
      t % len + (1 - if 2 ≤ t % len then 1 else 0) := Nat.mod_eq_of_lt hsafeLt
  have hsafeNe : ¬ (t % len + (1 - if 2 ≤ t % len then 1 else 0) = 0) := by
    omega
  have hsafeM' : (t % len + if 2 ≤ t % len then 0 else 1) % M =
      t % len + if 2 ≤ t % len then 0 else 1 := by
    by_cases hn2 : 2 ≤ t % len <;> simp [hn2, Nat.mod_eq_of_lt, hnltM]
    apply Nat.mod_eq_of_lt
    omega
  have hsafeNe' : ¬ ((t % len + if 2 ≤ t % len then 0 else 1) % M = 0) := by
    rw [hsafeM']
    split <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [sieveWeightedBody, AllDefined, ADefined, arun, astep,
      InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, AState.writeArr, RegState.set, Option.getD_some,
      reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true, hlmm, hlne, htM,
      hnM, hqM, hboundM, hweightM, hbonusM, h2M, h1M, hzeroM, hdM, hddM,
      hremM, hvaM, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite,
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]
    simp [hnlt, hsafeM', hsafeNe']
    omega
  · simp only [sieveWeightedBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, RegState.set, Option.getD_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, hlmm, hlne, htM, hnM, hqM,
      hboundM, hweightM, hbonusM, h2M, h1M, hzeroM, hdM, hddM, hremM,
      hvaM, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]
    funext c
    simp only [gstep, obs, sel_eq]
  · simp only [sieveWeightedBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, RegState.set, Option.getD_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, hlmm, hlne, htM, hnM, hqM,
      hboundM, hweightM, hbonusM, h2M, h1M, hzeroM, hdM, hddM, hremM,
      hvaM, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]
    simp only [gstep, obs, rowWeight]
    rw [hsafeM']
    simp [hsafeNe']
    by_cases hn2 : 2 ≤ t % len
    · have hnne : ¬ t % len = 0 := by omega
      simp [hn2, hnne, Nat.add_mod]
      split <;> simp [Nat.add_mod]
    · simp [hn2]

def CellsFit (s : AState) : Prop := ∀ c, s.arr c < M

theorem body_closed (bound len weight bonus t : Nat) (s : AState)
    (h0 : 0 < len) (hlm : len < M) (ht : t < M) (hq : t / len ≤ bound)
    (hB : (bound + 2) * (bound + 2) < M) (hw : weight < M)
    (hb : bonus < M) (hP : CellsFit s) :
    CellsFit (arun t s (sieveWeightedBody bound len weight bonus)) := by
  intro c
  rw [(body_spec bound len weight bonus t s h0 hlm ht hq hB hw hb hP).2.1]
  simp only [gstep, obs]
  by_cases hc : c = t % len
  · rw [if_pos hc]
    by_cases hq' : t / len < bound
    · rw [if_pos hq']
      unfold Sieve.spfStep
      split
      · have hb2 : bound + 2 ≤ (bound + 2) * (bound + 2) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · exact hP _
    · rw [if_neg hq']
      exact hP _
  · rw [if_neg hc]
    exact hP c

theorem markPass (bound len weight bonus q : Nat) (hq : q < bound)
    (h0 : 0 < len) (A : Nat → Nat) (acc : Nat) (hacc : acc < M) :
    ∀ k, k ≤ len →
      (List.range k).foldl
          (fun a r => gstep bound len weight bonus (q * len + r) a) (A, acc)
        = ((fun c => if c < k then Sieve.spfStep c (A c) q else A c), acc) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hklt : k < len := by omega
      have hmod : (q * len + k) % len = k := by
        rw [Nat.mul_comm q len, Nat.mul_add_mod, Nat.mod_eq_of_lt hklt]
      have hdiv : (q * len + k) / len = q := by
        rw [Nat.mul_comm q len, Nat.mul_add_div h0, Nat.div_eq_of_lt hklt,
          Nat.add_zero]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      simp only [gstep, hmod, hdiv, if_pos hq, if_neg (Nat.lt_irrefl k),
        Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c
        by_cases hc : c = k
        · subst hc
          rw [if_pos rfl, if_pos (Nat.lt_succ_self c)]
        · rw [if_neg hc]
          by_cases hc2 : c < k
          · rw [if_pos hc2, if_pos (by omega)]
          · rw [if_neg hc2, if_neg (by omega)]
      · rw [if_neg (fun hh => hh.1.1 hq), Nat.add_zero]
        exact Nat.mod_eq_of_lt hacc

def weightedPrefix (k weight bonus : Nat) (A : Nat → Nat) : Nat :=
  (List.range k).foldl (fun acc n =>
    acc + if 2 ≤ n ∧ A n = 0 then rowWeight weight bonus n else 0) 0

private theorem weightedPrefix_succ (k weight bonus : Nat) (A : Nat → Nat) :
    weightedPrefix (k + 1) weight bonus A = weightedPrefix k weight bonus A +
      if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0 := by
  simp [weightedPrefix, List.range_succ, List.foldl_append]

private theorem weightedPrefix_le (k weight bonus : Nat) (A : Nat → Nat) :
    weightedPrefix k weight bonus A ≤ k * (weight + bonus) := by
  induction k with
  | zero => simp [weightedPrefix]
  | succ k ih =>
      rw [weightedPrefix_succ]
      have hrow : (if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0) ≤
          weight + bonus := by
        split
        · simp only [rowWeight]
          have := Nat.div_le_self weight k
          omega
        · omega
      calc
        weightedPrefix k weight bonus A +
              (if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0) ≤
            k * (weight + bonus) + (weight + bonus) :=
          Nat.add_le_add ih hrow
        _ = (k + 1) * (weight + bonus) := by
          rw [Nat.add_mul]
          simp

theorem accPass (bound len weight bonus : Nat) (h0 : 0 < len)
    (hfit : len * (weight + bonus) < M) (A : Nat → Nat) :
    ∀ k, k ≤ len →
      (List.range k).foldl
          (fun a r => gstep bound len weight bonus (bound * len + r) a) (A, 0)
        = (A, weightedPrefix k weight bonus A) := by
  intro k
  induction k with
  | zero => intro _; simp [weightedPrefix]
  | succ k ih =>
      intro hk
      have hklt : k < len := by omega
      have hmod : (bound * len + k) % len = k := by
        rw [Nat.mul_comm bound len, Nat.mul_add_mod, Nat.mod_eq_of_lt hklt]
      have hdiv : (bound * len + k) / len = bound := by
        rw [Nat.mul_comm bound len, Nat.mul_add_div h0, Nat.div_eq_of_lt hklt,
          Nat.add_zero]
      rw [weightedPrefix_succ, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [gstep, hmod, hdiv, if_neg (Nat.lt_irrefl bound), Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c
        by_cases hc : c = k
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
      · have hpref := weightedPrefix_le k weight bonus A
        simp only [Nat.lt_irrefl, not_false_eq_true, true_and]
        have hif : (if A k = 0 ∧ 2 ≤ k then rowWeight weight bonus k else 0) =
            (if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0) := by
          by_cases ha : A k = 0 <;> by_cases hn : 2 ≤ k <;> simp [ha, hn]
        rw [hif]
        apply Nat.mod_eq_of_lt
        have hrowBound : (if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0) ≤
            weight + bonus := by
          split
          · simp only [rowWeight]
            have := Nat.div_le_self weight k
            omega
          · omega
        have hmul : (k + 1) * (weight + bonus) ≤ len * (weight + bonus) :=
          Nat.mul_le_mul_right _ hk
        have hsum : weightedPrefix k weight bonus A +
              (if 2 ≤ k ∧ A k = 0 then rowWeight weight bonus k else 0) ≤
            (k + 1) * (weight + bonus) := by
          calc
            _ ≤ k * (weight + bonus) + (weight + bonus) :=
              Nat.add_le_add hpref hrowBound
            _ = (k + 1) * (weight + bonus) := by
              rw [Nat.add_mul]
              simp
        exact Nat.lt_of_le_of_lt hsum (Nat.lt_of_le_of_lt hmul hfit)

theorem markRounds (bound len weight bonus : Nat) (h0 : 0 < len)
    (A : Nat → Nat) : ∀ j, j ≤ bound →
      (List.range j).foldl
          (LeanCompCert.Ports.BlockedFold.block len
            (fun a t => gstep bound len weight bonus t a)) (A, 0)
        = ((fun c => if c < len then
              (List.range j).foldl (Sieve.spfStep c) (A c) else A c), 0) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega), LeanCompCert.Ports.BlockedFold.block_eq_shift,
        markPass bound len weight bonus j (by omega) h0 _ 0 (by
          have := ArrayFoldBridge.one_lt_M; omega) len (Nat.le_refl len)]
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      funext c
      by_cases hc : c < len
      · rw [if_pos hc, if_pos hc, if_pos hc, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
      · rw [if_neg hc, if_neg hc, if_neg hc]

/-- Mathematical weighted sum over the finite prime predicate used by the
proved sieve. -/
def primeWeightedSum (len weight bonus : Nat) : Nat :=
  (((List.range len).filter
      (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n))).map
    (rowWeight weight bonus)).sum

/-- Opaque rewrite interface for consumers; using this theorem avoids
definitionally reducing a large concrete `List.range`. -/
theorem primeWeightedSum_eq (len weight bonus : Nat) :
    primeWeightedSum len weight bonus =
      ((((List.range len).filter
        (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n))).map
      (rowWeight weight bonus)).sum) := rfl

private theorem foldl_if_eq_filter_map_sum (xs : List Nat) (p : Nat → Prop)
    [DecidablePred p] (f : Nat → Nat) :
    xs.foldl (fun acc n => acc + if p n then f n else 0) 0 =
      ((xs.filter p).map f).sum := by
  have hgen : ∀ (ys : List Nat) (init : Nat),
      ys.foldl (fun acc n => acc + if p n then f n else 0) init =
        init + ((ys.filter p).map f).sum := by
    intro ys
    induction ys with
    | nil => intro init; simp
    | cons x ys ih =>
        intro init
        rw [List.foldl_cons, ih]
        by_cases hx : p x <;> simp [hx, Nat.add_assoc]
  simpa using hgen xs 0

private theorem foldl_eq_of_mem {α β : Type} (f g : α → β → α)
    (xs : List β) (init : α) (h : ∀ a x, x ∈ xs → f a x = g a x) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h init x (by simp)]
      apply ih
      intro a y hy
      exact h a y (by simp [hy])

set_option maxHeartbeats 1000000 in
theorem sieveWeightedProgram_denote (bound len weight bonus : Nat)
    (h0 : 0 < len) (hlm : len < M) (hLC : (bound + 1) * len < M)
    (hB : (bound + 2) * (bound + 2) < M)
    (hcover : len ≤ (bound + 2) * (bound + 2))
    (hw : weight < M) (hb : bonus < M)
    (hfit : len * (weight + bonus) < M) :
    (sieveWeightedProgram bound len weight bonus).denote =
      some (primeWeightedSum len weight bonus) := by
  have hstep : ∀ index s,
      index < (sieveWeightedProgram bound len weight bonus).loopCount →
      CellsFit s →
      denoteAInstrs (sieveWeightedProgram bound len weight bonus).arrayLen index s
          (sieveWeightedProgram bound len weight bonus).body =
        some (arun index s (sieveWeightedBody bound len weight bonus)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by
        rw [Nat.mul_comm]
        exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact denoteAInstrs_eq_arun len index _ s
      (body_spec bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs).1
  have hclosed : ∀ index s,
      index < (sieveWeightedProgram bound len weight bonus).loopCount →
      CellsFit s → CellsFit (arun index s (sieveWeightedBody bound len weight bonus)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact body_closed bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs
  have hobs : ∀ index s,
      index < (sieveWeightedProgram bound len weight bonus).loopCount →
      CellsFit s →
      obs (arun index s (sieveWeightedBody bound len weight bonus)) =
        gstep bound len weight bonus index (obs s) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    have hs := body_spec bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs
    exact Prod.ext hs.2.1 hs.2.2
  have hbridge :=
    AProgram.denote_eq_obs_foldl_mem
      (sieveWeightedProgram bound len weight bonus) CellsFit
      (fun index s => arun index s (sieveWeightedBody bound len weight bonus))
      obs (gstep bound len weight bonus) Prod.snd initialAState rfl
      (fun c => by have := ArrayFoldBridge.one_lt_M; simp [initialAState]; omega)
      hstep hclosed hobs (fun s _ => rfl)
  rw [hbridge]
  rw [show (sieveWeightedProgram bound len weight bonus).loopCount =
      (bound + 1) * len from rfl,
    LeanCompCert.Ports.BlockedFold.foldl_range_mul (bound + 1) len
      (fun a index => gstep bound len weight bonus index a) (obs initialAState)]
  have hinit : obs initialAState = ((fun _ => 0), 0) := rfl
  rw [hinit, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    markRounds bound len weight bonus h0 (fun _ => 0) bound (Nat.le_refl bound),
    LeanCompCert.Ports.BlockedFold.block_eq_shift,
    accPass bound len weight bonus h0 hfit _ len (Nat.le_refl len)]
  congr 1
  unfold weightedPrefix primeWeightedSum
  rw [← foldl_if_eq_filter_map_sum]
  apply foldl_eq_of_mem
  intro acc n hn
  have hnlt : n < len := List.mem_range.mp hn
  simp only [if_pos hnlt]
  congr 1
  by_cases h2 : 2 ≤ n
  · simp only [h2, true_and]
    have hc : n < (bound + 2) * (bound + 2) := by omega
    have hiff := ArraySieveCount.spfScan_eq_zero_iff bound n h2 hc
    unfold Sieve.spfScan at hiff
    by_cases hs : (List.range bound).foldl (Sieve.spfStep n) 0 = 0
    · rw [if_pos hs, if_pos (hiff.mp hs)]
    · rw [if_neg hs, if_neg]
      exact fun hp => hs (hiff.mpr hp)
  · simp [h2]

set_option maxHeartbeats 1000000 in
/-- The budget-verdict form denotes the comparison against the mathematical
weighted prime sum.  Its loop proof is the same size-independent simulation
as `sieveWeightedProgram_denote`; only the final comparison differs. -/
theorem sieveWeightedBudgetProgram_denote
    (bound len weight bonus budget : Nat)
    (h0 : 0 < len) (hlm : len < M) (hLC : (bound + 1) * len < M)
    (hB : (bound + 2) * (bound + 2) < M)
    (hcover : len ≤ (bound + 2) * (bound + 2))
    (hw : weight < M) (hb : bonus < M)
    (hfit : len * (weight + bonus) < M) (hbudgetM : budget < M) :
    (sieveWeightedBudgetProgram bound len weight bonus budget).denote =
      some (if primeWeightedSum len weight bonus > budget then 1 else 0) := by
  have hstep : ∀ index s,
      index < (sieveWeightedBudgetProgram bound len weight bonus budget).loopCount →
      CellsFit s →
      denoteAInstrs
          (sieveWeightedBudgetProgram bound len weight bonus budget).arrayLen index s
          (sieveWeightedBudgetProgram bound len weight bonus budget).body =
        some (arun index s (sieveWeightedBody bound len weight bonus)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by
        rw [Nat.mul_comm]
        exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact denoteAInstrs_eq_arun len index _ s
      (body_spec bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs).1
  have hclosed : ∀ index s,
      index < (sieveWeightedBudgetProgram bound len weight bonus budget).loopCount →
      CellsFit s → CellsFit (arun index s (sieveWeightedBody bound len weight bonus)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact body_closed bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs
  have hobs : ∀ index s,
      index < (sieveWeightedBudgetProgram bound len weight bonus budget).loopCount →
      CellsFit s →
      obs (arun index s (sieveWeightedBody bound len weight bonus)) =
        gstep bound len weight bonus index (obs s) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    have hs := body_spec bound len weight bonus index s h0 hlm (by omega) hqle hB hw hb hPs
    exact Prod.ext hs.2.1 hs.2.2
  have hbridge :=
    AProgram.denote_eq_obs_foldl_mem
      (sieveWeightedBudgetProgram bound len weight bonus budget) CellsFit
      (fun index s => arun index s (sieveWeightedBody bound len weight bonus))
      obs (gstep bound len weight bonus)
      (fun a => if a.2 > budget then 1 else 0) initialAState rfl
      (fun c => by have := ArrayFoldBridge.one_lt_M; simp [initialAState]; omega)
      hstep hclosed hobs (fun s _ => by
        simp only [sieveWeightedBudgetProgram, sieveWeightedProgram,
          denoteAInstrs, denoteAInstr,
          LeanCompCert.Verified.Reflect.denoteInstr, denoteOperand, denoteOp,
          Option.bind_some, Option.map_some, Function.comp_apply]
        simp only [Nat.mod_eq_of_lt hbudgetM]
        simp [RegState.set, obs])
  rw [hbridge]
  rw [show (sieveWeightedBudgetProgram bound len weight bonus budget).loopCount =
      (bound + 1) * len from rfl,
    LeanCompCert.Ports.BlockedFold.foldl_range_mul (bound + 1) len
      (fun a index => gstep bound len weight bonus index a) (obs initialAState)]
  have hinit : obs initialAState = ((fun _ => 0), 0) := rfl
  rw [hinit, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    markRounds bound len weight bonus h0 (fun _ => 0) bound (Nat.le_refl bound),
    LeanCompCert.Ports.BlockedFold.block_eq_shift,
    accPass bound len weight bonus h0 hfit _ len (Nat.le_refl len)]
  congr 1
  apply congrArg (fun total => if total > budget then 1 else 0)
  unfold weightedPrefix primeWeightedSum
  rw [← foldl_if_eq_filter_map_sum]
  apply foldl_eq_of_mem
  intro acc n hn
  have hnlt : n < len := List.mem_range.mp hn
  simp only [if_pos hnlt]
  congr 1
  by_cases h2 : 2 ≤ n
  · simp only [h2, true_and]
    have hc : n < (bound + 2) * (bound + 2) := by omega
    have hiff := ArraySieveCount.spfScan_eq_zero_iff bound n h2 hc
    unfold Sieve.spfScan at hiff
    by_cases hs : (List.range bound).foldl (Sieve.spfStep n) 0 = 0
    · rw [if_pos hs, if_pos (hiff.mp hs)]
    · rw [if_neg hs, if_neg]
      exact fun hp => hs (hiff.mpr hp)
  · simp [h2]

set_option maxHeartbeats 1000000 in
theorem sieveWeightedBody_wf (bound len weight bonus : Nat) :
    ∀ a ∈ sieveWeightedBody bound len weight bonus, a.WF regCount := by
  intro a ha
  simp only [sieveWeightedBody, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> simp +decide [AInstr.WF, Instr.WF, Operand.WF, regCount]

theorem sieveWeightedProgram_wf (bound len weight bonus : Nat) :
    (sieveWeightedProgram bound len weight bonus).WF :=
  ⟨by show 0 < 14; omega, (by intro a ha; cases ha),
    sieveWeightedBody_wf bound len weight bonus, (by intro a ha; cases ha)⟩

theorem sieveWeightedBudgetProgram_wf
    (bound len weight bonus budget : Nat) :
    (sieveWeightedBudgetProgram bound len weight bonus budget).WF := by
  refine ⟨by change 0 < 14; omega, ?_,
    sieveWeightedBody_wf bound len weight bonus, ?_⟩
  · intro a ha
    cases ha
  · intro a ha
    simp only [sieveWeightedBudgetProgram, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    subst a
    simp +decide [sieveWeightedBudgetProgram, sieveWeightedProgram,
      AInstr.WF, Instr.WF, Operand.WF, regCount]

end LeanCompCert.Ports.ArraySieveWeightedSum
