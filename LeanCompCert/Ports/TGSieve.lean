import LeanCompCert.Ports.TGSieveTable
import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.Frontend
import LeanCompCert.Verified.Rolled

/-!
# Stage (a) of the Helfgott–Platt prime ladder: the progression sieve

The reference producer `tg_goldbach_ladder_native.cpp`
(arXiv:1305.3062v2, sections 2--4) searches the arithmetic progression
`k · 2 ⁿ + 1` for Proth primes.  Before the expensive Proth test it removes
every candidate divisible by a prime below `16000`, via `ProgressionSieve`.

The mathematical content of that stage is one congruence fact
(`dvd_proth_iff`): for an **odd** modulus `p` the whole progression meets
`p` in a single residue class, namely the class of the `r` with
`p ∣ r · 2 ⁿ + 1`, so divisibility of a 90-bit Proth number is decided by a
64-bit remainder `k % p`.  That is what brings the stage inside the proved
`u64` fragment at all: no value the sieve looks at is ever wider than a
machine word, at any ladder height.

## What is here

* `dvd_proth_iff` — the congruence fact.  Odd modulus only; primality is
  never used, exactly as in the reference, whose `forbiddenResidue` is
  `p − (2ⁿ)⁻¹ mod p`.
* `sieveTable_valid` — the shipped table (`TGSieveTable`) really does list
  odd moduli with their forbidden residues.  Decided in the kernel.
* `hitCount_eq_zero_iff` — **the specification**: a candidate survives
  exactly when it is nonzero and no tabulated modulus divides its Proth
  number.  This is `ProgressionSieve::makeBlock`'s postcondition.
* `sieveProgram_denote` — **the bridge**: a `Reflect.Program` whose
  denotation is the survivor count of a window, proved by simulation.  Both
  the statement and the proof are `∀`-quantified in the window's start and
  length, so the bridge costs the same at a window of 10 and at a window of
  2⁵².

## What is *not* here

The reference sieves a **block** into a mutable byte array, which is why it
costs `O(1)` amortized operations per candidate.  The proved emission
fragment (`Reflect`/`Rolled`) has registers and no memory — `ArrayState`
and `MemFragment` model memory, but no compile-to-C bridge joins them — so
the expressible form is the memoryless one: test each candidate against
every tabulated modulus.  That is the same predicate computed by a
different algorithm, and it is slower by the ratio measured in
`bench/tg_goldbach.sh`.
-/

namespace LeanCompCert.Ports.TGSieve

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

/-! ## Proth numbers and the congruence fact -/

/-- The Proth number `k · 2 ⁿ + 1` of the reference producer. -/
def prothNumber (n k : Nat) : Nat := k * 2 ^ n + 1

/-- An odd modulus dividing `2 * m` divides `m`. -/
theorem dvd_of_odd_dvd_two_mul {p m : Nat} (hodd : p % 2 = 1)
    (h : p ∣ 2 * m) : p ∣ m := by
  obtain ⟨q, hq⟩ := h
  have hq2 : q % 2 = 0 := by
    have hz : (p * q) % 2 = 0 := by
      rw [← hq]; exact Nat.mul_mod_right 2 m
    rw [Nat.mul_mod, hodd, Nat.one_mul] at hz
    omega
  obtain ⟨t, ht⟩ : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq2
  refine ⟨t, ?_⟩
  have h2 : 2 * m = 2 * (p * t) := by
    calc 2 * m = p * q := hq
      _ = p * (2 * t) := by rw [ht]
      _ = 2 * (p * t) := by rw [Nat.mul_left_comm]
  omega

/-- An odd modulus dividing `2 ⁿ * m` divides `m`. -/
theorem dvd_of_odd_dvd_two_pow_mul {p : Nat} (hodd : p % 2 = 1) :
    ∀ (n m : Nat), p ∣ 2 ^ n * m → p ∣ m := by
  intro n
  induction n with
  | zero => intro m h; simpa using h
  | succ n ih =>
      intro m h
      refine ih m (dvd_of_odd_dvd_two_mul hodd ?_)
      have e : 2 ^ (n + 1) * m = 2 * (2 ^ n * m) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
      rwa [e] at h

/-- Splitting a Proth number along division by `p`. -/
private theorem proth_split (n k p : Nat) :
    prothNumber n k = p * (k / p * 2 ^ n) + (k % p * 2 ^ n + 1) := by
  unfold prothNumber
  calc k * 2 ^ n + 1 = (p * (k / p) + k % p) * 2 ^ n + 1 := by
        rw [Nat.div_add_mod]
    _ = p * (k / p * 2 ^ n) + (k % p * 2 ^ n + 1) := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- `p ∣ a + b` and `p ∣ a` give `p ∣ b`. -/
private theorem dvd_of_dvd_add_left {p a b : Nat} (h : p ∣ a + b)
    (ha : p ∣ a) : p ∣ b := by
  have hsub := Nat.dvd_sub h ha
  rwa [Nat.add_sub_cancel_left] at hsub

/--
**The congruence fact behind the progression sieve.**

For an odd modulus `p` and a residue `r` with `p ∣ r · 2 ⁿ + 1`, the modulus
divides the Proth number of `k` exactly when `k ≡ r (mod p)`.

Primality of `p` is never used; oddness is, and is exactly what the
reference's `sourceSievePrimes` enforces by skipping `p = 2`.  Nothing in
the statement bounds the width of `k · 2 ⁿ + 1`: this is the equation that
lets a 64-bit machine sieve a 90-bit progression.
-/
theorem dvd_proth_iff {p n k r : Nat} (hodd : p % 2 = 1)
    (hr : p ∣ prothNumber n r) :
    p ∣ prothNumber n k ↔ k % p = r % p := by
  have key : ∀ a b : Nat, b ≤ a → p ∣ prothNumber n a → p ∣ prothNumber n b →
      a % p = b % p := by
    intro a b hle ha hb
    have hsub : p ∣ prothNumber n a - prothNumber n b := Nat.dvd_sub ha hb
    have he : prothNumber n a - prothNumber n b = 2 ^ n * (a - b) := by
      unfold prothNumber
      rw [Nat.mul_comm (2 ^ n) (a - b), Nat.sub_mul]
      have hmono : b * 2 ^ n ≤ a * 2 ^ n := Nat.mul_le_mul_right _ hle
      omega
    rw [he] at hsub
    obtain ⟨t, ht⟩ := dvd_of_odd_dvd_two_pow_mul hodd n (a - b) hsub
    have hab : a = b + p * t := by omega
    rw [hab, Nat.add_mul_mod_self_left]
  constructor
  · intro hk
    rcases Nat.le_total r k with hle | hle
    · exact key k r hle hk hr
    · exact (key r k hle hr hk).symm
  · intro hkr
    have hrsplit : p ∣ r % p * 2 ^ n + 1 :=
      dvd_of_dvd_add_left (by rw [← proth_split]; exact hr) ⟨r / p * 2 ^ n, rfl⟩
    rw [proth_split n k p, hkr]
    exact Nat.dvd_add ⟨k / p * 2 ^ n, rfl⟩ hrsplit

/-! ## The table and its validity -/

/-- A tabulated row is usable: a nonzero, machine-width, odd modulus with a
reduced forbidden residue that really does kill the progression. -/
def RowValid (pr : Nat × Nat) : Prop :=
  0 < pr.1 ∧ pr.1 < M ∧ pr.2 < pr.1 ∧ pr.1 % 2 = 1 ∧
    pr.1 ∣ prothNumber prothExponent pr.2

instance (pr : Nat × Nat) : Decidable (RowValid pr) := by
  unfold RowValid; infer_instance

/-- Every shipped row satisfies its defining property.  Decided in the
kernel over all 1861 rows; no evaluation axiom is involved. -/
theorem sieveTable_valid : ∀ pr ∈ sieveTable, RowValid pr := by
  have h : sieveTable.all (fun pr => decide (RowValid pr)) = true := by
    decide +kernel
  intro pr hpr
  have hd := (List.all_eq_true.mp h) pr hpr
  exact of_decide_eq_true hd

/-! ## The survivor predicate -/

/-- One tabulated modulus's verdict on `k`: `1` if it kills the candidate. -/
def hitOf (k : Nat) (pr : Nat × Nat) : Nat :=
  if k % pr.1 = pr.2 then 1 else 0

/--
The reference's `block.survivor` cell, counted rather than flagged: the
number of reasons `k` is rejected.  The seed `if k = 0 then 1 else 0` is
`makeBlock`'s `if (begin == 0) block.survivor[0] = 0` — the candidate
`k = 0` gives the Proth number `1`.
-/
def hitCount (table : List (Nat × Nat)) (k : Nat) : Nat :=
  table.foldl (fun acc pr => acc + hitOf k pr) (if k = 0 then 1 else 0)

/-- `1` when `k` survives the sieve, `0` otherwise. -/
def survivorBit (table : List (Nat × Nat)) (k : Nat) : Nat :=
  if hitCount table k = 0 then 1 else 0

/-- A sum of naturals accumulated by `foldl` vanishes exactly when the seed
and every summand do. -/
private theorem foldl_add_eq_zero_iff {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (init : Nat),
      l.foldl (fun acc x => acc + f x) init = 0 ↔
        init = 0 ∧ ∀ x ∈ l, f x = 0 := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons x rest ih =>
      intro init
      rw [List.foldl_cons, ih (init + f x)]
      constructor
      · rintro ⟨hz, hrest⟩
        refine ⟨by omega, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact hrest y hy
      · rintro ⟨hz, hall⟩
        refine ⟨?_, fun y hy => hall y (List.mem_cons_of_mem _ hy)⟩
        rw [hz, hall x (List.mem_cons_self ..)]

/--
**The sieve stage's specification.**

A candidate survives exactly when it is nonzero and no tabulated modulus
divides its Proth number — `ProgressionSieve::makeBlock`'s postcondition,
stated about the 90-bit numbers and decided by 64-bit remainders.
-/
theorem hitCount_eq_zero_iff (table : List (Nat × Nat))
    (hvalid : ∀ pr ∈ table, RowValid pr) (k : Nat) :
    hitCount table k = 0 ↔
      k ≠ 0 ∧ ∀ pr ∈ table, ¬ pr.1 ∣ prothNumber prothExponent k := by
  rw [hitCount, foldl_add_eq_zero_iff]
  constructor
  · rintro ⟨hseed, hall⟩
    refine ⟨fun hk => by simp [hk] at hseed, ?_⟩
    intro pr hpr hdvd
    obtain ⟨_, _, hrlt, hodd, hrdvd⟩ := hvalid pr hpr
    have hz := hall pr hpr
    rw [hitOf, if_pos] at hz
    · exact absurd hz (by decide)
    · rw [(dvd_proth_iff hodd hrdvd).mp hdvd, Nat.mod_eq_of_lt hrlt]
  · rintro ⟨hk, hno⟩
    refine ⟨by simp [hk], ?_⟩
    intro pr hpr
    obtain ⟨_, _, hrlt, hodd, hrdvd⟩ := hvalid pr hpr
    rw [hitOf, if_neg]
    intro hmod
    exact hno pr hpr ((dvd_proth_iff hodd hrdvd).mpr
      (by rw [hmod, Nat.mod_eq_of_lt hrlt]))

/-! ## The window count -/

/-- The reference's per-block survivor tally over `[start, start + count)`. -/
def survivorCount (table : List (Nat × Nat)) (start count : Nat) : Nat :=
  (List.range count).foldl
    (fun acc i => acc + survivorBit table (start + i)) 0

/-! ## From the machine's modular sums to plain sums

Every accumulator in the fragment wraps at `2⁶⁴`.  These two lemmas say the
wrapping is invisible whenever the true total fits, and they are the only
place where a size hypothesis enters.
-/

private theorem foldl_add_shift {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (a : Nat),
      l.foldl (fun acc x => acc + f x) a =
        a + l.foldl (fun acc x => acc + f x) 0 := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x rest ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih (a + f x), ih (0 + f x)]
      omega

private theorem foldl_add_mod_eq {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (init : Nat),
      init + l.foldl (fun acc x => acc + f x) 0 < M →
        l.foldl (fun acc x => (acc + f x) % M) init =
          init + l.foldl (fun acc x => acc + f x) 0 := by
  intro l
  induction l with
  | nil => intro init _; simp
  | cons x rest ih =>
      intro init hlt
      rw [List.foldl_cons] at hlt
      rw [foldl_add_shift f rest (0 + f x)] at hlt
      rw [List.foldl_cons, Nat.mod_eq_of_lt (by omega),
        ih (init + f x) (by omega), List.foldl_cons,
        foldl_add_shift f rest (0 + f x)]
      omega

/-! ## The register program

Registers: `0` survivor count, `1` the candidate `k`, `2` the hit tally,
`3` scratch.  One tabulated modulus costs three instructions and no
memory.
-/

/-- The three instructions charged by one tabulated modulus. -/
def entryInstrs (pr : Nat × Nat) : List Instr :=
  [ .binop 3 .urem (.reg 1) (.lit pr.1)
  , .binop 3 .eq (.reg 3) (.lit pr.2)
  , .binop 2 .add (.reg 2) (.reg 3) ]

/-- The loop body: form the candidate, seed the tally with the `k = 0`
guard, charge every modulus, and add the survivor bit to the count. -/
def bodyInstrs (table : List (Nat × Nat)) (start : Nat) : List Instr :=
  [ .binop 1 .add .idx (.lit start)
  , .binop 2 .eq (.reg 1) (.lit 0) ]
    ++ table.flatMap entryInstrs
    ++ [ .binop 3 .eq (.reg 2) (.lit 0)
       , .binop 0 .add (.reg 0) (.reg 3) ]

/-- The sieve program over the window `[start, start + count)`. -/
def sieveProgram (table : List (Nat × Nat)) (start count : Nat) : Program := {
  regCount := 4
  loopCount := count
  init := []
  body := bodyInstrs table start
  epilogue := []
  output := 0
}

/-- Every instruction of the body addresses a declared register: the
program is well-formed for every table and window. -/
theorem bodyInstrs_wf (table : List (Nat × Nat)) (start : Nat) :
    ∀ instr ∈ bodyInstrs table start, instr.WF 4 := by
  intro instr hinstr
  unfold bodyInstrs at hinstr
  rcases List.mem_append.mp hinstr with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, trivial, trivial⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨by decide, by decide, trivial⟩
        · exact absurd h List.not_mem_nil
    · obtain ⟨pr, _, hpr⟩ := List.mem_flatMap.mp h
      unfold entryInstrs at hpr
      rcases List.mem_cons.mp hpr with rfl | hpr
      · exact ⟨by decide, by decide, trivial⟩
      · rcases List.mem_cons.mp hpr with rfl | hpr
        · exact ⟨by decide, by decide, trivial⟩
        · rcases List.mem_cons.mp hpr with rfl | hpr
          · exact ⟨by decide, by decide, by decide⟩
          · exact absurd hpr List.not_mem_nil
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by decide, by decide, trivial⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, by decide, by decide⟩
      · exact absurd h List.not_mem_nil

/-- The sieve program is well-formed at every table and window — the only
decidable obligation `Package.Program.toComputation` asks for, and it is
program-sized, not window-sized. -/
theorem sieveProgram_wf (table : List (Nat × Nat)) (start count : Nat) :
    (sieveProgram table start count).WF :=
  ⟨show (0 : Nat) < 4 by decide,
    by intro i h; exact absurd h List.not_mem_nil,
    bodyInstrs_wf table start,
    by intro i h; exact absurd h List.not_mem_nil⟩

/-! ### Simulation

The state reached after each block of the body is written in closed form,
so the `FoldBridge` hypotheses are equalities of register files rather than
a re-execution.
-/

/-- The machine's (wrapping) hit tally, accumulated left to right. -/
def foldHit (k : Nat) : List (Nat × Nat) → Nat → Nat
  | [], acc => acc
  | pr :: rest, acc => foldHit k rest ((acc + hitOf k pr) % M)

/-- The scratch register's value once the table block has run. -/
def lastHit (k : Nat) : List (Nat × Nat) → Nat → Nat
  | [], v => v
  | pr :: rest, _ => lastHit k rest (hitOf k pr)

/-- The candidate produced at loop index `index`. -/
def kAt (start index : Nat) : Nat := (index % M + start % M) % M

/-- The machine's hit tally at loop index `index`. -/
def hitAt (table : List (Nat × Nat)) (start index : Nat) : Nat :=
  foldHit (kAt start index) table (if kAt start index = 0 then 1 else 0)

/-- The survivor bit the machine adds to the count at loop index `index`. -/
def survAt (table : List (Nat × Nat)) (start index : Nat) : Nat :=
  if hitAt table start index = 0 then 1 else 0

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem denoteInstrs_cons (index : Nat) (s : RegState) (i : Instr)
    (rest : List Instr) :
    denoteInstrs index s (i :: rest) =
      (denoteInstr index s i).bind fun s' => denoteInstrs index s' rest := rfl

private theorem denoteInstr_binop_eq (index : Nat) (s : RegState) (dest : Nat)
    (op : Op) (l r : Operand) (v : Nat)
    (hv : denoteOp op (denoteOperand index s l) (denoteOperand index s r)
      = some v) :
    denoteInstr index s (.binop dest op l r) = some (s.set dest v) := by
  show (denoteOp op (denoteOperand index s l) (denoteOperand index s r)).bind
    (fun result => some (s.set dest result)) = _
  rw [hv]
  rfl

private theorem denote_entry (index : Nat) (s : RegState) (pr : Nat × Nat)
    (h : RowValid pr) :
    denoteInstrs index s (entryInstrs pr) =
      some (fun j =>
        if j = 2 then (s 2 + hitOf (s 1) pr) % M
        else if j = 3 then hitOf (s 1) pr
        else s j) := by
  obtain ⟨hpos, hlt, hrlt, _, _⟩ := h
  have hpM : pr.1 % M = pr.1 := Nat.mod_eq_of_lt hlt
  have hne : ¬ pr.1 % M = 0 := by rw [hpM]; exact Nat.ne_of_gt hpos
  have hrM : pr.2 % M = pr.2 := Nat.mod_eq_of_lt (Nat.lt_trans hrlt hlt)
  have hmod : s 1 % pr.1 % M = s 1 % pr.1 :=
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hpos) hlt)
  have h1 : denoteInstr index s (Instr.binop 3 Op.urem (.reg 1) (.lit pr.1))
      = some (s.set 3 (s 1 % pr.1)) :=
    denoteInstr_binop_eq index s 3 Op.urem (.reg 1) (.lit pr.1) _ (by
      show (if pr.1 % M = 0 then none else some (s 1 % (pr.1 % M) % M)) = _
      rw [if_neg hne, hpM, hmod])
  have h2 : denoteInstr index (s.set 3 (s 1 % pr.1))
        (Instr.binop 3 Op.eq (.reg 3) (.lit pr.2))
      = some ((s.set 3 (s 1 % pr.1)).set 3 (hitOf (s 1) pr)) :=
    denoteInstr_binop_eq index _ 3 Op.eq (.reg 3) (.lit pr.2) _ (by
      show (some (if (s.set 3 (s 1 % pr.1)) 3 = pr.2 % M then 1 else 0)) = _
      rw [hrM, show (s.set 3 (s 1 % pr.1)) 3 = s 1 % pr.1 by simp [RegState.set]]
      rfl)
  have h3 : denoteInstr index ((s.set 3 (s 1 % pr.1)).set 3 (hitOf (s 1) pr))
        (Instr.binop 2 Op.add (.reg 2) (.reg 3))
      = some ((((s.set 3 (s 1 % pr.1)).set 3 (hitOf (s 1) pr)).set 2
          ((s 2 + hitOf (s 1) pr) % M))) :=
    denoteInstr_binop_eq index _ 2 Op.add (.reg 2) (.reg 3) _ (by
      show (some ((((s.set 3 (s 1 % pr.1)).set 3 (hitOf (s 1) pr)) 2 +
        (((s.set 3 (s 1 % pr.1)).set 3 (hitOf (s 1) pr)) 3)) % M)) = _
      simp [RegState.set])
  show denoteInstrs index s
    (Instr.binop 3 Op.urem (.reg 1) (.lit pr.1) ::
      Instr.binop 3 Op.eq (.reg 3) (.lit pr.2) ::
      [Instr.binop 2 Op.add (.reg 2) (.reg 3)]) = _
  rw [denoteInstrs_cons, h1, obind_some, denoteInstrs_cons, h2, obind_some,
    denoteInstrs_cons, h3, obind_some]
  refine congrArg some (funext fun j => ?_)
  by_cases hj2 : j = 2
  · subst hj2; simp [RegState.set]
  · by_cases hj3 : j = 3
    · subst hj3; simp [RegState.set]
    · simp [RegState.set, hj2, hj3]

private theorem denote_table :
    ∀ (table : List (Nat × Nat)), (∀ pr ∈ table, RowValid pr) →
    ∀ (index : Nat) (s : RegState),
      denoteInstrs index s (table.flatMap entryInstrs) =
        some (fun j =>
          if j = 2 then foldHit (s 1) table (s 2)
          else if j = 3 then lastHit (s 1) table (s 3)
          else s j) := by
  intro table
  induction table with
  | nil =>
      intro _ index s
      refine congrArg some (funext fun j => ?_)
      simp only [foldHit, lastHit]
      by_cases hj2 : j = 2
      · subst hj2; simp
      · by_cases hj3 : j = 3
        · subst hj3; simp
        · simp [hj2, hj3]
  | cons pr rest ih =>
      intro hvalid index s
      have hpr : RowValid pr := hvalid pr (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, RowValid q :=
        fun q hq => hvalid q (List.mem_cons_of_mem _ hq)
      rw [List.flatMap_cons, Frontend.denoteInstrs_append,
        denote_entry index s pr hpr, obind_some, ih hrest index _]
      refine congrArg some (funext fun j => ?_)
      simp only [foldHit, lastHit]
      by_cases hj2 : j = 2
      · subst hj2; simp
      · by_cases hj3 : j = 3
        · subst hj3; simp
        · simp [hj2, hj3]

/-- The state after the two setup instructions. -/
private def stateB (start index : Nat) (s : RegState) : RegState :=
  (s.set 1 (kAt start index)).set 2 (if kAt start index = 0 then 1 else 0)

/-- The state after the table block. -/
private def stateC (table : List (Nat × Nat)) (start index : Nat)
    (s : RegState) : RegState :=
  fun j =>
    if j = 2 then
      foldHit (stateB start index s 1) table (stateB start index s 2)
    else if j = 3 then
      lastHit (stateB start index s 1) table (stateB start index s 3)
    else stateB start index s j

/-- The exact state after one pass of the loop body. -/
def stepState (table : List (Nat × Nat)) (start index : Nat) (s : RegState) :
    RegState :=
  fun j =>
    if j = 0 then (s 0 + survAt table start index) % M
    else if j = 1 then kAt start index
    else if j = 2 then hitAt table start index
    else if j = 3 then survAt table start index
    else s j

private theorem denote_body (table : List (Nat × Nat))
    (hvalid : ∀ pr ∈ table, RowValid pr) (start index : Nat) (s : RegState) :
    denoteInstrs index s (bodyInstrs table start) =
      some (stepState table start index s) := by
  have hzero : (0 : Nat) % M = 0 := by decide
  have hB1 : stateB start index s 1 = kAt start index := by
    simp [stateB, RegState.set]
  have hB2 : stateB start index s 2 = (if kAt start index = 0 then 1 else 0) := by
    simp [stateB, RegState.set]
  have hC2 : stateC table start index s 2 = hitAt table start index := by
    simp [stateC, hB1, hB2, hitAt]
  have hC0 : stateC table start index s 0 = s 0 := by
    simp [stateC, stateB, RegState.set]
  have h1 : denoteInstr index s (Instr.binop 1 Op.add .idx (.lit start))
      = some (s.set 1 (kAt start index)) :=
    denoteInstr_binop_eq index s 1 Op.add .idx (.lit start) _ rfl
  have h2 : denoteInstr index (s.set 1 (kAt start index))
        (Instr.binop 2 Op.eq (.reg 1) (.lit 0))
      = some (stateB start index s) :=
    denoteInstr_binop_eq index _ 2 Op.eq (.reg 1) (.lit 0) _ (by
      show (some (if (s.set 1 (kAt start index)) 1 = 0 % M then 1 else 0)) = _
      rw [hzero, show (s.set 1 (kAt start index)) 1 = kAt start index by
        simp [RegState.set]])
  have h3 : denoteInstr index (stateC table start index s)
        (Instr.binop 3 Op.eq (.reg 2) (.lit 0))
      = some ((stateC table start index s).set 3 (survAt table start index)) :=
    denoteInstr_binop_eq index _ 3 Op.eq (.reg 2) (.lit 0) _ (by
      show (some (if stateC table start index s 2 = 0 % M then 1 else 0)) = _
      rw [hzero, hC2]
      rfl)
  have h4 : denoteInstr index
        ((stateC table start index s).set 3 (survAt table start index))
        (Instr.binop 0 Op.add (.reg 0) (.reg 3))
      = some (((stateC table start index s).set 3
          (survAt table start index)).set 0
            ((s 0 + survAt table start index) % M)) :=
    denoteInstr_binop_eq index _ 0 Op.add (.reg 0) (.reg 3) _ (by
      show (some ((((stateC table start index s).set 3
        (survAt table start index)) 0 +
        ((stateC table start index s).set 3 (survAt table start index)) 3)
          % M)) = _
      simp [RegState.set, hC0])
  show denoteInstrs index s
    (Instr.binop 1 Op.add .idx (.lit start) ::
      Instr.binop 2 Op.eq (.reg 1) (.lit 0) ::
      (table.flatMap entryInstrs ++
        [Instr.binop 3 Op.eq (.reg 2) (.lit 0),
         Instr.binop 0 Op.add (.reg 0) (.reg 3)])) = _
  rw [denoteInstrs_cons, h1, obind_some, denoteInstrs_cons, h2, obind_some,
    Frontend.denoteInstrs_append,
    denote_table table hvalid index (stateB start index s), obind_some,
    show (fun j =>
        if j = 2 then foldHit (stateB start index s 1) table
          (stateB start index s 2)
        else if j = 3 then lastHit (stateB start index s 1) table
          (stateB start index s 3)
        else stateB start index s j) = stateC table start index s from rfl,
    denoteInstrs_cons, h3, obind_some, denoteInstrs_cons, h4, obind_some]
  refine congrArg some (funext fun j => ?_)
  by_cases hj0 : j = 0
  · subst hj0; simp [RegState.set, stepState]
  · by_cases hj1 : j = 1
    · subst hj1
      simp [RegState.set, stepState, stateC, stateB, hj0]
    · by_cases hj2 : j = 2
      · subst hj2
        simp [RegState.set, stepState, hC2, hj0, hj1]
      · by_cases hj3 : j = 3
        · subst hj3; simp [RegState.set, stepState, hj0, hj1, hj2]
        · simp [RegState.set, stepState, stateC, stateB,
            hj0, hj1, hj2, hj3]

/-! ### The bridge -/

/--
**The bridge, modular form.** The program's denotation is the wrapping sum,
over the window, of the wrapping survivor bit.  Proved by simulation: the
hypotheses of `FoldBridge.Program.denote_eq_scalar_foldl` are `∀`-quantified
over states and indices, so this costs the same at any window length.
-/
theorem sieveProgram_denote_mod (table : List (Nat × Nat))
    (hvalid : ∀ pr ∈ table, RowValid pr) (start count : Nat) :
    (sieveProgram table start count).denote =
      some ((List.range count).foldl
        (fun acc index => (acc + survAt table start index) % M) 0) :=
  FoldBridge.Program.denote_eq_scalar_foldl (sieveProgram table start count)
    (fun _ => True) (stepState table start)
    (fun index acc => (acc + survAt table start index) % M)
    initialState 0 rfl trivial rfl rfl
    (fun index s _ => denote_body table hvalid start index s)
    (fun _ _ _ => trivial)
    (fun _ _ _ => rfl)

/-- Inside a window that does not wrap, the loop index really is the offset. -/
private theorem kAt_eq (start count index : Nat) (hs : start + count ≤ M)
    (hi : index < count) : kAt start index = start + index := by
  have hstart : start % M = start := Nat.mod_eq_of_lt (by omega)
  have hidx : index % M = index := Nat.mod_eq_of_lt (by omega)
  rw [kAt, hstart, hidx, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The machine's wrapping tally is the plain tally when the table fits. -/
private theorem foldHit_eq (table : List (Nat × Nat)) (k : Nat)
    (hlen : table.length + 1 < M) :
    foldHit k table (if k = 0 then 1 else 0) = hitCount table k := by
  have hfold : ∀ (l : List (Nat × Nat)) (a : Nat),
      foldHit k l a = l.foldl (fun acc pr => (acc + hitOf k pr) % M) a := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons pr rest ih => intro a; rw [foldHit, List.foldl_cons, ih]
  have hbound : ∀ (l : List (Nat × Nat)),
      l.foldl (fun acc pr => acc + hitOf k pr) 0 ≤ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons pr rest ih =>
        rw [List.foldl_cons, foldl_add_shift (hitOf k) rest (0 + hitOf k pr)]
        have hb : hitOf k pr ≤ 1 := by unfold hitOf; split <;> omega
        simp only [List.length_cons]
        omega
  rw [hfold, hitCount,
    foldl_add_mod_eq (hitOf k) table (if k = 0 then 1 else 0)
      (by have hb := hbound table; split <;> omega),
    foldl_add_shift (hitOf k) table (if k = 0 then 1 else 0)]

/--
**The bridge.**

The sieve program's denotation is exactly the reference's survivor count of
the window `[start, start + count)`.

The two size hypotheses are the machine-word conditions and nothing else:
the window must not wrap `2⁶⁴`, and the table plus the count must fit in a
word.  Neither the statement nor the proof mentions the window's length, so
this is the same theorem at a window of ten candidates and at the reference
producer's block of `2²⁴`.
-/
theorem sieveProgram_denote (table : List (Nat × Nat))
    (hvalid : ∀ pr ∈ table, RowValid pr) (start count : Nat)
    (hwin : start + count ≤ M) (hlen : table.length + 1 < M)
    (hcount : count < M) :
    (sieveProgram table start count).denote =
      some (survivorCount table start count) := by
  rw [sieveProgram_denote_mod table hvalid start count]
  refine congrArg some ?_
  have hpoint : ∀ index ∈ List.range count,
      survAt table start index = survivorBit table (start + index) := by
    intro index hindex
    rw [survAt, hitAt, kAt_eq start count index hwin (List.mem_range.mp hindex),
      foldHit_eq table (start + index) hlen, survivorBit]
  have hbound : ∀ (l : List Nat),
      l.foldl (fun acc i => acc + survivorBit table (start + i)) 0
        ≤ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
        rw [List.foldl_cons,
          foldl_add_shift (fun i => survivorBit table (start + i)) rest
            (0 + survivorBit table (start + i))]
        have hb : survivorBit table (start + i) ≤ 1 := by
          unfold survivorBit; split <;> omega
        simp only [List.length_cons]
        omega
  have hcongr : ∀ (l : List Nat) (init : Nat),
      (∀ index ∈ l, survAt table start index
        = survivorBit table (start + index)) →
      l.foldl (fun acc index => (acc + survAt table start index) % M) init =
        l.foldl (fun acc index => (acc + survivorBit table (start + index)) % M)
          init := by
    intro l
    induction l with
    | nil => intro init _; rfl
    | cons i rest ih =>
        intro init hall
        rw [List.foldl_cons, List.foldl_cons, hall i (List.mem_cons_self ..)]
        exact ih _ (fun x hx => hall x (List.mem_cons_of_mem _ hx))
  rw [hcongr (List.range count) 0 hpoint,
    foldl_add_mod_eq (fun i => survivorBit table (start + i)) (List.range count) 0
      (by have hb := hbound (List.range count)
          simp only [List.length_range] at hb
          omega)]
  simp [survivorCount]

end LeanCompCert.Ports.TGSieve
