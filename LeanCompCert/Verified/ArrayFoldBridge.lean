import LeanCompCert.Verified.ArrayState
import LeanCompCert.Verified.InstrBlock

/-!
# From an array program to the fold it computes — once, for all sizes

`Verified/FoldBridge.lean` turns a `Reflect.Program` into the mathematical
fold it computes, structurally, by a simulation argument whose hypotheses do
not mention the trip count.  Every scalar port in this package is proved
through it.

**The array machine had no such bridge.**  `AProgram.denote` is a monadic fold
over `Option AState`, and the only way anything in `Ports/` related it to
mathematics was kernel evaluation at a toy size plus a C oracle at the real
one.  That is the gap this module closes.

## Two layers, both reusable

1. **Straight-line array blocks** (`arun`, `AllDefined`,
   `denoteAInstrs_eq_arun`).  A block of `AInstr`s has a *total* meaning,
   `arun`, obtained by running each instruction as a state update with the
   partial operations (`udiv`, `urem`, and the bounds-guarded `load`/`store`)
   read through `Option.getD`.  `denoteAInstrs_eq_arun` says the partial
   denotation agrees with it as soon as each partial operation is defined *at
   the point it executes* — `AllDefined`, a conjunction that unfolds
   mechanically for a concrete block.  This is what makes transcribing a
   ninety-instruction body a finite amount of `simp` rather than a
   hand-written chain of `bind` rewrites.

2. **The loop bridge** (`AProgram.denote_eq_foldl_mem`,
   `AProgram.denote_eq_obs_foldl_mem`).  The array analogue of
   `FoldBridge.Program.denote_eq_foldl`, with the body-simulation hypothesis
   restricted to `index < p.loopCount` — the restriction
   `Ports/RS62LadderEncoding.lean` found to be essential rather than
   convenient: an index-decoding body is genuinely undefined at an adversarial
   index, so the unrestricted form is unprovable for it.

`AProgram.denote_eq_obs_foldl_mem` is the shape a port quotes: an
*observation* of the machine state (typically the array contents paired with
an accumulator register) is folded by a step function stated in ordinary
mathematics, and the epilogue reads the answer out of it.  Nothing in the
statement mentions a register file, a trace, or a problem size.

All of this is size-independent in the same sense `FoldBridge` is: the
hypotheses quantify over states, so discharging them at any size discharges
them at every size.
-/

namespace LeanCompCert.Verified.ArrayFoldBridge

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-! ## Layer 0 — straight-line array blocks have a total meaning -/

/-- The total meaning of one array instruction: a state update, with a
failing `denoteOp` read as `0` (`InstrBlock.sval`) and the bounds guards of
`load`/`store` ignored.  `ADefined` below is what rules those cases out. -/
def astep (k : Nat) (s : AState) : AInstr → AState
  | .scalar i => s.writeReg (InstrBlock.sdest i) (InstrBlock.sval k s.regs i)
  | .load dest idxReg => s.writeReg dest (s.arr (s.regs idxReg))
  | .store idxReg srcReg => s.writeArr (s.regs idxReg) (s.regs srcReg)

/-- The total meaning of a straight-line block. -/
def arun (k : Nat) (s : AState) : List AInstr → AState
  | [] => s
  | i :: rest => arun k (astep k s i) rest

theorem arun_nil (k : Nat) (s : AState) : arun k s [] = s := rfl

theorem arun_cons (k : Nat) (s : AState) (i : AInstr) (rest : List AInstr) :
    arun k s (i :: rest) = arun k (astep k s i) rest := rfl

theorem arun_append (k : Nat) :
    ∀ (xs ys : List AInstr) (s : AState),
      arun k s (xs ++ ys) = arun k (arun k s xs) ys := by
  intro xs
  induction xs with
  | nil => intro ys s; rfl
  | cons x xs ih => intro ys s; exact ih ys (astep k s x)

/-- "This instruction is defined in this state": the divisor of a `udiv` or
`urem` is nonzero, and an array access is in bounds. -/
def ADefined (len k : Nat) (s : AState) : AInstr → Prop
  | .scalar (.mov _ _) => True
  | .scalar (.binop _ op l r) =>
      (denoteOp op (denoteOperand k s.regs l) (denoteOperand k s.regs r)).isSome = true
  | .load _ idxReg => s.regs idxReg < len
  | .store idxReg _ => s.regs idxReg < len

/-- Every instruction of the block is defined at the state it executes in.
Note the recursion: the guard on instruction `j` is read in the state
`arun` has reached after the first `j` instructions, which is exactly the
obligation the machine imposes. -/
def AllDefined (len k : Nat) : AState → List AInstr → Prop
  | _, [] => True
  | s, i :: rest => ADefined len k s i ∧ AllDefined len k (astep k s i) rest

/-- One defined instruction denotes its total meaning. -/
theorem denoteAInstr_eq_astep {len k : Nat} {s : AState} {i : AInstr}
    (h : ADefined len k s i) : denoteAInstr len k s i = some (astep k s i) := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov d src => rfl
      | binop d op l r =>
          simp only [ADefined] at h
          cases hv : denoteOp op (denoteOperand k s.regs l)
              (denoteOperand k s.regs r) with
          | none => rw [hv] at h; exact absurd h (by simp)
          | some v =>
              show (denoteInstr k s.regs (.binop d op l r)) >>= _ = _
              show ((denoteOp op (denoteOperand k s.regs l)
                (denoteOperand k s.regs r)).bind _) >>= _ = _
              rw [hv]
              show some _ = some (astep k s (.scalar (.binop d op l r)))
              simp only [astep, InstrBlock.sdest, InstrBlock.sval, hv,
                Option.getD_some]
              rfl
  | load dest idxReg =>
      simp only [ADefined] at h
      simp only [denoteAInstr, astep, if_pos h]
  | store idxReg srcReg =>
      simp only [ADefined] at h
      simp only [denoteAInstr, astep, if_pos h]

/-- Definedness splits along a block boundary, at the state the second block
starts in.  Transcribing a sixty-instruction body in one `simp` produces a
term whose printed size is quadratic in the block length; this is what lets a
port cut the body into named stages and pay only for one stage at a time. -/
theorem AllDefined_append (len k : Nat) :
    ∀ (xs ys : List AInstr) (s : AState),
      AllDefined len k s (xs ++ ys) ↔
        (AllDefined len k s xs ∧ AllDefined len k (arun k s xs) ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys s
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons x xs ih =>
      intro ys s
      constructor
      · intro h
        obtain ⟨hx, hrest⟩ := h
        obtain ⟨h1, h2⟩ := (ih ys (astep k s x)).mp hrest
        exact ⟨⟨hx, h1⟩, h2⟩
      · intro h
        obtain ⟨⟨hx, h1⟩, h2⟩ := h
        exact ⟨hx, (ih ys (astep k s x)).mpr ⟨h1, h2⟩⟩

/--
**A straight-line array block denotes its total run.**

The workhorse for transcribing a port's body: `arun` is a plain recursive
state update that `simp` evaluates, so the transcription obligation becomes
`AllDefined`, a conjunction of concrete arithmetic side conditions.
-/
theorem denoteAInstrs_eq_arun (len k : Nat) :
    ∀ (l : List AInstr) (s : AState), AllDefined len k s l →
      denoteAInstrs len k s l = some (arun k s l) := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      obtain ⟨hd, hrest⟩ := h
      show (denoteAInstr len k s i).bind _ = _
      rw [denoteAInstr_eq_astep hd]
      exact ih (astep k s i) hrest

/-! ## Layer 1 — the monadic loop is a pure fold -/

/--
**Body simulation, at the indices the loop visits.**

The array analogue of `FoldBridge.foldlM_body_eq_foldl`, with the simulation
hypothesis restricted by a predicate `Q` on the index.  A body that decodes a
divisor or an array offset from the loop index cannot satisfy the
unrestricted form; this is the weakest strengthening that admits it.
-/
theorem foldlM_abody_eq_foldl_mem
    (len : Nat) (body : List AInstr) (Q : Nat → Prop) (P : AState → Prop)
    (step : Nat → AState → AState)
    (hStep : ∀ index s, Q index → P s →
      denoteAInstrs len index s body = some (step index s))
    (hClosed : ∀ index s, Q index → P s → P (step index s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : AState, P s →
      indices.foldlM (fun s index => denoteAInstrs len index s body) s =
        some (indices.foldl (fun s index => step index s) s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show (denoteAInstrs len index s body).bind
        (fun s => rest.foldlM (fun s index => denoteAInstrs len index s body) s) = _
      rw [hStep index s hQi hP]
      exact ih (fun i hi => hQ i (by simp [hi])) (step index s)
        (hClosed index s hQi hP)

/-- The invariant survives the whole loop. -/
theorem foldl_closed_mem (Q : Nat → Prop) (P : AState → Prop)
    (step : Nat → AState → AState)
    (hClosed : ∀ index s, Q index → P s → P (step index s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : AState, P s →
      P (indices.foldl (fun s index => step index s) s) := by
  intro indices
  induction indices with
  | nil => intro _ s h; exact h
  | cons i rest ih =>
      intro hQ s hP
      exact ih (fun j hj => hQ j (by simp [hj])) (step i s)
        (hClosed i s (hQ i (by simp)) hP)

/-! ## Layer 2 — observing the folded state -/

/--
**Observation transfer**, at the indices the loop visits.

`obs` is typically `fun s => (s.arr, s.regs acc)`: the array contents and the
accumulator, which is all a segmented sieve carries between iterations.
-/
theorem foldl_obs_mem {A : Type _}
    (Q : Nat → Prop) (P : AState → Prop) (step : Nat → AState → AState)
    (obs : AState → A) (g : Nat → A → A)
    (hClosed : ∀ index s, Q index → P s → P (step index s))
    (hObs : ∀ index s, Q index → P s → obs (step index s) = g index (obs s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : AState, P s →
      obs (indices.foldl (fun s index => step index s) s) =
        indices.foldl (fun acc index => g index acc) (obs s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show obs (rest.foldl (fun s index => step index s) (step index s)) = _
      rw [ih (fun i hi => hQ i (by simp [hi])) (step index s)
          (hClosed index s hQi hP), hObs index s hQi hP]
      rfl

/-! ## Layer 3 — the assembled bridges -/

/--
**The array loop bridge, index-restricted.**

The array analogue of `FoldBridge.Program.denote_eq_foldl`: an `AProgram`
whose init block reaches `s₀`, whose body simulates `step` at every index the
loop visits, and whose epilogue acts as `fin`, denotes the output register of
the pure `List.foldl`.

Every hypothesis is size-independent.
-/
theorem AProgram.denote_eq_foldl_mem
    (p : AProgram) (P : AState → Prop) (step : Nat → AState → AState)
    (fin : AState → AState) (s₀ : AState)
    (hInit : denoteAInstrs p.arrayLen 0 initialAState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, index < p.loopCount → P s →
      denoteAInstrs p.arrayLen index s p.body = some (step index s))
    (hClosed : ∀ index s, index < p.loopCount → P s → P (step index s))
    (hEpilogue : ∀ s, P s → denoteAInstrs p.arrayLen 0 s p.epilogue = some (fin s)) :
    p.denote =
      some ((fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀)).regs p.output) := by
  have hmem : ∀ i ∈ List.range p.loopCount, i < p.loopCount :=
    fun i hi => List.mem_range.mp hi
  have hFoldP : P ((List.range p.loopCount).foldl
      (fun s index => step index s) s₀) :=
    foldl_closed_mem (fun i => i < p.loopCount) P step hClosed
      (List.range p.loopCount) hmem s₀ hP₀
  show (denoteAInstrs p.arrayLen 0 initialAState p.init).bind _ = _
  rw [hInit]
  show ((List.range p.loopCount).foldlM
    (fun s index => denoteAInstrs p.arrayLen index s p.body) s₀).bind _ = _
  rw [foldlM_abody_eq_foldl_mem p.arrayLen p.body (fun i => i < p.loopCount) P
    step hStep hClosed (List.range p.loopCount) hmem s₀ hP₀]
  show ((denoteAInstrs p.arrayLen 0 _ p.epilogue).bind _) = _
  rw [hEpilogue _ hFoldP]
  rfl

/--
**The statement a port quotes.**

An observation `obs` of the machine state is folded by `g`, and the epilogue
reads the answer out of the observation through `out`.  The conclusion
mentions no register, no trace and no problem size: it is an equation between
`AProgram.denote` and a fold written in ordinary mathematics.
-/
theorem AProgram.denote_eq_obs_foldl_mem {A : Type _}
    (p : AProgram) (P : AState → Prop) (step : Nat → AState → AState)
    (obs : AState → A) (g : Nat → A → A) (out : A → Nat) (s₀ : AState)
    (hInit : denoteAInstrs p.arrayLen 0 initialAState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, index < p.loopCount → P s →
      denoteAInstrs p.arrayLen index s p.body = some (step index s))
    (hClosed : ∀ index s, index < p.loopCount → P s → P (step index s))
    (hObs : ∀ index s, index < p.loopCount → P s →
      obs (step index s) = g index (obs s))
    (hOut : ∀ s, P s →
      (denoteAInstrs p.arrayLen 0 s p.epilogue).map (fun s' => s'.regs p.output)
        = some (out (obs s))) :
    p.denote =
      some (out ((List.range p.loopCount).foldl
        (fun acc index => g index acc) (obs s₀))) := by
  have hmem : ∀ i ∈ List.range p.loopCount, i < p.loopCount :=
    fun i hi => List.mem_range.mp hi
  have hFoldP : P ((List.range p.loopCount).foldl
      (fun s index => step index s) s₀) :=
    foldl_closed_mem (fun i => i < p.loopCount) P step hClosed
      (List.range p.loopCount) hmem s₀ hP₀
  have hView := foldl_obs_mem (fun i => i < p.loopCount) P step obs g hClosed
    hObs (List.range p.loopCount) hmem s₀ hP₀
  show (denoteAInstrs p.arrayLen 0 initialAState p.init).bind _ = _
  rw [hInit]
  show ((List.range p.loopCount).foldlM
    (fun s index => denoteAInstrs p.arrayLen index s p.body) s₀).bind _ = _
  rw [foldlM_abody_eq_foldl_mem p.arrayLen p.body (fun i => i < p.loopCount) P
    step hStep hClosed (List.range p.loopCount) hmem s₀ hP₀]
  show ((denoteAInstrs p.arrayLen 0 _ p.epilogue).bind
    (fun s => some (s.regs p.output))) = _
  have hmap := hOut _ hFoldP
  cases hE : denoteAInstrs p.arrayLen 0
      ((List.range p.loopCount).foldl (fun s index => step index s) s₀)
      p.epilogue with
  | none => rw [hE] at hmap; exact absurd hmap (by simp)
  | some s' =>
      rw [hE] at hmap
      simp only [Option.map_some] at hmap
      show some (s'.regs p.output) = _
      rw [Option.some_inj.mp hmap, hView]

/-! ## Branchless 0/1 flag algebra at `u64`

Every array port in this package is *branchless*: a condition is materialized
as a `0`/`1` register by a comparison, conditions are combined by
multiplication, and a value is selected by `g·x + (1−g)·y`.  The machine
truncates each step to `u64`, so the transcription of a body is a tower of
`(… ) % M` around nested `if`s.

These six rewrites collapse that tower.  Used as a `simp` set together with
the `x % M = x` facts a port's range hypotheses give, they normalize a
branchless block to a single `if` per selected value — which is what makes
the body-simulation lemma of a ninety-instruction body a one-tactic proof.
They are stated for arbitrary decidable propositions and mention no port.
-/

/-- `%` distributes through a selection. -/
theorem ite_mod (a : Prop) [Decidable a] (x y m : Nat) :
    (if a then x else y) % m = if a then x % m else y % m := by
  by_cases ha : a <;> simp [ha]

/-- Gating a value by a flag. -/
theorem bit_mul_val (a : Prop) [Decidable a] (x : Nat) :
    ((if a then (1:Nat) else 0) * x) = if a then x else 0 := by
  by_cases ha : a <;> simp [ha]

/-- Gating a value by the complement of a flag. -/
theorem bit'_mul_val (a : Prop) [Decidable a] (x : Nat) :
    ((if a then (0:Nat) else 1) * x) = if a then 0 else x := by
  by_cases ha : a <;> simp [ha]

/-- Conjunction of flags, in the nested form gating leaves behind. -/
theorem ite_ite_and (a b : Prop) [Decidable a] [Decidable b] :
    (if a then (if b then (1:Nat) else 0) else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- Conjunction with a negated flag. -/
theorem ite_ite_and' (a b : Prop) [Decidable a] [Decidable b] :
    (if a then (0:Nat) else (if b then 1 else 0)) = if ¬ a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- The branchless select `g·x + (1−g)·y`. -/
theorem ite_add_ite (a : Prop) [Decidable a] (x y : Nat) :
    ((if a then x else 0) + (if a then 0 else y)) = if a then x else y := by
  by_cases ha : a <;> simp [ha]

/-- Conjunction of flags, when the port combines them bitwise rather than by
multiplication (`ArrayMobius` and `ArraySegSieve` do both). -/
theorem bit_and_bit (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then (1:Nat) else 0) &&& (if b then 1 else 0)) =
      if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> decide

/-- Disjunction of flags. -/
theorem bit_or_bit (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then (1:Nat) else 0) ||| (if b then 1 else 0)) =
      if a ∨ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> decide

/-- Flag negation by `xor 1`, the other form ports write `1 − g` in. -/
theorem bit_xor_one (a : Prop) [Decidable a] :
    ((if a then (1:Nat) else 0) ^^^ 1) = if a then 0 else 1 := by
  by_cases ha : a <;> simp [ha] <;> decide

/-- Masking a flag with `1` is the identity. -/
theorem bit_and_one (a : Prop) [Decidable a] :
    ((if a then (1:Nat) else 0) &&& 1) = if a then 1 else 0 := by
  by_cases ha : a <;> simp [ha] <;> decide

/-- Conjunction with a negated flag, in the form a two-level phase gate
leaves behind (`ArrayMobius`'s cursor advance is exactly this). -/
theorem ite_ite_not_and (a b : Prop) [Decidable a] [Decidable b] :
    (if a then (if b then (0:Nat) else 1) else 0) = if a ∧ ¬ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- The branchless select with the gate on the *second* summand. -/
theorem ite_add_ite' (a : Prop) [Decidable a] (x y : Nat) :
    ((if a then (0:Nat) else x) + (if a then y else 0)) = if a then y else x := by
  by_cases ha : a <;> simp [ha]

theorem one_lt_M : 1 < M := by decide

/-- **The "or 1" idiom.**  A port that uses `0` to mean the empty product
materializes `max v 1` branchlessly as `v + [v = 0]`; below the word size the
machine's truncation is invisible. -/
theorem or_one_mod {v m : Nat} (hv : v < m) (hm : 1 < m) :
    (v + (if v = 0 then 1 else 0)) % m = if v = 0 then 1 else v := by
  by_cases h : v = 0
  · rw [if_pos h, if_pos h, h]
    exact Nat.mod_eq_of_lt hm
  · rw [if_neg h, if_neg h, Nat.add_zero]
    exact Nat.mod_eq_of_lt hv

/-- Flag negation, as the machine computes it: `1 - g` is
`(1 + (2⁶⁴ − g)) mod 2⁶⁴`. -/
theorem one_sub_bit (a : Prop) [Decidable a] :
    (1 + (M - (if a then (1:Nat) else 0))) % M = if a then 0 else 1 := by
  have hM : 1 ≤ M := Nat.le_of_lt one_lt_M
  by_cases ha : a
  · rw [if_pos ha, if_pos ha]
    have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]
  · rw [if_neg ha, if_neg ha]
    have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt one_lt_M]

/-! ## A counting fold in the 64-bit machine

The one arithmetic fact every accumulating port needs and no port states: an
accumulator that is incremented by `0` or `1` and truncated to `u64` at every
step equals the true count, provided the range is shorter than `2⁶⁴`.  Stated
here once rather than re-derived per port.
-/

theorem countP_range_le (p : Nat → Bool) (k : Nat) :
    (List.range k).countP p ≤ k := by
  have := List.countP_le_length (p := p) (l := List.range k)
  simpa using this

theorem countP_range_succ (p : Nat → Bool) (k : Nat) :
    (List.range (k + 1)).countP p =
      (List.range k).countP p + (if p k then 1 else 0) := by
  rw [List.range_succ, List.countP_append]
  cases h : p k <;> simp [List.countP, List.countP.go, h]

/-- Counting is insensitive to the predicate off the counted range. -/
theorem countP_congr_range (p q : Nat → Bool) :
    ∀ (k : Nat), (∀ n, n < k → p n = q n) →
      (List.range k).countP p = (List.range k).countP q := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [countP_range_succ, countP_range_succ, ih (fun n hn => h n (by omega)),
        h k (by omega)]

/-- **The counting fold is exact below the word size.** -/
theorem foldl_count_mod (p : Nat → Bool) :
    ∀ k : Nat, k < M →
      (List.range k).foldl (fun a n => (a + (if p n then 1 else 0)) % M) 0 =
        (List.range k).countP p := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [countP_range_succ, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih (by omega)]
      have hle : (List.range k).countP p ≤ k := countP_range_le p k
      have : (List.range k).countP p + (if p k then 1 else 0) < M := by
        cases p k <;> simp <;> omega
      exact Nat.mod_eq_of_lt this

end LeanCompCert.Verified.ArrayFoldBridge
