import LeanCompCert.Verified.Reflect
import LeanCompCert.Verified.Sieve

/-!
# M5 — DSL array state with a denotation

The array-extended register machine at the denotation level: the scalar
register DSL of `Reflect` (`Instr`, `denoteInstr`) plus one array with a
fixed static length, accessed through bounds-guarded `load`/`store`
instructions — an out-of-range index denotes `none`, the same failure
discipline as division by zero in the scalar fragment.

Contents:

* `AState`, `AInstr`, `denoteAInstr`, `denoteAInstrs`, `AProgram`,
  `AProgram.denote` — states, instructions, and the denotation.
* Frame lemmas: scalar steps never touch `arr`
  (`denoteAInstr_scalar_arr`, `denoteAInstrs_scalar_arr`); a `load`
  changes only its destination register (`denoteAInstr_load_some`); a
  `store` changes only the targeted cell (`denoteAInstr_store_some`);
  plus `denoteAInstrs_append` for sequencing.
* **Flagship** — `sieveSweep_cell`: an array-state Eratosthenes-style
  sweep (outer loop over divisor candidates `d = i + 2`, inner
  data-independent pass over all cells, "first write wins" through the
  `cell = 0` guard of `Sieve.spfStep`, then a finalize pass writing `n`
  into still-empty cells) computes, in every covered cell, exactly the
  reference smallest-factor function `Sieve.leastFactor`. The
  per-bound characterization `sieveMark_cell_spec` is the classical
  sieve invariant: after the divisors `2 .. bound + 1` have been
  processed, every cell holds `0` — and then all of its hits lie
  beyond the scanned window — or its least hit.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert.Verified.Reflect

/-! ## State and instructions -/

/-- Machine state: scalar registers plus one array. A fixed static
length (`len` below, `arrayLen` in a program) bounds the valid indices;
the state itself is total, as with `RegState`. -/
structure AState where
  regs : Nat → Nat
  arr : Nat → Nat

/-- Functional update of one register. -/
def AState.writeReg (s : AState) (index value : Nat) : AState :=
  { s with regs := fun c => if c = index then value else s.regs c }

/-- Functional update of one array cell. -/
def AState.writeArr (s : AState) (index value : Nat) : AState :=
  { s with arr := fun c => if c = index then value else s.arr c }

theorem AState.writeReg_arr (s : AState) (n v : Nat) :
    (s.writeReg n v).arr = s.arr := rfl

theorem AState.writeReg_regs_self (s : AState) (n v : Nat) :
    (s.writeReg n v).regs n = v := by
  simp [AState.writeReg]

theorem AState.writeReg_regs_ne (s : AState) {j n : Nat} (v : Nat)
    (h : j ≠ n) : (s.writeReg n v).regs j = s.regs j := by
  simp [AState.writeReg, h]

theorem AState.writeArr_regs (s : AState) (n v : Nat) :
    (s.writeArr n v).regs = s.regs := rfl

theorem AState.writeArr_arr_self (s : AState) (n v : Nat) :
    (s.writeArr n v).arr n = v := by
  simp [AState.writeArr]

theorem AState.writeArr_arr_ne (s : AState) {j n : Nat} (v : Nat)
    (h : j ≠ n) : (s.writeArr n v).arr j = s.arr j := by
  simp [AState.writeArr, h]

/-- Array-machine instructions: the scalar fragment reused wholesale,
plus bounds-guarded array read and write through an index register. -/
inductive AInstr where
  | scalar (i : Instr)
  | load (dest idxReg : Nat)
  | store (idxReg srcReg : Nat)
  deriving Repr, DecidableEq

/-! ## Denotation -/

/-- Denotation of one instruction against static array length `len` at
loop index `index`. Scalar instructions defer to `denoteInstr` on the
register file (the array unchanged); `load`/`store` denote `none` when
the index register is out of range (`regs idxReg ≥ len`), else a read /
functional update. -/
def denoteAInstr (len index : Nat) (s : AState) : AInstr → Option AState
  | .scalar i =>
      denoteInstr index s.regs i >>= fun regs => some { s with regs := regs }
  | .load dest idxReg =>
      if s.regs idxReg < len then
        some (s.writeReg dest (s.arr (s.regs idxReg)))
      else
        none
  | .store idxReg srcReg =>
      if s.regs idxReg < len then
        some (s.writeArr (s.regs idxReg) (s.regs srcReg))
      else
        none

/-- Sequencing, failure-propagating. -/
def denoteAInstrs (len index : Nat) (s : AState) :
    List AInstr → Option AState
  | [] => some s
  | instr :: rest => do
      denoteAInstrs len index (← denoteAInstr len index s instr) rest

/-- A bounded-fold array program: register count, static array length,
loop trip count, initialization block, loop body (executed with the
index running over `0, …, loopCount − 1`), epilogue, output register. -/
structure AProgram where
  regCount : Nat
  arrayLen : Nat
  loopCount : Nat
  init : List AInstr
  body : List AInstr
  epilogue : List AInstr
  output : Nat
  deriving Repr

/-- The all-zero initial state: zero registers, zero-filled array. -/
def initialAState : AState := { regs := initialState, arr := fun _ => 0 }

def AProgram.denote (p : AProgram) : Option Nat := do
  let s ← denoteAInstrs p.arrayLen 0 initialAState p.init
  let s ← (List.range p.loopCount).foldlM
    (fun s index => denoteAInstrs p.arrayLen index s p.body) s
  let s ← denoteAInstrs p.arrayLen 0 s p.epilogue
  pure (s.regs p.output)

/-! ## Basic theory: bind reduction, frame lemmas, sequencing -/

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

private theorem obind_none {α β : Type _} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl

private theorem opure {α : Type _} (a : α) :
    (pure a : Option α) = some a := rfl

/-- The scalar case, restated through `Option.map`: a scalar step is
exactly a `denoteInstr` step on the register file. -/
theorem denoteAInstr_scalar (len index : Nat) (s : AState) (i : Instr) :
    denoteAInstr len index s (.scalar i) =
      (denoteInstr index s.regs i).map fun regs => { s with regs := regs } := by
  simp only [denoteAInstr]
  cases denoteInstr index s.regs i <;> rfl

/-- Frame: a scalar step never changes the array. -/
theorem denoteAInstr_scalar_arr {len index : Nat} {s s' : AState}
    {i : Instr} (h : denoteAInstr len index s (.scalar i) = some s') :
    s'.arr = s.arr := by
  simp only [denoteAInstr] at h
  cases hd : denoteInstr index s.regs i with
  | none =>
      rw [hd] at h
      simp only [obind_none] at h
      cases h
  | some regs =>
      rw [hd] at h
      simp only [obind_some] at h
      cases h
      rfl

/-- Frame + characterization of a successful `load`: the index was in
bounds, the array is unchanged, the destination register holds the read
cell, and every other register is unchanged. -/
theorem denoteAInstr_load_some {len index dest idxReg : Nat}
    {s s' : AState}
    (h : denoteAInstr len index s (.load dest idxReg) = some s') :
    s.regs idxReg < len ∧ s'.arr = s.arr ∧
      s'.regs dest = s.arr (s.regs idxReg) ∧
      ∀ j, j ≠ dest → s'.regs j = s.regs j := by
  simp only [denoteAInstr] at h
  split at h
  · rename_i hlt
    cases h
    exact ⟨hlt, rfl, AState.writeReg_regs_self _ _ _,
      fun j hj => AState.writeReg_regs_ne _ _ hj⟩
  · cases h

/-- Frame + characterization of a successful `store`: the index was in
bounds, the registers are unchanged, the targeted cell holds the source
register, and every other cell is unchanged. -/
theorem denoteAInstr_store_some {len index idxReg srcReg : Nat}
    {s s' : AState}
    (h : denoteAInstr len index s (.store idxReg srcReg) = some s') :
    s.regs idxReg < len ∧ s'.regs = s.regs ∧
      s'.arr (s.regs idxReg) = s.regs srcReg ∧
      ∀ j, j ≠ s.regs idxReg → s'.arr j = s.arr j := by
  simp only [denoteAInstr] at h
  split at h
  · rename_i hlt
    cases h
    exact ⟨hlt, rfl, AState.writeArr_arr_self _ _ _,
      fun j hj => AState.writeArr_arr_ne _ _ hj⟩
  · cases h

/-- Bounds discipline: an out-of-range `load` denotes `none`. -/
theorem denoteAInstr_load_oob {len index dest idxReg : Nat} {s : AState}
    (h : len ≤ s.regs idxReg) :
    denoteAInstr len index s (.load dest idxReg) = none := by
  simp only [denoteAInstr]
  exact if_neg (by omega)

/-- Bounds discipline: an out-of-range `store` denotes `none`. -/
theorem denoteAInstr_store_oob {len index idxReg srcReg : Nat} {s : AState}
    (h : len ≤ s.regs idxReg) :
    denoteAInstr len index s (.store idxReg srcReg) = none := by
  simp only [denoteAInstr]
  exact if_neg (by omega)

/-- Sequencing distributes over append. -/
theorem denoteAInstrs_append (len index : Nat) (s : AState)
    (xs ys : List AInstr) :
    denoteAInstrs len index s (xs ++ ys) =
      denoteAInstrs len index s xs >>= fun s =>
        denoteAInstrs len index s ys := by
  induction xs generalizing s with
  | nil =>
      simp only [List.nil_append, denoteAInstrs, obind_some]
  | cons x xs ih =>
      simp only [List.cons_append, denoteAInstrs]
      cases hd : denoteAInstr len index s x with
      | none => simp only [obind_none]
      | some s1 =>
          simp only [obind_some]
          exact ih s1

/-- Frame, lifted to lists: a block of scalar instructions never
changes the array. -/
theorem denoteAInstrs_scalar_arr (len index : Nat) :
    ∀ (l : List AInstr) (s s' : AState),
      (∀ a ∈ l, ∃ i, a = AInstr.scalar i) →
      denoteAInstrs len index s l = some s' → s'.arr = s.arr := by
  intro l
  induction l with
  | nil =>
      intro s s' _ h
      simp only [denoteAInstrs] at h
      cases h
      rfl
  | cons a l ih =>
      intro s s' hall h
      obtain ⟨i, rfl⟩ := hall a (by simp)
      simp only [denoteAInstrs] at h
      cases hd : denoteAInstr len index s (.scalar i) with
      | none =>
          rw [hd] at h
          simp only [obind_none] at h
          cases h
      | some s1 =>
          rw [hd] at h
          simp only [obind_some] at h
          rw [ih s1 s' (fun a ha => hall a (List.mem_cons_of_mem _ ha)) h,
            denoteAInstr_scalar_arr hd]

/-! ## The array-realized smallest-prime-factor sweep

The sieve-style sweep over the functional array: the outer loop runs
over divisor candidates `d = i + 2` for `i ∈ [0, bound)`; each round is
a data-independent inner pass over **all** cells `n ∈ [0, len)` that
applies `Sieve.spfStep n · i` to cell `n` — write `d` into the cell iff
it is still `0` ("first write wins") and `d` is a hit for `n`. A final
pass writes `n` into every still-empty cell. Because each cell-update
reads and writes only its own cell, cell `n`'s trace through the sweep
is exactly the scalar scan `Sieve.spfScan`, and the existing Sieve
theory finishes the job. -/

/-- One data-independent pass over cells `0, …, len − 1`, rewriting
cell `n` to `g n (old value)`. Both sweep phases are instances. -/
def cellPass (g : Nat → Nat → Nat) (len : Nat) (s : AState) : AState :=
  (List.range len).foldl (fun s n => s.writeArr n (g n (s.arr n))) s

private theorem foldl_range_succ {α : Type _} (f : α → Nat → α) (a : α)
    (n : Nat) :
    (List.range (n + 1)).foldl f a = f ((List.range n).foldl f a) n := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Peeling the last cell of a pass. -/
theorem cellPass_succ (g : Nat → Nat → Nat) (len : Nat) (s : AState) :
    cellPass g (len + 1) s =
      (cellPass g len s).writeArr len (g len ((cellPass g len s).arr len)) := by
  unfold cellPass
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A pass never touches the registers. -/
theorem cellPass_regs (g : Nat → Nat → Nat) (len : Nat) (s : AState) :
    (cellPass g len s).regs = s.regs := by
  induction len with
  | zero => rfl
  | succ len ih =>
      rw [cellPass_succ, AState.writeArr_regs]
      exact ih

/-- The pass acts on each covered cell independently — cell `n` becomes
`g n (old value)` — and leaves cells at or beyond `len` unchanged. -/
theorem cellPass_arr (g : Nat → Nat → Nat) (len : Nat) (s : AState)
    (n : Nat) :
    (cellPass g len s).arr n =
      if n < len then g n (s.arr n) else s.arr n := by
  induction len with
  | zero =>
      rw [if_neg (Nat.not_lt_zero n)]
      rfl
  | succ len ih =>
      rw [cellPass_succ]
      by_cases hn : n = len
      · subst hn
        rw [AState.writeArr_arr_self, ih, if_neg (Nat.lt_irrefl _),
          if_pos (Nat.lt_succ_self _)]
      · rw [AState.writeArr_arr_ne _ _ hn, ih]
        by_cases h2 : n < len
        · rw [if_pos h2, if_pos (Nat.lt_succ_of_lt h2)]
        · rw [if_neg h2, if_neg (show ¬ n < len + 1 by omega)]

/-- The marking pass for divisor candidate `d = i + 2`: one guarded
select per cell, `Sieve.spfStep`. -/
def markPass (i len : Nat) (s : AState) : AState :=
  cellPass (fun n v => Sieve.spfStep n v i) len s

theorem markPass_regs (i len : Nat) (s : AState) :
    (markPass i len s).regs = s.regs :=
  cellPass_regs (fun n v => Sieve.spfStep n v i) len s

theorem markPass_arr (i len : Nat) (s : AState) (n : Nat) :
    (markPass i len s).arr n =
      if n < len then Sieve.spfStep n (s.arr n) i else s.arr n :=
  cellPass_arr (fun n v => Sieve.spfStep n v i) len s n

/-- The divisor sweep: marking passes for `i ∈ [0, bound)`, i.e.
divisor candidates `d ∈ [2, bound + 1]`. -/
def markSweep (bound len : Nat) (s : AState) : AState :=
  (List.range bound).foldl (fun s i => markPass i len s) s

/-- Peeling the last divisor round of the sweep. -/
theorem markSweep_succ (bound len : Nat) (s : AState) :
    markSweep (bound + 1) len s =
      markPass bound len (markSweep bound len s) := by
  unfold markSweep
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem markSweep_regs (bound len : Nat) (s : AState) :
    (markSweep bound len s).regs = s.regs := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      rw [markSweep_succ, markPass_regs]
      exact ih

/-- Cell decomposition of the sweep: within bounds, cell `n`'s trace is
exactly the scalar fold of `Sieve.spfStep n`. -/
theorem markSweep_arr (bound len : Nat) (s : AState) (n : Nat)
    (hn : n < len) :
    (markSweep bound len s).arr n =
      (List.range bound).foldl (Sieve.spfStep n) (s.arr n) := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      rw [markSweep_succ, markPass_arr, if_pos hn, ih,
        foldl_range_succ (Sieve.spfStep n) (s.arr n) bound]

/-- Cells at or beyond `len` are never written. -/
theorem markSweep_arr_oob (bound len : Nat) (s : AState) (n : Nat)
    (hn : ¬ n < len) :
    (markSweep bound len s).arr n = s.arr n := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      rw [markSweep_succ, markPass_arr, if_neg hn]
      exact ih

/-- The finalize pass: write `n` into every still-empty cell (a prime
or hit-free `n` keeps `leastFactor n = n`). -/
def finalizePass (len : Nat) (s : AState) : AState :=
  cellPass (fun n v => if v = 0 then n else v) len s

theorem finalizePass_regs (len : Nat) (s : AState) :
    (finalizePass len s).regs = s.regs :=
  cellPass_regs (fun n v => if v = 0 then n else v) len s

theorem finalizePass_arr (len : Nat) (s : AState) (n : Nat) :
    (finalizePass len s).arr n =
      if n < len then (if s.arr n = 0 then n else s.arr n) else s.arr n :=
  cellPass_arr (fun n v => if v = 0 then n else v) len s n

/-- The state after the divisor sweep, from the all-zero array. -/
def sieveMark (bound len : Nat) : AState :=
  markSweep bound len initialAState

/-- The full sweep: divisor sweep, then finalize. -/
def sieveSweep (bound len : Nat) : AState :=
  finalizePass len (sieveMark bound len)

/-- After the divisor sweep, an in-bounds cell holds exactly the scalar
scan value. -/
theorem sieveMark_arr (bound len n : Nat) (hn : n < len) :
    (sieveMark bound len).arr n = Sieve.spfScan bound n := by
  unfold sieveMark
  rw [markSweep_arr bound len initialAState n hn]
  rfl

/-- **The sieve invariant**, holding for every `bound` — i.e. at every
prefix of the divisor loop: after the divisors `2 .. bound + 1` have
been processed, every in-bounds cell `n` is either still `0` — and then
every hit of `n` lies beyond the scanned window — or holds the least
hit of `n`. -/
theorem sieveMark_cell_spec (bound len n : Nat) (hn : n < len) :
    ((sieveMark bound len).arr n = 0 ∧
        ∀ d, Sieve.Hit n d → bound + 2 ≤ d) ∨
      (Sieve.Hit n ((sieveMark bound len).arr n) ∧
        (sieveMark bound len).arr n ≤ bound + 1 ∧
        ∀ d, Sieve.Hit n d → (sieveMark bound len).arr n ≤ d) := by
  rw [sieveMark_arr bound len n hn]
  exact Sieve.spfScan_spec bound n

theorem sieveMark_arr_oob (bound len n : Nat) (hn : ¬ n < len) :
    (sieveMark bound len).arr n = 0 := by
  unfold sieveMark
  rw [markSweep_arr_oob bound len initialAState n hn]
  rfl

/-- After the full sweep, an in-bounds cell holds exactly the
fixed-shape smallest-prime-factor value. -/
theorem sieveSweep_arr (bound len n : Nat) (hn : n < len) :
    (sieveSweep bound len).arr n = Sieve.spfFixed bound n := by
  unfold sieveSweep
  rw [finalizePass_arr, if_pos hn, sieveMark_arr bound len n hn]
  rfl

/-- Cells at or beyond `len` come out `0`. -/
theorem sieveSweep_arr_oob (bound len n : Nat) (hn : ¬ n < len) :
    (sieveSweep bound len).arr n = 0 := by
  unfold sieveSweep
  rw [finalizePass_arr, if_neg hn, sieveMark_arr_oob bound len n hn]

/-- The sweep is pure array work: registers stay zero. -/
theorem sieveSweep_regs (bound len : Nat) :
    (sieveSweep bound len).regs = initialAState.regs := by
  unfold sieveSweep
  rw [finalizePass_regs]
  exact markSweep_regs bound len initialAState

/-- **Flagship**: with the static bound covering the square-root window
(`n < (bound + 2)²`), the array-realized sieve sweep materializes the
reference smallest-factor function `Sieve.leastFactor` in every
in-bounds cell. In particular `bound = 2 ^ 32` covers every cell value
below `2 ^ 64`. -/
theorem sieveSweep_cell (bound len n : Nat) (hn : n < len)
    (hCover : n < (bound + 2) * (bound + 2)) :
    (sieveSweep bound len).arr n = Sieve.leastFactor n := by
  rw [sieveSweep_arr bound len n hn]
  exact Sieve.spfFixed_eq_leastFactor bound n hCover

/-! ## Sanity checks -/

-- Store then load through an index register, in bounds.
example :
    (denoteAInstrs 4 0
      { regs := fun i => if i = 1 then 7 else 0, arr := fun _ => 0 }
      [.store 0 1, .load 2 0]).map (fun s => s.regs 2) = some 7 := rfl

-- Out-of-bounds access denotes `none`.
example :
    denoteAInstr 4 0 { regs := fun _ => 9, arr := fun _ => 0 }
      (.load 0 0) = none := rfl

/-- A tiny array program: store the loop index at `arr[index]` for
three iterations, then read `arr[2]` back into the output register. -/
def copyIdxProgram : AProgram := {
  regCount := 3
  arrayLen := 4
  loopCount := 3
  init := []
  body := [.scalar (.mov 0 .idx), .scalar (.mov 1 .idx), .store 0 1]
  epilogue := [.scalar (.mov 2 (.lit 2)), .load 1 2]
  output := 1
}

example : copyIdxProgram.denote = some 2 := rfl

-- A program that walks the index past the array length denotes `none`.
example :
    AProgram.denote {
      regCount := 1, arrayLen := 2, loopCount := 3, init := [],
      body := [.scalar (.mov 0 .idx), .store 0 0], epilogue := [],
      output := 0 } = none := rfl

-- The sweep at work: composite, prime, square, and degenerate cells.
example : (sieveSweep 4 16).arr 15 = 3 := by decide
example : (sieveSweep 4 16).arr 13 = 13 := by decide
example : (sieveSweep 4 16).arr 4 = 2 := by decide
example : (sieveSweep 4 16).arr 1 = 1 := by decide

-- The flagship theorem, instantiated.
example : (sieveSweep 4 16).arr 15 = Sieve.leastFactor 15 :=
  sieveSweep_cell 4 16 15 (by decide) (by decide)

end LeanCompCert.Verified.ArrayState
