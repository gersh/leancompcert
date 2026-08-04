import LeanCompCert.Ports.RamareMStar140M

/-!
# The `m★` sweep: what the configuration buys, and the machine's own arithmetic

`Ports/RamareMStar140M.lean` states the artifact, its well-formedness, and the
candidate-level reference `msRef`.  This module is the foundation of the
encoding proof:

* the `msOK` accessors — sixteen decidable facts, extracted once;
* the algebra of `MA`/`MS`/`MMul`/`bitOf`, which are *by definition* the
  machine's `denoteOp` at `.add`, `.sub`, `.mul` and at a comparison.  That is
  the design decision that makes this port cheap: `msRef` carries every
  `% 2⁶⁴` the machine has, so a value lemma is an **unconditional** rewrite
  wherever the operation is total, and no wrap-freedom side condition has to
  be proved to state one.

Nothing here mentions a block of the program, so nothing here can change the
emitted C.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.InstrBlock (srun sval sdest SDefined SAllDefined NoDivI)

/-! ## What `msOK` buys -/

theorem M_val : M = 18446744073709551616 := rfl

theorem M_pos' : 0 < M := M_pos

/-- The sixteen conjuncts of `msOK`, in order. -/
theorem msOK_parts {c : Cfg} (h : msOK c = true) :
    2 ≤ c.n0 ∧ 3 ≤ c.B ∧ 1 ≤ c.len ∧ c.limit = c.n0 + c.len - 1 ∧
      c.limit < c.B * c.B ∧ c.B + 1 < 2 ^ 20 ∧ c.limit < 2 ^ 32 ∧
      0 < c.tab ∧ c.tab ≤ 2 ^ 10 ∧ c.handoff < 2 ^ 32 ∧
      c.capL ≤ 2 ^ 51 ∧ c.capS ≤ 2 ^ 56 ∧ c.capLog ≤ 2 ^ 56 ∧
      c.seed < 2 ^ 56 ∧ c.cell1 = fpDlit + 2 * pack ∧
      c.logs.all (fun e => decide (e.1 < c.tab) && decide (e.2 < 2 ^ 56)) = true := by
  simp only [msOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2,
    h.1.1.1.1.2,
    h.1.1.1.2,
    h.1.1.2,
    h.1.2,
    h.2⟩

theorem ok_n0 {c : Cfg} (h : msOK c = true) : 2 ≤ c.n0 := (msOK_parts h).1
theorem ok_B3 {c : Cfg} (h : msOK c = true) : 3 ≤ c.B := (msOK_parts h).2.1
theorem ok_len {c : Cfg} (h : msOK c = true) : 1 ≤ c.len := (msOK_parts h).2.2.1
theorem ok_limit {c : Cfg} (h : msOK c = true) : c.limit = c.n0 + c.len - 1 :=
  (msOK_parts h).2.2.2.1
theorem ok_sq {c : Cfg} (h : msOK c = true) : c.limit < c.B * c.B :=
  (msOK_parts h).2.2.2.2.1
theorem ok_Blt {c : Cfg} (h : msOK c = true) : c.B + 1 < 2 ^ 20 :=
  (msOK_parts h).2.2.2.2.2.1
theorem ok_lim32 {c : Cfg} (h : msOK c = true) : c.limit < 2 ^ 32 :=
  (msOK_parts h).2.2.2.2.2.2.1
theorem ok_tab0 {c : Cfg} (h : msOK c = true) : 0 < c.tab :=
  (msOK_parts h).2.2.2.2.2.2.2.1
theorem ok_tab {c : Cfg} (h : msOK c = true) : c.tab ≤ 2 ^ 10 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.1
theorem ok_handoff {c : Cfg} (h : msOK c = true) : c.handoff < 2 ^ 32 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.1
theorem ok_capL {c : Cfg} (h : msOK c = true) : c.capL ≤ 2 ^ 51 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.1
theorem ok_capS {c : Cfg} (h : msOK c = true) : c.capS ≤ 2 ^ 56 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_capLog {c : Cfg} (h : msOK c = true) : c.capLog ≤ 2 ^ 56 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_seed {c : Cfg} (h : msOK c = true) : c.seed < 2 ^ 56 :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_cell1 {c : Cfg} (h : msOK c = true) : c.cell1 = fpDlit + 2 * pack :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_logs {c : Cfg} (h : msOK c = true) :
    c.logs.all (fun e => decide (e.1 < c.tab) && decide (e.2 < 2 ^ 56)) = true :=
  (msOK_parts h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ### Derived numeric facts -/

theorem one_lt_M : (1:Nat) < M := by decide
theorem two20_lt_M : (2:Nat) ^ 20 < M := by decide
theorem two32_lt_M : (2:Nat) ^ 32 < M := by decide

theorem ok_BM {c : Cfg} (h : msOK c = true) : c.B < M := by
  have h1 := ok_Blt h; have h2 := two20_lt_M; omega

theorem ok_B_pos {c : Cfg} (h : msOK c = true) : 0 < c.B := by
  have := ok_B3 h; omega

theorem ok_limM {c : Cfg} (h : msOK c = true) : c.limit < M := by
  have h1 := ok_lim32 h; have h2 := two32_lt_M; omega

theorem ok_tabM {c : Cfg} (h : msOK c = true) : c.tab < M := by
  have h1 := ok_tab h
  have h2 : (2:Nat) ^ 10 < M := by decide
  omega

theorem ok_handoffM {c : Cfg} (h : msOK c = true) : c.handoff < M := by
  have h1 := ok_handoff h; have h2 := two32_lt_M; omega

theorem ok_n0_le {c : Cfg} (h : msOK c = true) : c.n0 ≤ c.limit := by
  have h1 := ok_limit h; have h2 := ok_len h; omega

theorem ok_n0M {c : Cfg} (h : msOK c = true) : c.n0 < M :=
  Nat.lt_of_le_of_lt (ok_n0_le h) (ok_limM h)

/-- The flat loop index decodes without wrapping, and the candidate it decodes
to is in `[n0, limit]`. -/
theorem ok_idx {c : Cfg} (h : msOK c = true) {k : Nat} (hk : k < c.len * c.B) :
    k < M ∧ k / c.B < c.len ∧ k % c.B < c.B ∧
      c.n0 + k / c.B ≤ c.limit := by
  have hB : 0 < c.B := ok_B_pos h
  have hdiv : k / c.B < c.len := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have hlim := ok_limit h
  have hlen := ok_len h
  have hlt : c.len * c.B ≤ 2 ^ 32 * 2 ^ 20 := by
    have h1 : c.len ≤ 2 ^ 32 := by
      have := ok_lim32 h; omega
    have h2 : c.B ≤ 2 ^ 20 := by have := ok_Blt h; omega
    exact Nat.mul_le_mul h1 h2
  have hfits : (2:Nat) ^ 32 * 2 ^ 20 < M := by decide
  exact ⟨by omega, hdiv, Nat.mod_lt _ hB, by omega⟩

/-! ### Small facts about the wrappers -/

theorem MA_lt (a b : Nat) : MA a b < M := Nat.mod_lt _ M_pos
theorem MS_lt (a b : Nat) : MS a b < M := Nat.mod_lt _ M_pos
theorem MMul_lt (a b : Nat) : MMul a b < M := Nat.mod_lt _ M_pos

theorem bitOf_lt (p : Prop) [Decidable p] : bitOf p < M := by
  unfold bitOf; split <;> decide

theorem bitOf_le_one (p : Prop) [Decidable p] : bitOf p ≤ 1 := by
  unfold bitOf; split <;> omega

theorem bitOf_pos {p : Prop} [Decidable p] (h : p) : bitOf p = 1 := if_pos h
theorem bitOf_neg {p : Prop} [Decidable p] (h : ¬ p) : bitOf p = 0 := if_neg h


/-- `1 − flag` is the negated flag. -/
theorem MS_one_bit (p : Prop) [Decidable p] : MS 1 (bitOf p) = bitOf (¬ p) := by
  by_cases hp : p
  · rw [bitOf_pos hp, bitOf_neg (fun t => t hp)]
    show (1 + (M - 1)) % M = 0
    decide
  · rw [bitOf_neg hp, bitOf_pos hp]
    show (1 + (M - 0)) % M = 1
    decide

theorem MA_zero_right {a : Nat} (h : a < M) : MA a 0 = a := by
  show (a + 0) % M = a
  rw [Nat.add_zero, Nat.mod_eq_of_lt h]

theorem MA_zero_left {a : Nat} (h : a < M) : MA 0 a = a := by
  show (0 + a) % M = a
  rw [Nat.zero_add, Nat.mod_eq_of_lt h]

theorem MMul_one_right {a : Nat} (h : a < M) : MMul a 1 = a := by
  show (a * 1) % M = a
  rw [Nat.mul_one, Nat.mod_eq_of_lt h]

theorem MMul_one_left {a : Nat} (h : a < M) : MMul 1 a = a := by
  show (1 * a) % M = a
  rw [Nat.one_mul, Nat.mod_eq_of_lt h]

theorem MMul_zero_left (a : Nat) : MMul 0 a = 0 := by
  show (0 * a) % M = 0
  rw [Nat.zero_mul, Nat.zero_mod]

theorem MMul_zero_right (a : Nat) : MMul a 0 = 0 := by
  show (a * 0) % M = 0
  rw [Nat.mul_zero, Nat.zero_mod]

theorem MMul_comm (a b : Nat) : MMul a b = MMul b a := by
  show (a * b) % M = (b * a) % M
  rw [Nat.mul_comm]

/-- Two flags multiplied is their conjunction. -/
theorem MMul_bit (p q : Prop) [Decidable p] [Decidable q] :
    MMul (bitOf p) (bitOf q) = bitOf (p ∧ q) := by
  by_cases hp : p
  · by_cases hq : q
    · rw [bitOf_pos hp, bitOf_pos hq, bitOf_pos (show p ∧ q from ⟨hp, hq⟩)]; rfl
    · rw [bitOf_pos hp, bitOf_neg hq,
        bitOf_neg (show ¬ (p ∧ q) from fun t => hq t.2)]
      exact MMul_zero_right 1
  · rw [bitOf_neg hp, bitOf_neg (show ¬ (p ∧ q) from fun t => hp t.1)]
    exact MMul_zero_left _

/-- `MA` absorbs a `% M` on its left argument: this is what lets a chain of
`MA _ 0` steps be collapsed. -/
theorem MA_MA_zero (a b : Nat) : MA (MA a 0) b = MA a b := by
  show ((a + 0) % M + b) % M = (a + b) % M
  rw [Nat.add_zero, Nat.mod_add_mod]

/-- Gating a value by a flag on the left. -/
theorem MMul_bit_left (p : Prop) [Decidable p] {x : Nat} (hx : x < M) :
    MMul (bitOf p) x = if p then x else 0 := by
  by_cases hp : p
  · rw [bitOf_pos hp, if_pos hp, MMul_one_left hx]
  · rw [bitOf_neg hp, if_neg hp, MMul_zero_left]

/-- Gating a value by a flag on the right. -/
theorem MMul_bit_right (p : Prop) [Decidable p] {x : Nat} (hx : x < M) :
    MMul x (bitOf p) = if p then x else 0 := by
  rw [MMul_comm]; exact MMul_bit_left p hx

/-- The branchless select `g·x + (1−g)·y`. -/
theorem select_bit (p : Prop) [Decidable p] {x y : Nat} (hx : x < M) (hy : y < M) :
    MA (MMul (bitOf p) x) (MMul (bitOf (¬ p)) y) = if p then x else y := by
  by_cases hp : p
  · rw [MMul_bit_left p hx, MMul_bit_left (¬ p) hy, if_pos hp, if_neg (fun t => t hp),
      MA_zero_right hx, if_pos hp]
  · rw [MMul_bit_left p hx, MMul_bit_left (¬ p) hy, if_neg hp, if_pos hp,
      MA_zero_left hy, if_neg hp]


/-! ## The machine's own arithmetic

`MA`, `MS`, `MMul` and `bitOf` are `denoteOp` at `.add`, `.sub`, `.mul` and at
a comparison — *definitionally*, with no side condition.  Every lemma in this
section is therefore either `rfl` or one `Nat.mod` fact.
-/

theorem dop_add (a b : Nat) : denoteOp .add a b = some (MA a b) := rfl
theorem dop_sub (a b : Nat) : denoteOp .sub a b = some (MS a b) := rfl
theorem dop_mul (a b : Nat) : denoteOp .mul a b = some (MMul a b) := rfl
theorem dop_eq (a b : Nat) : denoteOp .eq a b = some (bitOf (a = b)) := rfl
theorem dop_lt (a b : Nat) : denoteOp .lt a b = some (bitOf (a < b)) := rfl
theorem dop_le (a b : Nat) : denoteOp .le a b = some (bitOf (a ≤ b)) := rfl
theorem dop_gt (a b : Nat) : denoteOp .gt a b = some (bitOf (b < a)) := rfl
theorem dop_ge (a b : Nat) : denoteOp .ge a b = some (bitOf (b ≤ a)) := rfl
theorem dop_shl (a b : Nat) : denoteOp .shl a b = some ((a <<< b) % M) := rfl

theorem dop_udiv {a b : Nat} (hb : b ≠ 0) (ha : a < M) :
    denoteOp .udiv a b = some (a / b) := denoteOp_udiv_of_ne hb ha

theorem dop_urem {a b : Nat} (hb : b ≠ 0) (ha : a < M) :
    denoteOp .urem a b = some (a % b) := denoteOp_urem_of_ne hb ha

theorem dop_lshr {a b : Nat} (ha : a < M) :
    denoteOp .lshr a b = some (a >>> b) := denoteOp_lshr_of_lt ha

/-- `bor` on two flags. -/
theorem dop_bor_bit (p q : Prop) [Decidable p] [Decidable q] :
    denoteOp .bor (bitOf p) (bitOf q) = some (bitOf (p ∨ q)) := by
  by_cases hp : p <;> by_cases hq : q
  · rw [bitOf_pos hp, bitOf_pos hq, bitOf_pos (show p ∨ q from Or.inl hp)]; rfl
  · rw [bitOf_pos hp, bitOf_neg hq, bitOf_pos (show p ∨ q from Or.inl hp)]; rfl
  · rw [bitOf_neg hp, bitOf_pos hq, bitOf_pos (show p ∨ q from Or.inr hq)]; rfl
  · rw [bitOf_neg hp, bitOf_neg hq,
      bitOf_neg (show ¬ (p ∨ q) from fun t => t.elim hp hq)]; rfl

/-! ## The read-then-evaluate step

One lemma joins `RegFrame.srun_read_write` to `BlockDefined.sval_binop_val`:
read a register out of a block at the instruction that wrote it, and evaluate
that instruction from named operand values.  Every value proof below is a
chain of these.
-/

theorem read_binop {k d : Nat} {xs : List Instr} {op : Op} {l r : Operand}
    {ys : List Instr} (hys : writes d ys = false) {s : RegState} {a b v : Nat}
    (hl : denoteOperand k (srun k s xs) l = a)
    (hr : denoteOperand k (srun k s xs) r = b)
    (hop : denoteOp op a b = some v) :
    srun k s (xs ++ .binop d op l r :: ys) d = v := by
  rw [srun_read_write k d xs (.binop d op l r) ys rfl hys]
  exact sval_binop_val hl hr hop

theorem read_mov {k d : Nat} {xs : List Instr} {src : Operand}
    {ys : List Instr} (hys : writes d ys = false) {s : RegState} {a : Nat}
    (hl : denoteOperand k (srun k s xs) src = a) :
    srun k s (xs ++ .mov d src :: ys) d = a := by
  rw [srun_read_write k d xs (.mov d src) ys rfl hys]
  exact hl

/-- Reading a register the block never writes. -/
theorem read_frame {k d : Nat} {l : List Instr} (h : writes d l = false)
    (s : RegState) : srun k s l d = s d := srun_frame k d l h s


/-- One step of a block walk: the instruction at the split point wrote `d`. -/
theorem step_write {k d : Nat} {s : RegState} {p q : List Instr} {op : Op}
    {l r : Operand} (hq : q = p ++ [Instr.binop d op l r]) {a b v : Nat}
    (hl : denoteOperand k (srun k s p) l = a)
    (hr : denoteOperand k (srun k s p) r = b)
    (hop : denoteOp op a b = some v) : srun k s q d = v := by
  rw [hq]
  exact read_binop (by rfl) hl hr hop

/-- One step of a block walk: the instruction at the split point did not write
`x`, so its value is carried. -/
theorem step_frame {k x : Nat} {s : RegState} {p q : List Instr} {i : Instr}
    (hq : q = p ++ [i]) (hw : writes x [i] = false) {v : Nat}
    (hv : srun k s p x = v) : srun k s q x = v := by
  rw [hq, srun_frame_append k x p [i] hw]; exact hv

/-- Several steps at once: a suffix that does not write `x`. -/
theorem run_frame {k x : Nat} {s : RegState} {p q ys : List Instr}
    (hq : q = p ++ ys) (hw : writes x ys = false) {v : Nat}
    (hv : srun k s p x = v) : srun k s q x = v := by
  rw [hq, srun_frame_append k x p ys hw]; exact hv

/-- The same, with the carried value **before** the (auto-discharged) frame
condition, so that the register is determined before the frame check runs. -/
theorem run_frameA {k x : Nat} {s : RegState} {p q ys : List Instr}
    (hq : q = p ++ ys) {v : Nat} (hv : srun k s p x = v)
    (hw : writes x ys = false := by rfl) : srun k s q x = v := by
  rw [hq, srun_frame_append k x p ys hw]; exact hv

/-- A register read at an empty prefix. -/
theorem srun_entry (k x : Nat) (s : RegState) (p : List Instr) (hp : p = []) :
    srun k s p x = s x := by rw [hp]; rfl

end LeanCompCert.Ports.RamareMStar140M
