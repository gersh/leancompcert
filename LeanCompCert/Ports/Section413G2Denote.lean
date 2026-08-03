import LeanCompCert.Ports.Section413G2Program
import LeanCompCert.Verified.Algorithm.ArrayBridge
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# The §4.1.3 `g₂` sweep: the machine denotes the transparent model

`Ports/Section413G2Program.lean` states two open obligations.  This file
attacks the first,

```text
(1)  (g2Program c).denote = some (c.tFlag)          [machine ⇒ model]
```

by the `ArrayMobiusDenotation` / `SingSeriesC17` architecture: one *spec
lemma per block*, proved against the total meaning `ArrayFoldBridge.arun`
of a straight-line array block, composed along `arun_append`.

The body is 1446 instructions, but it is built from seven reusable
sub-blocks — `guardBody`, `muxBody`, `smDecomp`, `cmpLtBody`, `selTriple`,
`mulWideBody`, `divP18Body` — of which `cmulBody` (378 instructions, used
three times per iteration) is a pure composite.  Each sub-block is proved
**once**, with variable register parameters, so the proof size is governed
by the number of *distinct* blocks and not by the instruction count.

## What is proved here

See the closing `## OPEN` section for the precise statements that remain.
Nothing below is an axiom, a `sorry`, or a weakened restatement of the
obligation.
-/

namespace LeanCompCert.Ports.Section413G2Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock (sdest sval srun srun_nil srun_cons
  srun_append srun_untouched srun_lt_of_lt SDefined SAllDefined NoDivI)
open LeanCompCert.Ports.Section413G2Program
open LeanCompCert.Ports.CDEMAbelScan (mulWideBody muxBody storeLit)

/-! ## §1 Straight-line array blocks: frame, bounds, definedness

Three facts about `arun` that every block spec below needs and that
`Verified/ArrayFoldBridge.lean` does not state: which registers a block can
touch, that every register stays a word, and that a block whose only
partial operations divide by a nonzero *literal* is defined in every state.
-/

/-- The register an array instruction writes, if any.  A `store` writes no
register. -/
def adest : AInstr → Option Nat
  | .scalar i => some (InstrBlock.sdest i)
  | .load dest _ => some dest
  | .store _ _ => none

/-- Whether an instruction writes the array. -/
def astores : AInstr → Bool
  | .store _ _ => true
  | _ => false

/-- **Register frame.**  A block that never writes `j` leaves `j` alone. -/
theorem arun_regs_frame (k : Nat) :
    ∀ (l : List AInstr) (s : AState) (j : Nat),
      (∀ i ∈ l, adest i ≠ some j) → (arun k s l).regs j = s.regs j := by
  intro l
  induction l with
  | nil => intro s j _; rfl
  | cons i rest ih =>
      intro s j h
      have hi : adest i ≠ some j := h i (by simp)
      have hstep : (astep k s i).regs j = s.regs j := by
        cases i with
        | scalar instr =>
            have hne : j ≠ InstrBlock.sdest instr := by
              intro hEq; exact hi (by rw [adest, hEq])
            simp only [astep, AState.writeReg, if_neg hne]
        | load dest idxReg =>
            have hne : j ≠ dest := by
              intro hEq; exact hi (by rw [adest, hEq])
            simp only [astep, AState.writeReg, if_neg hne]
        | store _ _ => rfl
      rw [arun_cons, ih (astep k s i) j (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        hstep]

/-- **Array frame.**  A block with no `store` leaves the array alone. -/
theorem arun_arr_frame (k : Nat) :
    ∀ (l : List AInstr) (s : AState),
      (∀ i ∈ l, astores i = false) → (arun k s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      have hi : astores i = false := h i (by simp)
      have hstep : (astep k s i).arr = s.arr := by
        cases i with
        | scalar instr => rfl
        | load dest idxReg => rfl
        | store a b => exact absurd hi (by simp [astores])
      rw [arun_cons, ih (astep k s i) (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        hstep]

/-- **Word bound.**  Every register and every array cell stays below `2⁶⁴`,
whatever the block does. -/
theorem arun_lt (k : Nat) :
    ∀ (l : List AInstr) (s : AState), (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
      (∀ j, (arun k s l).regs j < M) ∧ (∀ j, (arun k s l).arr j < M) := by
  intro l
  induction l with
  | nil => intro s hr ha; exact ⟨hr, ha⟩
  | cons i rest ih =>
      intro s hr ha
      refine ih (astep k s i) ?_ ?_
      · intro j
        cases i with
        | scalar instr =>
            by_cases hEq : j = InstrBlock.sdest instr
            · subst hEq
              simp only [astep, AState.writeReg, if_pos rfl]
              cases instr with
              | mov d src =>
                  show denoteOperand k s.regs src < M
                  cases src with
                  | reg i' => exact hr i'
                  | lit v => exact Nat.mod_lt _ M_pos
                  | idx => exact Nat.mod_lt _ M_pos
              | binop d op l' r' =>
                  show (denoteOp op (denoteOperand k s.regs l')
                    (denoteOperand k s.regs r')).getD 0 < M
                  cases hv : denoteOp op (denoteOperand k s.regs l')
                      (denoteOperand k s.regs r') with
                  | none => simpa [hv] using M_pos
                  | some v => exact denoteOp_lt op _ _ _ hv
            · simp only [astep, AState.writeReg, if_neg hEq]; exact hr j
        | load dest idxReg =>
            by_cases hEq : j = dest
            · subst hEq
              simp only [astep, AState.writeReg, if_pos rfl]
              exact ha _
            · simp only [astep, AState.writeReg, if_neg hEq]; exact hr j
        | store idxReg srcReg => exact hr j
      · intro j
        cases i with
        | scalar instr => exact ha j
        | load dest idxReg => exact ha j
        | store idxReg srcReg =>
            by_cases hEq : j = s.regs idxReg
            · subst hEq
              simp only [astep, AState.writeArr, if_pos rfl]
              exact hr _
            · simp only [astep, AState.writeArr, if_neg hEq]; exact ha j

theorem arun_regs_lt (k : Nat) (l : List AInstr) (s : AState)
    (hr : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    ∀ j, (arun k s l).regs j < M := (arun_lt k l s hr ha).1

theorem arun_arr_lt (k : Nat) (l : List AInstr) (s : AState)
    (hr : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    ∀ j, (arun k s l).arr j < M := (arun_lt k l s hr ha).2

/-- An instruction that is defined in **every** state: no `udiv`/`urem` by a
register, no array access.  The divisor of a literal division is checked
nonzero. -/
def alwaysDef : AInstr → Bool
  | .scalar (.mov _ _) => true
  | .scalar (.binop _ .udiv _ (.lit v)) => decide (v % M ≠ 0)
  | .scalar (.binop _ .urem _ (.lit v)) => decide (v % M ≠ 0)
  | .scalar (.binop _ .udiv _ _) => false
  | .scalar (.binop _ .urem _ _) => false
  | .scalar (.binop _ _ _ _) => true
  | .load _ _ => false
  | .store _ _ => false

/-- **Definedness for free.**  A block of always-defined instructions is
`AllDefined` at every array length, index and state. -/
theorem allDefined_of_alwaysDef (len k : Nat) :
    ∀ (l : List AInstr) (s : AState), l.all alwaysDef = true →
      AllDefined len k s l := by
  intro l
  induction l with
  | nil => intro s _; exact trivial
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, ih (astep k s i) h.2⟩
      cases i with
      | scalar instr =>
          cases instr with
          | mov d src => exact trivial
          | binop d op l' r' =>
              cases op <;>
                simp only [ADefined, denoteOp, Option.isSome] <;>
                first
                  | rfl
                  | (cases r' with
                      | reg i' => exact absurd h.1 (by simp [alwaysDef])
                      | idx => exact absurd h.1 (by simp [alwaysDef])
                      | lit v =>
                          have hv : v % M ≠ 0 := by
                            have := h.1
                            simp only [alwaysDef, decide_eq_true_eq] at this
                            exact this
                          simp only [denoteOperand, if_neg hv])
      | load _ _ => exact absurd h.1 (by simp [alwaysDef])
      | store _ _ => exact absurd h.1 (by simp [alwaysDef])

/-! ## §2 Word arithmetic used by the block specs -/

theorem lor_lt_M {a b : Nat} (ha : a < M) (hb : b < M) : a ||| b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem lxor_lt_M {a b : Nat} (ha : a < M) (hb : b < M) : a ^^^ b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem land_lt_M {a b : Nat} (ha : a < M) (hb : b < M) : a &&& b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem lor_mod_M {a b : Nat} (ha : a < M) (hb : b < M) :
    (a ||| b) % M = a ||| b := Nat.mod_eq_of_lt (lor_lt_M ha hb)

theorem bnat_le_one (p : Prop) [Decidable p] : bnat p ≤ 1 := by
  unfold bnat; split <;> omega

theorem bnat_lt_M (p : Prop) [Decidable p] : bnat p < M := by
  have := bnat_le_one p
  have : (1:Nat) < M := by decide
  omega

/-- A gated flag times a word is that word or zero, and the machine's
truncation is invisible. -/
theorem bnat_mul_mod (p : Prop) [Decidable p] {g : Nat} (hg : g < M) :
    (bnat p * g) % M = bnat p * g := by
  refine Nat.mod_eq_of_lt ?_
  unfold bnat
  split
  · omega
  · have : (0:Nat) < M := M_pos
    omega

theorem bnat_mul_lt_M (p : Prop) [Decidable p] {g : Nat} (hg : g < M) :
    bnat p * g < M := by
  unfold bnat; split
  · omega
  · rw [Nat.zero_mul]; exact M_pos

/-- The machine's `1 − x` on a flag. -/
theorem msub_bit {x : Nat} (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hM : (2:Nat) ≤ M := by decide
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]

theorem litM (v : Nat) (h : v < M) : v % M = v := Nat.mod_eq_of_lt h

theorem CAP_mod : CAP % M = CAP := by decide
theorem CAP2_mod : (2 * CAP) % M = 2 * CAP := by decide
theorem H63_mod : H63 % M = H63 := by decide
theorem zero_mod_M : (0:Nat) % M = 0 := by decide
theorem one_mod_M : (1:Nat) % M = 1 := by decide

/-- Reading the register a `set` just wrote. -/
theorem set_get (s : RegState) (i v : Nat) : (s.set i v) i = v := if_pos rfl

/-- Reading any other register through a `set`. -/
theorem set_get_ne (s : RegState) {i j : Nat} (v : Nat) (h : j ≠ i) :
    (s.set i v) j = s j := if_neg h

/-! ## §3 The sub-blocks, in the scalar machine

Every sub-block of the body except the four array-access points is pure
scalar code.  `Verified/ArrayScalarBlock.lean`'s `lift` moves it into the
scalar machine — `arun k s (lift xs) = ⟨srun k s.regs xs, s.arr⟩` — where
the existing `InstrBlock` library applies and the array is never carried
through a `simp`.  Each block below is therefore given twice: once as a
`List Instr` (with a `rfl` bridge to the port's `List AInstr`) and once as
its specification against the transparent model of §8 of the port.
-/

/-! ### `guardBody`: the accumulator width guard

Note the shape of `guardG`: the cap is a **variable**.  Lean's `Nat.add` and
`Nat.mul` recurse on their *second* argument, so a twenty-digit numeral
sitting there unary-unfolds the moment anything tries to whnf the term —
which a `simp only` chain over a branchless block does, at the `Decidable`
instance of every comparison.  Every block spec below is therefore proved
with its literals abstracted, and instantiated at the end.  The emitted
program is untouched: `guardBody_lift` is `rfl`.
-/

/-- `Section413G2Program.guardBody`, as a scalar block with its cap
abstracted. -/
def guardG (cap gate w sc : Nat) : List Instr :=
  [ .binop sc .add (.reg w) (.lit cap)
  , .binop sc .gt (.reg sc) (.lit (2 * cap))
  , .binop sc .mul (.reg sc) (.reg gate)
  , .binop rViol .bor (.reg rViol) (.reg sc) ]

theorem guardBody_lift (gate w sc : Nat) :
    guardBody gate w sc = lift (guardG CAP gate w sc) := rfl

theorem guardG_noDiv (cap gate w sc : Nat) :
    (guardG cap gate w sc).all NoDivI = true := rfl

/-- **The width guard, with an abstract cap.** -/
theorem guardG_spec (k : Nat) (s : RegState) (cap gate w sc : Nat)
    (hcap : cap % M = cap) (hcap2 : (2 * cap) % M = 2 * cap)
    (hV : sc ≠ rViol) (hg : sc ≠ gate) (hs : ∀ j, s j < M) :
    srun k s (guardG cap gate w sc) rViol
      = s rViol ||| ((if 2 * cap < (s w + cap) % M then (1:Nat) else 0) * s gate) := by
  have hM0 : 0 < M := M_pos
  have hM1 : (1:Nat) < M := by decide
  have hgM : s gate < M := hs gate
  have hvM : s rViol < M := hs rViol
  have key : srun k s (guardG cap gate w sc) rViol
      = (s rViol |||
          ((if 2 * cap < (s w + cap) % M then (1:Nat) else 0) * s gate) % M) % M := by
    simp only [guardG, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hcap, hcap2, if_true, gt_iff_lt,
      if_neg hg, if_neg (Ne.symm hg), if_neg hV, if_neg (Ne.symm hV)]
  have h1 : ((if 2 * cap < (s w + cap) % M then (1:Nat) else 0) * s gate) % M
      = (if 2 * cap < (s w + cap) % M then (1:Nat) else 0) * s gate := by
    refine Nat.mod_eq_of_lt ?_
    split <;> omega
  have h2 : (if 2 * cap < (s w + cap) % M then (1:Nat) else 0) * s gate < M := by
    split <;> omega
  rw [key, h1, lor_mod_M hvM h2]

/-- **The width guard computes `tguard`.**  `sc` is scratch: it must differ
from the gate register and from `rViol`; everything else is untouched. -/
theorem guardG_tguard (k : Nat) (s : RegState) (gate w sc : Nat)
    (hV : sc ≠ rViol) (hg : sc ≠ gate) (hs : ∀ j, s j < M) :
    srun k s (guardG CAP gate w sc) rViol = tguard (s gate) (s w) (s rViol) := by
  rw [guardG_spec k s CAP gate w sc CAP_mod CAP2_mod hV hg hs]
  simp only [tguard, bnat]

/-- The guard writes only `sc` and `rViol`. -/
theorem guardG_frame (k : Nat) (s : RegState) (cap gate w sc j : Nat)
    (h1 : j ≠ sc) (h2 : j ≠ rViol) :
    srun k s (guardG cap gate w sc) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [guardG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

/-! ### `muxBody`: the branchless select -/

/-- `CDEMAbelScan.muxBody`, as a scalar block. -/
def muxS (dst gate x y sc : Nat) : List Instr :=
  [ .binop sc .sub (.lit 1) (.reg gate)
  , .binop sc .mul (.reg sc) (.reg y)
  , .binop dst .mul (.reg gate) (.reg x)
  , .binop dst .add (.reg dst) (.reg sc) ]

theorem muxBody_lift (dst gate x y sc : Nat) :
    muxBody dst gate x y sc = lift (muxS dst gate x y sc) := rfl

theorem muxS_noDiv (dst gate x y sc : Nat) :
    (muxS dst gate x y sc).all NoDivI = true := rfl

/-- **The select computes a select.**  The scratch register `sc` must differ
from `dst`, `gate`, `x` and `y` — the instruction-order hazard recorded in
`muxBody`'s own docstring. -/
theorem muxS_spec (k : Nat) (s : RegState) (dst gate x y sc : Nat)
    (hd : sc ≠ dst) (hgt : sc ≠ gate) (hx : sc ≠ x) (hy : sc ≠ y)
    (hg1 : s gate ≤ 1) (hs : ∀ j, s j < M) :
    srun k s (muxS dst gate x y sc) dst = (if s gate = 1 then s x else s y) := by
  have hxM : s x < M := hs x
  have hyM : s y < M := hs y
  have key : srun k s (muxS dst gate x y sc) dst
      = ((s gate * s x) % M + ((1 + (M - s gate)) % M * s y) % M) % M := by
    simp only [muxS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, one_mod_M, if_true, if_neg hd, if_neg hgt, if_neg hx,
      if_neg hy, if_neg (Ne.symm hd), if_neg (Ne.symm hgt), if_neg (Ne.symm hx),
      if_neg (Ne.symm hy)]
  rw [key, msub_bit hg1]
  rcases (by omega : s gate = 0 ∨ s gate = 1) with h | h <;> rw [h]
  · rw [if_neg (by decide : ¬ (0:Nat) = 1), Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add, Nat.sub_zero, Nat.one_mul, Nat.mod_eq_of_lt hyM,
      Nat.mod_eq_of_lt hyM]
  · rw [if_pos rfl, Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.zero_mod,
      Nat.add_zero, Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt hxM]

/-- The select writes only `dst` and `sc`. -/
theorem muxS_frame (k : Nat) (s : RegState) (dst gate x y sc j : Nat)
    (h1 : j ≠ dst) (h2 : j ≠ sc) :
    srun k s (muxS dst gate x y sc) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [muxS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

end LeanCompCert.Ports.Section413G2Denote
