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

/-! ### `smDecomp`: sign bit, magnitude, and the magnitude guard -/

/-- The two instructions before the select. -/
def smPre (h63 w sg : Nat) : List Instr :=
  [ .binop sg .ge (.reg w) (.lit h63)
  , .binop 108 .sub (.lit 0) (.reg w) ]

/-- The three instructions after it: the gated magnitude guard. -/
def smPost (cap gate mg : Nat) : List Instr :=
  [ .binop 110 .gt (.reg mg) (.lit cap)
  , .binop 110 .mul (.reg 110) (.reg gate)
  , .binop rViol .bor (.reg rViol) (.reg 110) ]

/-- `Section413G2Program.smDecomp`, as a scalar block with its two bounds
abstracted. -/
def smDecompG (h63 cap gate w sg mg : Nat) : List Instr :=
  smPre h63 w sg ++ muxS mg sg 108 w 109 ++ smPost cap gate mg

theorem smDecomp_lift (gate w sg mg : Nat) :
    smDecomp gate w sg mg = lift (smDecompG H63 CAP gate w sg mg) := rfl

theorem smDecompG_noDiv (h63 cap gate w sg mg : Nat) :
    (smDecompG h63 cap gate w sg mg).all NoDivI = true := rfl

theorem smPre_spec (k : Nat) (s : RegState) (h63 w sg : Nat)
    (hh : h63 % M = h63) (hsg : sg ≠ 108) (hw : w ≠ sg) :
    srun k s (smPre h63 w sg) sg = (if h63 ≤ s w then 1 else 0) ∧
      srun k s (smPre h63 w sg) 108 = tsub 0 (s w) := by
  constructor <;>
    simp only [smPre, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hh, zero_mod_M, tsub, if_true, ge_iff_le,
      if_neg hsg, if_neg (Ne.symm hsg), if_neg hw, if_neg (Ne.symm hw)]

theorem smPre_frame (k : Nat) (s : RegState) (h63 w sg j : Nat)
    (h1 : j ≠ sg) (h2 : j ≠ 108) :
    srun k s (smPre h63 w sg) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [smPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp only [sdest] <;> omega

theorem smPost_spec (k : Nat) (s : RegState) (cap gate mg : Nat)
    (hc : cap % M = cap) (hs : ∀ j, s j < M)
    (h1 : mg ≠ 110) (h2 : gate ≠ 110) :
    srun k s (smPost cap gate mg) rViol
      = s rViol ||| ((if cap < s mg then 1 else 0) * s gate) := by
  have hM0 : 0 < M := M_pos
  have hM1 : (1:Nat) < M := by decide
  have hgM : s gate < M := hs gate
  have hvM : s rViol < M := hs rViol
  have key : srun k s (smPost cap gate mg) rViol
      = (s rViol ||| ((if cap < s mg then (1:Nat) else 0) * s gate) % M) % M := by
    simp only [smPost, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hc, if_true, if_false, gt_iff_lt,
      if_neg h1, if_neg (Ne.symm h1), if_neg h2, if_neg (Ne.symm h2),
      show (rViol : Nat) ≠ 110 by decide,
      show (110 : Nat) ≠ rViol by decide]
  have e1 : ((if cap < s mg then (1:Nat) else 0) * s gate) % M
      = (if cap < s mg then (1:Nat) else 0) * s gate := by
    refine Nat.mod_eq_of_lt ?_
    split <;> omega
  have e2 : (if cap < s mg then (1:Nat) else 0) * s gate < M := by
    split <;> omega
  rw [key, e1, lor_mod_M hvM e2]

theorem smPost_frame (k : Nat) (s : RegState) (cap gate mg j : Nat)
    (h1 : j ≠ 110) (h2 : j ≠ rViol) :
    srun k s (smPost cap gate mg) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [smPost, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [sdest] <;> omega

/-- The whole block writes only `sg`, `mg`, `rViol` and the three fixed
scratch registers `108`–`110`. -/
theorem smDecompG_frame (k : Nat) (s : RegState) (h63 cap gate w sg mg j : Nat)
    (h1 : j ≠ sg) (h2 : j ≠ mg) (h3 : j ≠ rViol)
    (h4 : j ≠ 108) (h5 : j ≠ 109) (h6 : j ≠ 110) :
    srun k s (smDecompG h63 cap gate w sg mg) j = s j := by
  rw [smDecompG, srun_append, srun_append, smPost_frame _ _ _ _ _ _ h6 h3,
    muxS_frame _ _ _ _ _ _ _ _ h2 h5, smPre_frame _ _ _ _ _ _ h1 h4]

/-- **The decomposition computes `tmag`, and guards the magnitude.** -/
theorem smDecompG_spec (k : Nat) (s : RegState) (h63 cap gate w sg mg : Nat)
    (hh : h63 % M = h63) (hc : cap % M = cap) (hs : ∀ j, s j < M)
    (hsg0 : sg ≠ rViol) (hsg8 : sg ≠ 108) (hsg9 : sg ≠ 109) (hsgA : sg ≠ 110)
    (hmg0 : mg ≠ rViol) (hmg9 : mg ≠ 109) (hmgA : mg ≠ 110)
    (hgt8 : gate ≠ 108) (hgt9 : gate ≠ 109) (hgtA : gate ≠ 110)
    (hw8 : w ≠ 108) (hw9 : w ≠ 109)
    (hsgmg : sg ≠ mg) (hwsg : w ≠ sg) (hgsg : gate ≠ sg) (hgmg : gate ≠ mg) :
    srun k s (smDecompG h63 cap gate w sg mg) sg = (if h63 ≤ s w then 1 else 0) ∧
    srun k s (smDecompG h63 cap gate w sg mg) mg
      = (if h63 ≤ s w then tsub 0 (s w) else s w) ∧
    srun k s (smDecompG h63 cap gate w sg mg) rViol
      = s rViol |||
        ((if cap < (if h63 ≤ s w then tsub 0 (s w) else s w) then 1 else 0) * s gate) := by
  -- stage 1: the two instructions before the select
  have h1s := smPre_spec k s h63 w sg hh hsg8 hwsg
  have h1lt : ∀ j, srun k s (smPre h63 w sg) j < M :=
    srun_lt_of_lt k (smPre h63 w sg) s hs
  have h1w : srun k s (smPre h63 w sg) w = s w :=
    smPre_frame k s h63 w sg w hwsg hw8
  have h1g : srun k s (smPre h63 w sg) gate = s gate :=
    smPre_frame k s h63 w sg gate hgsg hgt8
  have h1v : srun k s (smPre h63 w sg) rViol = s rViol :=
    smPre_frame k s h63 w sg rViol (Ne.symm hsg0) (by decide)
  -- stage 2: the select
  have h2m := muxS_spec k (srun k s (smPre h63 w sg)) mg sg 108 w 109
    (Ne.symm hmg9) (Ne.symm hsg9) (by decide) (Ne.symm hw9)
    (by rw [h1s.1]; split <;> omega) h1lt
  have h2lt : ∀ j, srun k (srun k s (smPre h63 w sg)) (muxS mg sg 108 w 109) j < M :=
    srun_lt_of_lt k _ _ h1lt
  have h2s : srun k (srun k s (smPre h63 w sg)) (muxS mg sg 108 w 109) sg
      = srun k s (smPre h63 w sg) sg :=
    muxS_frame k _ mg sg 108 w 109 sg hsgmg hsg9
  have h2g : srun k (srun k s (smPre h63 w sg)) (muxS mg sg 108 w 109) gate
      = srun k s (smPre h63 w sg) gate :=
    muxS_frame k _ mg sg 108 w 109 gate hgmg hgt9
  have h2v : srun k (srun k s (smPre h63 w sg)) (muxS mg sg 108 w 109) rViol
      = srun k s (smPre h63 w sg) rViol :=
    muxS_frame k _ mg sg 108 w 109 rViol (Ne.symm hmg0) (by decide)
  -- the magnitude, in closed form
  have hmag : srun k (srun k s (smPre h63 w sg)) (muxS mg sg 108 w 109) mg
      = (if h63 ≤ s w then tsub 0 (s w) else s w) := by
    rw [h2m, h1s.1, h1s.2, h1w]
    by_cases hb : h63 ≤ s w
    · rw [if_pos hb, if_pos hb, if_pos rfl]
    · rw [if_neg hb, if_neg hb, if_neg (by decide : ¬ (0:Nat) = 1)]
  -- stage 3: the guard
  refine ⟨?_, ?_, ?_⟩
  · rw [smDecompG, srun_append, srun_append,
      smPost_frame _ _ _ _ _ _ hsgA hsg0, h2s, h1s.1]
  · rw [smDecompG, srun_append, srun_append,
      smPost_frame _ _ _ _ _ _ hmgA hmg0, hmag]
  · rw [smDecompG, srun_append, srun_append,
      smPost_spec k _ cap gate mg hc h2lt hmgA hgtA, hmag, h2g, h1g, h2v, h1v]

/-- The `CAP`/`H63` instantiation: the block computes `tmag` and adds the
magnitude violation to `rViol`, exactly as `tcmul` reads it. -/
theorem smDecomp_tmag (k : Nat) (s : RegState) (gate w sg mg : Nat)
    (hs : ∀ j, s j < M)
    (hsg0 : sg ≠ rViol) (hsg8 : sg ≠ 108) (hsg9 : sg ≠ 109) (hsgA : sg ≠ 110)
    (hmg0 : mg ≠ rViol) (hmg9 : mg ≠ 109) (hmgA : mg ≠ 110)
    (hgt8 : gate ≠ 108) (hgt9 : gate ≠ 109) (hgtA : gate ≠ 110)
    (hw8 : w ≠ 108) (hw9 : w ≠ 109)
    (hsgmg : sg ≠ mg) (hwsg : w ≠ sg) (hgsg : gate ≠ sg) (hgmg : gate ≠ mg) :
    srun k s (smDecompG H63 CAP gate w sg mg) sg = (tmag (s w)).1 ∧
    srun k s (smDecompG H63 CAP gate w sg mg) mg = (tmag (s w)).2 ∧
    srun k s (smDecompG H63 CAP gate w sg mg) rViol
      = s rViol ||| (bnat (CAP < (tmag (s w)).2) * s gate) := by
  have h := smDecompG_spec k s H63 CAP gate w sg mg H63_mod CAP_mod hs
    hsg0 hsg8 hsg9 hsgA hmg0 hmg9 hmgA hgt8 hgt9 hgtA hw8 hw9
    hsgmg hwsg hgsg hgmg
  simp only [tmag, bnat]
  exact h

/-! ### `cmpLtBody`: the strict signed sign-magnitude comparison -/

/-- `Section413G2Program.cmpLtBody`, as a scalar block.  No literal in it is
larger than `1`, so nothing here needs abstracting. -/
def cmpLtS (sa la ha sb lb hb dst : Nat) : List Instr :=
  [ .binop 126 .lt (.reg ha) (.reg hb)
  , .binop 127 .eq (.reg ha) (.reg hb)
  , .binop 128 .lt (.reg la) (.reg lb)
  , .binop 129 .lt (.reg hb) (.reg ha)
  , .binop 130 .lt (.reg lb) (.reg la)
  , .binop 131 .mul (.reg 127) (.reg 128)
  , .binop 131 .add (.reg 131) (.reg 126)
  , .binop 139 .mul (.reg 127) (.reg 130)
  , .binop 139 .add (.reg 139) (.reg 129)
  , .binop 140 .sub (.lit 1) (.reg sb)
  , .binop 141 .mul (.reg sa) (.reg 140)
  , .binop 142 .mul (.reg sa) (.reg sb)
  , .binop 142 .mul (.reg 142) (.reg 139)
  , .binop 143 .sub (.lit 1) (.reg sa)
  , .binop 143 .mul (.reg 143) (.reg 140)
  , .binop 143 .mul (.reg 143) (.reg 131)
  , .binop dst .add (.reg 141) (.reg 142)
  , .binop dst .add (.reg dst) (.reg 143) ]

theorem cmpLtBody_lift (sa la ha sb lb hb dst : Nat) :
    cmpLtBody sa la ha sb lb hb dst = lift (cmpLtS sa la ha sb lb hb dst) := rfl

theorem cmpLtS_noDiv (sa la ha sb lb hb dst : Nat) :
    (cmpLtS sa la ha sb lb hb dst).all NoDivI = true := rfl

/-- The scratch registers `cmpLtBody` clobbers. -/
def CmpClear (r : Nat) : Prop :=
  r ≠ 126 ∧ r ≠ 127 ∧ r ≠ 128 ∧ r ≠ 129 ∧ r ≠ 130 ∧ r ≠ 131 ∧
  r ≠ 139 ∧ r ≠ 140 ∧ r ≠ 141 ∧ r ≠ 142 ∧ r ≠ 143

/-- The flag algebra of the comparison, with the machine's truncations, as a
statement about seven bits.  All eight quantities the block forms are at most
`2`, so every `% M` is the identity; this is what the `128`-way split
checks. -/
theorem cmpLt_arith (a b A B C D E : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hA : A ≤ 1) (hB : B ≤ 1) (hC : C ≤ 1)
    (hD : D ≤ 1) (hE : E ≤ 1) :
    (((a * ((1 + (M - b)) % M)) % M
        + ((a * b) % M * (((B * E) % M + D) % M)) % M) % M
      + ((((1 + (M - a)) % M * ((1 + (M - b)) % M)) % M
          * (((B * C) % M + A) % M)) % M)) % M
      = a * (1 - b) + a * b * (D + B * E) + (1 - a) * (1 - b) * (A + B * C) := by
  have m0 : (0:Nat) % M = 0 := by decide
  have m1 : (1:Nat) % M = 1 := by decide
  have m2 : (2:Nat) % M = 2 := by decide
  have m3 : (3:Nat) % M = 3 := by decide
  rw [msub_bit ha, msub_bit hb]
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;>
  rcases (by omega : A = 0 ∨ A = 1) with rfl | rfl <;>
  rcases (by omega : B = 0 ∨ B = 1) with rfl | rfl <;>
  rcases (by omega : C = 0 ∨ C = 1) with rfl | rfl <;>
  rcases (by omega : D = 0 ∨ D = 1) with rfl | rfl <;>
  rcases (by omega : E = 0 ∨ E = 1) with rfl | rfl <;>
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, Nat.sub_zero, Nat.sub_self, m0, m1, m2, m3]

set_option maxHeartbeats 1000000 in
/-- **The comparison block computes `tlt`.** -/
theorem cmpLtS_spec (k : Nat) (s : RegState) (sa la ha sb lb hb dst : Nat)
    (hf : ∀ r ∈ [sa, la, ha, sb, lb, hb], CmpClear r)
    (hdst : dst ≠ 143)
    (hsa : s sa ≤ 1) (hsb : s sb ≤ 1) :
    srun k s (cmpLtS sa la ha sb lb hb dst) dst
      = tlt (s sa) (s la) (s ha) (s sb) (s lb) (s hb) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hf sa (by simp)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hf la (by simp)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hf ha (by simp)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hf sb (by simp)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hf lb (by simp)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hf hb (by simp)
  have key : srun k s (cmpLtS sa la ha sb lb hb dst) dst
      = (((s sa * ((1 + (M - s sb)) % M)) % M
          + ((s sa * s sb) % M
              * ((((if s ha = s hb then (1:Nat) else 0)
                    * (if s lb < s la then (1:Nat) else 0)) % M
                  + (if s hb < s ha then (1:Nat) else 0)) % M)) % M) % M
        + ((((1 + (M - s sa)) % M * ((1 + (M - s sb)) % M)) % M
            * ((((if s ha = s hb then (1:Nat) else 0)
                  * (if s la < s lb then (1:Nat) else 0)) % M
                + (if s ha < s hb then (1:Nat) else 0)) % M)) % M)) % M := by
    simp only [cmpLtS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, one_mod_M, if_true, if_false, reduceIte,
      Nat.reduceEqDiff, reduceCtorEq, if_neg hdst, if_neg (Ne.symm hdst),
      a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b6,
      b7, b8, b9, b10, b11, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, d1,
      d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, e1, e2, e3, e4, e5, e6, e7,
      e8, e9, e10, e11, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11]
    rfl
  rw [key]
  simp only [tlt, bnat]
  exact cmpLt_arith (s sa) (s sb) _ _ _ _ _ hsa hsb
    (by split <;> omega) (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega)

/-- The comparison writes only `dst` and the eleven fixed scratch
registers. -/
theorem cmpLtS_frame (k : Nat) (s : RegState) (sa la ha sb lb hb dst j : Nat)
    (h0 : j ≠ dst) (hj : CmpClear j) :
    srun k s (cmpLtS sa la ha sb lb hb dst) j = s j := by
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11⟩ := hj
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [cmpLtS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [sdest] <;> omega

end LeanCompCert.Ports.Section413G2Denote
