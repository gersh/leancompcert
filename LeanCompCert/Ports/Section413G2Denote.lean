import LeanCompCert.Ports.Section413G2Program
import LeanCompCert.Verified.Algorithm.ArrayBridge
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined

/-!
# The §4.1.3 `g₂` sweep: the machine denotes the transparent model

`Ports/Section413G2Program.lean` states two open obligations.  This file
attacks the first,

```text
(1)  (g2Program c).denote = some (c.tFlag)          [machine ⇒ model]
```

by the `SingSeriesC17` architecture: one *spec lemma per block*, composed
along `srun_append`.

The body is 1446 instructions, but it is built from seven reusable
sub-blocks — `guardBody`, `muxBody`, `smDecomp`, `cmpLtBody`, `selTriple`,
`mulWideBody`, `divP18Body` — of which `cmulBody` (378 instructions, used
three times per iteration) is a pure composite.  Each sub-block is proved
**once**, with variable register parameters, so the proof size is governed
by the number of *distinct* blocks and not by the instruction count.

## Two mechanical decisions that govern everything below

**The blocks are proved in the SCALAR machine.**  All of them except the
two array-access points are pure scalar code, and
`Verified/ArrayScalarBlock.lean` says once that a lifted scalar block moves
the register file exactly as `InstrBlock.srun` does and does not touch the
array at all.  Pushing scalar instructions through `astep` instead carries
the array along and inlines it at every read site — which is precisely
where `Ports/ArrayMobiusDenotation.lean` stalled (its own docstring records
the ~57 kB goal).  Each block therefore appears twice: once as a
`List Instr` with a `rfl` bridge to the port's `List AInstr`
(`guardBody_lift`, `muxBody_lift`, …), and once as a specification.

**The literals are abstracted.**  `Nat.add` and `Nat.mul` recurse on their
*second* argument, so a twenty-digit numeral sitting there unary-unfolds
the moment anything whnfs the term — which a `simp only` chain over a
branchless block does, at the `Decidable` instance of every comparison.
So `guardG` takes its cap as a variable and is instantiated at `CAP`
afterwards; `smDecompG` takes both `H63` and `CAP`.  The emitted program is
**not** touched by any of this: every `_lift` bridge is `rfl`, so the
production artifact's sha256 is unchanged.

## What is proved here

* §1 — `arun_regs_frame`, `arun_arr_frame`, `arun_lt`,
  `allDefined_of_alwaysDef`: the four facts about straight-line array
  blocks that `Verified/ArrayFoldBridge.lean` does not state.
* §3 — `guardG_tguard` (`guardBody` computes `tguard`), `muxS_spec`,
  `smDecomp_tmag` (`smDecomp` computes `tmag` and the gated magnitude
  violation), `cmpLtS_spec` (`cmpLtBody` computes `tlt`),
  `selTripleS_spec`, `mulWideG_hl` (`mulWideBody` computes the upstream
  `Verified.MulWide.hl`, hence by `hl_spec` the exact 128-bit product),
  `divP18S_spec` (`divP18Body` computes `tdiv18`), the canonical-sign and
  endpoint-encoding circuits, `cmulDecompS_spec`, `cmulProductsS_spec`,
  and each block's frame lemma.  `cmulBody_lift` identifies the refactored
  production body with the compositional scalar block exactly.
* §4a — `touchBody_defined` and `touchBody_obs`: the first array boundary
  is defined under its three exact index bounds and computes `ttouch`.
* §4 — `Admissible`, and `production_admissible` / `smoke_admissible`.

See the closing `## OPEN` section for the precise statements that remain —
the six body stages, the body, and the loop.
Nothing in this file is an axiom, a `sorry`, or a weakened restatement of
the obligation; every theorem here has axiom set
`[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanCompCert.Ports.Section413G2Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
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

/-- The transparent signed comparison is a bit. -/
theorem tlt_le_one (sa la ha sb lb hb : Nat)
    (hsa : sa ≤ 1) (hsb : sb ≤ 1) : tlt sa la ha sb lb hb ≤ 1 := by
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
  by_cases h1 : ha < hb <;> by_cases h2 : ha = hb <;>
  by_cases h3 : hb < ha <;> by_cases h4 : la < lb <;>
  by_cases h5 : lb < la <;>
    simp [tlt, bnat, h1, h2, h3, h4, h5] <;> omega

/-! ### `selTriple`: the three-word select -/

/-- `Section413G2Program.selTriple`, as a scalar block. -/
def selTripleS (t sa la ha sb lb hb sd ld hd : Nat) : List Instr :=
  muxS sd t sa sb 144 ++ muxS ld t la lb 144 ++ muxS hd t ha hb 144

theorem selTriple_lift (t sa la ha sb lb hb sd ld hd : Nat) :
    selTriple t sa la ha sb lb hb sd ld hd
      = lift (selTripleS t sa la ha sb lb hb sd ld hd) := rfl

theorem selTripleS_noDiv (t sa la ha sb lb hb sd ld hd : Nat) :
    (selTripleS t sa la ha sb lb hb sd ld hd).all NoDivI = true := rfl

/-- The block writes only the three destinations and `144`. -/
theorem selTripleS_frame (k : Nat) (s : RegState)
    (t sa la ha sb lb hb sd ld hd j : Nat)
    (h1 : j ≠ sd) (h2 : j ≠ ld) (h3 : j ≠ hd) (h4 : j ≠ 144) :
    srun k s (selTripleS t sa la ha sb lb hb sd ld hd) j = s j := by
  rw [selTripleS, srun_append, srun_append,
    muxS_frame _ _ _ _ _ _ _ _ h3 h4, muxS_frame _ _ _ _ _ _ _ _ h2 h4,
    muxS_frame _ _ _ _ _ _ _ _ h1 h4]

/-- **The triple select selects.** -/
theorem selTripleS_spec (k : Nat) (s : RegState)
    (t sa la ha sb lb hb sd ld hd : Nat)
    (hts : t ≠ sd) (htl : t ≠ ld) (ht4 : t ≠ 144)
    (hsa4 : sa ≠ 144) (hsb4 : sb ≠ 144)
    (hlas : la ≠ sd) (hla4 : la ≠ 144) (hlbs : lb ≠ sd) (hlb4 : lb ≠ 144)
    (hhas : ha ≠ sd) (hhal : ha ≠ ld) (hha4 : ha ≠ 144)
    (hhbs : hb ≠ sd) (hhbl : hb ≠ ld) (hhb4 : hb ≠ 144)
    (hsdl : sd ≠ ld) (hsdh : sd ≠ hd) (hsd4 : sd ≠ 144)
    (hldh : ld ≠ hd) (hld4 : ld ≠ 144) (hhd4 : hd ≠ 144)
    (ht1 : s t ≤ 1) (hs : ∀ j, s j < M) :
    srun k s (selTripleS t sa la ha sb lb hb sd ld hd) sd
        = (if s t = 1 then s sa else s sb) ∧
      srun k s (selTripleS t sa la ha sb lb hb sd ld hd) ld
        = (if s t = 1 then s la else s lb) ∧
      srun k s (selTripleS t sa la ha sb lb hb sd ld hd) hd
        = (if s t = 1 then s ha else s hb) := by
  -- stage 1
  have e1 : srun k s (muxS sd t sa sb 144) sd = (if s t = 1 then s sa else s sb) :=
    muxS_spec k s sd t sa sb 144 (Ne.symm hsd4) (Ne.symm ht4) (Ne.symm hsa4)
      (Ne.symm hsb4) ht1 hs
  have l1 : ∀ j, srun k s (muxS sd t sa sb 144) j < M :=
    srun_lt_of_lt k _ s hs
  have t1 : srun k s (muxS sd t sa sb 144) t = s t :=
    muxS_frame k s sd t sa sb 144 t hts ht4
  have la1 : srun k s (muxS sd t sa sb 144) la = s la :=
    muxS_frame k s sd t sa sb 144 la hlas hla4
  have lb1 : srun k s (muxS sd t sa sb 144) lb = s lb :=
    muxS_frame k s sd t sa sb 144 lb hlbs hlb4
  have ha1 : srun k s (muxS sd t sa sb 144) ha = s ha :=
    muxS_frame k s sd t sa sb 144 ha hhas hha4
  have hb1 : srun k s (muxS sd t sa sb 144) hb = s hb :=
    muxS_frame k s sd t sa sb 144 hb hhbs hhb4
  -- stage 2
  have e2 : srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) ld
      = (if s t = 1 then s la else s lb) := by
    rw [muxS_spec k _ ld t la lb 144 (Ne.symm hld4) (Ne.symm ht4) (Ne.symm hla4)
      (Ne.symm hlb4) (by rw [t1]; exact ht1) l1, t1, la1, lb1]
  have l2 : ∀ j, srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) j < M :=
    srun_lt_of_lt k _ _ l1
  have t2 : srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) t = s t := by
    rw [muxS_frame k _ ld t la lb 144 t htl ht4, t1]
  have sd2 : srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) sd
      = (if s t = 1 then s sa else s sb) := by
    rw [muxS_frame k _ ld t la lb 144 sd hsdl hsd4, e1]
  have ha2 : srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) ha = s ha := by
    rw [muxS_frame k _ ld t la lb 144 ha hhal hha4, ha1]
  have hb2 : srun k (srun k s (muxS sd t sa sb 144)) (muxS ld t la lb 144) hb = s hb := by
    rw [muxS_frame k _ ld t la lb 144 hb hhbl hhb4, hb1]
  refine ⟨?_, ?_, ?_⟩
  · rw [selTripleS, srun_append, srun_append,
      muxS_frame k _ hd t ha hb 144 sd hsdh hsd4, sd2]
  · rw [selTripleS, srun_append, srun_append,
      muxS_frame k _ hd t ha hb 144 ld hldh hld4, e2]
  · rw [selTripleS, srun_append, srun_append,
      muxS_spec k _ hd t ha hb 144 (Ne.symm hhd4) (Ne.symm ht4) (Ne.symm hha4)
        (Ne.symm hhb4) (by rw [t2]; exact ht1) l2, t2, ha2, hb2]

/-! ### `mulWideBody`: the half-limb 128-bit product

Split in two: `mulWideG_raw` is the register bookkeeping — the eighteen
instructions inline `mwRaw`, the machine's own truncated circuit — and
`mwRaw_hl` is the arithmetic, which reduces `mwRaw` at the production
constants to the upstream-proved `Verified.MulWide.hl`.
-/

/-- `CDEMAbelScan.mulWideBody`, as a scalar block with its two half-limb
constants abstracted. -/
def mulWideG (mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) :
    List Instr :=
  [ .binop s0 .band (.reg ra) (.lit mask)
  , .binop s1 .lshr (.reg ra) (.lit 32)
  , .binop s2 .band (.reg rb) (.lit mask)
  , .binop s3 .lshr (.reg rb) (.lit 32)
  , .binop s4 .mul (.reg s0) (.reg s2)
  , .binop s5 .mul (.reg s0) (.reg s3)
  , .binop s6 .mul (.reg s1) (.reg s2)
  , .binop s7 .mul (.reg s1) (.reg s3)
  , .binop s0 .add (.reg s5) (.reg s6)
  , .binop s1 .lt (.reg s0) (.reg s5)
  , .binop s2 .shl (.reg s0) (.lit 32)
  , .binop rlo .add (.reg s4) (.reg s2)
  , .binop s3 .lt (.reg rlo) (.reg s4)
  , .binop s5 .lshr (.reg s0) (.lit 32)
  , .binop s6 .mul (.reg s1) (.lit base)
  , .binop rhi .add (.reg s7) (.reg s5)
  , .binop rhi .add (.reg rhi) (.reg s6)
  , .binop rhi .add (.reg rhi) (.reg s3) ]

theorem mulWideBody_lift (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) :
    mulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
      = lift (mulWideG 4294967295 4294967296 ra rb rlo rhi
          s0 s1 s2 s3 s4 s5 s6 s7) := rfl

theorem mulWideG_noDiv (mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) :
    (mulWideG mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7).all NoDivI
      = true := rfl

/-- **The machine's half-limb product circuit**, with every truncation it
performs written out.  `mwRaw 4294967295 4294967296` is `MulWide.hl`
(`mwRaw_hl`). -/
def mwRaw (mask base a b : Nat) : Nat × Nat :=
  let a0 := (a &&& mask) % M
  let a1 := (a >>> 32) % M
  let b0 := (b &&& mask) % M
  let b1 := (b >>> 32) % M
  let p00 := (a0 * b0) % M
  let p01 := (a0 * b1) % M
  let p10 := (a1 * b0) % M
  let p11 := (a1 * b1) % M
  let mid := (p01 + p10) % M
  let cm := if mid < p01 then 1 else 0
  let lo := (p00 + (mid <<< 32) % M) % M
  let cl := if lo < p00 then 1 else 0
  (lo, ((((p11 + (mid >>> 32) % M) % M + (cm * base) % M) % M) + cl) % M)

/-- The scratch registers are pairwise distinct … -/
def Distinct8 (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : Prop :=
  s0 ≠ s1 ∧ s0 ≠ s2 ∧ s0 ≠ s3 ∧ s0 ≠ s4 ∧
  s0 ≠ s5 ∧ s0 ≠ s6 ∧ s0 ≠ s7 ∧ s1 ≠ s2 ∧
  s1 ≠ s3 ∧ s1 ≠ s4 ∧ s1 ≠ s5 ∧ s1 ≠ s6 ∧
  s1 ≠ s7 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s2 ≠ s5 ∧
  s2 ≠ s6 ∧ s2 ≠ s7 ∧ s3 ≠ s4 ∧ s3 ≠ s5 ∧
  s3 ≠ s6 ∧ s3 ≠ s7 ∧ s4 ≠ s5 ∧ s4 ≠ s6 ∧
  s4 ≠ s7 ∧ s5 ≠ s6 ∧ s5 ≠ s7 ∧ s6 ≠ s7

/-- … and none of the operands is one of them. -/
def NotIn8 (r s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : Prop :=
  r ≠ s0 ∧ r ≠ s1 ∧ r ≠ s2 ∧ r ≠ s3 ∧ r ≠ s4 ∧ r ≠ s5 ∧ r ≠ s6 ∧ r ≠ s7

set_option maxHeartbeats 1000000 in
/-- **The eighteen instructions inline `mwRaw`.** -/
theorem mulWideG_raw (k : Nat) (s : RegState)
    (mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hmask : mask % M = mask) (hbase : base % M = base)
    (hD : Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) :
    srun k s (mulWideG mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7) rlo
        = (mwRaw mask base (s ra) (s rb)).1 ∧
      srun k s (mulWideG mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7) rhi
        = (mwRaw mask base (s ra) (s rb)).2 := by
  have h32 : (32:Nat) % M = 32 := by decide
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27⟩ := hD
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7⟩ := hra
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := hrb
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := hrlo
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := hrhi
  constructor <;>
    simp only [mulWideG, mwRaw, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, hmask, hbase, h32, if_true, if_false,
      p0, (Ne.symm p0), p1, (Ne.symm p1), p2, (Ne.symm p2), p3,
      (Ne.symm p3), p4, (Ne.symm p4), p5, (Ne.symm p5), p6, (Ne.symm p6),
      p7, (Ne.symm p7), p8, (Ne.symm p8), p9, (Ne.symm p9), p10,
      (Ne.symm p10), p11, (Ne.symm p11), p12, (Ne.symm p12), p13,
      (Ne.symm p13), p14, (Ne.symm p14), p15, (Ne.symm p15), p16,
      (Ne.symm p16), p17, (Ne.symm p17), p18, (Ne.symm p18), p19,
      (Ne.symm p19), p20, (Ne.symm p20), p21, (Ne.symm p21), p22,
      (Ne.symm p22), p23, (Ne.symm p23), p24, (Ne.symm p24), p25,
      (Ne.symm p25), p26, (Ne.symm p26), p27, (Ne.symm p27), q0, q1, q2,
      q3, q4, q5, q6, q7, w0, w1, w2, w3, w4, w5, w6, w7, x0, x1, x2, x3,
      x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7, hlohi,
      (Ne.symm hlohi), (Ne.symm x0), (Ne.symm x1), (Ne.symm x2),
      (Ne.symm x3), (Ne.symm x4), (Ne.symm x5), (Ne.symm x6), (Ne.symm x7),
      (Ne.symm y0), (Ne.symm y1), (Ne.symm y2), (Ne.symm y3), (Ne.symm y4),
      (Ne.symm y5), (Ne.symm y6), (Ne.symm y7), (Ne.symm q0), (Ne.symm q1),
      (Ne.symm q2), (Ne.symm q3), (Ne.symm q4), (Ne.symm q5), (Ne.symm q6),
      (Ne.symm q7), (Ne.symm w0), (Ne.symm w1), (Ne.symm w2), (Ne.symm w3),
      (Ne.symm w4), (Ne.symm w5), (Ne.symm w6), (Ne.symm w7)]

/-- Three nested `u64` truncations of a sum that the final value bounds. -/
theorem mod_chain3 (x y z w : Nat) (h : x + y + z + w < M) :
    (((x + y) % M + z) % M + w) % M = x + y + z + w := by
  have h1 : (x + y) % M = x + y := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : (x + y + z) % M = x + y + z := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  exact Nat.mod_eq_of_lt h

set_option maxHeartbeats 1000000 in
/-- **The machine's circuit is `Verified.MulWide.hl`.**  The upstream
`hl_spec` then gives the exact 128-bit product; `hl_hi_lt` is what makes the
three truncations in the high-word accumulation identities, so the two
halves of the circuit are not independent. -/
theorem mwRaw_hl (a b : Nat) (ha : a < M) (hb : b < M) :
    mwRaw 4294967295 4294967296 a b = Verified.MulWide.hl a b := by
  have hMval : M = 4294967296 * 4294967296 := by decide
  have hB64 : Verified.MulWide.B64 = M := by decide
  have hB32 : Verified.MulWide.B32 = 4294967296 := rfl
  have h32pos : 0 < 4294967296 := by decide
  have h32M : (4294967296 : Nat) < M := by decide
  -- bit operations as arithmetic
  have hand : ∀ n : Nat, n &&& 4294967295 = n % 4294967296 := fun n => by
    have := Nat.and_two_pow_sub_one_eq_mod n 32
    simpa using this
  have hshr : ∀ n : Nat, n >>> 32 = n / 4294967296 := fun n => by
    have := Nat.shiftRight_eq_div_pow n 32
    simpa using this
  have hshl : ∀ n : Nat, n <<< 32 = n * 4294967296 := fun n => by
    have := Nat.shiftLeft_eq n 32
    simpa using this
  -- the four half limbs
  have haM : a % 4294967296 < 4294967296 := Nat.mod_lt _ h32pos
  have hbM : b % 4294967296 < 4294967296 := Nat.mod_lt _ h32pos
  have haD : a / 4294967296 < 4294967296 :=
    (Nat.div_lt_iff_lt_mul h32pos).mpr (by rw [← hMval]; exact ha)
  have hbD : b / 4294967296 < 4294967296 :=
    (Nat.div_lt_iff_lt_mul h32pos).mpr (by rw [← hMval]; exact hb)
  have ha0 : (a &&& 4294967295) % M = a % 4294967296 := by
    rw [hand]; exact Nat.mod_eq_of_lt (Nat.lt_trans haM h32M)
  have hb0 : (b &&& 4294967295) % M = b % 4294967296 := by
    rw [hand]; exact Nat.mod_eq_of_lt (Nat.lt_trans hbM h32M)
  have ha1 : (a >>> 32) % M = a / 4294967296 := by
    rw [hshr]; exact Nat.mod_eq_of_lt (Nat.lt_trans haD h32M)
  have hb1 : (b >>> 32) % M = b / 4294967296 := by
    rw [hshr]; exact Nat.mod_eq_of_lt (Nat.lt_trans hbD h32M)
  have ha1' : (a / 4294967296) % M = a / 4294967296 :=
    Nat.mod_eq_of_lt (Nat.lt_trans haD h32M)
  have hb1' : (b / 4294967296) % M = b / 4294967296 :=
    Nat.mod_eq_of_lt (Nat.lt_trans hbD h32M)
  have ha0' : (a % 4294967296) % M = a % 4294967296 :=
    Nat.mod_eq_of_lt (Nat.lt_trans haM h32M)
  have hb0' : (b % 4294967296) % M = b % 4294967296 :=
    Nat.mod_eq_of_lt (Nat.lt_trans hbM h32M)
  -- the four partial products fit in a word
  have hprod : ∀ x y : Nat, x < 4294967296 → y < 4294967296 →
      (x * y) % M = x * y := by
    intro x y hx hy
    refine Nat.mod_eq_of_lt ?_
    rw [hMval]
    exact Nat.mul_lt_mul_of_lt_of_lt hx hy
  have hp00 := hprod _ _ haM hbM
  have hp01 := hprod _ _ haM hbD
  have hp10 := hprod _ _ haD hbM
  have hp11 := hprod _ _ haD hbD
  have hhi := Verified.MulWide.hl_hi_lt a b (by rw [hB64]; exact ha)
    (by rw [hB64]; exact hb)
  have hcm : ∀ (P : Prop) (_ : Decidable P),
      ((if P then (1:Nat) else 0) * 4294967296) % M
        = (if P then (1:Nat) else 0) * 4294967296 := by
    intro P inst
    refine Nat.mod_eq_of_lt ?_
    split
    · rw [Nat.one_mul]; exact h32M
    · rw [Nat.zero_mul]; exact M_pos
  have hmidlt : ∀ x : Nat, (x % M) / 4294967296 % M = (x % M) / 4294967296 :=
    fun x => Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ M_pos))
  simp only [Verified.MulWide.hl, Verified.MulWide.B32, hB64] at hhi
  simp only [mwRaw, Verified.MulWide.hl, Verified.MulWide.B32, hB64,
    ha0, hb0, ha1, hb1, ha0', hb0', ha1', hb1', hp00, hp01, hp10, hp11,
    hshl, hshr, hmidlt, hcm, Prod.mk.injEq] at hhi ⊢
  exact ⟨trivial, mod_chain3 _ _ _ _ hhi⟩

/-- The block writes only `rlo`, `rhi` and the eight scratch registers. -/
theorem mulWideG_frame (k : Nat) (s : RegState)
    (mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 j : Nat)
    (hlo : j ≠ rlo) (hhi : j ≠ rhi) (hj : NotIn8 j s0 s1 s2 s3 s4 s5 s6 s7) :
    srun k s (mulWideG mask base ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7) j
      = s j := by
  obtain ⟨j0, j1, j2, j3, j4, j5, j6, j7⟩ := hj
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [mulWideG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [sdest] <;>
    first
      | exact fun h => absurd h.symm j0 | exact fun h => absurd h.symm j1
      | exact fun h => absurd h.symm j2 | exact fun h => absurd h.symm j3
      | exact fun h => absurd h.symm j4 | exact fun h => absurd h.symm j5
      | exact fun h => absurd h.symm j6 | exact fun h => absurd h.symm j7
      | exact fun h => absurd h.symm hlo | exact fun h => absurd h.symm hhi

/-- **`mulWideBody` computes `Verified.MulWide.hl`.**  With the upstream
`hl_spec`, the eighteen instructions therefore compute the exact 128-bit
product of the two registers. -/
theorem mulWideG_hl (k : Nat) (s : RegState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hs : ∀ j, s j < M) :
    srun k s (mulWideG 4294967295 4294967296 ra rb rlo rhi
        s0 s1 s2 s3 s4 s5 s6 s7) rlo
        = (Verified.MulWide.hl (s ra) (s rb)).1 ∧
      srun k s (mulWideG 4294967295 4294967296 ra rb rlo rhi
        s0 s1 s2 s3 s4 s5 s6 s7) rhi
        = (Verified.MulWide.hl (s ra) (s rb)).2 := by
  have h := mulWideG_raw k s 4294967295 4294967296 ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7 (by decide) (by decide) hD hra hrb hrlo hrhi hlohi
  constructor
  · rw [h.1, mwRaw_hl (s ra) (s rb) (hs ra) (hs rb)]
  · rw [h.2, mwRaw_hl (s ra) (s rb) (hs ra) (hs rb)]

/-! ### `divP18Body`: scalar bridge and unconditional definedness

The divider contains `udiv`/`urem`, so it cannot use the division-free
`allDefined_lift_of_noDiv` bridge.  Every divisor is nevertheless the same
nonzero literal `D5 = 5^18`.  The two facts below record, once, that the
array block is scalar and that it is defined in every state.  The value
equations are proved separately because they are the long-division
transcription described in the closing checklist.
-/

/-- Recover the scalar instruction from an array instruction.  The fallback
cases are irrelevant for `divP18Body`; `divP18Body_lift` proves that every
instruction in that block is scalar. -/
def scalarOf : AInstr → Instr
  | .scalar i => i
  | .load _ _ => .mov 0 (.lit 0)
  | .store _ _ => .mov 0 (.lit 0)

/-- `divP18Body`, viewed in the scalar machine. -/
def divP18S (lo hi q qc : Nat) : List Instr :=
  (divP18Body lo hi q qc).map scalarOf

/-- The emitted divider is exactly the lift of its scalar view. -/
theorem divP18Body_lift (lo hi q qc : Nat) :
    divP18Body lo hi q qc = lift (divP18S lo hi q qc) := by
  simp [divP18S, divP18Body, scalarOf, lift]

/-- Every partial operation in the divider has the fixed nonzero divisor
`D5`; hence the block is defined independently of registers and array. -/
theorem divP18Body_alwaysDef (lo hi q qc : Nat) :
    (divP18Body lo hi q qc).all alwaysDef = true := by
  have hDlt : D5 < M := by decide
  have hD : D5 % M ≠ 0 := by
    rw [Nat.mod_eq_of_lt hDlt]
    decide
  simp [divP18Body, alwaysDef, hD]

/-- The divider cannot fail: all ten divisions/remainders use `D5 ≠ 0`. -/
theorem divP18Body_defined (len k : Nat) (st : AState) (lo hi q qc : Nat) :
    AllDefined len k st (divP18Body lo hi q qc) :=
  allDefined_of_alwaysDef len k _ st (divP18Body_alwaysDef lo hi q qc)

/-- The divider writes only its two outputs and scratch registers `168`–`175`. -/
theorem divP18S_frame (k : Nat) (s : RegState) (lo hi q qc j : Nat)
    (hq : j ≠ q) (hqc : j ≠ qc)
    (h168 : j ≠ 168) (h169 : j ≠ 169) (h170 : j ≠ 170)
    (h171 : j ≠ 171) (h172 : j ≠ 172) (h173 : j ≠ 173)
    (h174 : j ≠ 174) (h175 : j ≠ 175) :
    srun k s (divP18S lo hi q qc) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp [divP18S, divP18Body, scalarOf] at hiMem
  rcases hiMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

/-- The repeated six-instruction long-division digit with its large literals
abstracted, preventing `Nat.mul` from unfolding a unary numeral. -/
def divP18DigitG (base divisor : Nat) : List Instr :=
  [ .binop 170 .mul (.reg 172) (.lit base)
  , .binop 170 .add (.reg 170) (.reg 173)
  , .binop 171 .udiv (.reg 170) (.lit divisor)
  , .binop 178 .mul (.reg 178) (.lit base)
  , .binop 178 .add (.reg 178) (.reg 171)
  , .binop 172 .urem (.reg 170) (.lit divisor) ]

/-- The matching transparent digit with abstract literals. -/
def tldG (base divisor : Nat) (st : Nat × Nat) (dig : Nat) : Nat × Nat :=
  ((st.1 * base % M + (st.2 * base % M + dig) % M / divisor) % M,
   (st.2 * base % M + dig) % M % divisor)

/-- One repeated machine digit is exactly the transparent `tld` step. -/
theorem divP18DigitG_spec (k : Nat) (s : RegState) (base divisor : Nat)
    (hB : base % M = base) (hD : divisor % M = divisor)
    (hD0 : divisor ≠ 0) (hDlt : divisor < M) :
    srun k s (divP18DigitG base divisor) 178 =
        (tldG base divisor (s 178, s 172) (s 173)).1 ∧
      srun k s (divP18DigitG base divisor) 172 =
        (tldG base divisor (s 178, s 172) (s 173)).2 := by
  have hdiv (x : Nat) : ((x % M) / divisor) % M = (x % M) / divisor :=
    Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ M_pos))
  have hrem (x : Nat) : ((x % M) % divisor) % M = (x % M) % divisor :=
    Nat.mod_eq_of_lt
      (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hD0)) hDlt)
  constructor <;>
    simp only [divP18DigitG, tldG, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, hB, hD, hD0, if_false, if_true,
      Nat.reduceEqDiff, hdiv, hrem]

/-- The production repeated digit. -/
def divP18DigitS : List Instr := divP18DigitG 4194304 D5

theorem divP18DigitS_spec (k : Nat) (s : RegState) :
    srun k s divP18DigitS 178 = (tld (s 178, s 172) (s 173)).1 ∧
      srun k s divP18DigitS 172 = (tld (s 178, s 172) (s 173)).2 := by
  change srun k s (divP18DigitG 4194304 D5) 178 =
      (tldG 4194304 D5 (s 178, s 172) (s 173)).1 ∧
    srun k s (divP18DigitG 4194304 D5) 172 =
      (tldG 4194304 D5 (s 178, s 172) (s 173)).2
  exact divP18DigitG_spec k s 4194304 D5 (by decide)
    (Nat.mod_eq_of_lt (by decide)) (by decide) (by decide)

/-- The repeated digit writes only its quotient/remainder and two scratches. -/
theorem divP18DigitS_frame (k : Nat) (s : RegState) (j : Nat)
    (h170 : j ≠ 170) (h171 : j ≠ 171) (h172 : j ≠ 172) (h178 : j ≠ 178) :
    srun k s divP18DigitS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi
  simp only [divP18DigitS, divP18DigitG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-! The remaining divider fragments.  Naming these boundaries is essential:
expanding all 46 instructions in one theorem creates an 18-GiB proof term,
whereas each fragment below checks in isolation. -/

def divP18YLo (lo hi : Nat) : Nat :=
  ((lo >>> 18) + (hi <<< 46) % M) % M

def divP18YHi (hi : Nat) : Nat := hi >>> 18

def divP18Digits (lo hi : Nat) : List Nat :=
  let yLo := divP18YLo lo hi
  let yHi := divP18YHi hi
  [ yHi >>> 24
  , (yHi >>> 2) &&& 4194303
  , ((yLo >>> 44) + ((yHi &&& 3) * 1048576) % M) % M
  , (yLo >>> 22) &&& 4194303
  , yLo &&& 4194303 ]

theorem tdiv18_eq_ttail_digits (lo hi : Nat) :
    tdiv18 lo hi = ttail lo (divP18Digits lo hi) := rfl

def divP18PreS (lo hi : Nat) : List Instr :=
  [ .binop 168 .lshr (.reg lo) (.lit 18)
  , .binop 169 .shl (.reg hi) (.lit 46)
  , .binop 168 .add (.reg 168) (.reg 169)
  , .binop 169 .lshr (.reg hi) (.lit 18)
  , .binop 170 .lshr (.reg 169) (.lit 24) ]

def divP18InitG (divisor : Nat) : List Instr :=
  [ .binop 178 .udiv (.reg 170) (.lit divisor)
  , .binop 172 .urem (.reg 170) (.lit divisor) ]

def divP18InitS : List Instr := divP18InitG D5

def divP18D3PrepG (mask : Nat) : List Instr :=
  [ .binop 173 .lshr (.reg 169) (.lit 2)
  , .binop 173 .band (.reg 173) (.lit mask) ]

def divP18D3PrepS : List Instr := divP18D3PrepG 4194303

def divP18D2PrepG (scale : Nat) : List Instr :=
  [ .binop 173 .lshr (.reg 168) (.lit 44)
  , .binop 174 .band (.reg 169) (.lit 3)
  , .binop 174 .mul (.reg 174) (.lit scale)
  , .binop 173 .add (.reg 173) (.reg 174) ]

def divP18D2PrepS : List Instr := divP18D2PrepG 1048576

def divP18D1PrepG (mask : Nat) : List Instr :=
  [ .binop 173 .lshr (.reg 168) (.lit 22)
  , .binop 173 .band (.reg 173) (.lit mask) ]

def divP18D1PrepS : List Instr := divP18D1PrepG 4194303

def divP18D0PrepG (mask : Nat) : List Instr :=
  [ .binop 173 .band (.reg 168) (.lit mask) ]

def divP18D0PrepS : List Instr := divP18D0PrepG 4194303

def divP18CeilG (mask lo : Nat) : List Instr :=
  [ .binop 174 .band (.reg lo) (.lit mask)
  , .binop 174 .eq (.reg 174) (.lit 0)
  , .binop 175 .eq (.reg 172) (.lit 0)
  , .binop 174 .mul (.reg 174) (.reg 175)
  , .binop 179 .sub (.lit 1) (.reg 174)
  , .binop 179 .add (.reg 179) (.reg 178) ]

def divP18CeilS (lo : Nat) : List Instr := divP18CeilG 262143 lo

/-- The scalar divider is exactly the staged block used by the proof. -/
theorem divP18S_split (lo hi : Nat) :
    divP18S lo hi 178 179 =
      divP18PreS lo hi ++ divP18InitS ++
      divP18D3PrepS ++ divP18DigitS ++
      divP18D2PrepS ++ divP18DigitS ++
      divP18D1PrepS ++ divP18DigitS ++
      divP18D0PrepS ++ divP18DigitS ++ divP18CeilS lo := rfl

/-- The preparation computes the shifted two-word value and its top digit. -/
theorem divP18PreS_spec (k : Nat) (s : RegState) (lo hi : Nat)
    (hs : ∀ j, s j < M)
    (hlo8 : lo ≠ 168) (hlo9 : lo ≠ 169) (hloA : lo ≠ 170)
    (hhi8 : hi ≠ 168) (hhi9 : hi ≠ 169) (hhiA : hi ≠ 170) :
    srun k s (divP18PreS lo hi) 168 = divP18YLo (s lo) (s hi) ∧
      srun k s (divP18PreS lo hi) 169 = divP18YHi (s hi) ∧
      srun k s (divP18PreS lo hi) 170 = divP18YHi (s hi) >>> 24 := by
  have h18 : (18 : Nat) % M = 18 := by decide
  have h46 : (46 : Nat) % M = 46 := by decide
  have h24 : (24 : Nat) % M = 24 := by decide
  have hshr (x n : Nat) (hx : x < M) : (x >>> n) % M = x >>> n :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)
  have hhi18 : s hi >>> 18 < M :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (hs hi)
  constructor
  · simp only [divP18PreS, divP18YLo, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, h18, h46, h24, if_true,
      if_false, Nat.reduceEqDiff, hlo8, hlo9, hloA, hhi8, hhi9, hhiA,
      Ne.symm hlo8, Ne.symm hlo9, Ne.symm hloA, Ne.symm hhi8,
      Ne.symm hhi9, Ne.symm hhiA, hshr (s lo) 18 (hs lo)]
  · constructor
    · simp only [divP18PreS, divP18YHi, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, Option.getD_some, h18, h46, h24, if_true,
        if_false, Nat.reduceEqDiff, hlo8, hlo9, hloA, hhi8, hhi9, hhiA,
        Ne.symm hlo8, Ne.symm hlo9, Ne.symm hloA, Ne.symm hhi8,
        Ne.symm hhi9, Ne.symm hhiA, hshr (s hi) 18 (hs hi)]
    · simp only [divP18PreS, divP18YHi, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, Option.getD_some, h18, h46, h24, if_true,
        if_false, Nat.reduceEqDiff, hlo8, hlo9, hloA, hhi8, hhi9, hhiA,
        Ne.symm hlo8, Ne.symm hlo9, Ne.symm hloA, Ne.symm hhi8,
        Ne.symm hhi9, Ne.symm hhiA, hshr (s hi) 18 (hs hi),
        hshr (s hi >>> 18) 24 hhi18]

theorem divP18PreS_frame (k : Nat) (s : RegState) (lo hi j : Nat)
    (h168 : j ≠ 168) (h169 : j ≠ 169) (h170 : j ≠ 170) :
    srun k s (divP18PreS lo hi) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18PreS, List.mem_cons, List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-- The first digit starts the long division from quotient/remainder zero. -/
theorem divP18InitG_spec (k : Nat) (s : RegState) (base divisor : Nat)
    (h170 : s 170 < M) (hD : divisor % M = divisor)
    (hD0 : divisor ≠ 0) (hDlt : divisor < M) :
    srun k s (divP18InitG divisor) 178 =
        (tldG base divisor (0, 0) (s 170)).1 ∧
      srun k s (divP18InitG divisor) 172 =
        (tldG base divisor (0, 0) (s 170)).2 := by
  have h170m : s 170 % M = s 170 := Nat.mod_eq_of_lt h170
  have hrem : (s 170 % divisor) % M = s 170 % divisor :=
    Nat.mod_eq_of_lt
      (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hD0)) hDlt)
  constructor <;>
    simp only [divP18InitG, tldG, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, hD, hD0, h170m, hrem,
      if_false, if_true, Nat.reduceEqDiff, Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add]

theorem divP18InitS_spec (k : Nat) (s : RegState) (h170 : s 170 < M) :
    srun k s divP18InitS 178 = (tld (0, 0) (s 170)).1 ∧
      srun k s divP18InitS 172 = (tld (0, 0) (s 170)).2 := by
  change srun k s (divP18InitG D5) 178 =
      (tldG 4194304 D5 (0, 0) (s 170)).1 ∧
    srun k s (divP18InitG D5) 172 =
      (tldG 4194304 D5 (0, 0) (s 170)).2
  exact divP18InitG_spec k s 4194304 D5 h170
    (Nat.mod_eq_of_lt (by decide)) (by decide) (by decide)

theorem divP18InitS_frame (k : Nat) (s : RegState) (j : Nat)
    (h172 : j ≠ 172) (h178 : j ≠ 178) :
    srun k s divP18InitS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18InitS, divP18InitG, List.mem_cons, List.not_mem_nil,
    or_false] at hiMem
  rcases hiMem with rfl | rfl <;> simp only [sdest] <;> omega

theorem divP18D3PrepG_spec (k : Nat) (s : RegState) (mask : Nat)
    (h169 : s 169 < M) (hm : mask % M = mask) (hmlt : mask < M) :
    srun k s (divP18D3PrepG mask) 173 = (s 169 >>> 2) &&& mask := by
  have h2 : (2 : Nat) % M = 2 := by decide
  have hshr : (s 169 >>> 2) % M = s 169 >>> 2 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h169)
  have hband (x : Nat) : (x &&& mask) % M = x &&& mask :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hmlt)
  simp only [divP18D3PrepG, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, h2, hm, hshr, hband, if_true,
    if_false, Nat.reduceEqDiff]

theorem divP18D3PrepS_spec (k : Nat) (s : RegState) (h169 : s 169 < M) :
    srun k s divP18D3PrepS 173 = (s 169 >>> 2) &&& 4194303 := by
  change srun k s (divP18D3PrepG 4194303) 173 = _
  exact divP18D3PrepG_spec k s 4194303 h169 (by decide) (by decide)

theorem divP18D3PrepS_frame (k : Nat) (s : RegState) (j : Nat)
    (h173 : j ≠ 173) : srun k s divP18D3PrepS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18D3PrepS, divP18D3PrepG, List.mem_cons,
    List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl | rfl <;> simp only [sdest] <;> omega

theorem divP18D2PrepG_spec (k : Nat) (s : RegState) (scale : Nat)
    (h168 : s 168 < M) (hscale : scale % M = scale) :
    srun k s (divP18D2PrepG scale) 173 =
      ((s 168 >>> 44) + ((s 169 &&& 3) * scale) % M) % M := by
  have h44 : (44 : Nat) % M = 44 := by decide
  have h3 : (3 : Nat) % M = 3 := by decide
  have hshr : (s 168 >>> 44) % M = s 168 >>> 44 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h168)
  have hband (x : Nat) : (x &&& 3) % M = x &&& 3 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
  simp only [divP18D2PrepG, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, h44, h3, hscale, hshr, hband,
    if_true, if_false, Nat.reduceEqDiff]

theorem divP18D2PrepS_spec (k : Nat) (s : RegState) (h168 : s 168 < M) :
    srun k s divP18D2PrepS 173 =
      ((s 168 >>> 44) + ((s 169 &&& 3) * 1048576) % M) % M := by
  change srun k s (divP18D2PrepG 1048576) 173 = _
  exact divP18D2PrepG_spec k s 1048576 h168 (by decide)

theorem divP18D2PrepS_frame (k : Nat) (s : RegState) (j : Nat)
    (h173 : j ≠ 173) (h174 : j ≠ 174) :
    srun k s divP18D2PrepS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18D2PrepS, divP18D2PrepG, List.mem_cons,
    List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem divP18D1PrepG_spec (k : Nat) (s : RegState) (mask : Nat)
    (h168 : s 168 < M) (hm : mask % M = mask) (hmlt : mask < M) :
    srun k s (divP18D1PrepG mask) 173 = (s 168 >>> 22) &&& mask := by
  have h22 : (22 : Nat) % M = 22 := by decide
  have hshr : (s 168 >>> 22) % M = s 168 >>> 22 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h168)
  have hband (x : Nat) : (x &&& mask) % M = x &&& mask :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hmlt)
  simp only [divP18D1PrepG, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, h22, hm, hshr, hband, if_true,
    if_false, Nat.reduceEqDiff]

theorem divP18D1PrepS_spec (k : Nat) (s : RegState) (h168 : s 168 < M) :
    srun k s divP18D1PrepS 173 = (s 168 >>> 22) &&& 4194303 := by
  change srun k s (divP18D1PrepG 4194303) 173 = _
  exact divP18D1PrepG_spec k s 4194303 h168 (by decide) (by decide)

theorem divP18D1PrepS_frame (k : Nat) (s : RegState) (j : Nat)
    (h173 : j ≠ 173) : srun k s divP18D1PrepS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18D1PrepS, divP18D1PrepG, List.mem_cons,
    List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl | rfl <;> simp only [sdest] <;> omega

theorem divP18D0PrepG_spec (k : Nat) (s : RegState) (mask : Nat)
    (hm : mask % M = mask) (hmlt : mask < M) :
    srun k s (divP18D0PrepG mask) 173 = s 168 &&& mask := by
  have hband (x : Nat) : (x &&& mask) % M = x &&& mask :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hmlt)
  simp only [divP18D0PrepG, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, hm, hband, if_true]

theorem divP18D0PrepS_spec (k : Nat) (s : RegState) :
    srun k s divP18D0PrepS 173 = s 168 &&& 4194303 := by
  change srun k s (divP18D0PrepG 4194303) 173 = _
  exact divP18D0PrepG_spec k s 4194303 (by decide) (by decide)

theorem divP18D0PrepS_frame (k : Nat) (s : RegState) (j : Nat)
    (h173 : j ≠ 173) : srun k s divP18D0PrepS j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18D0PrepS, divP18D0PrepG, List.mem_cons,
    List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl <;> simp only [sdest] <;> omega

theorem divP18CeilG_spec (k : Nat) (s : RegState) (mask lo : Nat)
    (hm : mask % M = mask) (hmlt : mask < M) :
    srun k s (divP18CeilG mask lo) 179 =
      (tsub 1 (bnat (s lo &&& mask = 0) * bnat (s 172 = 0)) + s 178) % M := by
  have h0 : (0 : Nat) % M = 0 := by decide
  have h1 : (1 : Nat) % M = 1 := by decide
  have hband (x : Nat) : (x &&& mask) % M = x &&& mask :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hmlt)
  have hbitMul (P Q : Prop) [Decidable P] [Decidable Q] :
      ((if P then (1 : Nat) else 0) * (if Q then 1 else 0)) % M =
        (if P then 1 else 0) * (if Q then 1 else 0) := by
    split <;> split <;> simp only [Nat.one_mul, Nat.zero_mul, h0, h1]
  simp only [divP18CeilG, tsub, bnat, srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, Option.getD_some, hm, h0, h1, hband, hbitMul,
    if_true, if_false, Nat.reduceEqDiff]

theorem divP18CeilS_spec (k : Nat) (s : RegState) (lo : Nat) :
    srun k s (divP18CeilS lo) 179 =
      (tsub 1 (bnat (s lo &&& 262143 = 0) * bnat (s 172 = 0)) + s 178) % M := by
  change srun k s (divP18CeilG 262143 lo) 179 = _
  exact divP18CeilG_spec k s 262143 lo (by decide) (by decide)

theorem divP18CeilS_frame (k : Nat) (s : RegState) (lo j : Nat)
    (h174 : j ≠ 174) (h175 : j ≠ 175) (h179 : j ≠ 179) :
    srun k s (divP18CeilS lo) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hiMem
  simp only [divP18CeilS, divP18CeilG, List.mem_cons,
    List.not_mem_nil, or_false] at hiMem
  rcases hiMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-- Compose any digit-preparation fragment with the proved repeated digit. -/
theorem divP18PrepDigit_spec (k : Nat) (s : RegState) (prep : List Instr)
    (digit : Nat)
    (hdigit : srun k s prep 173 = digit)
    (hq : srun k s prep 178 = s 178)
    (hr : srun k s prep 172 = s 172) :
    srun k s (prep ++ divP18DigitS) 178 =
        (tld (s 178, s 172) digit).1 ∧
      srun k s (prep ++ divP18DigitS) 172 =
        (tld (s 178, s 172) digit).2 := by
  rw [srun_append]
  have h := divP18DigitS_spec k (srun k s prep)
  rw [hq, hr, hdigit] at h
  exact h

/-- A prepared digit followed by its division step preserves any register
preserved by both fragments. -/
theorem divP18PrepDigit_frame (k : Nat) (s : RegState) (prep : List Instr)
    (j : Nat) (hp : srun k s prep j = s j)
    (h170 : j ≠ 170) (h171 : j ≠ 171) (h172 : j ≠ 172)
    (h178 : j ≠ 178) :
    srun k s (prep ++ divP18DigitS) j = s j := by
  rw [srun_append, divP18DigitS_frame k _ j h170 h171 h172 h178, hp]

/-- **The production divider denotes its transparent model.**  The two live
call sites use outputs `178` and `179`, and inputs below the divider scratch
range.  Keeping those concrete output registers here lets every repeated
digit share the single small proof above instead of re-normalizing the
forty-six-instruction block. -/
theorem divP18S_spec (k : Nat) (s : RegState) (lo hi : Nat)
    (hs : ∀ j, s j < M) (hlo : lo < 168) (hhi : hi < 168) :
    srun k s (divP18S lo hi 178 179) 178 = (tdiv18 (s lo) (s hi)).1 ∧
      srun k s (divP18S lo hi 178 179) 179 = (tdiv18 (s lo) (s hi)).2 := by
  let s1 := srun k s (divP18PreS lo hi)
  let s2 := srun k s1 divP18InitS
  let s3 := srun k s2 (divP18D3PrepS ++ divP18DigitS)
  let s4 := srun k s3 (divP18D2PrepS ++ divP18DigitS)
  let s5 := srun k s4 (divP18D1PrepS ++ divP18DigitS)
  let s6 := srun k s5 (divP18D0PrepS ++ divP18DigitS)
  let sf := srun k s6 (divP18CeilS lo)
  have hs1 : ∀ j, s1 j < M := srun_lt_of_lt k _ s hs
  have hs2 : ∀ j, s2 j < M := srun_lt_of_lt k _ s1 hs1
  have hs3 : ∀ j, s3 j < M := srun_lt_of_lt k _ s2 hs2
  have hs4 : ∀ j, s4 j < M := srun_lt_of_lt k _ s3 hs3
  have hs5 : ∀ j, s5 j < M := srun_lt_of_lt k _ s4 hs4
  have hpre :
      s1 168 = divP18YLo (s lo) (s hi) ∧
        s1 169 = divP18YHi (s hi) ∧
        s1 170 = divP18YHi (s hi) >>> 24 := by
    exact divP18PreS_spec k s lo hi hs (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hs2_168 : s2 168 = s1 168 := divP18InitS_frame k s1 168 (by decide) (by decide)
  have hs2_169 : s2 169 = s1 169 := divP18InitS_frame k s1 169 (by decide) (by decide)
  have hs2_lo : s2 lo = s lo := by
    calc
      s2 lo = s1 lo := divP18InitS_frame k s1 lo (by omega) (by omega)
      _ = s lo := by
        change srun k s (divP18PreS lo hi) lo = s lo
        exact divP18PreS_frame k s lo hi lo (by omega) (by omega) (by omega)
  have h2 :
      s2 178 = (tld (0, 0) (divP18YHi (s hi) >>> 24)).1 ∧
        s2 172 = (tld (0, 0) (divP18YHi (s hi) >>> 24)).2 := by
    simpa only [s2, hpre.2.2] using divP18InitS_spec k s1 (hs1 170)
  have h3digit :
      srun k s2 divP18D3PrepS 173 =
        (divP18YHi (s hi) >>> 2) &&& 4194303 := by
    rw [divP18D3PrepS_spec k s2 (hs2 169), hs2_169, hpre.2.1]
  have h3 :
      s3 178 =
          (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
            ((divP18YHi (s hi) >>> 2) &&& 4194303)).1 ∧
        s3 172 =
          (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
            ((divP18YHi (s hi) >>> 2) &&& 4194303)).2 := by
    have h := divP18PrepDigit_spec k s2 divP18D3PrepS
      ((divP18YHi (s hi) >>> 2) &&& 4194303) h3digit
      (divP18D3PrepS_frame k s2 178 (by decide))
      (divP18D3PrepS_frame k s2 172 (by decide))
    rw [h2.1, h2.2] at h
    exact h
  have hs3_168 : s3 168 = s2 168 :=
    divP18PrepDigit_frame k s2 divP18D3PrepS 168
      (divP18D3PrepS_frame k s2 168 (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have hs3_169 : s3 169 = s2 169 :=
    divP18PrepDigit_frame k s2 divP18D3PrepS 169
      (divP18D3PrepS_frame k s2 169 (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have hs3_lo : s3 lo = s lo := by
    change srun k s2 (divP18D3PrepS ++ divP18DigitS) lo = s lo
    rw [divP18PrepDigit_frame k s2 divP18D3PrepS lo
      (divP18D3PrepS_frame k s2 lo (by omega))
      (by omega) (by omega) (by omega) (by omega), hs2_lo]
  have h4digit :
      srun k s3 divP18D2PrepS 173 =
        ((divP18YLo (s lo) (s hi) >>> 44) +
          ((divP18YHi (s hi) &&& 3) * 1048576) % M) % M := by
    rw [divP18D2PrepS_spec k s3 (hs3 168), hs3_168, hs2_168, hpre.1,
      hs3_169, hs2_169, hpre.2.1]
  have h4 :
      s4 178 =
          (tld
            (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
              ((divP18YHi (s hi) >>> 2) &&& 4194303))
            (((divP18YLo (s lo) (s hi) >>> 44) +
              ((divP18YHi (s hi) &&& 3) * 1048576) % M) % M)).1 ∧
        s4 172 =
          (tld
            (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
              ((divP18YHi (s hi) >>> 2) &&& 4194303))
            (((divP18YLo (s lo) (s hi) >>> 44) +
              ((divP18YHi (s hi) &&& 3) * 1048576) % M) % M)).2 := by
    have h := divP18PrepDigit_spec k s3 divP18D2PrepS _ h4digit
      (divP18D2PrepS_frame k s3 178 (by decide) (by decide))
      (divP18D2PrepS_frame k s3 172 (by decide) (by decide))
    rw [h3.1, h3.2] at h
    exact h
  have hs4_168 : s4 168 = s3 168 :=
    divP18PrepDigit_frame k s3 divP18D2PrepS 168
      (divP18D2PrepS_frame k s3 168 (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have hs4_lo : s4 lo = s lo := by
    change srun k s3 (divP18D2PrepS ++ divP18DigitS) lo = s lo
    rw [divP18PrepDigit_frame k s3 divP18D2PrepS lo
      (divP18D2PrepS_frame k s3 lo (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega), hs3_lo]
  have h5digit :
      srun k s4 divP18D1PrepS 173 =
        (divP18YLo (s lo) (s hi) >>> 22) &&& 4194303 := by
    rw [divP18D1PrepS_spec k s4 (hs4 168), hs4_168, hs3_168, hs2_168,
      hpre.1]
  have h5 :
      s5 178 =
          (tld
            (tld
              (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
                ((divP18YHi (s hi) >>> 2) &&& 4194303))
              (((divP18YLo (s lo) (s hi) >>> 44) +
                ((divP18YHi (s hi) &&& 3) * 1048576) % M) % M))
            ((divP18YLo (s lo) (s hi) >>> 22) &&& 4194303)).1 ∧
        s5 172 =
          (tld
            (tld
              (tld (tld (0, 0) (divP18YHi (s hi) >>> 24))
                ((divP18YHi (s hi) >>> 2) &&& 4194303))
              (((divP18YLo (s lo) (s hi) >>> 44) +
                ((divP18YHi (s hi) &&& 3) * 1048576) % M) % M))
            ((divP18YLo (s lo) (s hi) >>> 22) &&& 4194303)).2 := by
    have h := divP18PrepDigit_spec k s4 divP18D1PrepS _ h5digit
      (divP18D1PrepS_frame k s4 178 (by decide))
      (divP18D1PrepS_frame k s4 172 (by decide))
    rw [h4.1, h4.2] at h
    exact h
  have hs5_168 : s5 168 = s4 168 :=
    divP18PrepDigit_frame k s4 divP18D1PrepS 168
      (divP18D1PrepS_frame k s4 168 (by decide))
      (by decide) (by decide) (by decide) (by decide)
  have hs5_lo : s5 lo = s lo := by
    change srun k s4 (divP18D1PrepS ++ divP18DigitS) lo = s lo
    rw [divP18PrepDigit_frame k s4 divP18D1PrepS lo
      (divP18D1PrepS_frame k s4 lo (by omega))
      (by omega) (by omega) (by omega) (by omega), hs4_lo]
  have h6digit :
      srun k s5 divP18D0PrepS 173 =
        divP18YLo (s lo) (s hi) &&& 4194303 := by
    rw [divP18D0PrepS_spec k s5, hs5_168, hs4_168, hs3_168, hs2_168,
      hpre.1]
  have h6 :
      s6 178 = ((divP18Digits (s lo) (s hi)).foldl tld (0, 0)).1 ∧
        s6 172 = ((divP18Digits (s lo) (s hi)).foldl tld (0, 0)).2 := by
    have h := divP18PrepDigit_spec k s5 divP18D0PrepS _ h6digit
      (divP18D0PrepS_frame k s5 178 (by decide))
      (divP18D0PrepS_frame k s5 172 (by decide))
    rw [h5.1, h5.2] at h
    simpa only [divP18Digits, List.foldl_cons, List.foldl_nil] using h
  have hs6_lo : s6 lo = s lo := by
    change srun k s5 (divP18D0PrepS ++ divP18DigitS) lo = s lo
    rw [divP18PrepDigit_frame k s5 divP18D0PrepS lo
      (divP18D0PrepS_frame k s5 lo (by omega))
      (by omega) (by omega) (by omega) (by omega), hs5_lo]
  have hfloor : sf 178 = ((divP18Digits (s lo) (s hi)).foldl tld (0, 0)).1 := by
    change srun k s6 (divP18CeilS lo) 178 = _
    rw [divP18CeilS_frame k s6 lo 178 (by decide) (by decide) (by decide), h6.1]
  have hceil : sf 179 =
      (tsub 1
          (bnat (s lo &&& 262143 = 0) *
            bnat (((divP18Digits (s lo) (s hi)).foldl tld (0, 0)).2 = 0)) +
        ((divP18Digits (s lo) (s hi)).foldl tld (0, 0)).1) % M := by
    change srun k s6 (divP18CeilS lo) 179 = _
    rw [divP18CeilS_spec k s6 lo, hs6_lo, h6.1, h6.2]
  constructor
  · calc
      srun k s (divP18S lo hi 178 179) 178 = sf 178 := by
        rw [divP18S_split]
        simp only [sf, s6, s5, s4, s3, s2, s1, srun_append]
      _ = (tdiv18 (s lo) (s hi)).1 := by
        rw [tdiv18_eq_ttail_digits]
        simpa only [ttail] using hfloor
  · calc
      srun k s (divP18S lo hi 178 179) 179 = sf 179 := by
        rw [divP18S_split]
        simp only [sf, s6, s5, s4, s3, s2, s1, srun_append]
      _ = (tdiv18 (s lo) (s hi)).2 := by
        rw [tdiv18_eq_ttail_digits]
        simpa only [ttail] using hceil

/-! ### `cmulBody`: canonical signs and final endpoint encoding

These two small scalar circuits are the remaining non-library arithmetic
inside `cmulBody`.  Naming them keeps the full proof compositional: the
four product signs and the two final endpoint encodings can be rewritten
without normalizing the 378-instruction body.
-/

/-- `canonSignBody`, viewed in the scalar machine. -/
def canonSignS (sa sb lo hi dst : Nat) : List Instr :=
  [ .binop dst .bxor (.reg sa) (.reg sb)
  , .binop 123 .eq (.reg lo) (.lit 0)
  , .binop 124 .eq (.reg hi) (.lit 0)
  , .binop 125 .mul (.reg 123) (.reg 124)
  , .binop 125 .sub (.lit 1) (.reg 125)
  , .binop dst .mul (.reg dst) (.reg 125) ]

theorem canonSignBody_lift (sa sb lo hi dst : Nat) :
    canonSignBody sa sb lo hi dst = lift (canonSignS sa sb lo hi dst) := rfl

/-- The complete four-sign stage, viewed in the scalar machine. -/
def cmulSignsS : List Instr :=
  canonSignS 100 102 111 112 119 ++
  canonSignS 100 103 113 114 120 ++
  canonSignS 101 102 115 116 121 ++
  canonSignS 101 103 117 118 122

theorem cmulSignsBody_lift : cmulSignsBody = lift cmulSignsS := by
  simp only [cmulSignsBody, cmulSignsS, canonSignBody_lift, lift,
    List.map_append]

/-- Registers clear of the fixed sign-canonicalization scratch area. -/
def CanonClear (r : Nat) : Prop := r ≠ 123 ∧ r ≠ 124 ∧ r ≠ 125

/-- **A product's canonical sign is xor for a nonzero magnitude and zero
for the two-limb zero.** -/
theorem canonSignS_spec (k : Nat) (s : RegState) (sa sb lo hi dst : Nat)
    (hc : ∀ r ∈ [sa, sb, lo, hi, dst], CanonClear r)
    (hdl : dst ≠ lo) (hdh : dst ≠ hi)
    (hsa : s sa ≤ 1) (hsb : s sb ≤ 1) :
    srun k s (canonSignS sa sb lo hi dst) dst =
      (s sa ^^^ s sb) * (1 - bnat (s lo = 0) * bnat (s hi = 0)) := by
  obtain ⟨hsa3, hsa4, hsa5⟩ := hc sa (by simp)
  obtain ⟨hsb3, hsb4, hsb5⟩ := hc sb (by simp)
  obtain ⟨hlo3, hlo4, hlo5⟩ := hc lo (by simp)
  obtain ⟨hhi3, hhi4, hhi5⟩ := hc hi (by simp)
  obtain ⟨hd3, hd4, hd5⟩ := hc dst (by simp)
  rcases (by omega : s sa = 0 ∨ s sa = 1) with h | h <;>
  rcases (by omega : s sb = 0 ∨ s sb = 1) with h' | h' <;>
  by_cases hL : s lo = 0 <;> by_cases hH : s hi = 0 <;>
  simp only [canonSignS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, zero_mod_M, one_mod_M, if_true, if_false,
    hsa3, hsa4, hsa5, hsb3, hsb4, hsb5, hlo3, hlo4, hlo5,
    hhi3, hhi4, hhi5, hd3, hd4, hd5, hdl, hdh,
    Ne.symm hsa3, Ne.symm hsa4, Ne.symm hsa5,
    Ne.symm hsb3, Ne.symm hsb4, Ne.symm hsb5,
    Ne.symm hlo3, Ne.symm hlo4, Ne.symm hlo5,
    Ne.symm hhi3, Ne.symm hhi4, Ne.symm hhi5,
    Ne.symm hd3, Ne.symm hd4, Ne.symm hd5,
    Ne.symm hdl, Ne.symm hdh, h, h', hL, hH, bnat, Nat.reduceEqDiff]
  all_goals decide

/-- The sign circuit writes only its destination and `123`--`125`. -/
theorem canonSignS_frame (k : Nat) (s : RegState) (sa sb lo hi dst j : Nat)
    (hd : j ≠ dst) (h3 : j ≠ 123) (h4 : j ≠ 124) (h5 : j ≠ 125) :
    srun k s (canonSignS sa sb lo hi dst) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi'
  simp only [canonSignS, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-- **The four-sign stage canonicalizes all four endpoint-product signs.** -/
theorem cmulSignsS_spec (k : Nat) (s : RegState)
    (h100 : s 100 ≤ 1) (h101 : s 101 ≤ 1)
    (h102 : s 102 ≤ 1) (h103 : s 103 ≤ 1) :
    srun k s cmulSignsS 119 =
        (s 100 ^^^ s 102) * (1 - bnat (s 111 = 0) * bnat (s 112 = 0)) ∧
      srun k s cmulSignsS 120 =
        (s 100 ^^^ s 103) * (1 - bnat (s 113 = 0) * bnat (s 114 = 0)) ∧
      srun k s cmulSignsS 121 =
        (s 101 ^^^ s 102) * (1 - bnat (s 115 = 0) * bnat (s 116 = 0)) ∧
      srun k s cmulSignsS 122 =
        (s 101 ^^^ s 103) * (1 - bnat (s 117 = 0) * bnat (s 118 = 0)) := by
  let s1 := srun k s (canonSignS 100 102 111 112 119)
  let s2 := srun k s1 (canonSignS 100 103 113 114 120)
  let s3 := srun k s2 (canonSignS 101 102 115 116 121)
  let s4 := srun k s3 (canonSignS 101 103 117 118 122)
  have h1 := canonSignS_spec k s 100 102 111 112 119
    (by simp [CanonClear]) (by decide) (by decide) h100 h102
  have s1_100 : s1 100 = s 100 :=
    canonSignS_frame k s 100 102 111 112 119 100
      (by decide) (by decide) (by decide) (by decide)
  have s1_101 : s1 101 = s 101 :=
    canonSignS_frame k s 100 102 111 112 119 101
      (by decide) (by decide) (by decide) (by decide)
  have s1_102 : s1 102 = s 102 :=
    canonSignS_frame k s 100 102 111 112 119 102
      (by decide) (by decide) (by decide) (by decide)
  have s1_103 : s1 103 = s 103 :=
    canonSignS_frame k s 100 102 111 112 119 103
      (by decide) (by decide) (by decide) (by decide)
  have s1_113 : s1 113 = s 113 :=
    canonSignS_frame k s 100 102 111 112 119 113
      (by decide) (by decide) (by decide) (by decide)
  have s1_114 : s1 114 = s 114 :=
    canonSignS_frame k s 100 102 111 112 119 114
      (by decide) (by decide) (by decide) (by decide)
  have s1_115 : s1 115 = s 115 :=
    canonSignS_frame k s 100 102 111 112 119 115
      (by decide) (by decide) (by decide) (by decide)
  have s1_116 : s1 116 = s 116 :=
    canonSignS_frame k s 100 102 111 112 119 116
      (by decide) (by decide) (by decide) (by decide)
  have s1_117 : s1 117 = s 117 :=
    canonSignS_frame k s 100 102 111 112 119 117
      (by decide) (by decide) (by decide) (by decide)
  have s1_118 : s1 118 = s 118 :=
    canonSignS_frame k s 100 102 111 112 119 118
      (by decide) (by decide) (by decide) (by decide)
  have h2 := canonSignS_spec k s1 100 103 113 114 120
    (by simp [CanonClear]) (by decide) (by decide)
    (by rw [s1_100]; exact h100) (by rw [s1_103]; exact h103)
  rw [s1_100, s1_103, s1_113, s1_114] at h2
  have s2_101 : s2 101 = s 101 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 101 = s 101
    rw [canonSignS_frame k s1 100 103 113 114 120 101
      (by decide) (by decide) (by decide) (by decide), s1_101]
  have s2_102 : s2 102 = s 102 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 102 = s 102
    rw [canonSignS_frame k s1 100 103 113 114 120 102
      (by decide) (by decide) (by decide) (by decide), s1_102]
  have s2_115 : s2 115 = s 115 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 115 = s 115
    rw [canonSignS_frame k s1 100 103 113 114 120 115
      (by decide) (by decide) (by decide) (by decide), s1_115]
  have s2_116 : s2 116 = s 116 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 116 = s 116
    rw [canonSignS_frame k s1 100 103 113 114 120 116
      (by decide) (by decide) (by decide) (by decide), s1_116]
  have h3 := canonSignS_spec k s2 101 102 115 116 121
    (by simp [CanonClear]) (by decide) (by decide)
    (by rw [s2_101]; exact h101) (by rw [s2_102]; exact h102)
  rw [s2_101, s2_102, s2_115, s2_116] at h3
  have s2_103 : s2 103 = s 103 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 103 = s 103
    rw [canonSignS_frame k s1 100 103 113 114 120 103
      (by decide) (by decide) (by decide) (by decide), s1_103]
  have s2_117 : s2 117 = s 117 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 117 = s 117
    rw [canonSignS_frame k s1 100 103 113 114 120 117
      (by decide) (by decide) (by decide) (by decide), s1_117]
  have s2_118 : s2 118 = s 118 := by
    change srun k s1 (canonSignS 100 103 113 114 120) 118 = s 118
    rw [canonSignS_frame k s1 100 103 113 114 120 118
      (by decide) (by decide) (by decide) (by decide), s1_118]
  have s3_101 : s3 101 = s 101 := by
    change srun k s2 (canonSignS 101 102 115 116 121) 101 = s 101
    rw [canonSignS_frame k s2 101 102 115 116 121 101
      (by decide) (by decide) (by decide) (by decide), s2_101]
  have s3_103 : s3 103 = s 103 := by
    change srun k s2 (canonSignS 101 102 115 116 121) 103 = s 103
    rw [canonSignS_frame k s2 101 102 115 116 121 103
      (by decide) (by decide) (by decide) (by decide), s2_103]
  have s3_117 : s3 117 = s 117 := by
    change srun k s2 (canonSignS 101 102 115 116 121) 117 = s 117
    rw [canonSignS_frame k s2 101 102 115 116 121 117
      (by decide) (by decide) (by decide) (by decide), s2_117]
  have s3_118 : s3 118 = s 118 := by
    change srun k s2 (canonSignS 101 102 115 116 121) 118 = s 118
    rw [canonSignS_frame k s2 101 102 115 116 121 118
      (by decide) (by decide) (by decide) (by decide), s2_118]
  have h4 := canonSignS_spec k s3 101 103 117 118 122
    (by simp [CanonClear]) (by decide) (by decide)
    (by rw [s3_101]; exact h101) (by rw [s3_103]; exact h103)
  rw [s3_101, s3_103, s3_117, s3_118] at h4
  have s2_119 : s2 119 =
      (s 100 ^^^ s 102) * (1 - bnat (s 111 = 0) * bnat (s 112 = 0)) := by
    change srun k s1 (canonSignS 100 103 113 114 120) 119 = _
    rw [canonSignS_frame k s1 100 103 113 114 120 119
      (by decide) (by decide) (by decide) (by decide)]
    exact h1
  have s3_119 : s3 119 =
      (s 100 ^^^ s 102) * (1 - bnat (s 111 = 0) * bnat (s 112 = 0)) := by
    change srun k s2 (canonSignS 101 102 115 116 121) 119 = _
    rw [canonSignS_frame k s2 101 102 115 116 121 119
      (by decide) (by decide) (by decide) (by decide), s2_119]
  have s3_120 : s3 120 =
      (s 100 ^^^ s 103) * (1 - bnat (s 113 = 0) * bnat (s 114 = 0)) := by
    change srun k s2 (canonSignS 101 102 115 116 121) 120 = _
    rw [canonSignS_frame k s2 101 102 115 116 121 120
      (by decide) (by decide) (by decide) (by decide)]
    exact h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change s4 119 = _
    change srun k s3 (canonSignS 101 103 117 118 122) 119 = _
    rw [canonSignS_frame k s3 101 103 117 118 122 119
      (by decide) (by decide) (by decide) (by decide), s3_119]
  · change s4 120 = _
    change srun k s3 (canonSignS 101 103 117 118 122) 120 = _
    rw [canonSignS_frame k s3 101 103 117 118 122 120
      (by decide) (by decide) (by decide) (by decide), s3_120]
  · change s4 121 = _
    change srun k s3 (canonSignS 101 103 117 118 122) 121 = _
    rw [canonSignS_frame k s3 101 103 117 118 122 121
      (by decide) (by decide) (by decide) (by decide)]
    exact h3
  · change s4 122 = _
    exact h4

/-- The shared scalar endpoint encoder.  `neg` supplies the quotient to
negate for a negative endpoint and `pos` supplies the nonnegative one. -/
def cmulEncodeS (sign neg pos dst : Nat) : List Instr :=
  [ .binop 108 .sub (.lit 0) (.reg neg)
  , .binop 109 .sub (.lit 1) (.reg sign)
  , .binop dst .mul (.reg 109) (.reg pos)
  , .binop 108 .mul (.reg sign) (.reg 108)
  , .binop dst .add (.reg dst) (.reg 108) ]

theorem cmulLowerBody_lift (sign q qc dst : Nat) :
    cmulLowerBody sign q qc dst = lift (cmulEncodeS sign qc q dst) := rfl

theorem cmulUpperBody_lift (sign q qc dst : Nat) :
    cmulUpperBody sign q qc dst = lift (cmulEncodeS sign q qc dst) := rfl

/-- Registers clear of the endpoint encoder's two scratch registers. -/
def EncodeClear (r : Nat) : Prop := r ≠ 108 ∧ r ≠ 109

/-- **The endpoint encoder selects `-neg` for sign one and `pos` for sign
zero.** -/
theorem cmulEncodeS_spec (k : Nat) (s : RegState) (sign neg pos dst : Nat)
    (hc : ∀ r ∈ [sign, neg, pos, dst], EncodeClear r)
    (hds : dst ≠ sign) (hsign : s sign ≤ 1) (hs : ∀ j, s j < M) :
    srun k s (cmulEncodeS sign neg pos dst) dst =
      if s sign = 1 then tsub 0 (s neg) else s pos := by
  obtain ⟨sg8, sg9⟩ := hc sign (by simp)
  obtain ⟨n8, n9⟩ := hc neg (by simp)
  obtain ⟨p8, p9⟩ := hc pos (by simp)
  obtain ⟨d8, d9⟩ := hc dst (by simp)
  have hplus : (1 + M) % M = 1 := by decide
  have hminus : (1 + (M - 1)) % M = 0 := by decide
  have hp : s pos % M = s pos := Nat.mod_eq_of_lt (hs pos)
  rcases (by omega : s sign = 0 ∨ s sign = 1) with h | h
  · simp only [cmulEncodeS, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, zero_mod_M, one_mod_M, if_true, if_false,
      sg8, sg9, n8, n9, p8, p9, d8, d9, hds,
      Ne.symm sg8, Ne.symm sg9, Ne.symm n8, Ne.symm n9,
      Ne.symm p8, Ne.symm p9, Ne.symm d8, Ne.symm d9,
      Ne.symm hds, h, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
      Nat.zero_add, Nat.sub_zero, Nat.one_mul, Nat.reduceEqDiff, hplus, hp,
      Nat.mod_mod]
  · simp only [cmulEncodeS, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, zero_mod_M, one_mod_M, if_true, if_false,
      sg8, sg9, n8, n9, p8, p9, d8, d9, hds,
      Ne.symm sg8, Ne.symm sg9, Ne.symm n8, Ne.symm n9,
      Ne.symm p8, Ne.symm p9, Ne.symm d8, Ne.symm d9,
      Ne.symm hds, h, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
      Nat.zero_add, Nat.sub_self, Nat.one_mul, tsub, Nat.mod_mod,
      Nat.reduceEqDiff, hminus]

/-- The endpoint encoder writes only its destination and `108`--`109`. -/
theorem cmulEncodeS_frame (k : Nat) (s : RegState)
    (sign neg pos dst j : Nat) (hd : j ≠ dst) (h8 : j ≠ 108) (h9 : j ≠ 109) :
    srun k s (cmulEncodeS sign neg pos dst) j = s j := by
  refine srun_untouched k j _ ?_ s
  intro i hi'
  simp only [cmulEncodeS, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-- The input-decomposition stage in the scalar machine. -/
def cmulDecompS (gate aLo aHi bLo bHi : Nat) : List Instr :=
  smDecompG H63 CAP gate aLo 100 104 ++
  smDecompG H63 CAP gate aHi 101 105 ++
  smDecompG H63 CAP gate bLo 102 106 ++
  smDecompG H63 CAP gate bHi 103 107

/-- The four-product stage in the scalar machine. -/
def cmulProductsS : List Instr :=
  mulWideG 4294967295 4294967296 104 106 111 112
    154 155 156 157 158 159 160 161 ++
  mulWideG 4294967295 4294967296 104 107 113 114
    154 155 156 157 158 159 160 161 ++
  mulWideG 4294967295 4294967296 105 106 115 116
    154 155 156 157 158 159 160 161 ++
  mulWideG 4294967295 4294967296 105 107 117 118
    154 155 156 157 158 159 160 161

/-- The two pair-comparison flags in the scalar machine. -/
def cmulPairFlagsS : List Instr :=
  cmpLtS 119 111 112 120 113 114 132 ++
  cmpLtS 121 115 116 122 117 118 133

/-- The four pairwise extrema selects in the scalar machine. -/
def cmulPairSelectsS : List Instr :=
  selTripleS 132 119 111 112 120 113 114 134 135 136 ++
  selTripleS 132 120 113 114 119 111 112 137 138 153 ++
  selTripleS 133 121 115 116 122 117 118 162 163 164 ++
  selTripleS 133 122 117 118 121 115 116 165 166 167

/-- The final min/max comparison flags in the scalar machine. -/
def cmulExtremaFlagsS : List Instr :=
  cmpLtS 134 135 136 162 163 164 176 ++
  cmpLtS 137 138 153 165 166 167 177

/-- The global minimum and maximum selects in the scalar machine. -/
def cmulExtremaSelectsS : List Instr :=
  selTripleS 176 134 135 136 162 163 164 134 135 136 ++
  selTripleS 177 165 166 167 137 138 153 137 138 153

/-- The four-way ordering stage in the scalar machine. -/
def cmulOrderS : List Instr :=
  cmulPairFlagsS ++ cmulPairSelectsS ++
  cmulExtremaFlagsS ++ cmulExtremaSelectsS

/-- The division and endpoint-encoding stage in the scalar machine. -/
def cmulFinishS (cLo cHi : Nat) : List Instr :=
  divP18S 135 136 178 179 ++ cmulEncodeS 134 179 178 cLo ++
  divP18S 138 153 178 179 ++ cmulEncodeS 137 178 179 cHi

/-- The complete interval multiplier in the scalar machine. -/
def cmulS (gate aLo aHi bLo bHi cLo cHi : Nat) : List Instr :=
  cmulDecompS gate aLo aHi bLo bHi ++ cmulProductsS ++ cmulSignsS ++
  cmulOrderS ++ cmulFinishS cLo cHi

theorem cmulDecompBody_lift (gate aLo aHi bLo bHi : Nat) :
    cmulDecompBody gate aLo aHi bLo bHi =
      lift (cmulDecompS gate aLo aHi bLo bHi) := by
  simp only [cmulDecompBody, cmulDecompS, smDecomp_lift, lift,
    List.map_append]

theorem cmulProductsBody_lift : cmulProductsBody = lift cmulProductsS := by
  simp only [cmulProductsBody, cmulProductsS, mulWideBody_lift, lift,
    List.map_append]

theorem cmulPairFlagsBody_lift : cmulPairFlagsBody = lift cmulPairFlagsS := by
  simp only [cmulPairFlagsBody, cmulPairFlagsS, cmpLtBody_lift, lift,
    List.map_append]

theorem cmulPairSelectsBody_lift :
    cmulPairSelectsBody = lift cmulPairSelectsS := by
  simp only [cmulPairSelectsBody, cmulPairSelectsS, selTriple_lift, lift,
    List.map_append]

theorem cmulExtremaFlagsBody_lift :
    cmulExtremaFlagsBody = lift cmulExtremaFlagsS := by
  simp only [cmulExtremaFlagsBody, cmulExtremaFlagsS, cmpLtBody_lift, lift,
    List.map_append]

theorem cmulExtremaSelectsBody_lift :
    cmulExtremaSelectsBody = lift cmulExtremaSelectsS := by
  simp only [cmulExtremaSelectsBody, cmulExtremaSelectsS, selTriple_lift,
    lift, List.map_append]

theorem cmulOrderBody_lift : cmulOrderBody = lift cmulOrderS := by
  simp only [cmulOrderBody, cmulOrderS, cmulPairFlagsBody,
    cmulPairSelectsBody, cmulExtremaFlagsBody, cmulExtremaSelectsBody,
    cmulPairFlagsS, cmulPairSelectsS, cmulExtremaFlagsS,
    cmulExtremaSelectsS, cmpLtBody_lift, selTriple_lift, lift,
    List.map_append]

theorem cmulFinishBody_lift (cLo cHi : Nat) :
    cmulFinishBody cLo cHi = lift (cmulFinishS cLo cHi) := by
  simp only [cmulFinishBody, cmulFinishS, divP18Body_lift,
    cmulLowerBody_lift, cmulUpperBody_lift, lift, List.map_append]

/-- **The production `cmulBody` is exactly the lift of the compositional
scalar block.** -/
theorem cmulBody_lift (gate aLo aHi bLo bHi cLo cHi : Nat) :
    cmulBody gate aLo aHi bLo bHi cLo cHi =
      lift (cmulS gate aLo aHi bLo bHi cLo cHi) := by
  simp only [cmulBody, cmulS, cmulDecompBody_lift, cmulProductsBody_lift,
    cmulSignsBody_lift, cmulOrderBody_lift, cmulFinishBody_lift, lift,
    List.map_append]

/-- External `cmul` registers are outside its fixed scratch allocation and
are never the global violation register. -/
def CmulExternal (r : Nat) : Prop := r ≠ rViol ∧ (r < 100 ∨ 179 < r)

theorem cmulExternal_ne_scratch {r x : Nat} (hr : CmulExternal r)
    (hx0 : 100 ≤ x) (hx1 : x ≤ 179) : r ≠ x := by
  simp only [CmulExternal] at hr
  omega

/-- One decomposition block preserves every external register. -/
theorem smDecomp_external_frame (k : Nat) (s : RegState)
    (gate w sg mg j : Nat) (hsg0 : 100 ≤ sg) (hsg1 : sg ≤ 179)
    (hmg0 : 100 ≤ mg) (hmg1 : mg ≤ 179) (hj : CmulExternal j) :
    srun k s (smDecompG H63 CAP gate w sg mg) j = s j := by
  apply smDecompG_frame
  · exact cmulExternal_ne_scratch hj hsg0 hsg1
  · exact cmulExternal_ne_scratch hj hmg0 hmg1
  · exact hj.1
  · exact cmulExternal_ne_scratch hj (by decide) (by decide)
  · exact cmulExternal_ne_scratch hj (by decide) (by decide)
  · exact cmulExternal_ne_scratch hj (by decide) (by decide)

/-- The complete decomposition stage preserves every external register. -/
theorem cmulDecompS_external_frame (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi j : Nat) (hj : CmulExternal j) :
    srun k s (cmulDecompS gate aLo aHi bLo bHi) j = s j := by
  simp only [cmulDecompS, srun_append]
  rw [smDecomp_external_frame _ _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) hj,
    smDecomp_external_frame _ _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) hj,
    smDecomp_external_frame _ _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) hj,
    smDecomp_external_frame _ _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) hj]

/-- **The four decomposition blocks compute the four `tmag` pairs and the
same left-associated violation accumulation used by `tcmul`.** -/
theorem cmulDecompS_spec (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi : Nat)
    (hc : ∀ r ∈ [gate, aLo, aHi, bLo, bHi], CmulExternal r)
    (hs : ∀ j, s j < M) :
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 100 = (tmag (s aLo)).1 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 104 = (tmag (s aLo)).2 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 101 = (tmag (s aHi)).1 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 105 = (tmag (s aHi)).2 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 102 = (tmag (s bLo)).1 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 106 = (tmag (s bLo)).2 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 103 = (tmag (s bHi)).1 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) 107 = (tmag (s bHi)).2 ∧
    srun k s (cmulDecompS gate aLo aHi bLo bHi) rViol =
      (((s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate)) |||
          (bnat (CAP < (tmag (s aHi)).2) * s gate)) |||
        (bnat (CAP < (tmag (s bLo)).2) * s gate)) |||
      (bnat (CAP < (tmag (s bHi)).2) * s gate) := by
  have cg := hc gate (by simp)
  have caL := hc aLo (by simp)
  have caH := hc aHi (by simp)
  have cbL := hc bLo (by simp)
  have cbH := hc bHi (by simp)
  let d1 := srun k s (smDecompG H63 CAP gate aLo 100 104)
  let d2 := srun k d1 (smDecompG H63 CAP gate aHi 101 105)
  let d3 := srun k d2 (smDecompG H63 CAP gate bLo 102 106)
  let d4 := srun k d3 (smDecompG H63 CAP gate bHi 103 107)
  have h1 := smDecomp_tmag k s gate aLo 100 104 hs
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch caL (by decide) (by decide))
    (cmulExternal_ne_scratch caL (by decide) (by decide))
    (by decide) (cmulExternal_ne_scratch caL (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
  have hd1 : ∀ j, d1 j < M := srun_lt_of_lt k _ s hs
  have d1g : d1 gate = s gate := smDecomp_external_frame k s gate aLo 100 104 gate
    (by decide) (by decide) (by decide) (by decide) cg
  have d1aH : d1 aHi = s aHi := smDecomp_external_frame k s gate aLo 100 104 aHi
    (by decide) (by decide) (by decide) (by decide) caH
  have d1v : d1 rViol =
      s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate) := h1.2.2
  have h2 := smDecomp_tmag k d1 gate aHi 101 105 hd1
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch caH (by decide) (by decide))
    (cmulExternal_ne_scratch caH (by decide) (by decide))
    (by decide) (cmulExternal_ne_scratch caH (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
  rw [d1aH, d1g, d1v] at h2
  have hd2 : ∀ j, d2 j < M := srun_lt_of_lt k _ d1 hd1
  have d2g : d2 gate = s gate := by
    change srun k d1 (smDecompG H63 CAP gate aHi 101 105) gate = s gate
    rw [smDecomp_external_frame k d1 gate aHi 101 105 gate
      (by decide) (by decide) (by decide) (by decide) cg, d1g]
  have d2bL : d2 bLo = s bLo := by
    change srun k d1 (smDecompG H63 CAP gate aHi 101 105) bLo = s bLo
    rw [smDecomp_external_frame k d1 gate aHi 101 105 bLo
      (by decide) (by decide) (by decide) (by decide) cbL]
    change d1 bLo = s bLo
    exact smDecomp_external_frame k s gate aLo 100 104 bLo
      (by decide) (by decide) (by decide) (by decide) cbL
  have d2v : d2 rViol =
      (s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate)) |||
        (bnat (CAP < (tmag (s aHi)).2) * s gate) := h2.2.2
  have h3 := smDecomp_tmag k d2 gate bLo 102 106 hd2
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cbL (by decide) (by decide))
    (cmulExternal_ne_scratch cbL (by decide) (by decide))
    (by decide) (cmulExternal_ne_scratch cbL (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
  rw [d2bL, d2g, d2v] at h3
  have hd3 : ∀ j, d3 j < M := srun_lt_of_lt k _ d2 hd2
  have d3g : d3 gate = s gate := by
    change srun k d2 (smDecompG H63 CAP gate bLo 102 106) gate = s gate
    rw [smDecomp_external_frame k d2 gate bLo 102 106 gate
      (by decide) (by decide) (by decide) (by decide) cg, d2g]
  have d3bH : d3 bHi = s bHi := by
    change srun k d2 (smDecompG H63 CAP gate bLo 102 106) bHi = s bHi
    rw [smDecomp_external_frame k d2 gate bLo 102 106 bHi
      (by decide) (by decide) (by decide) (by decide) cbH]
    change d2 bHi = s bHi
    rw [show d2 bHi = d1 bHi from
      smDecomp_external_frame k d1 gate aHi 101 105 bHi
        (by decide) (by decide) (by decide) (by decide) cbH]
    change d1 bHi = s bHi
    exact smDecomp_external_frame k s gate aLo 100 104 bHi
      (by decide) (by decide) (by decide) (by decide) cbH
  have d3v : d3 rViol =
      ((s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate)) |||
          (bnat (CAP < (tmag (s aHi)).2) * s gate)) |||
        (bnat (CAP < (tmag (s bLo)).2) * s gate) := h3.2.2
  have h4 := smDecomp_tmag k d3 gate bHi 103 107 hd3
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cbH (by decide) (by decide))
    (cmulExternal_ne_scratch cbH (by decide) (by decide))
    (by decide) (cmulExternal_ne_scratch cbH (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
    (cmulExternal_ne_scratch cg (by decide) (by decide))
  rw [d3bH, d3g, d3v] at h4
  have f (st : RegState) (gate w sg mg j : Nat)
      (hsg : j ≠ sg) (hmg : j ≠ mg) (hv : j ≠ rViol)
      (h8 : j ≠ 108) (h9 : j ≠ 109) (hA : j ≠ 110) :
      srun k st (smDecompG H63 CAP gate w sg mg) j = st j :=
    smDecompG_frame k st H63 CAP gate w sg mg j hsg hmg hv h8 h9 hA
  have f4 (j : Nat) (hsg : j ≠ 103) (hmg : j ≠ 107) (hv : j ≠ rViol)
      (h8 : j ≠ 108) (h9 : j ≠ 109) (hA : j ≠ 110) : d4 j = d3 j :=
    f d3 gate bHi 103 107 j hsg hmg hv h8 h9 hA
  have f3 (j : Nat) (hsg : j ≠ 102) (hmg : j ≠ 106) (hv : j ≠ rViol)
      (h8 : j ≠ 108) (h9 : j ≠ 109) (hA : j ≠ 110) : d3 j = d2 j :=
    f d2 gate bLo 102 106 j hsg hmg hv h8 h9 hA
  have f2 (j : Nat) (hsg : j ≠ 101) (hmg : j ≠ 105) (hv : j ≠ rViol)
      (h8 : j ≠ 108) (h9 : j ≠ 109) (hA : j ≠ 110) : d2 j = d1 j :=
    f d1 gate aHi 101 105 j hsg hmg hv h8 h9 hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cmulDecompS, srun_append] <;> change d4 _ = _
  · rw [f4 100 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), f3 100 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), f2 100 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h1.1
  · rw [f4 104 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), f3 104 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), f2 104 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h1.2.1
  · rw [f4 101 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), f3 101 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact h2.1
  · rw [f4 105 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), f3 105 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact h2.2.1
  · rw [f4 102 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact h3.1
  · rw [f4 106 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact h3.2.1
  · exact h4.1
  · exact h4.2.1
  · exact h4.2.2

/-- **The four-product stage computes the four exact `MulWide.hl`
products of the decoded endpoint magnitudes.** -/
theorem cmulProductsS_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun k s cmulProductsS 111 = (Verified.MulWide.hl (s 104) (s 106)).1 ∧
    srun k s cmulProductsS 112 = (Verified.MulWide.hl (s 104) (s 106)).2 ∧
    srun k s cmulProductsS 113 = (Verified.MulWide.hl (s 104) (s 107)).1 ∧
    srun k s cmulProductsS 114 = (Verified.MulWide.hl (s 104) (s 107)).2 ∧
    srun k s cmulProductsS 115 = (Verified.MulWide.hl (s 105) (s 106)).1 ∧
    srun k s cmulProductsS 116 = (Verified.MulWide.hl (s 105) (s 106)).2 ∧
    srun k s cmulProductsS 117 = (Verified.MulWide.hl (s 105) (s 107)).1 ∧
    srun k s cmulProductsS 118 = (Verified.MulWide.hl (s 105) (s 107)).2 := by
  let p1 := srun k s (mulWideG 4294967295 4294967296 104 106 111 112
    154 155 156 157 158 159 160 161)
  let p2 := srun k p1 (mulWideG 4294967295 4294967296 104 107 113 114
    154 155 156 157 158 159 160 161)
  let p3 := srun k p2 (mulWideG 4294967295 4294967296 105 106 115 116
    154 155 156 157 158 159 160 161)
  let p4 := srun k p3 (mulWideG 4294967295 4294967296 105 107 117 118
    154 155 156 157 158 159 160 161)
  have h1 := mulWideG_hl k s 104 106 111 112
    154 155 156 157 158 159 160 161
    (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8]) (by decide) hs
  have hp1 : ∀ j, p1 j < M := srun_lt_of_lt k _ s hs
  have frame (st : RegState) (ra rb lo hi j : Nat)
      (hlo : j ≠ lo) (hhi : j ≠ hi)
      (hj : NotIn8 j 154 155 156 157 158 159 160 161) :
      srun k st (mulWideG 4294967295 4294967296 ra rb lo hi
        154 155 156 157 158 159 160 161) j = st j :=
    mulWideG_frame k st 4294967295 4294967296 ra rb lo hi
      154 155 156 157 158 159 160 161 j hlo hhi hj
  have p1_104 : p1 104 = s 104 := frame s 104 106 111 112 104
    (by decide) (by decide) (by simp [NotIn8])
  have p1_105 : p1 105 = s 105 := frame s 104 106 111 112 105
    (by decide) (by decide) (by simp [NotIn8])
  have p1_106 : p1 106 = s 106 := frame s 104 106 111 112 106
    (by decide) (by decide) (by simp [NotIn8])
  have p1_107 : p1 107 = s 107 := frame s 104 106 111 112 107
    (by decide) (by decide) (by simp [NotIn8])
  have h2 := mulWideG_hl k p1 104 107 113 114
    154 155 156 157 158 159 160 161
    (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8]) (by decide) hp1
  rw [p1_104, p1_107] at h2
  have hp2 : ∀ j, p2 j < M := srun_lt_of_lt k _ p1 hp1
  have p2_105 : p2 105 = s 105 := by
    change srun k p1 (mulWideG 4294967295 4294967296 104 107 113 114
      154 155 156 157 158 159 160 161) 105 = s 105
    rw [frame p1 104 107 113 114 105 (by decide) (by decide)
      (by simp [NotIn8]), p1_105]
  have p2_106 : p2 106 = s 106 := by
    change srun k p1 (mulWideG 4294967295 4294967296 104 107 113 114
      154 155 156 157 158 159 160 161) 106 = s 106
    rw [frame p1 104 107 113 114 106 (by decide) (by decide)
      (by simp [NotIn8]), p1_106]
  have p2_107 : p2 107 = s 107 := by
    change srun k p1 (mulWideG 4294967295 4294967296 104 107 113 114
      154 155 156 157 158 159 160 161) 107 = s 107
    rw [frame p1 104 107 113 114 107 (by decide) (by decide)
      (by simp [NotIn8]), p1_107]
  have h3 := mulWideG_hl k p2 105 106 115 116
    154 155 156 157 158 159 160 161
    (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8]) (by decide) hp2
  rw [p2_105, p2_106] at h3
  have hp3 : ∀ j, p3 j < M := srun_lt_of_lt k _ p2 hp2
  have p3_105 : p3 105 = s 105 := by
    change srun k p2 (mulWideG 4294967295 4294967296 105 106 115 116
      154 155 156 157 158 159 160 161) 105 = s 105
    rw [frame p2 105 106 115 116 105 (by decide) (by decide)
      (by simp [NotIn8]), p2_105]
  have p3_107 : p3 107 = s 107 := by
    change srun k p2 (mulWideG 4294967295 4294967296 105 106 115 116
      154 155 156 157 158 159 160 161) 107 = s 107
    rw [frame p2 105 106 115 116 107 (by decide) (by decide)
      (by simp [NotIn8]), p2_107]
  have h4 := mulWideG_hl k p3 105 107 117 118
    154 155 156 157 158 159 160 161
    (by simp [Distinct8]) (by simp [NotIn8]) (by simp [NotIn8])
    (by simp [NotIn8]) (by simp [NotIn8]) (by decide) hp3
  rw [p3_105, p3_107] at h4
  have f4 (j : Nat) (hl : j ≠ 117) (hh : j ≠ 118)
      (hj : NotIn8 j 154 155 156 157 158 159 160 161) : p4 j = p3 j :=
    frame p3 105 107 117 118 j hl hh hj
  have f3 (j : Nat) (hl : j ≠ 115) (hh : j ≠ 116)
      (hj : NotIn8 j 154 155 156 157 158 159 160 161) : p3 j = p2 j :=
    frame p2 105 106 115 116 j hl hh hj
  have f2 (j : Nat) (hl : j ≠ 113) (hh : j ≠ 114)
      (hj : NotIn8 j 154 155 156 157 158 159 160 161) : p2 j = p1 j :=
    frame p1 104 107 113 114 j hl hh hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cmulProductsS, srun_append] <;> change p4 _ = _
  · rw [f4 111 (by decide) (by decide) (by simp [NotIn8]),
      f3 111 (by decide) (by decide) (by simp [NotIn8]),
      f2 111 (by decide) (by decide) (by simp [NotIn8])]
    exact h1.1
  · rw [f4 112 (by decide) (by decide) (by simp [NotIn8]),
      f3 112 (by decide) (by decide) (by simp [NotIn8]),
      f2 112 (by decide) (by decide) (by simp [NotIn8])]
    exact h1.2
  · rw [f4 113 (by decide) (by decide) (by simp [NotIn8]),
      f3 113 (by decide) (by decide) (by simp [NotIn8])]
    exact h2.1
  · rw [f4 114 (by decide) (by decide) (by simp [NotIn8]),
      f3 114 (by decide) (by decide) (by simp [NotIn8])]
    exact h2.2
  · rw [f4 115 (by decide) (by decide) (by simp [NotIn8])]
    exact h3.1
  · rw [f4 116 (by decide) (by decide) (by simp [NotIn8])]
    exact h3.2
  · exact h4.1
  · exact h4.2

/-- The four-product stage writes only its eight outputs and the common
`154`--`161` multiplication scratch area. -/
theorem cmulProductsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h111 : j ≠ 111) (h112 : j ≠ 112) (h113 : j ≠ 113) (h114 : j ≠ 114)
    (h115 : j ≠ 115) (h116 : j ≠ 116) (h117 : j ≠ 117) (h118 : j ≠ 118)
    (hj : NotIn8 j 154 155 156 157 158 159 160 161) :
    srun k s cmulProductsS j = s j := by
  simp only [cmulProductsS, srun_append]
  rw [mulWideG_frame k _ 4294967295 4294967296 105 107 117 118
      154 155 156 157 158 159 160 161 j h117 h118 hj,
    mulWideG_frame k _ 4294967295 4294967296 105 106 115 116
      154 155 156 157 158 159 160 161 j h115 h116 hj,
    mulWideG_frame k _ 4294967295 4294967296 104 107 113 114
      154 155 156 157 158 159 160 161 j h113 h114 hj,
    mulWideG_frame k s 4294967295 4294967296 104 106 111 112
      154 155 156 157 158 159 160 161 j h111 h112 hj]

/-- The four canonical-sign calls write only their four outputs and the
common `123`--`125` scratch area. -/
theorem cmulSignsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h119 : j ≠ 119) (h120 : j ≠ 120) (h121 : j ≠ 121) (h122 : j ≠ 122)
    (h123 : j ≠ 123) (h124 : j ≠ 124) (h125 : j ≠ 125) :
    srun k s cmulSignsS j = s j := by
  simp only [cmulSignsS, srun_append]
  rw [canonSignS_frame k _ 101 103 117 118 122 j h122 h123 h124 h125,
    canonSignS_frame k _ 101 102 115 116 121 j h121 h123 h124 h125,
    canonSignS_frame k _ 100 103 113 114 120 j h120 h123 h124 h125,
    canonSignS_frame k s 100 102 111 112 119 j h119 h123 h124 h125]

/-- A canonicalized xor sign is still a bit. -/
theorem canonSignValue_le_one (sa sb lo hi : Nat)
    (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (sa ^^^ sb) * (1 - bnat (lo = 0) * bnat (hi = 0)) ≤ 1 := by
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
  by_cases hlo : lo = 0 <;> by_cases hhi : hi = 0 <;>
    simp [bnat, hlo, hhi]

/-- The two initial comparisons preserve every register outside their flags
and the fixed comparison scratch area. -/
theorem cmulPairFlagsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h132 : j ≠ 132) (h133 : j ≠ 133) (hj : CmpClear j) :
    srun k s cmulPairFlagsS j = s j := by
  simp only [cmulPairFlagsS, srun_append]
  rw [cmpLtS_frame k _ 121 115 116 122 117 118 133 j h133 hj,
    cmpLtS_frame k s 119 111 112 120 113 114 132 j h132 hj]

/-- **The pair-flag stage computes `p1 < p2` and `p3 < p4`.** -/
theorem cmulPairFlagsS_spec (k : Nat) (s : RegState)
    (h119 : s 119 ≤ 1) (h120 : s 120 ≤ 1)
    (h121 : s 121 ≤ 1) (h122 : s 122 ≤ 1) :
    srun k s cmulPairFlagsS 132 = tlt (s 119) (s 111) (s 112)
        (s 120) (s 113) (s 114) ∧
      srun k s cmulPairFlagsS 133 = tlt (s 121) (s 115) (s 116)
        (s 122) (s 117) (s 118) := by
  let c1 := srun k s (cmpLtS 119 111 112 120 113 114 132)
  let c2 := srun k c1 (cmpLtS 121 115 116 122 117 118 133)
  have h1 := cmpLtS_spec k s 119 111 112 120 113 114 132
    (by simp [CmpClear]) (by decide) h119 h120
  have c1_121 : c1 121 = s 121 := cmpLtS_frame k s
    119 111 112 120 113 114 132 121 (by decide) (by simp [CmpClear])
  have c1_115 : c1 115 = s 115 := cmpLtS_frame k s
    119 111 112 120 113 114 132 115 (by decide) (by simp [CmpClear])
  have c1_116 : c1 116 = s 116 := cmpLtS_frame k s
    119 111 112 120 113 114 132 116 (by decide) (by simp [CmpClear])
  have c1_122 : c1 122 = s 122 := cmpLtS_frame k s
    119 111 112 120 113 114 132 122 (by decide) (by simp [CmpClear])
  have c1_117 : c1 117 = s 117 := cmpLtS_frame k s
    119 111 112 120 113 114 132 117 (by decide) (by simp [CmpClear])
  have c1_118 : c1 118 = s 118 := cmpLtS_frame k s
    119 111 112 120 113 114 132 118 (by decide) (by simp [CmpClear])
  have h2 := cmpLtS_spec k c1 121 115 116 122 117 118 133
    (by simp [CmpClear]) (by decide)
    (by rw [c1_121]; exact h121) (by rw [c1_122]; exact h122)
  rw [c1_121, c1_115, c1_116, c1_122, c1_117, c1_118] at h2
  have c2_132 : c2 132 = c1 132 := cmpLtS_frame k c1
    121 115 116 122 117 118 133 132 (by decide) (by simp [CmpClear])
  constructor <;> simp only [cmulPairFlagsS, srun_append] <;> change c2 _ = _
  · rw [c2_132]
    exact h1
  · exact h2

/-- A canonical signed two-limb value, matching the triples used by `tcmul`. -/
structure CmulWide where
  sign : Nat
  lo : Nat
  hi : Nat

def readCmulWide (s : RegState) (sg lo hi : Nat) : CmulWide :=
  ⟨s sg, s lo, s hi⟩

def selectCmulWide (t : Nat) (a b : CmulWide) : CmulWide :=
  ⟨if t = 1 then a.sign else b.sign,
   if t = 1 then a.lo else b.lo,
   if t = 1 then a.hi else b.hi⟩

def cmulWideLt (a b : CmulWide) : Nat :=
  tlt a.sign a.lo a.hi b.sign b.lo b.hi

def cmulOrderModel (p1 p2 p3 p4 : CmulWide) : CmulWide × CmulWide :=
  let t12 := cmulWideLt p1 p2
  let t34 := cmulWideLt p3 p4
  let mn12 := selectCmulWide t12 p1 p2
  let mx12 := selectCmulWide t12 p2 p1
  let mn34 := selectCmulWide t34 p3 p4
  let mx34 := selectCmulWide t34 p4 p3
  let tn := cmulWideLt mn12 mn34
  let tx := cmulWideLt mx12 mx34
  (selectCmulWide tn mn12 mn34, selectCmulWide tx mx34 mx12)

theorem selectCmulWide_sign_le (t : Nat) (a b : CmulWide)
    (ha : a.sign ≤ 1) (hb : b.sign ≤ 1) : (selectCmulWide t a b).sign ≤ 1 := by
  simp only [selectCmulWide]
  split <;> assumption

theorem cmulOrderModel_sign_le (p1 p2 p3 p4 : CmulWide)
    (h1 : p1.sign ≤ 1) (h2 : p2.sign ≤ 1)
    (h3 : p3.sign ≤ 1) (h4 : p4.sign ≤ 1) :
    (cmulOrderModel p1 p2 p3 p4).1.sign ≤ 1 ∧
      (cmulOrderModel p1 p2 p3 p4).2.sign ≤ 1 := by
  simp only [cmulOrderModel]
  constructor
  · apply selectCmulWide_sign_le
    · exact selectCmulWide_sign_le _ _ _ h1 h2
    · exact selectCmulWide_sign_le _ _ _ h3 h4
  · apply selectCmulWide_sign_le
    · exact selectCmulWide_sign_le _ _ _ h4 h3
    · exact selectCmulWide_sign_le _ _ _ h2 h1

/-- A selected triple, packaged as a `CmulWide`. -/
theorem selTripleS_read_spec (k : Nat) (s : RegState)
    (t sa la ha sb lb hb sd ld hd : Nat)
    (hts : t ≠ sd) (htl : t ≠ ld) (ht4 : t ≠ 144)
    (hsa4 : sa ≠ 144) (hsb4 : sb ≠ 144)
    (hlas : la ≠ sd) (hla4 : la ≠ 144) (hlbs : lb ≠ sd) (hlb4 : lb ≠ 144)
    (hhas : ha ≠ sd) (hhal : ha ≠ ld) (hha4 : ha ≠ 144)
    (hhbs : hb ≠ sd) (hhbl : hb ≠ ld) (hhb4 : hb ≠ 144)
    (hsdl : sd ≠ ld) (hsdh : sd ≠ hd) (hsd4 : sd ≠ 144)
    (hldh : ld ≠ hd) (hld4 : ld ≠ 144) (hhd4 : hd ≠ 144)
    (ht1 : s t ≤ 1) (hs : ∀ j, s j < M) :
    readCmulWide (srun k s (selTripleS t sa la ha sb lb hb sd ld hd)) sd ld hd =
      selectCmulWide (s t) (readCmulWide s sa la ha) (readCmulWide s sb lb hb) := by
  have h := selTripleS_spec k s t sa la ha sb lb hb sd ld hd
    hts htl ht4 hsa4 hsb4 hlas hla4 hlbs hlb4 hhas hhal hha4
    hhbs hhbl hhb4 hsdl hsdh hsd4 hldh hld4 hhd4 ht1 hs
  rcases h with ⟨hsg, hlo, hhi⟩
  simp only [readCmulWide, selectCmulWide]
  rw [hsg, hlo, hhi]

/-- **The four pairwise selects produce both minima and maxima.** -/
theorem cmulPairSelectsS_spec (k : Nat) (s : RegState)
    (h132 : s 132 ≤ 1) (h133 : s 133 ≤ 1) (hs : ∀ j, s j < M) :
    let p1 := readCmulWide s 119 111 112
    let p2 := readCmulWide s 120 113 114
    let p3 := readCmulWide s 121 115 116
    let p4 := readCmulWide s 122 117 118
    let t12 := s 132
    let t34 := s 133
    let sf := srun k s cmulPairSelectsS
    readCmulWide sf 134 135 136 = selectCmulWide t12 p1 p2 ∧
    readCmulWide sf 137 138 153 = selectCmulWide t12 p2 p1 ∧
    readCmulWide sf 162 163 164 = selectCmulWide t34 p3 p4 ∧
    readCmulWide sf 165 166 167 = selectCmulWide t34 p4 p3 := by
  let s1 := srun k s (selTripleS 132 119 111 112 120 113 114 134 135 136)
  let s2 := srun k s1 (selTripleS 132 120 113 114 119 111 112 137 138 153)
  let s3 := srun k s2 (selTripleS 133 121 115 116 122 117 118 162 163 164)
  let s4 := srun k s3 (selTripleS 133 122 117 118 121 115 116 165 166 167)
  have h1 : readCmulWide s1 134 135 136 =
      selectCmulWide (s 132) (readCmulWide s 119 111 112)
        (readCmulWide s 120 113 114) := by
    apply selTripleS_read_spec <;> try decide
    · exact h132
    · exact hs
  have fr1 (j : Nat) (h1 : j ≠ 134) (h2 : j ≠ 135)
      (h3 : j ≠ 136) (h4 : j ≠ 144) : s1 j = s j :=
    selTripleS_frame k s 132 119 111 112 120 113 114 134 135 136 j h1 h2 h3 h4
  have hs1 : ∀ j, s1 j < M := srun_lt_of_lt k _ s hs
  have h2 : readCmulWide s2 137 138 153 =
      selectCmulWide (s 132) (readCmulWide s 120 113 114)
        (readCmulWide s 119 111 112) := by
    have h := selTripleS_read_spec k s1 132 120 113 114 119 111 112 137 138 153
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr1 132 (by decide) (by decide) (by decide) (by decide)]; exact h132) hs1
    simp only [readCmulWide, selectCmulWide] at h ⊢
    rw [fr1 132 (by decide) (by decide) (by decide) (by decide),
      fr1 120 (by decide) (by decide) (by decide) (by decide),
      fr1 113 (by decide) (by decide) (by decide) (by decide),
      fr1 114 (by decide) (by decide) (by decide) (by decide),
      fr1 119 (by decide) (by decide) (by decide) (by decide),
      fr1 111 (by decide) (by decide) (by decide) (by decide),
      fr1 112 (by decide) (by decide) (by decide) (by decide)] at h
    exact h
  have fr2 (j : Nat) (h1 : j ≠ 137) (h2 : j ≠ 138)
      (h3 : j ≠ 153) (h4 : j ≠ 144) : s2 j = s1 j :=
    selTripleS_frame k s1 132 120 113 114 119 111 112 137 138 153 j h1 h2 h3 h4
  have hs2 : ∀ j, s2 j < M := srun_lt_of_lt k _ s1 hs1
  have h3 : readCmulWide s3 162 163 164 =
      selectCmulWide (s 133) (readCmulWide s 121 115 116)
        (readCmulWide s 122 117 118) := by
    have h := selTripleS_read_spec k s2 133 121 115 116 122 117 118 162 163 164
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr2 133 (by decide) (by decide) (by decide) (by decide),
          fr1 133 (by decide) (by decide) (by decide) (by decide)]; exact h133) hs2
    simp only [readCmulWide, selectCmulWide] at h ⊢
    rw [fr2 133 (by decide) (by decide) (by decide) (by decide),
      fr2 121 (by decide) (by decide) (by decide) (by decide),
      fr2 115 (by decide) (by decide) (by decide) (by decide),
      fr2 116 (by decide) (by decide) (by decide) (by decide),
      fr2 122 (by decide) (by decide) (by decide) (by decide),
      fr2 117 (by decide) (by decide) (by decide) (by decide),
      fr2 118 (by decide) (by decide) (by decide) (by decide),
      fr1 133 (by decide) (by decide) (by decide) (by decide),
      fr1 121 (by decide) (by decide) (by decide) (by decide),
      fr1 115 (by decide) (by decide) (by decide) (by decide),
      fr1 116 (by decide) (by decide) (by decide) (by decide),
      fr1 122 (by decide) (by decide) (by decide) (by decide),
      fr1 117 (by decide) (by decide) (by decide) (by decide),
      fr1 118 (by decide) (by decide) (by decide) (by decide)] at h
    exact h
  have fr3 (j : Nat) (h1 : j ≠ 162) (h2 : j ≠ 163)
      (h3 : j ≠ 164) (h4 : j ≠ 144) : s3 j = s2 j :=
    selTripleS_frame k s2 133 121 115 116 122 117 118 162 163 164 j h1 h2 h3 h4
  have hs3 : ∀ j, s3 j < M := srun_lt_of_lt k _ s2 hs2
  have h4 : readCmulWide s4 165 166 167 =
      selectCmulWide (s 133) (readCmulWide s 122 117 118)
        (readCmulWide s 121 115 116) := by
    have h := selTripleS_read_spec k s3 133 122 117 118 121 115 116 165 166 167
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr3 133 (by decide) (by decide) (by decide) (by decide),
          fr2 133 (by decide) (by decide) (by decide) (by decide),
          fr1 133 (by decide) (by decide) (by decide) (by decide)]; exact h133) hs3
    simp only [readCmulWide, selectCmulWide] at h ⊢
    rw [fr3 133 (by decide) (by decide) (by decide) (by decide),
      fr3 122 (by decide) (by decide) (by decide) (by decide),
      fr3 117 (by decide) (by decide) (by decide) (by decide),
      fr3 118 (by decide) (by decide) (by decide) (by decide),
      fr3 121 (by decide) (by decide) (by decide) (by decide),
      fr3 115 (by decide) (by decide) (by decide) (by decide),
      fr3 116 (by decide) (by decide) (by decide) (by decide),
      fr2 133 (by decide) (by decide) (by decide) (by decide),
      fr2 122 (by decide) (by decide) (by decide) (by decide),
      fr2 117 (by decide) (by decide) (by decide) (by decide),
      fr2 118 (by decide) (by decide) (by decide) (by decide),
      fr2 121 (by decide) (by decide) (by decide) (by decide),
      fr2 115 (by decide) (by decide) (by decide) (by decide),
      fr2 116 (by decide) (by decide) (by decide) (by decide),
      fr1 133 (by decide) (by decide) (by decide) (by decide),
      fr1 122 (by decide) (by decide) (by decide) (by decide),
      fr1 117 (by decide) (by decide) (by decide) (by decide),
      fr1 118 (by decide) (by decide) (by decide) (by decide),
      fr1 121 (by decide) (by decide) (by decide) (by decide),
      fr1 115 (by decide) (by decide) (by decide) (by decide),
      fr1 116 (by decide) (by decide) (by decide) (by decide)] at h
    exact h
  have keep (j : Nat) (h1 : j ≠ 165) (h2 : j ≠ 166)
      (h3 : j ≠ 167) (h4 : j ≠ 144) : s4 j = s3 j :=
    selTripleS_frame k s3 133 122 117 118 121 115 116 165 166 167 j h1 h2 h3 h4
  simp only [cmulPairSelectsS, srun_append]
  change readCmulWide s4 134 135 136 = _ ∧
    readCmulWide s4 137 138 153 = _ ∧
    readCmulWide s4 162 163 164 = _ ∧ readCmulWide s4 165 166 167 = _
  refine ⟨?_, ?_, ?_, h4⟩
  · simp only [readCmulWide]
    rw [keep 134 (by decide) (by decide) (by decide) (by decide),
      keep 135 (by decide) (by decide) (by decide) (by decide),
      keep 136 (by decide) (by decide) (by decide) (by decide),
      fr3 134 (by decide) (by decide) (by decide) (by decide),
      fr3 135 (by decide) (by decide) (by decide) (by decide),
      fr3 136 (by decide) (by decide) (by decide) (by decide),
      fr2 134 (by decide) (by decide) (by decide) (by decide),
      fr2 135 (by decide) (by decide) (by decide) (by decide),
      fr2 136 (by decide) (by decide) (by decide) (by decide)]
    exact h1
  · simp only [readCmulWide]
    rw [keep 137 (by decide) (by decide) (by decide) (by decide),
      keep 138 (by decide) (by decide) (by decide) (by decide),
      keep 153 (by decide) (by decide) (by decide) (by decide),
      fr3 137 (by decide) (by decide) (by decide) (by decide),
      fr3 138 (by decide) (by decide) (by decide) (by decide),
      fr3 153 (by decide) (by decide) (by decide) (by decide)]
    exact h2
  · simp only [readCmulWide]
    rw [keep 162 (by decide) (by decide) (by decide) (by decide),
      keep 163 (by decide) (by decide) (by decide) (by decide),
      keep 164 (by decide) (by decide) (by decide) (by decide)]
    exact h3

/-- The final comparisons preserve every register outside their flags and
comparison scratch. -/
theorem cmulExtremaFlagsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h176 : j ≠ 176) (h177 : j ≠ 177) (hj : CmpClear j) :
    srun k s cmulExtremaFlagsS j = s j := by
  simp only [cmulExtremaFlagsS, srun_append]
  rw [cmpLtS_frame k _ 137 138 153 165 166 167 177 j h177 hj,
    cmpLtS_frame k s 134 135 136 162 163 164 176 j h176 hj]

/-- **The extrema-flag stage compares the two minima and two maxima.** -/
theorem cmulExtremaFlagsS_spec (k : Nat) (s : RegState)
    (h134 : s 134 ≤ 1) (h162 : s 162 ≤ 1)
    (h137 : s 137 ≤ 1) (h165 : s 165 ≤ 1) :
    srun k s cmulExtremaFlagsS 176 = tlt (s 134) (s 135) (s 136)
        (s 162) (s 163) (s 164) ∧
      srun k s cmulExtremaFlagsS 177 = tlt (s 137) (s 138) (s 153)
        (s 165) (s 166) (s 167) := by
  let c1 := srun k s (cmpLtS 134 135 136 162 163 164 176)
  let c2 := srun k c1 (cmpLtS 137 138 153 165 166 167 177)
  have h1 := cmpLtS_spec k s 134 135 136 162 163 164 176
    (by simp [CmpClear]) (by decide) h134 h162
  have c1_137 : c1 137 = s 137 := cmpLtS_frame k s
    134 135 136 162 163 164 176 137 (by decide) (by simp [CmpClear])
  have c1_138 : c1 138 = s 138 := cmpLtS_frame k s
    134 135 136 162 163 164 176 138 (by decide) (by simp [CmpClear])
  have c1_153 : c1 153 = s 153 := cmpLtS_frame k s
    134 135 136 162 163 164 176 153 (by decide) (by simp [CmpClear])
  have c1_165 : c1 165 = s 165 := cmpLtS_frame k s
    134 135 136 162 163 164 176 165 (by decide) (by simp [CmpClear])
  have c1_166 : c1 166 = s 166 := cmpLtS_frame k s
    134 135 136 162 163 164 176 166 (by decide) (by simp [CmpClear])
  have c1_167 : c1 167 = s 167 := cmpLtS_frame k s
    134 135 136 162 163 164 176 167 (by decide) (by simp [CmpClear])
  have h2 := cmpLtS_spec k c1 137 138 153 165 166 167 177
    (by simp [CmpClear]) (by decide)
    (by rw [c1_137]; exact h137) (by rw [c1_165]; exact h165)
  rw [c1_137, c1_138, c1_153, c1_165, c1_166, c1_167] at h2
  have c2_176 : c2 176 = c1 176 := cmpLtS_frame k c1
    137 138 153 165 166 167 177 176 (by decide) (by simp [CmpClear])
  constructor <;> simp only [cmulExtremaFlagsS, srun_append] <;> change c2 _ = _
  · rw [c2_176]
    exact h1
  · exact h2

/-- **The final selects produce the global minimum and maximum.** -/
theorem cmulExtremaSelectsS_spec (k : Nat) (s : RegState)
    (h176 : s 176 ≤ 1) (h177 : s 177 ≤ 1) (hs : ∀ j, s j < M) :
    let mn12 := readCmulWide s 134 135 136
    let mx12 := readCmulWide s 137 138 153
    let mn34 := readCmulWide s 162 163 164
    let mx34 := readCmulWide s 165 166 167
    let sf := srun k s cmulExtremaSelectsS
    readCmulWide sf 134 135 136 = selectCmulWide (s 176) mn12 mn34 ∧
      readCmulWide sf 137 138 153 = selectCmulWide (s 177) mx34 mx12 := by
  let s1 := srun k s (selTripleS 176 134 135 136 162 163 164 134 135 136)
  let s2 := srun k s1 (selTripleS 177 165 166 167 137 138 153 137 138 153)
  have h1 : readCmulWide s1 134 135 136 =
      selectCmulWide (s 176) (readCmulWide s 134 135 136)
        (readCmulWide s 162 163 164) := by
    apply selTripleS_read_spec <;> try decide
    · exact h176
    · exact hs
  have fr1 (j : Nat) (h1 : j ≠ 134) (h2 : j ≠ 135)
      (h3 : j ≠ 136) (h4 : j ≠ 144) : s1 j = s j :=
    selTripleS_frame k s 176 134 135 136 162 163 164 134 135 136 j h1 h2 h3 h4
  have hs1 : ∀ j, s1 j < M := srun_lt_of_lt k _ s hs
  have h2 : readCmulWide s2 137 138 153 =
      selectCmulWide (s 177) (readCmulWide s 165 166 167)
        (readCmulWide s 137 138 153) := by
    have h := selTripleS_read_spec k s1 177 165 166 167 137 138 153 137 138 153
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr1 177 (by decide) (by decide) (by decide) (by decide)]; exact h177) hs1
    simp only [readCmulWide, selectCmulWide] at h ⊢
    rw [fr1 177 (by decide) (by decide) (by decide) (by decide),
      fr1 165 (by decide) (by decide) (by decide) (by decide),
      fr1 166 (by decide) (by decide) (by decide) (by decide),
      fr1 167 (by decide) (by decide) (by decide) (by decide),
      fr1 137 (by decide) (by decide) (by decide) (by decide),
      fr1 138 (by decide) (by decide) (by decide) (by decide),
      fr1 153 (by decide) (by decide) (by decide) (by decide)] at h
    exact h
  have keep (j : Nat) (h1 : j ≠ 137) (h2 : j ≠ 138)
      (h3 : j ≠ 153) (h4 : j ≠ 144) : s2 j = s1 j :=
    selTripleS_frame k s1 177 165 166 167 137 138 153 137 138 153 j h1 h2 h3 h4
  simp only [cmulExtremaSelectsS, srun_append]
  change readCmulWide s2 134 135 136 = _ ∧ readCmulWide s2 137 138 153 = _
  constructor
  · simp only [readCmulWide]
    rw [keep 134 (by decide) (by decide) (by decide) (by decide),
      keep 135 (by decide) (by decide) (by decide) (by decide),
      keep 136 (by decide) (by decide) (by decide) (by decide)]
    exact h1
  · exact h2

/-- The pair-select stage writes only its twelve output registers and
register `144`. -/
theorem cmulPairSelectsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h134 : j ≠ 134) (h135 : j ≠ 135) (h136 : j ≠ 136)
    (h137 : j ≠ 137) (h138 : j ≠ 138) (h153 : j ≠ 153)
    (h162 : j ≠ 162) (h163 : j ≠ 163) (h164 : j ≠ 164)
    (h165 : j ≠ 165) (h166 : j ≠ 166) (h167 : j ≠ 167)
    (h144 : j ≠ 144) : srun k s cmulPairSelectsS j = s j := by
  simp only [cmulPairSelectsS, srun_append]
  rw [selTripleS_frame k _ 133 122 117 118 121 115 116 165 166 167 j
      h165 h166 h167 h144,
    selTripleS_frame k _ 133 121 115 116 122 117 118 162 163 164 j
      h162 h163 h164 h144,
    selTripleS_frame k _ 132 120 113 114 119 111 112 137 138 153 j
      h137 h138 h153 h144,
    selTripleS_frame k s 132 119 111 112 120 113 114 134 135 136 j
      h134 h135 h136 h144]

/-- The final-select stage writes only its two output triples and `144`. -/
theorem cmulExtremaSelectsS_frame (k : Nat) (s : RegState) (j : Nat)
    (h134 : j ≠ 134) (h135 : j ≠ 135) (h136 : j ≠ 136)
    (h137 : j ≠ 137) (h138 : j ≠ 138) (h153 : j ≠ 153)
    (h144 : j ≠ 144) : srun k s cmulExtremaSelectsS j = s j := by
  simp only [cmulExtremaSelectsS, srun_append]
  rw [selTripleS_frame k _ 177 165 166 167 137 138 153 137 138 153 j
      h137 h138 h153 h144,
    selTripleS_frame k s 176 134 135 136 162 163 164 134 135 136 j
      h134 h135 h136 h144]

/-- The ordering network preserves the global violation register. -/
theorem cmulOrderS_viol_frame (k : Nat) (s : RegState) :
    srun k s cmulOrderS rViol = s rViol := by
  simp only [cmulOrderS, srun_append]
  rw [cmulExtremaSelectsS_frame k _ rViol (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    cmulExtremaFlagsS_frame k _ rViol (by decide) (by decide)
      (by simp [CmpClear, rViol]),
    cmulPairSelectsS_frame k _ rViol (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    cmulPairFlagsS_frame k s rViol (by decide) (by decide)
      (by simp [CmpClear, rViol])]

/-- **The full branchless ordering network selects the signed global minimum
and maximum of its four canonical products.** -/
theorem cmulOrderS_spec (k : Nat) (s : RegState)
    (h119 : s 119 ≤ 1) (h120 : s 120 ≤ 1)
    (h121 : s 121 ≤ 1) (h122 : s 122 ≤ 1)
    (hs : ∀ j, s j < M) :
    let p1 := readCmulWide s 119 111 112
    let p2 := readCmulWide s 120 113 114
    let p3 := readCmulWide s 121 115 116
    let p4 := readCmulWide s 122 117 118
    let sf := srun k s cmulOrderS
    readCmulWide sf 134 135 136 = (cmulOrderModel p1 p2 p3 p4).1 ∧
      readCmulWide sf 137 138 153 = (cmulOrderModel p1 p2 p3 p4).2 := by
  let a := srun k s cmulPairFlagsS
  let b := srun k a cmulPairSelectsS
  let c := srun k b cmulExtremaFlagsS
  let d := srun k c cmulExtremaSelectsS
  have ha (j : Nat) (h132 : j ≠ 132) (h133 : j ≠ 133)
      (hj : CmpClear j) : a j = s j :=
    cmulPairFlagsS_frame k s j h132 h133 hj
  have hflags := cmulPairFlagsS_spec k s h119 h120 h121 h122
  have ha132 : a 132 = cmulWideLt (readCmulWide s 119 111 112)
      (readCmulWide s 120 113 114) := by
    simpa only [cmulWideLt, readCmulWide] using hflags.1
  have ha133 : a 133 = cmulWideLt (readCmulWide s 121 115 116)
      (readCmulWide s 122 117 118) := by
    simpa only [cmulWideLt, readCmulWide] using hflags.2
  have ha132bit : a 132 ≤ 1 := by
    rw [ha132]
    exact tlt_le_one _ _ _ _ _ _ h119 h120
  have ha133bit : a 133 ≤ 1 := by
    rw [ha133]
    exact tlt_le_one _ _ _ _ _ _ h121 h122
  have hsa : ∀ j, a j < M := srun_lt_of_lt k _ s hs
  have hpairs := cmulPairSelectsS_spec k a ha132bit ha133bit hsa
  simp only [readCmulWide] at hpairs
  rw [ha132, ha133,
    ha 119 (by decide) (by decide) (by simp [CmpClear]),
    ha 111 (by decide) (by decide) (by simp [CmpClear]),
    ha 112 (by decide) (by decide) (by simp [CmpClear]),
    ha 120 (by decide) (by decide) (by simp [CmpClear]),
    ha 113 (by decide) (by decide) (by simp [CmpClear]),
    ha 114 (by decide) (by decide) (by simp [CmpClear]),
    ha 121 (by decide) (by decide) (by simp [CmpClear]),
    ha 115 (by decide) (by decide) (by simp [CmpClear]),
    ha 116 (by decide) (by decide) (by simp [CmpClear]),
    ha 122 (by decide) (by decide) (by simp [CmpClear]),
    ha 117 (by decide) (by decide) (by simp [CmpClear]),
    ha 118 (by decide) (by decide) (by simp [CmpClear])] at hpairs
  let p1 := readCmulWide s 119 111 112
  let p2 := readCmulWide s 120 113 114
  let p3 := readCmulWide s 121 115 116
  let p4 := readCmulWide s 122 117 118
  let t12 := cmulWideLt p1 p2
  let t34 := cmulWideLt p3 p4
  let mn12 := selectCmulWide t12 p1 p2
  let mx12 := selectCmulWide t12 p2 p1
  let mn34 := selectCmulWide t34 p3 p4
  let mx34 := selectCmulWide t34 p4 p3
  have hb_mn12 : readCmulWide b 134 135 136 = mn12 := hpairs.1
  have hb_mx12 : readCmulWide b 137 138 153 = mx12 := hpairs.2.1
  have hb_mn34 : readCmulWide b 162 163 164 = mn34 := hpairs.2.2.1
  have hb_mx34 : readCmulWide b 165 166 167 = mx34 := hpairs.2.2.2
  have hb134 : b 134 ≤ 1 := by
    have h := congrArg CmulWide.sign hb_mn12
    change b 134 = mn12.sign at h
    rw [h]
    exact selectCmulWide_sign_le t12 p1 p2 h119 h120
  have hb137 : b 137 ≤ 1 := by
    have h := congrArg CmulWide.sign hb_mx12
    change b 137 = mx12.sign at h
    rw [h]
    exact selectCmulWide_sign_le t12 p2 p1 h120 h119
  have hb162 : b 162 ≤ 1 := by
    have h := congrArg CmulWide.sign hb_mn34
    change b 162 = mn34.sign at h
    rw [h]
    exact selectCmulWide_sign_le t34 p3 p4 h121 h122
  have hb165 : b 165 ≤ 1 := by
    have h := congrArg CmulWide.sign hb_mx34
    change b 165 = mx34.sign at h
    rw [h]
    exact selectCmulWide_sign_le t34 p4 p3 h122 h121
  have hext := cmulExtremaFlagsS_spec k b hb134 hb162 hb137 hb165
  have hc176 : c 176 = cmulWideLt mn12 mn34 := by
    change srun k b cmulExtremaFlagsS 176 = _
    rw [hext.1]
    rw [← hb_mn12, ← hb_mn34]
    rfl
  have hc177 : c 177 = cmulWideLt mx12 mx34 := by
    change srun k b cmulExtremaFlagsS 177 = _
    rw [hext.2]
    rw [← hb_mx12, ← hb_mx34]
    rfl
  have hc176bit : c 176 ≤ 1 := by
    rw [hc176]
    exact tlt_le_one _ _ _ _ _ _
      (selectCmulWide_sign_le t12 p1 p2 h119 h120)
      (selectCmulWide_sign_le t34 p3 p4 h121 h122)
  have hc177bit : c 177 ≤ 1 := by
    rw [hc177]
    exact tlt_le_one _ _ _ _ _ _
      (selectCmulWide_sign_le t12 p2 p1 h120 h119)
      (selectCmulWide_sign_le t34 p4 p3 h122 h121)
  have hsb : ∀ j, b j < M := srun_lt_of_lt k _ a hsa
  have hsc : ∀ j, c j < M := srun_lt_of_lt k _ b hsb
  have hfinal := cmulExtremaSelectsS_spec k c hc176bit hc177bit hsc
  have hc (j : Nat) (h176 : j ≠ 176) (h177 : j ≠ 177)
      (hj : CmpClear j) : c j = b j :=
    cmulExtremaFlagsS_frame k b j h176 h177 hj
  have hc_mn12 : readCmulWide c 134 135 136 = readCmulWide b 134 135 136 := by
    simp only [readCmulWide]
    rw [hc 134 (by decide) (by decide) (by simp [CmpClear]),
      hc 135 (by decide) (by decide) (by simp [CmpClear]),
      hc 136 (by decide) (by decide) (by simp [CmpClear])]
  have hc_mx12 : readCmulWide c 137 138 153 = readCmulWide b 137 138 153 := by
    simp only [readCmulWide]
    rw [hc 137 (by decide) (by decide) (by simp [CmpClear]),
      hc 138 (by decide) (by decide) (by simp [CmpClear]),
      hc 153 (by decide) (by decide) (by simp [CmpClear])]
  have hc_mn34 : readCmulWide c 162 163 164 = readCmulWide b 162 163 164 := by
    simp only [readCmulWide]
    rw [hc 162 (by decide) (by decide) (by simp [CmpClear]),
      hc 163 (by decide) (by decide) (by simp [CmpClear]),
      hc 164 (by decide) (by decide) (by simp [CmpClear])]
  have hc_mx34 : readCmulWide c 165 166 167 = readCmulWide b 165 166 167 := by
    simp only [readCmulWide]
    rw [hc 165 (by decide) (by decide) (by simp [CmpClear]),
      hc 166 (by decide) (by decide) (by simp [CmpClear]),
      hc 167 (by decide) (by decide) (by simp [CmpClear])]
  rw [hc176, hc177, hc_mn12, hc_mx12, hc_mn34, hc_mx34,
    hb_mn12, hb_mx12, hb_mn34, hb_mx34] at hfinal
  simp only [cmulOrderS, srun_append]
  change readCmulWide d 134 135 136 = _ ∧ readCmulWide d 137 138 153 = _
  simpa only [cmulOrderModel, p1, p2, p3, p4, t12, t34, mn12, mx12,
    mn34, mx34] using hfinal

/-- **The finish stage divides the selected endpoint magnitudes by `10^18`
and restores their canonical signs.** -/
theorem cmulFinishS_spec (k : Nat) (s : RegState) (cLo cHi : Nat)
    (hcLo : CmulExternal cLo) (hcHi : CmulExternal cHi) (hLH : cLo ≠ cHi)
    (h134 : s 134 ≤ 1) (h137 : s 137 ≤ 1) (hs : ∀ j, s j < M) :
    let sf := srun k s (cmulFinishS cLo cHi)
    sf cLo =
        (if s 134 = 1 then tsub 0 (tdiv18 (s 135) (s 136)).2
         else (tdiv18 (s 135) (s 136)).1) ∧
      sf cHi =
        (if s 137 = 1 then tsub 0 (tdiv18 (s 138) (s 153)).1
         else (tdiv18 (s 138) (s 153)).2) ∧
      sf rViol = s rViol := by
  let a := srun k s (divP18S 135 136 178 179)
  let b := srun k a (cmulEncodeS 134 179 178 cLo)
  let c := srun k b (divP18S 138 153 178 179)
  let d := srun k c (cmulEncodeS 137 178 179 cHi)
  have extNe {r x : Nat} (hr : CmulExternal r) (hx0 : 100 ≤ x)
      (hx1 : x ≤ 179) : r ≠ x := cmulExternal_ne_scratch hr hx0 hx1
  have ha := divP18S_spec k s 135 136 hs (by decide) (by decide)
  have fra (j : Nat) (hj : CmulExternal j) : a j = s j := by
    apply divP18S_frame <;> exact extNe hj (by decide) (by decide)
  have ha134 : a 134 = s 134 := divP18S_frame k s 135 136 178 179 134
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hbLo := cmulEncodeS_spec k a 134 179 178 cLo
    (by
      intro r hr
      simp only [EncodeClear]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨extNe hcLo (by decide) (by decide),
          extNe hcLo (by decide) (by decide)⟩)
    (by exact extNe hcLo (by decide) (by decide))
    (by rw [ha134]; exact h134) (srun_lt_of_lt k _ s hs)
  have ha178 : a 178 = (tdiv18 (s 135) (s 136)).1 := ha.1
  have ha179 : a 179 = (tdiv18 (s 135) (s 136)).2 := ha.2
  rw [ha134, ha178, ha179] at hbLo
  have frb (j : Nat) (hj : j ≠ cLo) (h8 : j ≠ 108) (h9 : j ≠ 109) :
      b j = a j := cmulEncodeS_frame k a 134 179 178 cLo j hj h8 h9
  have b138 : b 138 = s 138 := by
    rw [frb 138 (Ne.symm (extNe hcLo (by decide) (by decide)))
      (by decide) (by decide)]
    exact divP18S_frame k s 135 136 178 179 138
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have b153 : b 153 = s 153 := by
    rw [frb 153 (Ne.symm (extNe hcLo (by decide) (by decide)))
      (by decide) (by decide)]
    exact divP18S_frame k s 135 136 178 179 153
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have b137 : b 137 = s 137 := by
    rw [frb 137 (Ne.symm (extNe hcLo (by decide) (by decide)))
      (by decide) (by decide)]
    exact divP18S_frame k s 135 136 178 179 137
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hbHi := divP18S_spec k b 138 153 (srun_lt_of_lt k _ a
    (srun_lt_of_lt k _ s hs)) (by decide) (by decide)
  rw [b138, b153] at hbHi
  have frc (j : Nat) (hj : CmulExternal j) : c j = b j := by
    apply divP18S_frame <;> exact extNe hj (by decide) (by decide)
  have c137 : c 137 = s 137 := by
    change srun k b (divP18S 138 153 178 179) 137 = s 137
    rw [divP18S_frame k b 138 153 178 179 137
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), b137]
  have hdHi := cmulEncodeS_spec k c 137 178 179 cHi
    (by
      intro r hr
      simp only [EncodeClear]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨extNe hcHi (by decide) (by decide),
          extNe hcHi (by decide) (by decide)⟩)
    (by exact extNe hcHi (by decide) (by decide))
    (by rw [c137]; exact h137) (srun_lt_of_lt k _ b
      (srun_lt_of_lt k _ a (srun_lt_of_lt k _ s hs)))
  have hc178 : c 178 = (tdiv18 (s 138) (s 153)).1 := hbHi.1
  have hc179 : c 179 = (tdiv18 (s 138) (s 153)).2 := hbHi.2
  rw [c137, hc178, hc179] at hdHi
  have dLo : d cLo = b cLo := by
    change srun k c (cmulEncodeS 137 178 179 cHi) cLo = b cLo
    rw [cmulEncodeS_frame k c 137 178 179 cHi cLo hLH
      (extNe hcLo (by decide) (by decide))
      (extNe hcLo (by decide) (by decide)), frc cLo hcLo]
  have dViol : d rViol = s rViol := by
    have hd : d rViol = c rViol := cmulEncodeS_frame k c 137 178 179 cHi
      rViol (Ne.symm hcHi.1) (by decide) (by decide)
    have hc : c rViol = b rViol := divP18S_frame k b 138 153 178 179 rViol
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    have hb : b rViol = a rViol := cmulEncodeS_frame k a 134 179 178 cLo
      rViol (Ne.symm hcLo.1) (by decide) (by decide)
    have ha' : a rViol = s rViol := divP18S_frame k s 135 136 178 179 rViol
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact hd.trans (hc.trans (hb.trans ha'))
  simp only [cmulFinishS, srun_append]
  change d cLo = _ ∧ d cHi = _ ∧ d rViol = _
  exact ⟨dLo.trans hbLo, hdHi, dViol⟩

/-- Convert the proof-oriented record to `torder`'s tuple presentation. -/
def CmulWide.toTriple (q : CmulWide) : Nat × Nat × Nat := (q.sign, q.lo, q.hi)

def cmulWideProduct (sa sb : Nat) (p : Nat × Nat) : CmulWide :=
  ⟨(sa ^^^ sb) * (1 - bnat (p.1 = 0) * bnat (p.2 = 0)), p.1, p.2⟩

theorem cmulWideProduct_toTriple (sa sb : Nat) (p : Nat × Nat) :
    (cmulWideProduct sa sb p).toTriple = tproduct sa sb p := by
  rfl

theorem CmulWide.toTriple_select (t : Nat) (a b : CmulWide) :
    (selectCmulWide t a b).toTriple =
      if t = 1 then a.toTriple else b.toTriple := by
  by_cases h : t = 1 <;> simp [CmulWide.toTriple, selectCmulWide, h]

theorem cmulWideLt_toTriple (a b : CmulWide) :
    cmulWideLt a b =
      tlt a.toTriple.1 a.toTriple.2.1 a.toTriple.2.2
        b.toTriple.1 b.toTriple.2.1 b.toTriple.2.2 := by
  rfl

/-- The record-valued ordering network is the tuple-valued `torder` network
under the fieldwise conversion. -/
theorem cmulOrderModel_toTriple (q1 q2 q3 q4 : CmulWide) :
    let m := cmulOrderModel q1 q2 q3 q4
    let t := torder q1.toTriple q2.toTriple q3.toTriple q4.toTriple
    m.1.toTriple = t.1 ∧ m.2.toTriple = t.2 := by
  simp only [cmulOrderModel, torder, cmulWideLt_toTriple,
    CmulWide.toTriple_select]
  exact ⟨trivial, trivial⟩

/-- Lower endpoint selected and rounded from four canonical products. -/
def cmulOrderedLo (q1 q2 q3 q4 : CmulWide) : Nat :=
  troundLo (cmulOrderModel q1 q2 q3 q4).1.toTriple

/-- Upper endpoint selected and rounded from four canonical products. -/
def cmulOrderedHi (q1 q2 q3 q4 : CmulWide) : Nat :=
  troundHi (cmulOrderModel q1 q2 q3 q4).2.toTriple

/-- The record-valued and tuple-valued ordering networks have the same
rounded lower endpoint.  This generic bridge keeps large product terms
abstract during normalization. -/
theorem cmulOrderedLo_torder (q1 q2 q3 q4 : CmulWide) :
    cmulOrderedLo q1 q2 q3 q4 =
      torderedLo q1.toTriple q2.toTriple q3.toTriple q4.toTriple := by
  exact congrArg troundLo (cmulOrderModel_toTriple q1 q2 q3 q4).1

/-- The corresponding generic upper-endpoint bridge. -/
theorem cmulOrderedHi_torder (q1 q2 q3 q4 : CmulWide) :
    cmulOrderedHi q1 q2 q3 q4 =
      torderedHi q1.toTriple q2.toTriple q3.toTriple q4.toTriple := by
  exact congrArg troundHi (cmulOrderModel_toTriple q1 q2 q3 q4).2

/-- The `CmulWide` presentation of the transparent interval multiplier.
Keeping this representation separate makes the machine composition small;
`cmulModel_eq_tcmul` below discharges the representation change once. -/
@[irreducible] def cmulModel (gate aLo aHi bLo bHi viol : Nat) : Nat × Nat × Nat :=
  let (saL, maL) := tmag aLo
  let (saH, maH) := tmag aHi
  let (sbL, mbL) := tmag bLo
  let (sbH, mbH) := tmag bHi
  let p1 := Verified.MulWide.hl maL mbL
  let p2 := Verified.MulWide.hl maL mbH
  let p3 := Verified.MulWide.hl maH mbL
  let p4 := Verified.MulWide.hl maH mbH
  let q1 := cmulWideProduct saL sbL p1
  let q2 := cmulWideProduct saL sbH p2
  let q3 := cmulWideProduct saH sbL p3
  let q4 := cmulWideProduct saH sbH p4
  let cLo := cmulOrderedLo q1 q2 q3 q4
  let cHi := cmulOrderedHi q1 q2 q3 q4
  let viol := viol ||| (bnat (CAP < maL) * gate)
  let viol := viol ||| (bnat (CAP < maH) * gate)
  let viol := viol ||| (bnat (CAP < mbL) * gate)
  let viol := viol ||| (bnat (CAP < mbH) * gate)
  (cLo, cHi, viol)

theorem cmulModel_lo (gate aLo aHi bLo bHi viol : Nat) :
    (cmulModel gate aLo aHi bLo bHi viol).1 =
      cmulOrderedLo
        (cmulWideProduct (tmag aLo).1 (tmag bLo).1
          (Verified.MulWide.hl (tmag aLo).2 (tmag bLo).2))
        (cmulWideProduct (tmag aLo).1 (tmag bHi).1
          (Verified.MulWide.hl (tmag aLo).2 (tmag bHi).2))
        (cmulWideProduct (tmag aHi).1 (tmag bLo).1
          (Verified.MulWide.hl (tmag aHi).2 (tmag bLo).2))
        (cmulWideProduct (tmag aHi).1 (tmag bHi).1
          (Verified.MulWide.hl (tmag aHi).2 (tmag bHi).2)) := by
  cases hAL : tmag aLo with
  | mk saL maL =>
    cases hAH : tmag aHi with
    | mk saH maH =>
      cases hBL : tmag bLo with
      | mk sbL mbL =>
        cases hBH : tmag bHi with
        | mk sbH mbH => simp only [cmulModel, hAL, hAH, hBL, hBH]

theorem cmulModel_hi (gate aLo aHi bLo bHi viol : Nat) :
    (cmulModel gate aLo aHi bLo bHi viol).2.1 =
      cmulOrderedHi
        (cmulWideProduct (tmag aLo).1 (tmag bLo).1
          (Verified.MulWide.hl (tmag aLo).2 (tmag bLo).2))
        (cmulWideProduct (tmag aLo).1 (tmag bHi).1
          (Verified.MulWide.hl (tmag aLo).2 (tmag bHi).2))
        (cmulWideProduct (tmag aHi).1 (tmag bLo).1
          (Verified.MulWide.hl (tmag aHi).2 (tmag bLo).2))
        (cmulWideProduct (tmag aHi).1 (tmag bHi).1
          (Verified.MulWide.hl (tmag aHi).2 (tmag bHi).2)) := by
  cases hAL : tmag aLo with
  | mk saL maL =>
    cases hAH : tmag aHi with
    | mk saH maH =>
      cases hBL : tmag bLo with
      | mk sbL mbL =>
        cases hBH : tmag bHi with
        | mk sbH mbH => simp only [cmulModel, hAL, hAH, hBL, hBH]

theorem cmulModel_viol (gate aLo aHi bLo bHi viol : Nat) :
    (cmulModel gate aLo aHi bLo bHi viol).2.2 =
      (((viol ||| (bnat (CAP < (tmag aLo).2) * gate)) |||
          (bnat (CAP < (tmag aHi).2) * gate)) |||
        (bnat (CAP < (tmag bLo).2) * gate)) |||
      (bnat (CAP < (tmag bHi).2) * gate) := by
  cases hAL : tmag aLo with
  | mk saL maL =>
    cases hAH : tmag aHi with
    | mk saH maH =>
      cases hBL : tmag bLo with
      | mk sbL mbL =>
        cases hBH : tmag bHi with
        | mk sbH mbH => simp only [cmulModel, hAL, hAH, hBL, hBH]

/-- The structure-valued presentation is definitionally the existing
tuple-valued `tcmul` model. -/
theorem cmulModel_eq_tcmul (gate aLo aHi bLo bHi viol : Nat) :
    cmulModel gate aLo aHi bLo bHi viol =
      tcmul gate aLo aHi bLo bHi viol := by
  simp only [cmulModel, tcmul]
  rw [cmulOrderedLo_torder, cmulOrderedHi_torder]
  rw [cmulWideProduct_toTriple, cmulWideProduct_toTriple,
    cmulWideProduct_toTriple, cmulWideProduct_toTriple]

/-- The decomposition/product/sign prefix produces the four canonical wide
products, their bit-valued signs, and the guarded violation accumulator. -/
theorem cmulPreparedS_spec (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi : Nat)
    (hc : ∀ r ∈ [gate, aLo, aHi, bLo, bHi], CmulExternal r)
    (hs : ∀ j, s j < M) :
    let d := srun k s (cmulDecompS gate aLo aHi bLo bHi)
    let p := srun k d cmulProductsS
    let g := srun k p cmulSignsS
    let q1 := readCmulWide g 119 111 112
    let q2 := readCmulWide g 120 113 114
    let q3 := readCmulWide g 121 115 116
    let q4 := readCmulWide g 122 117 118
    q1 = cmulWideProduct (tmag (s aLo)).1 (tmag (s bLo)).1
        (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bLo)).2) ∧
    q2 = cmulWideProduct (tmag (s aLo)).1 (tmag (s bHi)).1
        (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bHi)).2) ∧
    q3 = cmulWideProduct (tmag (s aHi)).1 (tmag (s bLo)).1
        (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bLo)).2) ∧
    q4 = cmulWideProduct (tmag (s aHi)).1 (tmag (s bHi)).1
        (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bHi)).2) ∧
    g 119 ≤ 1 ∧ g 120 ≤ 1 ∧ g 121 ≤ 1 ∧ g 122 ≤ 1 ∧
    g rViol =
      (((s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate)) |||
          (bnat (CAP < (tmag (s aHi)).2) * s gate)) |||
        (bnat (CAP < (tmag (s bLo)).2) * s gate)) |||
      (bnat (CAP < (tmag (s bHi)).2) * s gate) := by
  let d := srun k s (cmulDecompS gate aLo aHi bLo bHi)
  let p := srun k d cmulProductsS
  let g := srun k p cmulSignsS
  have hd := cmulDecompS_spec k s gate aLo aHi bLo bHi hc hs
  rcases hd with ⟨hd100, hd104, hd101, hd105, hd102, hd106, hd103, hd107, hdv⟩
  change d 100 = _ at hd100
  change d 104 = _ at hd104
  change d 101 = _ at hd101
  change d 105 = _ at hd105
  change d 102 = _ at hd102
  change d 106 = _ at hd106
  change d 103 = _ at hd103
  change d 107 = _ at hd107
  change d rViol = _ at hdv
  have pf (j : Nat) (hj : j < 111) : p j = d j := by
    apply cmulProductsS_frame <;> simp [NotIn8] <;> omega
  have hp := cmulProductsS_spec k d (srun_lt_of_lt k _ s hs)
  rcases hp with ⟨hp111, hp112, hp113, hp114, hp115, hp116, hp117, hp118⟩
  change p 111 = _ at hp111
  change p 112 = _ at hp112
  change p 113 = _ at hp113
  change p 114 = _ at hp114
  change p 115 = _ at hp115
  change p 116 = _ at hp116
  change p 117 = _ at hp117
  change p 118 = _ at hp118
  have p100bit : p 100 ≤ 1 := by
    rw [pf 100 (by decide), hd100]; exact bnat_le_one _
  have p101bit : p 101 ≤ 1 := by
    rw [pf 101 (by decide), hd101]; exact bnat_le_one _
  have p102bit : p 102 ≤ 1 := by
    rw [pf 102 (by decide), hd102]; exact bnat_le_one _
  have p103bit : p 103 ≤ 1 := by
    rw [pf 103 (by decide), hd103]; exact bnat_le_one _
  have hg := cmulSignsS_spec k p p100bit p101bit p102bit p103bit
  rcases hg with ⟨hg119, hg120, hg121, hg122⟩
  change g 119 = _ at hg119
  change g 120 = _ at hg120
  change g 121 = _ at hg121
  change g 122 = _ at hg122
  have gf (j : Nat) (hj : j < 119) : g j = p j := by
    apply cmulSignsS_frame <;> omega
  have g119bit : g 119 ≤ 1 := by
    rw [hg119]; exact canonSignValue_le_one _ _ _ _ p100bit p102bit
  have g120bit : g 120 ≤ 1 := by
    rw [hg120]; exact canonSignValue_le_one _ _ _ _ p100bit p103bit
  have g121bit : g 121 ≤ 1 := by
    rw [hg121]; exact canonSignValue_le_one _ _ _ _ p101bit p102bit
  have g122bit : g 122 ≤ 1 := by
    rw [hg122]; exact canonSignValue_le_one _ _ _ _ p101bit p103bit
  let q1 := readCmulWide g 119 111 112
  let q2 := readCmulWide g 120 113 114
  let q3 := readCmulWide g 121 115 116
  let q4 := readCmulWide g 122 117 118
  have q1eq : q1 = cmulWideProduct (tmag (s aLo)).1 (tmag (s bLo)).1
      (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bLo)).2) := by
    simp only [q1, readCmulWide, cmulWideProduct]
    rw [hg119, pf 100 (by decide), pf 102 (by decide), hd100, hd102,
      gf 111 (by decide), gf 112 (by decide), hp111, hp112, hd104, hd106]
  have q2eq : q2 = cmulWideProduct (tmag (s aLo)).1 (tmag (s bHi)).1
      (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bHi)).2) := by
    simp only [q2, readCmulWide, cmulWideProduct]
    rw [hg120, pf 100 (by decide), pf 103 (by decide), hd100, hd103,
      gf 113 (by decide), gf 114 (by decide), hp113, hp114, hd104, hd107]
  have q3eq : q3 = cmulWideProduct (tmag (s aHi)).1 (tmag (s bLo)).1
      (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bLo)).2) := by
    simp only [q3, readCmulWide, cmulWideProduct]
    rw [hg121, pf 101 (by decide), pf 102 (by decide), hd101, hd102,
      gf 115 (by decide), gf 116 (by decide), hp115, hp116, hd105, hd106]
  have q4eq : q4 = cmulWideProduct (tmag (s aHi)).1 (tmag (s bHi)).1
      (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bHi)).2) := by
    simp only [q4, readCmulWide, cmulWideProduct]
    rw [hg122, pf 101 (by decide), pf 103 (by decide), hd101, hd103,
      gf 117 (by decide), gf 118 (by decide), hp117, hp118, hd105, hd107]
  have pv : p rViol = d rViol := pf rViol (by simp [rViol])
  have gv : g rViol = p rViol := gf rViol (by simp [rViol])
  exact ⟨q1eq, q2eq, q3eq, q4eq, g119bit, g120bit, g121bit, g122bit,
    gv.trans (pv.trans hdv)⟩

/-- Running `cmulS` is running its five named stages in sequence. -/
theorem cmulS_run_eq (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi : Nat) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) =
      srun k
        (srun k
          (srun k
            (srun k (srun k s (cmulDecompS gate aLo aHi bLo bHi))
              cmulProductsS)
            cmulSignsS)
          cmulOrderS)
        (cmulFinishS cLo cHi) := by
  simp only [cmulS, srun_append]

set_option maxHeartbeats 1000000 in
/-- Ordering followed by endpoint rounding, independent of the product prefix. -/
theorem cmulOrderedFinishS_spec (k : Nat) (g : RegState) (cLo cHi : Nat)
    (hcLo : CmulExternal cLo) (hcHi : CmulExternal cHi) (hLH : cLo ≠ cHi)
    (h119 : g 119 ≤ 1) (h120 : g 120 ≤ 1)
    (h121 : g 121 ≤ 1) (h122 : g 122 ≤ 1)
    (hglt : ∀ j, g j < M) :
    let o := srun k g cmulOrderS
    let f := srun k o (cmulFinishS cLo cHi)
    let q1 := readCmulWide g 119 111 112
    let q2 := readCmulWide g 120 113 114
    let q3 := readCmulWide g 121 115 116
    let q4 := readCmulWide g 122 117 118
    f cLo = cmulOrderedLo q1 q2 q3 q4 ∧
      f cHi = cmulOrderedHi q1 q2 q3 q4 ∧
      f rViol = g rViol := by
  let o := srun k g cmulOrderS
  let f := srun k o (cmulFinishS cLo cHi)
  let q1 := readCmulWide g 119 111 112
  let q2 := readCmulWide g 120 113 114
  let q3 := readCmulWide g 121 115 116
  let q4 := readCmulWide g 122 117 118
  have hoSpec := cmulOrderS_spec k g h119 h120 h121 h122 hglt
  have hoMin : readCmulWide o 134 135 136 = (cmulOrderModel q1 q2 q3 q4).1 := hoSpec.1
  have hoMax : readCmulWide o 137 138 153 = (cmulOrderModel q1 q2 q3 q4).2 := hoSpec.2
  have hbits := cmulOrderModel_sign_le q1 q2 q3 q4 h119 h120 h121 h122
  have o134bit : o 134 ≤ 1 := by
    have h := congrArg CmulWide.sign hoMin
    change o 134 = (cmulOrderModel q1 q2 q3 q4).1.sign at h
    rw [h]; exact hbits.1
  have o137bit : o 137 ≤ 1 := by
    have h := congrArg CmulWide.sign hoMax
    change o 137 = (cmulOrderModel q1 q2 q3 q4).2.sign at h
    rw [h]; exact hbits.2
  have hf := cmulFinishS_spec k o cLo cHi hcLo hcHi hLH o134bit o137bit
    (srun_lt_of_lt k _ g hglt)
  have ominS := congrArg CmulWide.sign hoMin
  have ominL := congrArg CmulWide.lo hoMin
  have ominH := congrArg CmulWide.hi hoMin
  have omaxS := congrArg CmulWide.sign hoMax
  have omaxL := congrArg CmulWide.lo hoMax
  have omaxH := congrArg CmulWide.hi hoMax
  change o 134 = (cmulOrderModel q1 q2 q3 q4).1.sign at ominS
  change o 135 = (cmulOrderModel q1 q2 q3 q4).1.lo at ominL
  change o 136 = (cmulOrderModel q1 q2 q3 q4).1.hi at ominH
  change o 137 = (cmulOrderModel q1 q2 q3 q4).2.sign at omaxS
  change o 138 = (cmulOrderModel q1 q2 q3 q4).2.lo at omaxL
  change o 153 = (cmulOrderModel q1 q2 q3 q4).2.hi at omaxH
  rw [ominS, ominL, ominH, omaxS, omaxL, omaxH] at hf
  have hfLo := hf.1
  have hfHi := hf.2.1
  change f cLo = cmulOrderedLo q1 q2 q3 q4 at hfLo
  change f cHi = cmulOrderedHi q1 q2 q3 q4 at hfHi
  exact ⟨hfLo, hfHi, hf.2.2.trans (cmulOrderS_viol_frame k g)⟩

/-- Composition of the prepared products with ordering and endpoint rounding,
stated against the structure-valued model so that kernel checking does not
duplicate the transparent tuple computation. -/
theorem cmulS_model_spec (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi : Nat)
    (hc : ∀ r ∈ [gate, aLo, aHi, bLo, bHi, cLo, cHi], CmulExternal r)
    (hLH : cLo ≠ cHi) (hs : ∀ j, s j < M) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cLo =
        (cmulModel (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cHi =
        (cmulModel (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) rViol =
        (cmulModel (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.2 := by
  let d := srun k s (cmulDecompS gate aLo aHi bLo bHi)
  let p := srun k d cmulProductsS
  let g := srun k p cmulSignsS
  let o := srun k g cmulOrderS
  let f := srun k o (cmulFinishS cLo cHi)
  let q1 := readCmulWide g 119 111 112
  let q2 := readCmulWide g 120 113 114
  let q3 := readCmulWide g 121 115 116
  let q4 := readCmulWide g 122 117 118
  have hp := cmulPreparedS_spec k s gate aLo aHi bLo bHi
    (by
      intro r hr
      apply hc r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) hs
  rcases hp with ⟨q1eq, q2eq, q3eq, q4eq, g119bit, g120bit, g121bit,
    g122bit, hgv⟩
  have hglt : ∀ j, g j < M := srun_lt_of_lt k _ p
    (srun_lt_of_lt k _ d (srun_lt_of_lt k _ s hs))
  have hf := cmulOrderedFinishS_spec k g cLo cHi (hc cLo (by simp))
    (hc cHi (by simp)) hLH g119bit g120bit g121bit g122bit hglt
  have hrun : srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) = f :=
    cmulS_run_eq k s gate aLo aHi bLo bHi cLo cHi
  constructor
  · rw [hrun, cmulModel_lo]
    exact hf.1.trans (by rw [q1eq, q2eq, q3eq, q4eq])
  constructor
  · rw [hrun, cmulModel_hi]
    exact hf.2.1.trans (by rw [q1eq, q2eq, q3eq, q4eq])
  · rw [hrun, cmulModel_viol]
    exact hf.2.2.trans hgv

/-- The structure-valued composition is the transparent tuple model. -/
theorem cmulS_spec_split (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi : Nat)
    (hc : ∀ r ∈ [gate, aLo, aHi, bLo, bHi, cLo, cHi], CmulExternal r)
    (hLH : cLo ≠ cHi) (hs : ∀ j, s j < M) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cLo =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cHi =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) rViol =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.2 := by
  rw [← cmulModel_eq_tcmul]
  exact cmulS_model_spec k s gate aLo aHi bLo bHi cLo cHi hc hLH hs

/-- **The complete scalar interval multiplier denotes `tcmul`.**  This is
the arithmetic core used by every `cmulBody` call in the production sweep. -/
theorem cmulS_spec (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi : Nat)
    (hc : ∀ r ∈ [gate, aLo, aHi, bLo, bHi, cLo, cHi], CmulExternal r)
    (hLH : cLo ≠ cHi) (hs : ∀ j, s j < M) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cLo =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cHi =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) rViol =
        (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.2 := by
  exact cmulS_spec_split k s gate aLo aHi bLo bHi cLo cHi hc hLH hs

/-- The ordering network preserves every register outside its fixed scratch
allocation. -/
theorem cmulOrderS_external_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : CmulExternal j) : srun k s cmulOrderS j = s j := by
  have hne (x : Nat) (hx0 : 100 ≤ x) (hx1 : x ≤ 179) : j ≠ x :=
    cmulExternal_ne_scratch hj hx0 hx1
  have hclear : CmpClear j := by simp [CmpClear, CmulExternal] at * <;> omega
  simp only [cmulOrderS, srun_append]
  rw [cmulExtremaSelectsS_frame k _ j
      (hne 134 (by decide) (by decide)) (hne 135 (by decide) (by decide))
      (hne 136 (by decide) (by decide)) (hne 137 (by decide) (by decide))
      (hne 138 (by decide) (by decide)) (hne 153 (by decide) (by decide))
      (hne 144 (by decide) (by decide)),
    cmulExtremaFlagsS_frame k _ j
      (hne 176 (by decide) (by decide)) (hne 177 (by decide) (by decide)) hclear,
    cmulPairSelectsS_frame k _ j
      (hne 134 (by decide) (by decide)) (hne 135 (by decide) (by decide))
      (hne 136 (by decide) (by decide)) (hne 137 (by decide) (by decide))
      (hne 138 (by decide) (by decide)) (hne 153 (by decide) (by decide))
      (hne 162 (by decide) (by decide)) (hne 163 (by decide) (by decide))
      (hne 164 (by decide) (by decide)) (hne 165 (by decide) (by decide))
      (hne 166 (by decide) (by decide)) (hne 167 (by decide) (by decide))
      (hne 144 (by decide) (by decide)),
    cmulPairFlagsS_frame k s j
      (hne 132 (by decide) (by decide)) (hne 133 (by decide) (by decide)) hclear]

/-- The divider/encoder finish stage preserves every external register other
than its two explicit endpoint destinations. -/
theorem cmulFinishS_external_frame (k : Nat) (s : RegState) (cLo cHi j : Nat)
    (hj : CmulExternal j) (hLo : j ≠ cLo) (hHi : j ≠ cHi) :
    srun k s (cmulFinishS cLo cHi) j = s j := by
  have hne (x : Nat) (hx0 : 100 ≤ x) (hx1 : x ≤ 179) : j ≠ x :=
    cmulExternal_ne_scratch hj hx0 hx1
  simp only [cmulFinishS, srun_append]
  rw [cmulEncodeS_frame k _ 137 178 179 cHi j hHi
      (hne 108 (by decide) (by decide)) (hne 109 (by decide) (by decide)),
    divP18S_frame k _ 138 153 178 179 j
      (hne 178 (by decide) (by decide)) (hne 179 (by decide) (by decide))
      (hne 168 (by decide) (by decide)) (hne 169 (by decide) (by decide))
      (hne 170 (by decide) (by decide)) (hne 171 (by decide) (by decide))
      (hne 172 (by decide) (by decide)) (hne 173 (by decide) (by decide))
      (hne 174 (by decide) (by decide)) (hne 175 (by decide) (by decide)),
    cmulEncodeS_frame k _ 134 179 178 cLo j hLo
      (hne 108 (by decide) (by decide)) (hne 109 (by decide) (by decide)),
    divP18S_frame k s 135 136 178 179 j
      (hne 178 (by decide) (by decide)) (hne 179 (by decide) (by decide))
      (hne 168 (by decide) (by decide)) (hne 169 (by decide) (by decide))
      (hne 170 (by decide) (by decide)) (hne 171 (by decide) (by decide))
      (hne 172 (by decide) (by decide)) (hne 173 (by decide) (by decide))
      (hne 174 (by decide) (by decide)) (hne 175 (by decide) (by decide))]

/-- The complete multiplier preserves every external register other than its
two explicit endpoint destinations. -/
theorem cmulS_external_frame (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi j : Nat)
    (hj : CmulExternal j) (hLo : j ≠ cLo) (hHi : j ≠ cHi) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) j = s j := by
  have hne (x : Nat) (hx0 : 100 ≤ x) (hx1 : x ≤ 179) : j ≠ x :=
    cmulExternal_ne_scratch hj hx0 hx1
  simp only [cmulS, srun_append]
  rw [cmulFinishS_external_frame k _ cLo cHi j hj hLo hHi,
    cmulOrderS_external_frame k _ j hj,
    cmulSignsS_frame k _ j
      (hne 119 (by decide) (by decide)) (hne 120 (by decide) (by decide))
      (hne 121 (by decide) (by decide)) (hne 122 (by decide) (by decide))
      (hne 123 (by decide) (by decide)) (hne 124 (by decide) (by decide))
      (hne 125 (by decide) (by decide)),
    cmulProductsS_frame k _ j
      (hne 111 (by decide) (by decide)) (hne 112 (by decide) (by decide))
      (hne 113 (by decide) (by decide)) (hne 114 (by decide) (by decide))
      (hne 115 (by decide) (by decide)) (hne 116 (by decide) (by decide))
      (hne 117 (by decide) (by decide)) (hne 118 (by decide) (by decide))
      (by simp [NotIn8, CmulExternal] at * <;> omega),
    cmulDecompS_external_frame k s gate aLo aHi bLo bHi j hj]
/- Historical direct composition proof, retained as derivation notes.
  let d := srun k s (cmulDecompS gate aLo aHi bLo bHi)
  let p := srun k d cmulProductsS
  let g := srun k p cmulSignsS
  let o := srun k g cmulOrderS
  let f := srun k o (cmulFinishS cLo cHi)
  have cg := hc gate (by simp)
  have caL := hc aLo (by simp)
  have caH := hc aHi (by simp)
  have cbL := hc bLo (by simp)
  have cbH := hc bHi (by simp)
  have ccL := hc cLo (by simp)
  have ccH := hc cHi (by simp)
  have hd := cmulDecompS_spec k s gate aLo aHi bLo bHi
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hs
  rcases hd with ⟨hd100, hd104, hd101, hd105, hd102, hd106, hd103, hd107, hdv⟩
  change d 100 = _ at hd100
  change d 104 = _ at hd104
  change d 101 = _ at hd101
  change d 105 = _ at hd105
  change d 102 = _ at hd102
  change d 106 = _ at hd106
  change d 103 = _ at hd103
  change d 107 = _ at hd107
  change d rViol = _ at hdv
  have pf (j : Nat) (hj : j < 111) : p j = d j := by
    apply cmulProductsS_frame <;> simp [NotIn8] <;> omega
  have hp := cmulProductsS_spec k d (srun_lt_of_lt k _ s hs)
  rcases hp with ⟨hp111, hp112, hp113, hp114, hp115, hp116, hp117, hp118⟩
  change p 111 = _ at hp111
  change p 112 = _ at hp112
  change p 113 = _ at hp113
  change p 114 = _ at hp114
  change p 115 = _ at hp115
  change p 116 = _ at hp116
  change p 117 = _ at hp117
  change p 118 = _ at hp118
  have p100bit : p 100 ≤ 1 := by
    rw [pf 100 (by decide), hd100]
    exact bnat_le_one _
  have p101bit : p 101 ≤ 1 := by
    rw [pf 101 (by decide), hd101]
    exact bnat_le_one _
  have p102bit : p 102 ≤ 1 := by
    rw [pf 102 (by decide), hd102]
    exact bnat_le_one _
  have p103bit : p 103 ≤ 1 := by
    rw [pf 103 (by decide), hd103]
    exact bnat_le_one _
  have hg := cmulSignsS_spec k p p100bit p101bit p102bit p103bit
  rcases hg with ⟨hg119, hg120, hg121, hg122⟩
  change g 119 = _ at hg119
  change g 120 = _ at hg120
  change g 121 = _ at hg121
  change g 122 = _ at hg122
  have gf (j : Nat) (hj : j < 119) : g j = p j := by
    apply cmulSignsS_frame <;> omega
  have g119bit : g 119 ≤ 1 := by
    rw [hg119]
    exact canonSignValue_le_one _ _ _ _ p100bit p102bit
  have g120bit : g 120 ≤ 1 := by
    rw [hg120]
    exact canonSignValue_le_one _ _ _ _ p100bit p103bit
  have g121bit : g 121 ≤ 1 := by
    rw [hg121]
    exact canonSignValue_le_one _ _ _ _ p101bit p102bit
  have g122bit : g 122 ≤ 1 := by
    rw [hg122]
    exact canonSignValue_le_one _ _ _ _ p101bit p103bit
  have ho := cmulOrderS_spec k g g119bit g120bit g121bit g122bit
    (srun_lt_of_lt k _ p (srun_lt_of_lt k _ d (srun_lt_of_lt k _ s hs)))
  let q1 := readCmulWide g 119 111 112
  let q2 := readCmulWide g 120 113 114
  let q3 := readCmulWide g 121 115 116
  let q4 := readCmulWide g 122 117 118
  have hbits := cmulOrderModel_sign_le q1 q2 q3 q4
    g119bit g120bit g121bit g122bit
  have hoMin : readCmulWide o 134 135 136 = (cmulOrderModel q1 q2 q3 q4).1 := ho.1
  have hoMax : readCmulWide o 137 138 153 = (cmulOrderModel q1 q2 q3 q4).2 := ho.2
  have o134bit : o 134 ≤ 1 := by
    have h := congrArg CmulWide.sign hoMin
    change o 134 = (cmulOrderModel q1 q2 q3 q4).1.sign at h
    rw [h]
    exact hbits.1
  have o137bit : o 137 ≤ 1 := by
    have h := congrArg CmulWide.sign hoMax
    change o 137 = (cmulOrderModel q1 q2 q3 q4).2.sign at h
    rw [h]
    exact hbits.2
  have hf := cmulFinishS_spec k o cLo cHi ccL ccH hLH o134bit o137bit
    (srun_lt_of_lt k _ g (srun_lt_of_lt k _ p
      (srun_lt_of_lt k _ d (srun_lt_of_lt k _ s hs))))
  have ominS := congrArg CmulWide.sign hoMin
  have ominL := congrArg CmulWide.lo hoMin
  have ominH := congrArg CmulWide.hi hoMin
  have omaxS := congrArg CmulWide.sign hoMax
  have omaxL := congrArg CmulWide.lo hoMax
  have omaxH := congrArg CmulWide.hi hoMax
  change o 134 = (cmulOrderModel q1 q2 q3 q4).1.sign at ominS
  change o 135 = (cmulOrderModel q1 q2 q3 q4).1.lo at ominL
  change o 136 = (cmulOrderModel q1 q2 q3 q4).1.hi at ominH
  change o 137 = (cmulOrderModel q1 q2 q3 q4).2.sign at omaxS
  change o 138 = (cmulOrderModel q1 q2 q3 q4).2.lo at omaxL
  change o 153 = (cmulOrderModel q1 q2 q3 q4).2.hi at omaxH
  rw [ominS, ominL, ominH, omaxS, omaxL, omaxH] at hf
  have pv : p rViol = d rViol := pf rViol (by simp [rViol])
  have gv : g rViol = p rViol := gf rViol (by simp [rViol])
  have ov : o rViol = g rViol := cmulOrderS_viol_frame k g
  have hfV : f rViol = o rViol := hf.2.2
  have hfv : f rViol =
      (((s rViol ||| (bnat (CAP < (tmag (s aLo)).2) * s gate)) |||
          (bnat (CAP < (tmag (s aHi)).2) * s gate)) |||
        (bnat (CAP < (tmag (s bLo)).2) * s gate)) |||
      (bnat (CAP < (tmag (s bHi)).2) * s gate) := by
    rw [hfV, ov, gv, pv, hdv]
  have q1eq : q1 =
      cmulWideProduct (tmag (s aLo)).1 (tmag (s bLo)).1
        (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bLo)).2) := by
    simp only [q1, readCmulWide, cmulWideProduct]
    rw [hg119, pf 100 (by decide), pf 102 (by decide), hd100, hd102,
      gf 111 (by decide), gf 112 (by decide), hp111, hp112, hd104, hd106]
  have q2eq : q2 =
      cmulWideProduct (tmag (s aLo)).1 (tmag (s bHi)).1
        (Verified.MulWide.hl (tmag (s aLo)).2 (tmag (s bHi)).2) := by
    simp only [q2, readCmulWide, cmulWideProduct]
    rw [hg120, pf 100 (by decide), pf 103 (by decide), hd100, hd103,
      gf 113 (by decide), gf 114 (by decide), hp113, hp114, hd104, hd107]
  have q3eq : q3 =
      cmulWideProduct (tmag (s aHi)).1 (tmag (s bLo)).1
        (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bLo)).2) := by
    simp only [q3, readCmulWide, cmulWideProduct]
    rw [hg121, pf 101 (by decide), pf 102 (by decide), hd101, hd102,
      gf 115 (by decide), gf 116 (by decide), hp115, hp116, hd105, hd106]
  have q4eq : q4 =
      cmulWideProduct (tmag (s aHi)).1 (tmag (s bHi)).1
        (Verified.MulWide.hl (tmag (s aHi)).2 (tmag (s bHi)).2) := by
    simp only [q4, readCmulWide, cmulWideProduct]
    rw [hg122, pf 101 (by decide), pf 103 (by decide), hd101, hd103,
      gf 117 (by decide), gf 118 (by decide), hp117, hp118, hd105, hd107]
  simp only [cmulS, srun_append]
  change f cLo = _ ∧ f cHi = _ ∧ f rViol = _
  have hfLo := hf.1
  have hfHi := hf.2.1
  change f cLo = cmulOrderedLo q1 q2 q3 q4 at hfLo
  change f cHi = cmulOrderedHi q1 q2 q3 q4 at hfHi
  rw [← cmulModel_eq_tcmul]
  constructor
  · rw [hfLo, q1eq, q2eq, q3eq, q4eq]
    rfl
  · constructor
    · rw [hfHi, q1eq, q2eq, q3eq, q4eq]
      rfl
    · rw [hfv]
      rfl
-/

/-! ## §4a Array-machine observation and initialization -/

/-! ### Selector and index-decode stage -/

def selS (c : Cfg) : List Instr := c.selBody.map scalarOf

theorem selBody_lift (c : Cfg) : c.selBody = lift (selS c) := by
  simp [selS, Cfg.selBody, scalarOf, lift]

set_option maxRecDepth 2000 in
theorem selS_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hidx : idx < M) (hR0 : c.rounds ≠ 0) (hR : c.rounds < M)
    (hP : c.p < M) (hPh : c.phase1 < M) (hS : 2 * c.s + 2 < M) :
    let z := c.tsel idx
    let f := srun idx s (selS c)
    f 20 = z.inP1 ∧ f 21 = z.inP2 ∧ f 22 = z.q1 ∧
    f 23 = z.r1 ∧ f 24 = z.n1 ∧ f 25 = z.d1 ∧
    f 26 = z.isD0 ∧ f 27 = z.isDL ∧ f 28 = z.b2 ∧
    f 29 = z.x0 ∧ f 30 = z.pX ∧ f 31 = z.X ∧
    f 32 = z.inA ∧ f 33 = z.isW ∧ f 34 = z.inB ∧
    f 35 = z.isF ∧ f 36 = z.rA ∧ f 37 = z.rBr ∧ f 38 = z.rB := by
  have hRmod : c.rounds % M = c.rounds := Nat.mod_eq_of_lt hR
  have hPmod : c.p % M = c.p := Nat.mod_eq_of_lt hP
  have hPhmod : c.phase1 % M = c.phase1 := Nat.mod_eq_of_lt hPh
  have hS0 : c.s < M := by omega
  have hS1 : c.s + 1 < M := by omega
  have hS2 : 2 * c.s < M := by omega
  have hS3 : 2 * c.s + 1 < M := by omega
  have hSm : c.s % M = c.s := Nat.mod_eq_of_lt hS0
  have hS1m : (c.s + 1) % M = c.s + 1 := Nat.mod_eq_of_lt hS1
  have hS2m : (2 * c.s) % M = 2 * c.s := Nat.mod_eq_of_lt hS2
  have hS3m : (2 * c.s + 1) % M = 2 * c.s + 1 := Nat.mod_eq_of_lt hS3
  have hRm1 : (c.rounds - 1) % M = c.rounds - 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hR)
  have hP0 : c.p ≠ 0 := by simp [Cfg.p]
  have hqR : (idx / c.rounds) % M = idx / c.rounds :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx)
  have hrR : (idx % c.rounds) % M = idx % c.rounds :=
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hR0)) hR)
  have hb2 : (idx + (M - c.phase1)) % M < M := Nat.mod_lt _ M_pos
  have hqP : (((idx + (M - c.phase1)) % M) / c.p) % M =
      ((idx + (M - c.phase1)) % M) / c.p :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb2)
  have hrP : (((idx + (M - c.phase1)) % M) % c.p) % M =
      ((idx + (M - c.phase1)) % M) % c.p :=
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hP0)) hP)
  have h0 : (0 : Nat) % M = 0 := by decide
  have h1 : (1 : Nat) % M = 1 := by decide
  have hsub1 : (1 + (M - 1)) % M = 0 := by decide
  have hbit (p : Prop) [Decidable p] :
      (if p then 1 else 0) % M = (if p then 1 else 0) := by
    split <;> decide
  have hbits (p q : Prop) [Decidable p] [Decidable q] :
      ((if p then 1 else 0) * (if q then 1 else 0)) % M =
        (if p then 1 else 0) * (if q then 1 else 0) := by
    split <;> split <;> decide
  simp only [selS, Cfg.selBody, scalarOf, List.map_cons, List.map_nil,
    srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, if_true, if_false, Nat.reduceEqDiff, hRmod, hPmod,
    hPhmod, hSm, hS1m, hS2m, hS3m, hRm1, Nat.mod_eq_of_lt hidx,
    hR0, hP0, hqR, hrR, hqP, hrP, h0, h1]
  by_cases hphase : idx < c.phase1 <;>
    simp [Cfg.tsel, bnat, tsub, hphase, hbit, hbits, hsub1]
  all_goals first | rfl | exact ⟨h1, rfl, rfl⟩

theorem selS_frame (c : Cfg) (idx : Nat) (s : RegState) (j : Nat)
    (hj : j < 20 ∨ 39 < j) : srun idx s (selS c) j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [selS, Cfg.selBody, scalarOf, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem selBody_alwaysDef (c : Cfg) (hR0 : c.rounds ≠ 0)
    (hR : c.rounds < M) (hP : c.p < M) :
    c.selBody.all alwaysDef = true := by
  have hP0 : c.p ≠ 0 := by simp [Cfg.p]
  have hRm : c.rounds % M = c.rounds := Nat.mod_eq_of_lt hR
  have hPm : c.p % M = c.p := Nat.mod_eq_of_lt hP
  simp [Cfg.selBody, alwaysDef, hRm, hPm, hR0, hP0]

theorem selBody_defined (c : Cfg) (len idx : Nat) (st : AState)
    (hR0 : c.rounds ≠ 0) (hR : c.rounds < M) (hP : c.p < M) :
    AllDefined len idx st c.selBody :=
  allDefined_of_alwaysDef len idx c.selBody st (selBody_alwaysDef c hR0 hR hP)

/-! ### Phase-1 trial-division stage -/

def trialS : List Instr := trialScalarBody.map scalarOf

theorem trialScalarBody_lift : trialScalarBody = lift trialS := by
  simp [trialS, trialScalarBody, muxBody, scalarOf, lift]

def trialResetTailS : List Instr :=
  [ .binop 41 .sub (.lit 1) (.reg 26)
  , .binop 3 .mul (.reg 3) (.reg 41)
  , .binop 4 .mul (.reg 4) (.reg 41)
  , .binop 42 .urem (.reg 2) (.reg 25)
  , .binop 43 .eq (.reg 42) (.lit 0)
  , .binop 43 .mul (.reg 43) (.reg 20)
  , .binop 44 .udiv (.reg 2) (.reg 25) ]

def trialResetS : List Instr := muxS 2 26 24 2 40 ++ trialResetTailS

theorem trialResetTailS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h20 : s 20 ≤ 1) (h26 : s 26 ≤ 1)
    (hd : s 25 ≠ 0) :
    let f := srun k s trialResetTailS
    f 2 = s 2 ∧ f 3 = s 3 * (1 - s 26) ∧
      f 4 = s 4 * (1 - s 26) ∧
      f 43 = bnat (s 2 % s 25 = 0) * s 20 ∧
      f 44 = s 2 / s 25 := by
  simp only [trialResetTailS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff]
  have h25pos : 0 < s 25 := Nat.pos_of_ne_zero hd
  have hremLt : s 2 % s 25 < M := Nat.lt_trans (Nat.mod_lt _ h25pos) (hs 25)
  have hdivLt : s 2 / s 25 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hs 2)
  have hrem : s 2 % s 25 % M = s 2 % s 25 := Nat.mod_eq_of_lt hremLt
  have hdiv : s 2 / s 25 % M = s 2 / s 25 := Nat.mod_eq_of_lt hdivLt
  have h3m : s 3 % M = s 3 := Nat.mod_eq_of_lt (hs 3)
  have h4m : s 4 % M = s 4 := Nat.mod_eq_of_lt (hs 4)
  have hM2 : 1 < M := by decide
  have hhitLt : (if s 2 % s 25 = 0 then 1 else 0) * s 20 < M := by
    split <;> omega
  have hhit : (if s 2 % s 25 = 0 then 1 else 0) * s 20 % M =
      (if s 2 % s 25 = 0 then 1 else 0) * s 20 := Nat.mod_eq_of_lt hhitLt
  have hMsub : 1 + (M - 1) = M := by have := M_pos; omega
  rcases (by omega : s 26 = 0 ∨ s 26 = 1) with h0 | h1
  · simp [h0, hd, hrem, hdiv, h3m, h4m, hhit, bnat, one_mod_M]
  · simp [h1, hd, hrem, hdiv, hhit, hMsub, bnat, one_mod_M]

theorem trialResetS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M)
    (h2 : s 2 = t.res) (h3 : s 3 = t.sq) (h4 : s 4 = t.par)
    (h20 : s 20 = z.inP1) (h24 : s 24 = z.n1)
    (h25 : s 25 = z.d1) (h26 : s 26 = z.isD0)
    (hP1 : z.inP1 ≤ 1) (hD0 : z.isD0 ≤ 1) (hd : z.d1 ≠ 0) :
    let f := srun k s trialResetS
    let res0 := if z.isD0 = 1 then z.n1 else t.res
    let hit := bnat (res0 % z.d1 = 0) * z.inP1
    f 2 = res0 ∧ f 3 = t.sq * (1 - z.isD0) ∧
      f 4 = t.par * (1 - z.isD0) ∧ f 43 = hit ∧
      f 44 = res0 / z.d1 := by
  let m := srun k s (muxS 2 26 24 2 40)
  have hm2 := muxS_spec k s 2 26 24 2 40 (by omega) (by omega)
    (by omega) (by omega) (by simpa [h26] using hD0) hs
  have hmf (j : Nat) (h2j : j ≠ 2) (h40j : j ≠ 40) : m j = s j :=
    muxS_frame k s 2 26 24 2 40 j h2j h40j
  have hm2' : m 2 = (if z.isD0 = 1 then z.n1 else t.res) := by
    simpa [m, h26, h24, h2] using hm2
  have hm3 : m 3 = t.sq := (hmf 3 (by omega) (by omega)).trans h3
  have hm4 : m 4 = t.par := (hmf 4 (by omega) (by omega)).trans h4
  have hm20 : m 20 = z.inP1 := (hmf 20 (by omega) (by omega)).trans h20
  have hm25 : m 25 = z.d1 := (hmf 25 (by omega) (by omega)).trans h25
  have hm26 : m 26 = z.isD0 := (hmf 26 (by omega) (by omega)).trans h26
  have hmLt : ∀ j, m j < M := srun_lt_of_lt k _ s hs
  have hm20bit : m 20 ≤ 1 := by simpa [hm20] using hP1
  have hm26bit : m 26 ≤ 1 := by simpa [hm26] using hD0
  have hm25nz : m 25 ≠ 0 := by simpa [hm25] using hd
  have ht := trialResetTailS_spec k m hmLt hm20bit hm26bit hm25nz
  simp only [trialResetS, srun_append]
  change let f := srun k m trialResetTailS; _
  simpa [hm2', hm3, hm4, hm20, hm25, hm26] using ht

theorem trialResetS_frame (k : Nat) (s : RegState) (j : Nat)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h40 : j ≠ 40)
    (h41 : j ≠ 41) (h42 : j ≠ 42) (h43 : j ≠ 43) (h44 : j ≠ 44) :
    srun k s trialResetS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [trialResetS, trialResetTailS, muxS, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp only [sdest] <;> omega

def trialDivideS : List Instr := muxS 2 43 44 2 45

theorem trialDivideS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h43 : s 43 ≤ 1) :
    srun k s trialDivideS 2 = (if s 43 = 1 then s 44 else s 2) := by
  exact muxS_spec k s 2 43 44 2 45 (by omega) (by omega) (by omega)
    (by omega) h43 hs

theorem trialDivideS_frame (k : Nat) (s : RegState) (j : Nat)
    (h2 : j ≠ 2) (h45 : j ≠ 45) :
    srun k s trialDivideS j = s j :=
  muxS_frame k s 2 43 44 2 45 j h2 h45

def trialFinishS : List Instr :=
  [ .binop 46 .urem (.reg 2) (.reg 25)
  , .binop 47 .eq (.reg 46) (.lit 0)
  , .binop 47 .mul (.reg 47) (.reg 43)
  , .binop 3 .bor (.reg 3) (.reg 47)
  , .binop 4 .bxor (.reg 4) (.reg 43)
  , .binop 48 .ne (.reg 2) (.lit 1)
  , .binop 49 .bxor (.reg 4) (.reg 48)
  , .binop 50 .sub (.lit 1) (.reg 3)
  , .binop 51 .add (.reg 49) (.lit 1)
  , .binop 51 .mul (.reg 51) (.reg 50)
  , .binop 52 .mul (.reg 27) (.reg 24)
  , .binop 53 .mul (.reg 27) (.reg 51) ]

theorem trialFinishS_spec (k : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hd : s 25 ≠ 0)
    (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1) (h43 : s 43 ≤ 1) :
    let f := srun k s trialFinishS
    let hit2 := bnat (s 2 % s 25 = 0) * s 43
    let sq := s 3 ||| hit2
    let par := s 4 ^^^ s 43
    let om := par ^^^ bnat (s 2 ≠ 1)
    let code := ((om + 1) % M) * (1 - sq) % M
    f 2 = s 2 ∧ f 3 = sq ∧ f 4 = par ∧
      f 52 = s 27 * s 24 % M ∧ f 53 = s 27 * code % M := by
  simp only [trialFinishS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff]
  have h25pos : 0 < s 25 := Nat.pos_of_ne_zero hd
  have hremLt : s 2 % s 25 < M := Nat.lt_trans (Nat.mod_lt _ h25pos) (hs 25)
  have hrem : s 2 % s 25 % M = s 2 % s 25 := Nat.mod_eq_of_lt hremLt
  let hit2 := bnat (s 2 % s 25 = 0) * s 43
  have hhit2 : hit2 ≤ 1 := by simp only [hit2, bnat]; split <;> omega
  have hM2 : 1 < M := by decide
  have hhit2M : hit2 < M := Nat.lt_of_le_of_lt hhit2 hM2
  have hhit2mod : hit2 % M = hit2 := Nat.mod_eq_of_lt hhit2M
  let sq := s 3 ||| hit2
  let par := s 4 ^^^ s 43
  have hsq : sq ≤ 1 := by
    rcases (by omega : s 3 = 0 ∨ s 3 = 1) with h30 | h31
    · rcases (by omega : hit2 = 0 ∨ hit2 = 1) with hh0 | hh1
      · simp [sq, h30, hh0]
      · simp [sq, h30, hh1]
    · rcases (by omega : hit2 = 0 ∨ hit2 = 1) with hh0 | hh1
      · simp [sq, h31, hh0]
      · simp [sq, h31, hh1]
  have hpar : par ≤ 1 := by
    rcases (by omega : s 4 = 0 ∨ s 4 = 1) with h40 | h41
    · rcases (by omega : s 43 = 0 ∨ s 43 = 1) with hh0 | hh1
      · simp [par, h40, hh0]
      · simp [par, h40, hh1]
    · rcases (by omega : s 43 = 0 ∨ s 43 = 1) with hh0 | hh1
      · simp [par, h41, hh0]
      · simp [par, h41, hh1]
  have hsqM : sq < M := Nat.lt_of_le_of_lt hsq hM2
  have hparM : par < M := Nat.lt_of_le_of_lt hpar hM2
  have hsqmod : sq % M = sq := Nat.mod_eq_of_lt hsqM
  have hparmod : par % M = par := Nat.mod_eq_of_lt hparM
  have hsqMachine : (s 3 ||| hit2 % M) % M = sq := by
    rw [hhit2mod]
    exact lor_mod_M (hs 3) hhit2M
  have hsqMachine' :
      (s 3 ||| (if s 2 % s 25 = 0 then 1 else 0) * s 43 % M) % M =
        s 3 ||| bnat (s 2 % s 25 = 0) * s 43 := by
    change (s 3 ||| hit2 % M) % M = sq
    exact hsqMachine
  have hparMachine : (s 4 ^^^ s 43) % M = par := by
    exact Nat.mod_eq_of_lt (lxor_lt_M (hs 4) (hs 43))
  let ne1 := bnat (s 2 ≠ 1)
  have hne1M : ne1 < M := by
    simp only [ne1, bnat]
    split <;> omega
  let om := par ^^^ ne1
  have homM : om < M := lxor_lt_M hparM hne1M
  have hneMachine : (if s 2 ≠ 1 % M then 1 else 0) = ne1 := by
    simp [one_mod_M, ne1, bnat]
  have homMachine :
      ((s 4 ^^^ s 43) % M ^^^ (if s 2 ≠ 1 % M then 1 else 0)) % M = om := by
    rw [hparMachine, hneMachine]
    exact Nat.mod_eq_of_lt (lxor_lt_M hparM hne1M)
  have homMachine' :
      (par ^^^ (if s 2 ≠ 1 % M then 1 else 0)) % M = om := by
    rw [hneMachine]
    exact Nat.mod_eq_of_lt (lxor_lt_M hparM hne1M)
  have hsubMachine : (1 % M + (M - sq)) % M = 1 - sq := by
    rw [one_mod_M, msub_bit hsq]
  have hsubMachine' :
      (1 % M + (M - (s 3 ||| bnat (s 2 % s 25 = 0) * s 43))) % M =
        1 - (s 3 ||| bnat (s 2 % s 25 = 0) * s 43) := by
    change (1 % M + (M - sq)) % M = 1 - sq
    exact hsubMachine
  have hzero : 0 % M = 0 := by decide
  simp only [hd, if_false, Option.getD_some, hrem, hzero]
  simp only [true_and]
  constructor
  · exact hsqMachine'
  constructor
  · change (s 4 ^^^ s 43) % M = par
    exact hparMachine
  rw [hsqMachine', hparMachine]
  rw [homMachine', hsubMachine', one_mod_M]

theorem trialS_decomp : trialS = trialResetS ++ trialDivideS ++ trialFinishS := by
  simp [trialS, trialScalarBody, trialResetS, trialResetTailS, trialDivideS,
    trialFinishS, muxBody, muxS, scalarOf]

theorem trialS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M)
    (h2 : s 2 = t.res) (h3 : s 3 = t.sq) (h4 : s 4 = t.par)
    (h20 : s 20 = z.inP1) (h24 : s 24 = z.n1)
    (h25 : s 25 = z.d1) (h26 : s 26 = z.isD0)
    (h27 : s 27 = z.isDL)
    (hP1 : z.inP1 ≤ 1) (hD0 : z.isD0 ≤ 1)
    (hSq : t.sq ≤ 1) (hPar : t.par ≤ 1) (hd : z.d1 ≠ 0) :
    let f := srun k s trialS
    let u := ttrial z t
    let wrAddr := z.isDL * z.n1 % M
    f 2 = u.res ∧ f 3 = u.sq ∧ f 4 = u.par ∧
      f 52 = wrAddr ∧ f 53 = u.arr wrAddr := by
  let a := srun k s trialResetS
  have ha := trialResetS_spec k s z t hs h2 h3 h4 h20 h24 h25 h26 hP1 hD0 hd
  dsimp only at ha
  rcases ha with ⟨ha2, ha3, ha4, ha43, ha44⟩
  change a 2 = _ at ha2
  change a 3 = _ at ha3
  change a 4 = _ at ha4
  change a 43 = _ at ha43
  change a 44 = _ at ha44
  have haf (j : Nat) (h2j : j ≠ 2) (h3j : j ≠ 3) (h4j : j ≠ 4)
      (h40j : j ≠ 40) (h41j : j ≠ 41) (h42j : j ≠ 42)
      (h43j : j ≠ 43) (h44j : j ≠ 44) : a j = s j :=
    trialResetS_frame k s j h2j h3j h4j h40j h41j h42j h43j h44j
  have ha24 : a 24 = z.n1 := (haf 24 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans h24
  have ha25 : a 25 = z.d1 := (haf 25 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans h25
  have ha27 : a 27 = z.isDL := (haf 27 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans h27
  have haLt : ∀ j, a j < M := srun_lt_of_lt k _ s hs
  have ha43bit : a 43 ≤ 1 := by
    rw [ha43]
    simpa only [Nat.one_mul] using Nat.mul_le_mul
      (bnat_le_one ((if z.isD0 = 1 then z.n1 else t.res) % z.d1 = 0)) hP1
  let b := srun k a trialDivideS
  have hb2 := trialDivideS_spec k a haLt ha43bit
  change b 2 = _ at hb2
  have hbf (j : Nat) (h2j : j ≠ 2) (h45j : j ≠ 45) : b j = a j :=
    trialDivideS_frame k a j h2j h45j
  have hb3 : b 3 = t.sq * (1 - z.isD0) :=
    (hbf 3 (by omega) (by omega)).trans ha3
  have hb4 : b 4 = t.par * (1 - z.isD0) :=
    (hbf 4 (by omega) (by omega)).trans ha4
  have hb24 : b 24 = z.n1 := (hbf 24 (by omega) (by omega)).trans ha24
  have hb25 : b 25 = z.d1 := (hbf 25 (by omega) (by omega)).trans ha25
  have hb27 : b 27 = z.isDL := (hbf 27 (by omega) (by omega)).trans ha27
  have hb43 : b 43 = bnat ((if z.isD0 = 1 then z.n1 else t.res) % z.d1 = 0) *
      z.inP1 := (hbf 43 (by omega) (by omega)).trans ha43
  have hbLt : ∀ j, b j < M := srun_lt_of_lt k _ a haLt
  have hb3bit : b 3 ≤ 1 := by
    rw [hb3]
    rcases (by omega : z.isD0 = 0 ∨ z.isD0 = 1) with hz | ho
    · simpa [hz] using hSq
    · simp [ho]
  have hb4bit : b 4 ≤ 1 := by
    rw [hb4]
    rcases (by omega : z.isD0 = 0 ∨ z.isD0 = 1) with hz | ho
    · simpa [hz] using hPar
    · simp [ho]
  have hb43bit : b 43 ≤ 1 := by
    rw [hb43]
    simpa only [Nat.one_mul] using Nat.mul_le_mul
      (bnat_le_one ((if z.isD0 = 1 then z.n1 else t.res) % z.d1 = 0)) hP1
  have hb25nz : b 25 ≠ 0 := by simpa [hb25] using hd
  have hf := trialFinishS_spec k b hbLt hb25nz hb3bit hb4bit hb43bit
  dsimp only at hf
  rw [trialS_decomp, srun_append, srun_append]
  change let f := srun k b trialFinishS; _
  simpa [ttrial, ha2, ha3, ha4, ha43, ha44, hb2, hb3, hb4, hb24, hb25,
    hb27, hb43] using hf

theorem trialResetTailS_defined (k : Nat) (s : RegState) (hd : s 25 ≠ 0) :
    SAllDefined k s trialResetTailS := by
  simp [trialResetTailS, SAllDefined, SDefined, sdest, sval,
    denoteOperand, denoteOp, RegState.set, hd]

theorem trialResetS_defined (k : Nat) (s : RegState) (hd : s 25 ≠ 0) :
    SAllDefined k s trialResetS := by
  rw [trialResetS]
  apply sAllDefined_append (sAllDefined_of_noDiv k _ s (by decide))
  apply trialResetTailS_defined
  rw [muxS_frame k s 2 26 24 2 40 25 (by omega) (by omega)]
  exact hd

theorem trialFinishS_defined (k : Nat) (s : RegState) (hd : s 25 ≠ 0) :
    SAllDefined k s trialFinishS := by
  simp [trialFinishS, SAllDefined, SDefined, sdest, sval,
    denoteOperand, denoteOp, RegState.set, hd]

theorem trialS_defined (k : Nat) (s : RegState) (hd : s 25 ≠ 0) :
    SAllDefined k s trialS := by
  let a := srun k s trialResetS
  let b := srun k a trialDivideS
  rw [trialS_decomp, LeanCompCert.Verified.InstrBlock.SAllDefined_append]
  constructor
  · rw [LeanCompCert.Verified.InstrBlock.SAllDefined_append]
    exact ⟨trialResetS_defined k s hd,
      sAllDefined_of_noDiv k trialDivideS a (by decide)⟩
  · apply trialFinishS_defined
    rw [srun_append]
    change b 25 ≠ 0
    have hb25 : b 25 = a 25 := trialDivideS_frame k a 25 (by omega) (by omega)
    have ha25 : a 25 = s 25 := trialResetS_frame k s 25 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hb25, ha25]
    exact hd

theorem trialFinishS_frame (k : Nat) (s : RegState) (j : Nat)
    (h3 : j ≠ 3) (h4 : j ≠ 4) (h46 : j ≠ 46) (h47 : j ≠ 47)
    (h48 : j ≠ 48) (h49 : j ≠ 49) (h50 : j ≠ 50) (h51 : j ≠ 51)
    (h52 : j ≠ 52) (h53 : j ≠ 53) : srun k s trialFinishS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [trialFinishS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem trialFinishS_addr (k : Nat) (s : RegState) :
    srun k s trialFinishS 52 = s 27 * s 24 % M := by
  simp [trialFinishS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set]

theorem trialS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 2 ∨ (4 < j ∧ j < 40) ∨ 53 < j) : srun k s trialS j = s j := by
  rw [trialS_decomp, srun_append, srun_append,
    trialFinishS_frame k _ j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    trialDivideS_frame k _ j (by omega) (by omega),
    trialResetS_frame k s j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]

theorem trialS_addr (k : Nat) (s : RegState) :
    srun k s trialS 52 = s 27 * s 24 % M := by
  let a := srun k s trialResetS
  let b := srun k a trialDivideS
  have ha24 : a 24 = s 24 := trialResetS_frame k s 24 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ha27 : a 27 = s 27 := trialResetS_frame k s 27 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb24 : b 24 = a 24 := trialDivideS_frame k a 24 (by omega) (by omega)
  have hb27 : b 27 = a 27 := trialDivideS_frame k a 27 (by omega) (by omega)
  rw [trialS_decomp, srun_append, srun_append]
  change srun k b trialFinishS 52 = _
  rw [trialFinishS_addr, hb24, hb27, ha24, ha27]

theorem trialBody_defined (len k : Nat) (st : AState)
    (hd : st.regs 25 ≠ 0) (hAddr : st.regs 27 * st.regs 24 % M < len) :
    AllDefined len k st trialBody := by
  rw [trialBody, AllDefined_append]
  constructor
  · rw [trialScalarBody_lift, allDefined_lift]
    exact trialS_defined k st.regs hd
  · rw [trialScalarBody_lift, arun_lift]
    simp [AllDefined, ADefined, trialS_addr, hAddr]

def passAS : List Instr := passABody.map scalarOf

theorem passABody_lift : passABody = lift passAS := by
  simp [passAS, passABody, muxBody, scalarOf, lift]

def passAGateS : List Instr :=
  [ .binop 56 .eq (.reg 30) (.lit 0)
  , .binop 56 .mul (.reg 56) (.reg 21) ]

theorem passAGateS_spec (k : Nat) (s : RegState) (h21 : s 21 ≤ 1) :
    srun k s passAGateS 56 = bnat (s 30 = 0) * s 21 := by
  simp only [passAGateS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff,
    zero_mod_M]
  have hM2 : 1 < M := by decide
  exact bnat_mul_mod _ (Nat.lt_of_le_of_lt h21 hM2)

theorem passAGateS_frame (k : Nat) (s : RegState) (j : Nat) (h56 : j ≠ 56) :
    srun k s passAGateS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [passAGateS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp only [sdest] <;> omega

def passAResetS : List Instr := passAGateS ++ muxS 5 56 1 5 57

theorem passAResetS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M) (h1 : s 1 = 0) (h5 : s 5 = t.sigma)
    (h21 : s 21 = z.inP2) (h30 : s 30 = z.pX) (hP2 : z.inP2 ≤ 1) :
    let f := srun k s passAResetS
    let isX0 := bnat (z.pX = 0) * z.inP2
    f 5 = (if isX0 = 1 then 0 else t.sigma) ∧ f 56 = isX0 := by
  let m := srun k s passAGateS
  have hm56 := passAGateS_spec k s (by simpa [h21] using hP2)
  change m 56 = _ at hm56
  have hmf (j : Nat) (hj : j ≠ 56) : m j = s j := passAGateS_frame k s j hj
  have hm1 : m 1 = 0 := (hmf 1 (by omega)).trans h1
  have hm5 : m 5 = t.sigma := (hmf 5 (by omega)).trans h5
  have hmLt : ∀ j, m j < M := srun_lt_of_lt k _ s hs
  have hm56bit : m 56 ≤ 1 := by
    rw [hm56, h21, h30]
    simpa only [Nat.one_mul] using Nat.mul_le_mul (bnat_le_one (z.pX = 0)) hP2
  have hout := muxS_spec k m 5 56 1 5 57 (by omega) (by omega) (by omega)
    (by omega) hm56bit hmLt
  have hf56 := muxS_frame k m 5 56 1 5 57 56 (by omega) (by omega)
  simp only [passAResetS, srun_append]
  change let f := srun k m (muxS 5 56 1 5 57); _
  constructor
  · simpa [hm56, hm1, hm5, h21, h30] using hout
  · simpa [hm56, h21, h30] using hf56

theorem passAResetS_frame (k : Nat) (s : RegState) (j : Nat)
    (h5 : j ≠ 5) (h56 : j ≠ 56) (h57 : j ≠ 57) :
    srun k s passAResetS j = s j := by
  rw [passAResetS, srun_append, muxS_frame k _ 5 56 1 5 57 j h5 h57,
    passAGateS_frame k s j h56]

def passATailS : List Instr :=
  [ .binop 58 .urem (.reg 31) (.reg 36)
  , .binop 59 .eq (.reg 58) (.lit 0)
  , .binop 60 .mul (.reg 36) (.reg 36)
  , .binop 61 .le (.reg 60) (.reg 31)
  , .binop 62 .mul (.reg 59) (.reg 61)
  , .binop 62 .mul (.reg 62) (.reg 32)
  , .binop 63 .udiv (.reg 31) (.reg 36)
  , .binop 64 .eq (.reg 63) (.reg 36)
  , .binop 65 .sub (.lit 1) (.reg 64)
  , .binop 65 .mul (.reg 65) (.reg 63)
  , .binop 66 .add (.reg 36) (.reg 65)
  , .binop 66 .mul (.reg 66) (.reg 62)
  , .binop 5 .add (.reg 5) (.reg 66) ]

theorem passATailS_spec (k : Nat) (s : RegState) (z : TSel)
    (hs : ∀ j, s j < M) (h31 : s 31 = z.X) (h32 : s 32 = z.inA)
    (h36 : s 36 = z.rA) (hrA : z.rA ≠ 0) :
    let f := srun k s passATailS
    let hit := bnat (z.X % z.rA = 0) * bnat (z.rA * z.rA % M ≤ z.X) * z.inA
    let q := z.X / z.rA
    let add := ((z.rA + (1 - bnat (q = z.rA)) * q % M) % M) * hit % M
    f 5 = (s 5 + add) % M := by
  simp only [passATailS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff]
  have hrApos : 0 < z.rA := Nat.pos_of_ne_zero hrA
  have hrAm : z.rA < M := by rw [← h36]; exact hs 36
  have hXm : z.X < M := by rw [← h31]; exact hs 31
  have hremLt : z.X % z.rA < M := Nat.lt_trans (Nat.mod_lt _ hrApos) hrAm
  have hrem : z.X % z.rA % M = z.X % z.rA := Nat.mod_eq_of_lt hremLt
  have hqLt : z.X / z.rA < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hXm
  have hqmod : z.X / z.rA % M = z.X / z.rA := Nat.mod_eq_of_lt hqLt
  simp [h31, h32, h36, hrA, hrem, hqmod, bnat]
  by_cases heq : z.X / z.rA = z.rA
  · simp only [heq, if_pos, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    let H := ((if z.X % z.rA = 0 then 1 else 0) *
      if z.rA * z.rA % M ≤ z.X then 1 else 0) * z.inA
    change (s 5 + (z.rA + (1 + (M - 1)) * z.rA) * H) % M =
      (s 5 + z.rA * H) % M
    have hM : 1 + (M - 1) = M := by have := M_pos; omega
    rw [hM]
    have hform : s 5 + (z.rA + M * z.rA) * H =
        (s 5 + z.rA * H) + (z.rA * H) * M := by
      simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hform, Nat.add_mul_mod_self_right]
  · simp [heq]
    let q := z.X / z.rA
    let H := ((if z.X % z.rA = 0 then 1 else 0) *
      if z.rA * z.rA % M ≤ z.X then 1 else 0) * z.inA
    change (s 5 + (z.rA + (1 + M) * q) * H) % M =
      (s 5 + (z.rA + q) * H) % M
    have hform : s 5 + (z.rA + (1 + M) * q) * H =
        (s 5 + (z.rA + q) * H) + (q * H) * M := by
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hform, Nat.add_mul_mod_self_right]

theorem passATailS_frame (k : Nat) (s : RegState) (j : Nat)
    (h5 : j ≠ 5) (h58 : j ≠ 58) (h59 : j ≠ 59) (h60 : j ≠ 60)
    (h61 : j ≠ 61) (h62 : j ≠ 62) (h63 : j ≠ 63) (h64 : j ≠ 64)
    (h65 : j ≠ 65) (h66 : j ≠ 66) : srun k s passATailS j = s j := by
  apply LeanCompCert.Verified.InstrBlock.srun_untouched
  intro i hi
  simp only [passATailS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem passAS_decomp : passAS = passAResetS ++ passATailS := by
  simp [passAS, passABody, passAResetS, passAGateS, passATailS, muxBody,
    muxS, scalarOf]

theorem passAS_spec (k : Nat) (s : RegState) (z : TSel) (t : TState)
    (hs : ∀ j, s j < M) (h1 : s 1 = 0) (h5 : s 5 = t.sigma)
    (h21 : s 21 = z.inP2) (h30 : s 30 = z.pX) (h31 : s 31 = z.X)
    (h32 : s 32 = z.inA) (h36 : s 36 = z.rA)
    (hP2 : z.inP2 ≤ 1) (hrA : z.rA ≠ 0) :
    srun k s passAS 5 = (tpassA z t).sigma := by
  let a := srun k s passAResetS
  have ha := passAResetS_spec k s z t hs h1 h5 h21 h30 hP2
  dsimp only at ha
  rcases ha with ⟨ha5, ha56⟩
  change a 5 = _ at ha5
  have haf (j : Nat) (h5j : j ≠ 5) (h56j : j ≠ 56) (h57j : j ≠ 57) :
      a j = s j := passAResetS_frame k s j h5j h56j h57j
  have ha31 : a 31 = z.X := (haf 31 (by omega) (by omega) (by omega)).trans h31
  have ha32 : a 32 = z.inA := (haf 32 (by omega) (by omega) (by omega)).trans h32
  have ha36 : a 36 = z.rA := (haf 36 (by omega) (by omega) (by omega)).trans h36
  have haLt : ∀ j, a j < M := srun_lt_of_lt k _ s hs
  have ht := passATailS_spec k a z haLt ha31 ha32 ha36 hrA
  dsimp only at ht
  rw [passAS_decomp, srun_append]
  change srun k a passATailS 5 = _
  simpa [tpassA, ha5, h21, h30] using ht

theorem passAS_frame (k : Nat) (s : RegState) (j : Nat)
    (hj : j < 5 ∨ (5 < j ∧ j < 56) ∨ 66 < j) : srun k s passAS j = s j := by
  rw [passAS_decomp, srun_append,
    passATailS_frame k _ j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    passAResetS_frame k s j (by omega) (by omega) (by omega)]

theorem passATailS_defined (k : Nat) (s : RegState) (hd : s 36 ≠ 0) :
    SAllDefined k s passATailS := by
  simp [passATailS, SAllDefined, SDefined, sdest, sval, denoteOperand,
    denoteOp, RegState.set, hd]

theorem passAS_defined (k : Nat) (s : RegState) (hd : s 36 ≠ 0) :
    SAllDefined k s passAS := by
  rw [passAS_decomp, LeanCompCert.Verified.InstrBlock.SAllDefined_append]
  constructor
  · exact sAllDefined_of_noDiv k passAResetS s (by decide)
  · apply passATailS_defined
    rw [passAResetS_frame k s 36 (by omega) (by omega) (by omega)]
    exact hd

theorem passABody_defined (len k : Nat) (st : AState) (hd : st.regs 36 ≠ 0) :
    AllDefined len k st passABody := by
  rw [passABody_lift, allDefined_lift]
  exact passAS_defined k st.regs hd

/-- State reached after computing the three touch addresses and loading both
accumulator endpoints. -/
def touchLoadState (c : Cfg) (g dSlot : Nat) (st : AState) : AState :=
  let base := c.touchBase (st.regs g) (st.regs dSlot)
  let a1 := c.touchA1 (st.regs g) (st.regs dSlot)
  let a2 := c.touchA2 (st.regs g) (st.regs dSlot)
  let st := st.writeReg 194 base
  let st := st.writeReg 191 a1
  let st := st.writeReg 192 a2
  let st := st.writeReg 180 (st.arr a1)
  st.writeReg 181 (st.arr a2)

/-- Total semantics of the address/load prefix. -/
theorem touchLoadBody_run (c : Cfg) (k g dSlot : Nat) (st : AState)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2) :
    arun k st (c.touchLoadBody g dSlot) = touchLoadState c g dSlot st := by
  simp [Cfg.touchLoadBody, touchLoadState, Cfg.touchBase, Cfg.touchA1,
    Cfg.touchA2, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
    denoteOp, hP1, hP2]

/-- The only partial operations in the load prefix are its two array reads. -/
theorem touchLoadBody_defined (c : Cfg) (k g dSlot : Nat) (st : AState)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2)
    (hA1 : c.touchA1 (st.regs g) (st.regs dSlot) < c.arrayLen)
    (hA2 : c.touchA2 (st.regs g) (st.regs dSlot) < c.arrayLen) :
    AllDefined c.arrayLen k st (c.touchLoadBody g dSlot) := by
  simp only [Cfg.touchLoadBody, AllDefined, ADefined, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, hP1, hP2,
    Option.getD_some, if_true]
  simpa [Cfg.touchA1, Cfg.touchA2, Cfg.touchBase, Nat.add_mod] using
    And.intro hA1 hA2

/-- Scalar view of the product and its two immediate width guards. -/
def touchProductS (g : Nat) : List Instr :=
  cmulS g 180 181 6 7 182 183 ++ guardG CAP g 182 195 ++
    guardG CAP g 183 195

theorem touchProductBody_lift (c : Cfg) (g : Nat) :
    c.touchProductBody g = lift (touchProductS g) := by
  simp only [Cfg.touchProductBody, touchProductS, cmulBody_lift,
    guardBody_lift, lift_append]

set_option maxRecDepth 4000 in
theorem cmulBody_alwaysDef (gate aLo aHi bLo bHi cLo cHi : Nat) :
    (cmulBody gate aLo aHi bLo bHi cLo cHi).all alwaysDef = true := by
  simp [cmulBody, cmulDecompBody, smDecomp, cmulProductsBody,
    LeanCompCert.Ports.CDEMAbelScan.mulWideBody, cmulSignsBody, canonSignBody,
    LeanCompCert.Ports.CDEMAbelScan.muxBody,
    cmulOrderBody, cmulPairFlagsBody, cmulPairSelectsBody,
    cmulExtremaFlagsBody, cmulExtremaSelectsBody, cmpLtBody, selTriple,
    cmulFinishBody, cmulLowerBody, cmulUpperBody, divP18Body_alwaysDef,
    alwaysDef]

theorem touchProductBody_defined (c : Cfg) (len k g : Nat) (st : AState) :
    AllDefined len k st (c.touchProductBody g) := by
  apply allDefined_of_alwaysDef
  simp [Cfg.touchProductBody, guardBody, cmulBody_alwaysDef, alwaysDef]

/-- Registers outside the product outputs and guard scratch survive the whole
product prefix. -/
theorem touchProductS_external_frame (k : Nat) (s : RegState) (g j : Nat)
    (hj : CmulExternal j) (h182 : j ≠ 182) (h183 : j ≠ 183)
    (h195 : j ≠ 195) : srun k s (touchProductS g) j = s j := by
  simp only [touchProductS, srun_append]
  rw [guardG_frame k _ CAP g 183 195 j h195 hj.1,
    guardG_frame k _ CAP g 182 195 j h195 hj.1,
    cmulS_external_frame k s g 180 181 6 7 182 183 j hj h182 h183]

/-- The product prefix computes `tcmul` and applies exactly its two output
guards. -/
theorem touchProductS_spec (k : Nat) (s : RegState) (g : Nat)
    (hg : CmulExternal g) (hg182 : g ≠ 182) (hg183 : g ≠ 183)
    (hg195 : g ≠ 195) (hs : ∀ j, s j < M) :
    let r := tcmul (s g) (s 180) (s 181) (s 6) (s 7) (s rViol)
    let f := srun k s (touchProductS g)
    f 182 = r.1 ∧ f 183 = r.2.1 ∧
      f rViol = tguard (s g) r.2.1 (tguard (s g) r.1 r.2.2) := by
  let m := srun k s (cmulS g 180 181 6 7 182 183)
  let u := srun k m (guardG CAP g 182 195)
  let f := srun k u (guardG CAP g 183 195)
  let r := tcmul (s g) (s 180) (s 181) (s 6) (s 7) (s rViol)
  have hc : ∀ x ∈ [g, 180, 181, 6, 7, 182, 183], CmulExternal x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg
    all_goals simp [CmulExternal, rViol]
  have hm := cmulS_spec k s g 180 181 6 7 182 183 hc (by decide) hs
  have mg : m g = s g :=
    cmulS_external_frame k s g 180 181 6 7 182 183 g hg hg182 hg183
  have hm182 : m 182 = r.1 := hm.1
  have hm183 : m 183 = r.2.1 := hm.2.1
  have hmv : m rViol = r.2.2 := hm.2.2
  have hmlt : ∀ j, m j < M := srun_lt_of_lt k _ s hs
  have huV := guardG_tguard k m g 182 195 (by simp [rViol]) hg195.symm hmlt
  change u rViol = tguard (m g) (m 182) (m rViol) at huV
  have ug : u g = m g := guardG_frame k m CAP g 182 195 g hg195 hg.1
  have u182 : u 182 = m 182 := guardG_frame k m CAP g 182 195 182
    (by decide) (by simp [rViol])
  have u183 : u 183 = m 183 := guardG_frame k m CAP g 182 195 183
    (by decide) (by simp [rViol])
  have hult : ∀ j, u j < M := srun_lt_of_lt k _ m hmlt
  have hfV := guardG_tguard k u g 183 195 (by simp [rViol]) hg195.symm hult
  change f rViol = tguard (u g) (u 183) (u rViol) at hfV
  have f182 : f 182 = u 182 := guardG_frame k u CAP g 183 195 182
    (by decide) (by simp [rViol])
  have f183 : f 183 = u 183 := guardG_frame k u CAP g 183 195 183
    (by decide) (by simp [rViol])
  simp only [touchProductS, srun_append]
  change f 182 = _ ∧ f 183 = _ ∧ f rViol = _
  constructor
  · exact f182.trans (u182.trans hm182)
  constructor
  · exact f183.trans (u183.trans hm183)
  · rw [hfV, ug, mg, u183, hm183, huV, mg, hm182, hmv]

/-- Four additions that form the two `2P + w²` endpoints. -/
def touchTermCalcS : List Instr :=
  [ .binop 184 .add (.reg 182) (.reg 182)
  , .binop 184 .add (.reg 184) (.reg 8)
  , .binop 185 .add (.reg 183) (.reg 183)
  , .binop 185 .add (.reg 185) (.reg 9) ]

/-- Scalar view of the term calculation and its two width guards. -/
def touchTermS (g : Nat) : List Instr :=
  touchTermCalcS ++ guardG CAP g 184 195 ++ guardG CAP g 185 195

theorem touchTermScalarBody_lift (c : Cfg) (g : Nat) :
    c.touchTermScalarBody g = lift (touchTermS g) := by
  simp only [Cfg.touchTermScalarBody, touchTermS, touchTermCalcS,
    guardBody_lift, lift, List.map_cons, List.map_nil, List.map_append]

theorem touchTermCalcS_spec (k : Nat) (s : RegState) :
    let f := srun k s touchTermCalcS
    f 184 = ((s 182 + s 182) % M + s 8) % M ∧
      f 185 = ((s 183 + s 183) % M + s 9) % M := by
  simp only [touchTermCalcS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, if_true, if_false, Nat.reduceEqDiff,
    true_and]

theorem touchTermCalcS_frame (k : Nat) (s : RegState) (j : Nat)
    (h184 : j ≠ 184) (h185 : j ≠ 185) :
    srun k s touchTermCalcS j = s j := by
  apply srun_untouched
  intro i hi
  simp only [touchTermCalcS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem touchTermS_frame (k : Nat) (s : RegState) (g j : Nat)
    (h184 : j ≠ 184) (h185 : j ≠ 185) (h195 : j ≠ 195)
    (hV : j ≠ rViol) : srun k s (touchTermS g) j = s j := by
  simp only [touchTermS, srun_append]
  rw [guardG_frame k _ CAP g 185 195 j h195 hV,
    guardG_frame k _ CAP g 184 195 j h195 hV,
    touchTermCalcS_frame k s j h184 h185]

/-- The term stage computes `ttouchTerm`. -/
theorem touchTermS_spec (k : Nat) (s : RegState) (g : Nat)
    (hg184 : g ≠ 184) (hg185 : g ≠ 185) (hg195 : g ≠ 195)
    (hgV : g ≠ rViol) (hs : ∀ j, s j < M) :
    let t := ttouchTerm (s g) (s 182) (s 183) (s 8) (s 9) (s rViol)
    let f := srun k s (touchTermS g)
    f 184 = t.1 ∧ f 185 = t.2.1 ∧ f rViol = t.2.2 := by
  let m := srun k s touchTermCalcS
  let u := srun k m (guardG CAP g 184 195)
  let f := srun k u (guardG CAP g 185 195)
  have hm := touchTermCalcS_spec k s
  have hm184 : m 184 = ((s 182 + s 182) % M + s 8) % M := hm.1
  have hm185 : m 185 = ((s 183 + s 183) % M + s 9) % M := hm.2
  have mg : m g = s g := touchTermCalcS_frame k s g hg184 hg185
  have mv : m rViol = s rViol := touchTermCalcS_frame k s rViol
    (by simp [rViol]) (by simp [rViol])
  have hmlt : ∀ j, m j < M := srun_lt_of_lt k _ s hs
  have huV := guardG_tguard k m g 184 195 (by simp [rViol]) hg195.symm hmlt
  change u rViol = tguard (m g) (m 184) (m rViol) at huV
  have ug : u g = m g := guardG_frame k m CAP g 184 195 g hg195 hgV
  have u184 : u 184 = m 184 := guardG_frame k m CAP g 184 195 184
    (by decide) (by simp [rViol])
  have u185 : u 185 = m 185 := guardG_frame k m CAP g 184 195 185
    (by decide) (by simp [rViol])
  have hult : ∀ j, u j < M := srun_lt_of_lt k _ m hmlt
  have hfV := guardG_tguard k u g 185 195 (by simp [rViol]) hg195.symm hult
  change f rViol = tguard (u g) (u 185) (u rViol) at hfV
  have f184 : f 184 = u 184 := guardG_frame k u CAP g 185 195 184
    (by decide) (by simp [rViol])
  have f185 : f 185 = u 185 := guardG_frame k u CAP g 185 195 185
    (by decide) (by simp [rViol])
  simp only [touchTermS, srun_append]
  change f 184 = _ ∧ f 185 = _ ∧ f rViol = _
  simp only [ttouchTerm]
  constructor
  · exact f184.trans (u184.trans hm184)
  constructor
  · exact f185.trans (u185.trans hm185)
  · rw [hfV, ug, mg, u185, hm185, huV, mg, hm184, mv]

/-- Total semantics and definedness of the single Möbius-code load. -/
theorem touchMuLoadBody_run (c : Cfg) (k : Nat) (st : AState) :
    arun k st c.touchMuLoadBody = st.writeReg 186 (st.arr (st.regs 194)) := rfl

theorem touchMuLoadBody_defined (c : Cfg) (k : Nat) (st : AState)
    (h : st.regs 194 < c.arrayLen) :
    AllDefined c.arrayLen k st c.touchMuLoadBody := ⟨h, trivial⟩

/-- Scalar arithmetic that forms the signed Möbius contribution. -/
def touchDeltaCalcS : List Instr :=
  [ .binop 187 .eq (.reg 186) (.lit 1)
  , .binop 188 .eq (.reg 186) (.lit 2)
  , .binop 196 .sub (.lit 0) (.reg 185)
  , .binop 197 .sub (.lit 0) (.reg 184)
  , .binop 189 .mul (.reg 187) (.reg 184)
  , .binop 198 .mul (.reg 188) (.reg 196)
  , .binop 189 .add (.reg 189) (.reg 198)
  , .binop 190 .mul (.reg 187) (.reg 185)
  , .binop 199 .mul (.reg 188) (.reg 197)
  , .binop 190 .add (.reg 190) (.reg 199)
  , .binop 10 .add (.reg 10) (.reg 189)
  , .binop 11 .add (.reg 11) (.reg 190) ]

def touchDeltaS (g : Nat) : List Instr :=
  touchDeltaCalcS ++ guardG CAP g 10 195 ++ guardG CAP g 11 195

theorem touchDeltaCalcBody_lift (c : Cfg) :
    c.touchDeltaCalcBody = lift touchDeltaCalcS := rfl

theorem touchDeltaBody_lift (c : Cfg) (g : Nat) :
    c.touchDeltaBody g = lift (touchDeltaS g) := by
  simp only [Cfg.touchDeltaBody, touchDeltaS, touchDeltaCalcBody_lift,
    guardBody_lift, lift, List.map_append]

theorem touchDeltaCalcS_spec (k : Nat) (s : RegState) (g : Nat) :
    let f := srun k s touchDeltaCalcS
    let d := ttouchDelta (s g) (s 186) (s 184) (s 185)
      (s 10) (s 11) (s rViol)
    f 10 = d.1 ∧ f 11 = d.2.1 := by
  have two_mod_M : (2 : Nat) % M = 2 := by decide
  simp only [touchDeltaCalcS, ttouchDelta, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, Option.getD_some, if_true,
    if_false, Nat.reduceEqDiff, one_mod_M, two_mod_M, zero_mod_M, tsub,
    bnat, true_and]

theorem touchDeltaCalcS_frame (k : Nat) (s : RegState) (j : Nat)
    (h187 : j ≠ 187) (h188 : j ≠ 188) (h196 : j ≠ 196)
    (h197 : j ≠ 197) (h189 : j ≠ 189) (h198 : j ≠ 198)
    (h190 : j ≠ 190) (h199 : j ≠ 199) (h10 : j ≠ 10)
    (h11 : j ≠ 11) : srun k s touchDeltaCalcS j = s j := by
  apply srun_untouched
  intro i hi
  simp only [touchDeltaCalcS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem touchDeltaS_frame (k : Nat) (s : RegState) (g j : Nat)
    (h187 : j ≠ 187) (h188 : j ≠ 188) (h196 : j ≠ 196)
    (h197 : j ≠ 197) (h189 : j ≠ 189) (h198 : j ≠ 198)
    (h190 : j ≠ 190) (h199 : j ≠ 199) (h10 : j ≠ 10)
    (h11 : j ≠ 11) (h195 : j ≠ 195) (hV : j ≠ rViol) :
    srun k s (touchDeltaS g) j = s j := by
  simp only [touchDeltaS, srun_append]
  rw [guardG_frame k _ CAP g 11 195 j h195 hV,
    guardG_frame k _ CAP g 10 195 j h195 hV,
    touchDeltaCalcS_frame k s j h187 h188 h196 h197 h189 h198 h190 h199 h10 h11]

/-- The delta stage computes `ttouchDelta`.  Live touch gates are registers
`214` and `218`, hence the compact `199 < g` freshness premise. -/
theorem touchDeltaS_spec (k : Nat) (s : RegState) (g : Nat) (hg : 199 < g)
    (hs : ∀ j, s j < M) :
    let d := ttouchDelta (s g) (s 186) (s 184) (s 185)
      (s 10) (s 11) (s rViol)
    let f := srun k s (touchDeltaS g)
    f 10 = d.1 ∧ f 11 = d.2.1 ∧ f rViol = d.2.2 := by
  let m := srun k s touchDeltaCalcS
  let u := srun k m (guardG CAP g 10 195)
  let f := srun k u (guardG CAP g 11 195)
  let d := ttouchDelta (s g) (s 186) (s 184) (s 185)
    (s 10) (s 11) (s rViol)
  have hm := touchDeltaCalcS_spec k s g
  have hm10 : m 10 = d.1 := hm.1
  have hm11 : m 11 = d.2.1 := hm.2
  have mg : m g = s g := touchDeltaCalcS_frame k s g (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have mv : m rViol = s rViol := touchDeltaCalcS_frame k s rViol
    (by simp [rViol]) (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
    (by simp [rViol]) (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
    (by simp [rViol]) (by simp [rViol])
  have hmlt : ∀ j, m j < M := srun_lt_of_lt k _ s hs
  have huV := guardG_tguard k m g 10 195 (by simp [rViol]) (by omega) hmlt
  change u rViol = tguard (m g) (m 10) (m rViol) at huV
  have ug : u g = m g := guardG_frame k m CAP g 10 195 g (by omega)
    (by simp [rViol]; omega)
  have u10 : u 10 = m 10 := guardG_frame k m CAP g 10 195 10
    (by decide) (by simp [rViol])
  have u11 : u 11 = m 11 := guardG_frame k m CAP g 10 195 11
    (by decide) (by simp [rViol])
  have hult : ∀ j, u j < M := srun_lt_of_lt k _ m hmlt
  have hfV := guardG_tguard k u g 11 195 (by simp [rViol]) (by omega) hult
  change f rViol = tguard (u g) (u 11) (u rViol) at hfV
  have f10 : f 10 = u 10 := guardG_frame k u CAP g 11 195 10
    (by decide) (by simp [rViol])
  have f11 : f 11 = u 11 := guardG_frame k u CAP g 11 195 11
    (by decide) (by simp [rViol])
  simp only [touchDeltaS, srun_append]
  change f 10 = _ ∧ f 11 = _ ∧ f rViol = _
  constructor
  · exact f10.trans (u10.trans hm10)
  constructor
  · exact f11.trans (u11.trans hm11)
  · rw [hfV, ug, mg, u11, hm11, huV, mg, hm10, mv]
    rfl

/-- The final two stores implement `ttouchStore` on the two saved plane
addresses. -/
theorem touchStoreBody_arr (c : Cfg) (k g : Nat) (st : AState)
    (hg196 : g ≠ 196) (hg197 : g ≠ 197) :
    let n := ttouchStore (st.regs g) (st.regs 180) (st.regs 181)
      (st.regs 6) (st.regs 7)
    (arun k st (c.touchStoreBody g)).arr =
      fun i => if i = st.regs 192 then n.2
        else if i = st.regs 191 then n.1 else st.arr i := by
  simp [Cfg.touchStoreBody, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, denoteOp, ttouchStore, hg196, hg197]

theorem touchStoreBody_regs_frame (c : Cfg) (k g j : Nat) (st : AState)
    (h196 : j ≠ 196) (h197 : j ≠ 197)
    (h198 : j ≠ 198) (h199 : j ≠ 199) :
    (arun k st (c.touchStoreBody g)).regs j = st.regs j := by
  simp [Cfg.touchStoreBody, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, denoteOp, h196, h197, h198, h199]

theorem touchStoreBody_defined (c : Cfg) (k g : Nat) (st : AState)
    (h191 : st.regs 191 < c.arrayLen) (h192 : st.regs 192 < c.arrayLen) :
    AllDefined c.arrayLen k st (c.touchStoreBody g) := by
  simp [Cfg.touchStoreBody, AllDefined, ADefined, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, h191, h192]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem touchBody_defined (c : Cfg) (k g dSlot : Nat) (st : AState)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2)
    (hA1 : c.touchA1 (st.regs g) (st.regs dSlot) < c.arrayLen)
    (hA2 : c.touchA2 (st.regs g) (st.regs dSlot) < c.arrayLen)
    (hBase : c.touchBase (st.regs g) (st.regs dSlot) < c.arrayLen) :
    AllDefined c.arrayLen k st (c.touchBody g dSlot) := by
  let L := touchLoadState c g dSlot st
  let P : AState := ⟨srun k L.regs (touchProductS g), L.arr⟩
  let T0 : AState := ⟨srun k P.regs (touchTermS g), P.arr⟩
  let T := T0.writeReg 186 (T0.arr (T0.regs 194))
  let D : AState := ⟨srun k T.regs (touchDeltaS g), T.arr⟩
  let base := c.touchBase (st.regs g) (st.regs dSlot)
  let a1 := c.touchA1 (st.regs g) (st.regs dSlot)
  let a2 := c.touchA2 (st.regs g) (st.regs dSlot)
  have hL : arun k st (c.touchLoadBody g dSlot) = L :=
    touchLoadBody_run c k g dSlot st hP1 hP2
  have hLbase : L.regs 194 = base := by rfl
  have hLa1 : L.regs 191 = a1 := by rfl
  have hLa2 : L.regs 192 = a2 := by rfl
  have hP194 : P.regs 194 = L.regs 194 :=
    touchProductS_external_frame k L.regs g 194 (by simp [CmulExternal, rViol])
      (by omega) (by omega) (by omega)
  have hP191 : P.regs 191 = L.regs 191 :=
    touchProductS_external_frame k L.regs g 191 (by simp [CmulExternal, rViol])
      (by omega) (by omega) (by omega)
  have hP192 : P.regs 192 = L.regs 192 :=
    touchProductS_external_frame k L.regs g 192 (by simp [CmulExternal, rViol])
      (by omega) (by omega) (by omega)
  have hT0frame (j : Nat) (h184 : j ≠ 184) (h185 : j ≠ 185)
      (h195 : j ≠ 195) (hV : j ≠ rViol) : T0.regs j = P.regs j :=
    touchTermS_frame k P.regs g j h184 h185 h195 hV
  have hT0194 : T0.regs 194 = L.regs 194 :=
    (hT0frame 194 (by omega) (by omega) (by omega) (by simp [rViol])).trans hP194
  have hT0191 : T0.regs 191 = L.regs 191 :=
    (hT0frame 191 (by omega) (by omega) (by omega) (by simp [rViol])).trans hP191
  have hT0192 : T0.regs 192 = L.regs 192 :=
    (hT0frame 192 (by omega) (by omega) (by omega) (by simp [rViol])).trans hP192
  have hT191 : T.regs 191 = L.regs 191 := by
    simpa [T, AState.writeReg] using hT0191
  have hT192 : T.regs 192 = L.regs 192 := by
    simpa [T, AState.writeReg] using hT0192
  have hDframe (j : Nat) (h187 : j ≠ 187) (h188 : j ≠ 188)
      (h196 : j ≠ 196) (h197 : j ≠ 197) (h189 : j ≠ 189)
      (h198 : j ≠ 198) (h190 : j ≠ 190) (h199 : j ≠ 199)
      (h10 : j ≠ 10) (h11 : j ≠ 11) (h195 : j ≠ 195)
      (hV : j ≠ rViol) : D.regs j = T.regs j :=
    touchDeltaS_frame k T.regs g j h187 h188 h196 h197 h189 h198 h190 h199
      h10 h11 h195 hV
  have hD191 : D.regs 191 = L.regs 191 :=
    (hDframe 191 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [rViol])).trans hT191
  have hD192 : D.regs 192 = L.regs 192 :=
    (hDframe 192 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [rViol])).trans hT192
  rw [show c.touchBody g dSlot = c.touchLoadBody g dSlot ++
      (c.touchProductBody g ++ (c.touchTermBody g ++
        (c.touchDeltaBody g ++ c.touchStoreBody g))) from by
      simp [Cfg.touchBody, List.append_assoc], AllDefined_append]
  refine ⟨touchLoadBody_defined c k g dSlot st hP1 hP2 hA1 hA2, ?_⟩
  rw [hL, AllDefined_append]
  refine ⟨touchProductBody_defined c c.arrayLen k g L, ?_⟩
  rw [touchProductBody_lift, arun_lift, AllDefined_append]
  refine ⟨?_, ?_⟩
  · rw [Cfg.touchTermBody, AllDefined_append]
    refine ⟨?_, ?_⟩
    · exact allDefined_lift_of_noDiv c.arrayLen k (touchTermS g) P (by rfl)
    rw [touchTermScalarBody_lift, arun_lift]
    apply touchMuLoadBody_defined
    rw [hT0194, hLbase]
    exact hBase
  rw [Cfg.touchTermBody, arun_append, touchTermScalarBody_lift, arun_lift,
    touchMuLoadBody_run, AllDefined_append]
  refine ⟨?_, ?_⟩
  · exact allDefined_lift_of_noDiv c.arrayLen k (touchDeltaS g) T (by rfl)
  rw [touchDeltaBody_lift, arun_lift]
  apply touchStoreBody_defined
  · rw [hD191, hLa1]
    exact hA1
  · rw [hD192, hLa2]
    exact hA2



/-- Read the persistent machine registers and array as the transparent state. -/
def obsT (st : AState) : TState :=
  { viol := st.regs rViol
    res := st.regs 2
    sq := st.regs 3
    par := st.regs 4
    sigma := st.regs 5
    wLo := st.regs 6
    wHi := st.regs 7
    wwLo := st.regs 8
    wwHi := st.regs 9
    dLo := st.regs 10
    dHi := st.regs 11
    gLo := st.regs 12
    gHi := st.regs 13
    arr := st.arr }

/-- Selector decoding writes only scratch registers `20`--`39`, so the
persistent transparent observation is unchanged. -/
theorem selBody_obs (c : Cfg) (idx : Nat) (st : AState) :
    obsT (arun idx st c.selBody) = obsT st := by
  rw [selBody_lift, arun_lift]
  change
    ({ viol := srun idx st.regs (selS c) rViol,
       res := srun idx st.regs (selS c) 2,
       sq := srun idx st.regs (selS c) 3,
       par := srun idx st.regs (selS c) 4,
       sigma := srun idx st.regs (selS c) 5,
       wLo := srun idx st.regs (selS c) 6,
       wHi := srun idx st.regs (selS c) 7,
       wwLo := srun idx st.regs (selS c) 8,
       wwHi := srun idx st.regs (selS c) 9,
       dLo := srun idx st.regs (selS c) 10,
       dHi := srun idx st.regs (selS c) 11,
       gLo := srun idx st.regs (selS c) 12,
       gHi := srun idx st.regs (selS c) 13, arr := st.arr } : TState) = obsT st
  simp only [obsT, TState.mk.injEq]
  exact ⟨selS_frame c idx st.regs rViol (by simp [rViol]),
    selS_frame c idx st.regs 2 (by omega),
    selS_frame c idx st.regs 3 (by omega),
    selS_frame c idx st.regs 4 (by omega),
    selS_frame c idx st.regs 5 (by omega),
    selS_frame c idx st.regs 6 (by omega),
    selS_frame c idx st.regs 7 (by omega),
    selS_frame c idx st.regs 8 (by omega),
    selS_frame c idx st.regs 9 (by omega),
    selS_frame c idx st.regs 10 (by omega),
    selS_frame c idx st.regs 11 (by omega),
    selS_frame c idx st.regs 12 (by omega),
    selS_frame c idx st.regs 13 (by omega), trivial⟩

theorem trialBody_obs (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M)
    (h20 : st.regs 20 = z.inP1) (h24 : st.regs 24 = z.n1)
    (h25 : st.regs 25 = z.d1) (h26 : st.regs 26 = z.isD0)
    (h27 : st.regs 27 = z.isDL)
    (hP1 : z.inP1 ≤ 1) (hD0 : z.isD0 ≤ 1)
    (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) (hd : z.d1 ≠ 0) :
    obsT (arun k st trialBody) = ttrial z (obsT st) := by
  let f := srun k st.regs trialS
  have hf := trialS_spec k st.regs z (obsT st) hs rfl rfl rfl h20 h24 h25 h26
    h27 hP1 hD0 hSq hPar hd
  dsimp only at hf
  rcases hf with ⟨hf2, hf3, hf4, hf52, hf53⟩
  change f 2 = _ at hf2
  change f 3 = _ at hf3
  change f 4 = _ at hf4
  change f 52 = _ at hf52
  change f 53 = _ at hf53
  rw [trialBody, arun_append, trialScalarBody_lift, arun_lift]
  change obsT (arun k ({ regs := f, arr := st.arr } : AState) [.store 52 53]) = _
  simp only [arun, astep, AState.writeArr]
  change
    ({ viol := f rViol, res := f 2, sq := f 3, par := f 4,
       sigma := f 5, wLo := f 6, wHi := f 7, wwLo := f 8, wwHi := f 9,
       dLo := f 10, dHi := f 11, gLo := f 12, gHi := f 13,
       arr := fun i => if i = f 52 then f 53 else st.arr i } : TState) = _
  rw [TState.mk.injEq]
  simp only [hf2, hf3, hf4, hf52, hf53, true_and, ttrial, obsT]
  constructor
  · exact trialS_frame k st.regs rViol (by simp [rViol])
  constructor
  · exact trialS_frame k st.regs 5 (by omega)
  constructor
  · exact trialS_frame k st.regs 6 (by omega)
  constructor
  · exact trialS_frame k st.regs 7 (by omega)
  constructor
  · exact trialS_frame k st.regs 8 (by omega)
  constructor
  · exact trialS_frame k st.regs 9 (by omega)
  constructor
  · exact trialS_frame k st.regs 10 (by omega)
  constructor
  · exact trialS_frame k st.regs 11 (by omega)
  constructor
  · exact trialS_frame k st.regs 12 (by omega)
  constructor
  · exact trialS_frame k st.regs 13 (by omega)
  rfl

theorem passABody_obs (k : Nat) (st : AState) (z : TSel)
    (hs : ∀ j, st.regs j < M) (h1 : st.regs 1 = 0)
    (h21 : st.regs 21 = z.inP2) (h30 : st.regs 30 = z.pX)
    (h31 : st.regs 31 = z.X) (h32 : st.regs 32 = z.inA)
    (h36 : st.regs 36 = z.rA) (hP2 : z.inP2 ≤ 1) (hrA : z.rA ≠ 0) :
    obsT (arun k st passABody) = tpassA z (obsT st) := by
  let f := srun k st.regs passAS
  have hf := passAS_spec k st.regs z (obsT st) hs h1 rfl h21 h30 h31 h32 h36
    hP2 hrA
  change f 5 = (tpassA z (obsT st)).sigma at hf
  rw [passABody_lift, arun_lift]
  change
    ({ viol := f rViol, res := f 2, sq := f 3, par := f 4,
       sigma := f 5, wLo := f 6, wHi := f 7, wwLo := f 8, wwHi := f 9,
       dLo := f 10, dHi := f 11, gLo := f 12, gHi := f 13,
       arr := st.arr } : TState) = tpassA z (obsT st)
  rw [TState.mk.injEq]
  simp only [hf, true_and, tpassA, obsT]
  exact ⟨passAS_frame k st.regs rViol (by simp [rViol]),
    passAS_frame k st.regs 2 (by omega), passAS_frame k st.regs 3 (by omega),
    passAS_frame k st.regs 4 (by omega), passAS_frame k st.regs 6 (by omega),
    passAS_frame k st.regs 7 (by omega), passAS_frame k st.regs 8 (by omega),
    passAS_frame k st.regs 9 (by omega), passAS_frame k st.regs 10 (by omega),
    passAS_frame k st.regs 11 (by omega), passAS_frame k st.regs 12 (by omega),
    passAS_frame k st.regs 13 (by omega), trivial⟩

set_option maxRecDepth 2000 in
theorem touchBody_obs (c : Cfg) (k g dSlot : Nat) (st : AState)
    (hg : 199 < g)
    (hP1 : c.plane1 % M = c.plane1)
    (hP2 : c.plane2 % M = c.plane2)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M) :
    obsT (arun k st (c.touchBody g dSlot)) =
      c.ttouch (st.regs g) (st.regs dSlot) (obsT st) := by
  let L := touchLoadState c g dSlot st
  let P : AState := ⟨srun k L.regs (touchProductS g), L.arr⟩
  let T0 : AState := ⟨srun k P.regs (touchTermS g), P.arr⟩
  let T := T0.writeReg 186 (T0.arr (T0.regs 194))
  let D : AState := ⟨srun k T.regs (touchDeltaS g), T.arr⟩
  let S := arun k D (c.touchStoreBody g)
  let a1 := c.touchA1 (st.regs g) (st.regs dSlot)
  let a2 := c.touchA2 (st.regs g) (st.regs dSlot)
  let base := c.touchBase (st.regs g) (st.regs dSlot)
  let r := tcmul (st.regs g) (st.arr a1) (st.arr a2)
    (st.regs 6) (st.regs 7) (st.regs rViol)
  let pViol := ttouchProductViol (st.regs g) r.1 r.2.1 r.2.2
  let term := ttouchTerm (st.regs g) r.1 r.2.1
    (st.regs 8) (st.regs 9) pViol
  let delta := ttouchDelta (st.regs g) (st.arr base) term.1 term.2.1
    (st.regs 10) (st.regs 11) term.2.2
  let stored := ttouchStore (st.regs g) (st.arr a1) (st.arr a2)
    (st.regs 6) (st.regs 7)
  have hL : arun k st (c.touchLoadBody g dSlot) = L :=
    touchLoadBody_run c k g dSlot st hP1 hP2
  have hbody : arun k st (c.touchBody g dSlot) = S := by
    simp only [Cfg.touchBody, arun_append, hL, Cfg.touchTermBody]
    rw [touchProductBody_lift, arun_lift, touchTermScalarBody_lift, arun_lift,
      touchMuLoadBody_run, touchDeltaBody_lift, arun_lift]
  have hLarr : L.arr = st.arr := by rfl
  have hLbase : L.regs 194 = base := by rfl
  have hLa1 : L.regs 191 = a1 := by rfl
  have hLa2 : L.regs 192 = a2 := by rfl
  have hLaLo : L.regs 180 = st.arr a1 := by rfl
  have hLaHi : L.regs 181 = st.arr a2 := by rfl
  have hLframe (j : Nat) (hj : j ≠ 180) (hj181 : j ≠ 181)
      (hj191 : j ≠ 191) (hj192 : j ≠ 192) (hj194 : j ≠ 194) :
      L.regs j = st.regs j := by
    simp [L, touchLoadState, AState.writeReg, hj, hj181, hj191, hj192, hj194]
  have hLg : L.regs g = st.regs g :=
    hLframe g (by omega) (by omega) (by omega) (by omega) (by omega)
  have hLlt : ∀ j, L.regs j < M := by
    rw [← hL]
    exact (arun_lt k _ st hs harr).1
  have hps := touchProductS_spec k L.regs g
    (by simp [CmulExternal, rViol]; omega) (by omega) (by omega) (by omega) hLlt
  have hP182 : P.regs 182 = r.1 := by
    simpa [P, r, hLg, hLaLo, hLaHi, hLframe 6 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe 7 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol]) (by simp [rViol])] using hps.1
  have hP183 : P.regs 183 = r.2.1 := by
    simpa [P, r, hLg, hLaLo, hLaHi, hLframe 6 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe 7 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol]) (by simp [rViol])] using hps.2.1
  have hPV : P.regs rViol = pViol := by
    simpa [P, r, hLg, hLaLo, hLaHi, hLframe 6 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe 7 (by omega) (by omega) (by omega)
      (by omega) (by omega), hLframe rViol (by simp [rViol]) (by simp [rViol])
      (by simp [rViol]) (by simp [rViol]) (by simp [rViol]),
      pViol, ttouchProductViol] using hps.2.2
  have hPframe (j : Nat) (hj : CmulExternal j) (h182 : j ≠ 182)
      (h183 : j ≠ 183) (h195 : j ≠ 195) : P.regs j = L.regs j :=
    touchProductS_external_frame k L.regs g j hj h182 h183 h195
  have hPlt : ∀ j, P.regs j < M := srun_lt_of_lt k _ L.regs hLlt
  have hts := touchTermS_spec k P.regs g (by omega) (by omega) (by omega)
    (by simp [rViol]; omega) hPlt
  have hT0184 : T0.regs 184 = term.1 := by
    simpa [T0, term, hP182, hP183, hPV,
      hPframe 8 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe 9 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe g (by simp [CmulExternal, rViol]; omega) (by omega) (by omega) (by omega),
      hLframe 8 (by omega) (by omega) (by omega) (by omega) (by omega),
      hLframe 9 (by omega) (by omega) (by omega) (by omega) (by omega), hLg] using hts.1
  have hT0185 : T0.regs 185 = term.2.1 := by
    simpa [T0, term, hP182, hP183, hPV,
      hPframe 8 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe 9 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe g (by simp [CmulExternal, rViol]; omega) (by omega) (by omega) (by omega),
      hLframe 8 (by omega) (by omega) (by omega) (by omega) (by omega),
      hLframe 9 (by omega) (by omega) (by omega) (by omega) (by omega), hLg] using hts.2.1
  have hT0V : T0.regs rViol = term.2.2 := by
    simpa [T0, term, hP182, hP183, hPV,
      hPframe 8 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe 9 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hPframe g (by simp [CmulExternal, rViol]; omega) (by omega) (by omega) (by omega),
      hLframe 8 (by omega) (by omega) (by omega) (by omega) (by omega),
      hLframe 9 (by omega) (by omega) (by omega) (by omega) (by omega), hLg] using hts.2.2
  have hT0frame (j : Nat) (h184 : j ≠ 184) (h185 : j ≠ 185)
      (h195 : j ≠ 195) (hV : j ≠ rViol) : T0.regs j = P.regs j :=
    touchTermS_frame k P.regs g j h184 h185 h195 hV
  have hTframe (j : Nat) (h186 : j ≠ 186) : T.regs j = T0.regs j := by
    simp [T, AState.writeReg, h186]
  have hTarr : T.arr = st.arr := by rfl
  have hTg : T.regs g = st.regs g := by
    rw [hTframe g (by omega), hT0frame g (by omega) (by omega) (by omega)
      (by simp [rViol]; omega), hPframe g (by simp [CmulExternal, rViol]; omega)
      (by omega) (by omega) (by omega), hLg]
  have hT184 : T.regs 184 = term.1 := by
    rw [hTframe 184 (by omega), hT0184]
  have hT185 : T.regs 185 = term.2.1 := by
    rw [hTframe 185 (by omega), hT0185]
  have hTV : T.regs rViol = term.2.2 := by
    rw [hTframe rViol (by simp [rViol]), hT0V]
  have hTbase : T.regs 186 = st.arr base := by
    simp only [T, AState.writeReg, if_pos]
    rw [hT0frame 194 (by omega) (by omega) (by omega) (by simp [rViol]),
      hPframe 194 (by simp [CmulExternal, rViol]) (by omega) (by omega) (by omega),
      hLbase]
    rfl
  have hT10 : T.regs 10 = st.regs 10 := by
    rw [hTframe 10 (by omega), hT0frame 10 (by omega) (by omega) (by omega)
      (by simp [rViol]), hPframe 10 (by simp [CmulExternal, rViol]) (by omega)
      (by omega) (by omega), hLframe 10 (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  have hT11 : T.regs 11 = st.regs 11 := by
    rw [hTframe 11 (by omega), hT0frame 11 (by omega) (by omega) (by omega)
      (by simp [rViol]), hPframe 11 (by simp [CmulExternal, rViol]) (by omega)
      (by omega) (by omega), hLframe 11 (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  have hTlt : ∀ j, T.regs j < M := by
    intro j
    simp only [T, AState.writeReg]
    split
    · exact harr _
    · exact srun_lt_of_lt k _ P.regs hPlt j
  have hds := touchDeltaS_spec k T.regs g hg hTlt
  have hD10 : D.regs 10 = delta.1 := by
    simpa [D, delta, hTg, hTbase, hT184, hT185, hT10, hT11, hTV] using hds.1
  have hD11 : D.regs 11 = delta.2.1 := by
    simpa [D, delta, hTg, hTbase, hT184, hT185, hT10, hT11, hTV] using hds.2.1
  have hDV : D.regs rViol = delta.2.2 := by
    simpa [D, delta, hTg, hTbase, hT184, hT185, hT10, hT11, hTV] using hds.2.2
  have hDfromL (j : Nat) (hj : CmulExternal j)
      (h10 : j ≠ 10) (h11 : j ≠ 11) (hV : j ≠ rViol)
      (h182 : j ≠ 182) (h183 : j ≠ 183) (h184 : j ≠ 184)
      (h185 : j ≠ 185) (h186 : j ≠ 186) (h187 : j ≠ 187)
      (h188 : j ≠ 188) (h189 : j ≠ 189) (h190 : j ≠ 190)
      (h195 : j ≠ 195) (h196 : j ≠ 196) (h197 : j ≠ 197)
      (h198 : j ≠ 198) (h199 : j ≠ 199) : D.regs j = L.regs j := by
    exact (touchDeltaS_frame k T.regs g j h187 h188 h196 h197 h189 h198
      h190 h199 h10 h11 h195 hV).trans ((hTframe j h186).trans
        ((hT0frame j h184 h185 h195 hV).trans
          (hPframe j hj h182 h183 h195)))
  have hD191 : D.regs 191 = a1 := by
    rw [hDfromL 191 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLa1]
  have hD192 : D.regs 192 = a2 := by
    rw [hDfromL 192 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLa2]
  have hD180 : D.regs 180 = st.arr a1 := by
    rw [hDfromL 180 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLaLo]
  have hD181 : D.regs 181 = st.arr a2 := by
    rw [hDfromL 181 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLaHi]
  have hD6 : D.regs 6 = st.regs 6 := by
    rw [hDfromL 6 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLframe 6 (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  have hD7 : D.regs 7 = st.regs 7 := by
    rw [hDfromL 7 (by simp [CmulExternal, rViol]) (by omega) (by omega)
      (by simp [rViol]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hLframe 7 (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  have hDg : D.regs g = st.regs g := by
    rw [hDfromL g (by simp [CmulExternal, rViol]; omega) (by omega) (by omega)
      (by simp [rViol]; omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hLg]
  have hDarr : D.arr = st.arr := by rfl
  have hSarr : S.arr = fun i => if i = a2 then stored.2
      else if i = a1 then stored.1 else st.arr i := by
    have h := touchStoreBody_arr c k g D (by omega) (by omega)
    change S.arr = _ at h
    simpa [stored, hD191, hD192, hD180, hD181, hD6, hD7, hDg, hDarr] using h
  have hSframe (j : Nat) (h196 : j ≠ 196) (h197 : j ≠ 197)
      (h198 : j ≠ 198) (h199 : j ≠ 199) : S.regs j = D.regs j :=
    touchStoreBody_regs_frame c k g j D h196 h197 h198 h199
  have hSV : S.regs rViol = delta.2.2 :=
    (hSframe rViol (by simp [rViol]) (by simp [rViol]) (by simp [rViol])
      (by simp [rViol])).trans hDV
  have hS10 : S.regs 10 = delta.1 :=
    (hSframe 10 (by omega) (by omega) (by omega) (by omega)).trans hD10
  have hS11 : S.regs 11 = delta.2.1 :=
    (hSframe 11 (by omega) (by omega) (by omega) (by omega)).trans hD11
  have hSst (j : Nat) (hj : j ∈ [2, 3, 4, 5, 6, 7, 8, 9, 12, 13]) :
      S.regs j = st.regs j := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hSframe _ (by omega) (by omega) (by omega) (by omega),
        hDfromL _ (by simp [CmulExternal, rViol]) (by omega) (by omega)
          (by simp [rViol]) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega),
        hLframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  rw [hbody]
  change
    ({ viol := S.regs rViol, res := S.regs 2, sq := S.regs 3, par := S.regs 4,
       sigma := S.regs 5, wLo := S.regs 6, wHi := S.regs 7,
       wwLo := S.regs 8, wwHi := S.regs 9, dLo := S.regs 10, dHi := S.regs 11,
       gLo := S.regs 12, gHi := S.regs 13, arr := S.arr } : TState) =
    { viol := delta.2.2, res := st.regs 2, sq := st.regs 3, par := st.regs 4,
      sigma := st.regs 5, wLo := st.regs 6, wHi := st.regs 7,
      wwLo := st.regs 8, wwHi := st.regs 9, dLo := delta.1, dHi := delta.2.1,
      gLo := st.regs 12, gHi := st.regs 13,
      arr := fun i => if i = a2 then stored.2 else if i = a1 then stored.1 else st.arr i }
  rw [TState.mk.injEq]
  exact ⟨hSV, hSst 2 (by simp), hSst 3 (by simp), hSst 4 (by simp),
    hSst 5 (by simp), hSst 6 (by simp), hSst 7 (by simp), hSst 8 (by simp),
    hSst 9 (by simp), hS10, hS11, hSst 12 (by simp), hSst 13 (by simp), hSarr⟩

/-- The three-instruction seed block is defined and reaches `tInit`. -/
theorem init_reaches_tInit (c : Cfg) (h1 : 1 < c.arrayLen) :
    AllDefined c.arrayLen 0 initialAState c.init ∧
      obsT (arun 0 initialAState c.init) = tInit := by
  constructor <;>
    simp [Cfg.init, storeLit, AllDefined, ADefined, obsT, tInit, arun, astep,
      initialAState, AState.writeReg, AState.writeArr, sdest, sval,
      denoteOperand, initialState, rViol, one_mod_M, h1]

/-! ## §4 Admissibility

The arithmetic side conditions under which the machine is expected to
denote the transparent model.  Each one rules out a specific `u64` wrap or
a specific undefined operation; none of them is about the mathematics of
the sweep.  They are the `Admissible` predicate that
`AProgramRefinement.ofDenotationOn` demands the decoder reject the
complement of.
-/

/-- `Nat.sqrt` never grows its argument. -/
theorem sqrt_le_self (n : Nat) : Nat.sqrt n ≤ n := by
  have h := Nat.sqrt_le n
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | h0
  · omega
  · have h1 : Nat.sqrt n * 1 ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul_left _ h0
    omega

theorem p_pos (c : Cfg) : 0 < c.p := by
  show 0 < 2 * c.s + 2
  omega

/-- The configuration's arithmetic side conditions. -/
structure Admissible (c : Cfg) : Prop where
  /-- There is at least one candidate beyond the `μ(1)` seed. -/
  capPos : 2 ≤ c.cap
  /-- `selBody` divides by `c.rounds`. -/
  roundsPos : 0 < c.rounds
  /-- Every array index the body forms stays a `Nat` below the word size,
  so the compiled `u64` address arithmetic is the mathematical one. -/
  arrayLt : c.arrayLen < M
  /-- The loop index does not wrap. -/
  loopLt : c.loopCount < M
  /-- The lower-check literal is represented without word reduction. -/
  checkLoLt : c.checkLo < M

/-- The selector-stage bounds supplied by admissibility and a live loop
index. -/
theorem Admissible.selBounds (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) :
    idx < M ∧ c.rounds ≠ 0 ∧ c.rounds < M ∧ c.p < M ∧
      c.phase1 < M ∧ 2 * c.s + 2 < M := by
  have hcap1 : 1 ≤ c.cap := Nat.le_trans (by decide) hc.capPos
  have hcapm1 : 1 ≤ c.cap - 1 := by
    have hcap2 := hc.capPos
    omega
  have hRle : c.rounds ≤ (c.cap - 1) * c.rounds := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.rounds hcapm1
  have hPle : c.p ≤ c.cap * c.p := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.p hcap1
  have hPhase : c.phase1 ≤ c.loopCount := by
    simp only [Cfg.loopCount]
    exact Nat.le_add_right _ _
  have hTail : c.cap * c.p ≤ c.loopCount := by
    simp only [Cfg.loopCount]
    exact Nat.le_add_left _ _
  refine ⟨Nat.lt_trans hidx hc.loopLt, Nat.ne_of_gt hc.roundsPos,
    Nat.lt_of_le_of_lt (Nat.le_trans hRle hPhase) hc.loopLt,
    Nat.lt_of_le_of_lt (Nat.le_trans hPle hTail) hc.loopLt,
    Nat.lt_of_le_of_lt hPhase hc.loopLt, ?_⟩
  change c.p < M
  exact Nat.lt_of_le_of_lt (Nat.le_trans hPle hTail) hc.loopLt

theorem Admissible.trialFacts (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) :
    let z := c.tsel idx
    z.inP1 ≤ 1 ∧ z.isD0 ≤ 1 ∧ z.isDL ≤ 1 ∧ z.d1 ≠ 0 ∧
      z.isDL * z.n1 % M < c.arrayLen := by
  have hsel := Admissible.selBounds c hc idx hidx
  rcases hsel with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hRpos : 0 < c.rounds := Nat.pos_of_ne_zero hR0
  have hcapm1 : 1 ≤ c.cap - 1 := by have := hc.capPos; omega
  have hRle : c.rounds ≤ c.phase1 := by
    change c.rounds ≤ (c.cap - 1) * c.rounds
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.rounds hcapm1
  have htailPos : 0 < c.cap * c.p := Nat.mul_pos (by omega) (p_pos c)
  have hPhSucc : c.phase1 + 1 ≤ c.loopCount := by
    simp only [Cfg.loopCount]
    omega
  have hRsuccM : c.rounds + 1 < M := by
    have := hc.loopLt
    omega
  have hr : idx % c.rounds < c.rounds := Nat.mod_lt _ hRpos
  have hDlt : idx % c.rounds + 2 < M := by omega
  have hDmod : (idx % c.rounds + 2) % M = idx % c.rounds + 2 :=
    Nat.mod_eq_of_lt hDlt
  have hDnz : (idx % c.rounds + 2) % M ≠ 0 := by omega
  have hP1bit : bnat (idx < c.phase1) ≤ 1 := bnat_le_one _
  have hD0bit : bnat (idx % c.rounds = 0) * bnat (idx < c.phase1) ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (bnat_le_one _) hP1bit
  have hDLbit : bnat (idx % c.rounds = c.rounds - 1) *
      bnat (idx < c.phase1) ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (bnat_le_one _) hP1bit
  have hzeroArr : 0 < c.arrayLen := by simp [Cfg.arrayLen]
  refine ⟨hP1bit, hD0bit, hDLbit, hDnz, ?_⟩
  by_cases hp : idx < c.phase1
  · have hq : idx / c.rounds < c.cap - 1 :=
      (Nat.div_lt_iff_lt_mul hRpos).mpr hp
    have hcapArr : c.cap < c.arrayLen := by simp [Cfg.arrayLen]; omega
    have hn : idx / c.rounds + 2 < c.arrayLen := by omega
    have hnM : idx / c.rounds + 2 < M := Nat.lt_trans hn hc.arrayLt
    have hnmod : (idx / c.rounds + 2) % M = idx / c.rounds + 2 :=
      Nat.mod_eq_of_lt hnM
    by_cases hl : idx % c.rounds = c.rounds - 1
    · simpa [Cfg.tsel, hp, hl, bnat, hnmod] using hn
    · simp [Cfg.tsel, hp, hl, bnat, hzeroArr]
  · simp [Cfg.tsel, hp, bnat, hzeroArr]

theorem selTrial_obs (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState) (hs : ∀ j, st.regs j < M)
    (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) :
    obsT (arun idx st (c.selBody ++ trialBody)) =
      ttrial (c.tsel idx) (obsT st) := by
  let S := arun idx st c.selBody
  let z := c.tsel idx
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 20 = z.inP1 at hz20
  change srun idx st.regs (selS c) 24 = z.n1 at hz24
  change srun idx st.regs (selS c) 25 = z.d1 at hz25
  change srun idx st.regs (selS c) 26 = z.isD0 at hz26
  change srun idx st.regs (selS c) 27 = z.isDL at hz27
  have hfacts := Admissible.trialFacts c hc idx hidx
  dsimp only at hfacts
  rcases hfacts with ⟨hP1, hD0, hDL, hdnz, haddr⟩
  have hSregs : S.regs = srun idx st.regs (selS c) := by
    simp [S, selBody_lift, arun_lift]
  have hSlt : ∀ j, S.regs j < M := by
    rw [hSregs]
    exact srun_lt_of_lt idx _ st.regs hs
  have hS20 : S.regs 20 = z.inP1 := by rw [hSregs]; exact hz20
  have hS24 : S.regs 24 = z.n1 := by rw [hSregs]; exact hz24
  have hS25 : S.regs 25 = z.d1 := by rw [hSregs]; exact hz25
  have hS26 : S.regs 26 = z.isD0 := by rw [hSregs]; exact hz26
  have hS27 : S.regs 27 = z.isDL := by rw [hSregs]; exact hz27
  have hS3 : S.regs 3 ≤ 1 := by
    rw [hSregs, selS_frame c idx st.regs 3 (by omega)]
    exact hSq
  have hS4 : S.regs 4 ≤ 1 := by
    rw [hSregs, selS_frame c idx st.regs 4 (by omega)]
    exact hPar
  have ht := trialBody_obs idx S z hSlt hS20 hS24 hS25 hS26 hS27 hP1 hD0
    hS3 hS4 hdnz
  have hSelObs : obsT S = obsT st := by
    exact selBody_obs c idx st
  rw [hSelObs] at ht
  rw [arun_append]
  exact ht

theorem selTrial_defined (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState) :
    AllDefined c.arrayLen idx st (c.selBody ++ trialBody) := by
  rw [AllDefined_append]
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  constructor
  · exact selBody_defined c c.arrayLen idx st hR0 hRM hPM
  let S := arun idx st c.selBody
  let z := c.tsel idx
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 24 = z.n1 at hz24
  change srun idx st.regs (selS c) 25 = z.d1 at hz25
  change srun idx st.regs (selS c) 27 = z.isDL at hz27
  have hfacts := Admissible.trialFacts c hc idx hidx
  dsimp only at hfacts
  rcases hfacts with ⟨hP1, hD0, hDL, hdnz, haddr⟩
  have hSregs : S.regs = srun idx st.regs (selS c) := by
    simp [S, selBody_lift, arun_lift]
  apply trialBody_defined
  · rw [hSregs, hz25]
    exact hdnz
  · rw [hSregs, hz27, hz24]
    exact haddr

theorem Admissible.passAFacts (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) :
    let z := c.tsel idx
    z.inP2 ≤ 1 ∧ z.rA ≠ 0 := by
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hp0 : c.p ≠ 0 := by simp [Cfg.p]
  let b2 := tsub idx c.phase1
  let pX := b2 % c.p
  have hpX : pX < c.p := Nat.mod_lt _ (Nat.pos_of_ne_zero hp0)
  have hpXM : pX + 1 < M := by omega
  have hpXmod : (pX + 1) % M = pX + 1 := Nat.mod_eq_of_lt hpXM
  constructor
  · simp only [Cfg.tsel]
    have := bnat_le_one (idx < c.phase1)
    omega
  · change (pX + 1) % M ≠ 0
    rw [hpXmod]
    omega

open LeanCompCert.Ports.Section413G2Program

theorem trialBody_regs_frame (k : Nat) (st : AState) (j : Nat)
    (hj : j < 2 ∨ (4 < j ∧ j < 40) ∨ 53 < j) :
    (arun k st trialBody).regs j = st.regs j := by
  rw [trialBody, arun_append, trialScalarBody_lift, arun_lift]
  simp only [arun, astep]
  exact trialS_frame k st.regs j hj

theorem selTrialPassA_obs (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState) (hs : ∀ j, st.regs j < M)
    (h1 : st.regs 1 = 0) (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) :
    obsT (arun idx st ((c.selBody ++ trialBody) ++ passABody)) =
      tpassA (c.tsel idx) (ttrial (c.tsel idx) (obsT st)) := by
  let S := arun idx st (c.selBody ++ trialBody)
  let z := c.tsel idx
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 21 = z.inP2 at hz21
  change srun idx st.regs (selS c) 30 = z.pX at hz30
  change srun idx st.regs (selS c) 31 = z.X at hz31
  change srun idx st.regs (selS c) 32 = z.inA at hz32
  change srun idx st.regs (selS c) 36 = z.rA at hz36
  have hfacts := Admissible.passAFacts c hc idx hidx
  dsimp only at hfacts
  rcases hfacts with ⟨hP2, hrA⟩
  have hSregs : S.regs = srun idx (srun idx st.regs (selS c)) trialS := by
    simp [S, arun_append, selBody_lift, trialBody, trialScalarBody_lift,
      arun_lift, arun, astep]
    rfl
  have hSlt : ∀ j, S.regs j < M := by
    rw [hSregs]
    exact srun_lt_of_lt idx _ _ (srun_lt_of_lt idx _ st.regs hs)
  have hSj (j : Nat) (hj : 4 < j ∧ j < 40) :
      S.regs j = srun idx st.regs (selS c) j := by
    rw [hSregs, trialS_frame idx _ j (by omega)]
  have hS1 : S.regs 1 = 0 := by
    rw [hSregs, trialS_frame idx _ 1 (by omega), selS_frame c idx st.regs 1 (by omega)]
    exact h1
  have hS21 : S.regs 21 = z.inP2 := (hSj 21 (by omega)).trans hz21
  have hS30 : S.regs 30 = z.pX := (hSj 30 (by omega)).trans hz30
  have hS31 : S.regs 31 = z.X := (hSj 31 (by omega)).trans hz31
  have hS32 : S.regs 32 = z.inA := (hSj 32 (by omega)).trans hz32
  have hS36 : S.regs 36 = z.rA := (hSj 36 (by omega)).trans hz36
  have hp := passABody_obs idx S z hSlt hS1 hS21 hS30 hS31 hS32 hS36 hP2 hrA
  have ht := selTrial_obs c hc idx hidx st hs hSq hPar
  change obsT S = ttrial z (obsT st) at ht
  rw [arun_append]
  rw [ht] at hp
  exact hp

theorem selTrialPassA_defined (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState) :
    AllDefined c.arrayLen idx st ((c.selBody ++ trialBody) ++ passABody) := by
  rw [AllDefined_append]
  constructor
  · exact selTrial_defined c hc idx hidx st
  · let z := c.tsel idx
    have hb := Admissible.selBounds c hc idx hidx
    rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
    have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
    dsimp only at hz
    rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
      hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
    change srun idx st.regs (selS c) 36 = z.rA at hz36
    have hfacts := Admissible.passAFacts c hc idx hidx
    dsimp only at hfacts
    rcases hfacts with ⟨hP2, hrA⟩
    apply passABody_defined
    change (arun idx st (c.selBody ++ trialBody)).regs 36 ≠ 0
    rw [arun_append, trialBody_regs_frame idx _ 36 (by omega),
      selBody_lift, arun_lift]
    change srun idx st.regs (selS c) 36 ≠ 0
    rw [hz36]
    exact hrA

/-- **The production configuration is admissible**: `cap = 10⁶`,
`rounds = 999`, `checkLo = 33`. -/
theorem loopCount_le (c : Cfg) :
    c.loopCount ≤ (c.cap - 1) * c.rounds + c.cap * (2 * c.cap + 2) := by
  have hs : c.s ≤ c.cap := sqrt_le_self c.cap
  have e : c.loopCount = (c.cap - 1) * c.rounds + c.cap * (2 * c.s + 2) := rfl
  rw [e]
  exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.le_refl _) (by omega)) _

theorem production_admissible : Admissible production := by
  have h := loopCount_le production
  rw [show production.cap = 1000000 from rfl,
    show production.rounds = 999 from rfl] at h
  have hM : (1000000 - 1) * 999 + 1000000 * (2 * 1000000 + 2) < M := by decide
  exact ⟨by decide, by decide, by decide, by omega, by decide⟩

/-- The smoke configuration is admissible too. -/
theorem smoke_admissible : Admissible smoke := by
  have h := loopCount_le smoke
  rw [show smoke.cap = 2000 from rfl, show smoke.rounds = 999 from rfl] at h
  have hM : (2000 - 1) * 999 + 2000 * (2 * 2000 + 2) < M := by decide
  exact ⟨by decide, by decide, by decide, by omega, by decide⟩

/-! ## OPEN: what obligation (1) still needs

Nothing below is proved.  Each item is stated here at the exact strength it
has to be proved at; none of them is an axiom, a `sorry`, or a weakened
restatement.

The scalar `cmulBody` obligation is closed by `cmulS_spec`; the first array
boundary is closed by `touchBody_defined` and `touchBody_obs`.  The remaining
stage proofs must derive their three touch index bounds from the loop
invariant: gating gives `base = g * dSlot % M` with `g ∈ {0,1}`, while the
live slot supplies `dSlot ≤ c.cap`.

### (1c) the six body stages, the body, and the loop

```text
theorem body_defined (c : Cfg) (idx : Nat) (st : AState)
    (hadm : Admissible c) (hidx : idx < c.loopCount) (hInv : Inv c st) :
    AllDefined c.arrayLen idx st c.body

theorem body_obs (c : Cfg) (idx : Nat) (st : AState)
    (hadm : Admissible c) (hidx : idx < c.loopCount) (hInv : Inv c st) :
    obsT (arun idx st c.body) = c.tstep idx (obsT st)

theorem body_inv (c : Cfg) (idx : Nat) (st : AState)
    (hadm : Admissible c) (hidx : idx < c.loopCount) (hInv : Inv c st) :
    Inv c (arun idx st c.body)

theorem init_reaches (c : Cfg) (hadm : Admissible c) :
    denoteAInstrs c.arrayLen 0 initialAState c.init = some entry ∧
      obsT entry = tInit
```

with `Inv c st` at least: every register and every array cell is a word;
`st.regs 1 = 0` (the `rZero` constant); and the fourteen persistent
registers agree with the observation.  `obsT` reads registers
`0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13` and `st.arr` into a `TState`.
These assemble by `Verified.Algorithm.ArrayBridge.ArrayLoop` — whose four
fields are exactly `init_reaches`, `body_defined` + `denoteAInstrs_eq_arun`,
`body_inv` and `body_obs`, with `epilogue_reads` trivial (`epilogue = []`,
`output = rViol`) — into

```text
theorem g2Program_denote (c : Cfg) (hc : Admissible c) :
    (g2Program c).denote = some (c.tFlag)
```

which is obligation (1).  `production_admissible` above discharges `hc` at
the production configuration.
-/

end LeanCompCert.Ports.Section413G2Denote
