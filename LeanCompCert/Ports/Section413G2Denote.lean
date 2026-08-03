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
  and each block's frame lemma.
* §4 — `Admissible`, and `production_admissible` / `smoke_admissible`.

See the closing `## OPEN` section for the precise statements that remain —
`divP18Body`, `cmulBody`, `touchBody`, the six body stages and the loop.
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
  exact ⟨by decide, by decide, by decide, by omega⟩

/-- The smoke configuration is admissible too. -/
theorem smoke_admissible : Admissible smoke := by
  have h := loopCount_le smoke
  rw [show smoke.cap = 2000 from rfl, show smoke.rounds = 999 from rfl] at h
  have hM : (2000 - 1) * 999 + 2000 * (2 * 2000 + 2) < M := by decide
  exact ⟨by decide, by decide, by decide, by omega⟩

/-! ## OPEN: what obligation (1) still needs

Nothing below is proved.  Each item is stated here at the exact strength it
has to be proved at; none of them is an axiom, a `sorry`, or a weakened
restatement.  The scalar blocks are the ones `lift` puts into the scalar
machine (`§3` above); the two that touch the array are stated over
`AState`.

### (1a) `divP18Body` computes `tdiv18`

```text
theorem divP18S_spec (k : Nat) (s : RegState) (lo hi q qc : Nat)
    (hfresh : <lo, hi, q, qc ∉ [168,175]; q ≠ qc; lo ≠ q; lo ≠ qc>)
    (hs : ∀ j, s j < M) :
    srun k s (divP18S lo hi q qc) q  = (tdiv18 (s lo) (s hi)).1 ∧
    srun k s (divP18S lo hi q qc) qc = (tdiv18 (s lo) (s hi)).2
```

`Section413G2Program` §9 already proves `tdiv18_eq`: on every input the
width guards admit, `tdiv18` **is** the proved exact divider
`(divP18q, divP18ceil)`.  So all that is owed here is the transcription —
forty-six instructions against `tld`/`ttail`, whose only content is that
each of the six `% M` per digit is the identity below the quotient cap.
⚠ `4194304` and `D5` both occur as second operands of `mul`/`udiv`; they
must be abstracted.

### (1b) `cmulBody` computes `tcmul`

```text
theorem cmulS_spec (k : Nat) (s : RegState)
    (gate aLo aHi bLo bHi cLo cHi : Nat)
    (hfresh : <gate, aLo, aHi, bLo, bHi, cLo, cHi outside [100,179]
               and ≠ rViol; cLo ≠ cHi>)
    (hs : ∀ j, s j < M) :
    srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cLo
        = (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) cHi
        = (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.1 ∧
      srun k s (cmulS gate aLo aHi bLo bHi cLo cHi) rViol
        = (tcmul (s gate) (s aLo) (s aHi) (s bLo) (s bHi) (s rViol)).2.2
```

This is pure composition of `mulWideG_hl`, (1a), `smDecomp_tmag`,
`cmpLtS_spec` and `selTripleS_spec` along `srun_append`, in the order `cmulBody` writes them:
four `smDecomp`, four `mulWide`, the sign canonicalization, two `cmpLt`,
four `selTriple`, two `cmpLt`, two `selTriple`, `divP18`, five
instructions, `divP18`, five instructions.  Every one of those calls is at
**concrete** register numbers, so no further freshness hypothesis appears.

### (1c) `touchBody` computes `ttouch`

The first statement that touches the array, so it is stated over `AState`
and `arun`, with `obsT` the observation of §5's loop package:

```text
theorem touchBody_spec (c : Cfg) (k : Nat) (st : AState) (g dSlot : Nat)
    (hadm : Admissible c) (hInv : Inv c st)
    (hidx : <the slot index is in range: (st.regs g * st.regs dSlot) % M
             + c.plane2 < c.arrayLen>) :
    AllDefined c.arrayLen k st (c.touchBody g dSlot) ∧
      obsT (arun k st (c.touchBody g dSlot))
        = c.ttouch (st.regs g) (st.regs dSlot) (obsT st)
```

`touchBody` has two `load`s and two `store`s, so it is exactly the place
where `lift` stops applying and the index-range half of admissibility is
consumed: `denoteAInstr` returns `none` when the index register is at least
`arrayLen`.  The gating discipline — `base = g * dSlot % M` with `g ∈ {0,1}`
— is what makes the three indices `base`, `base + plane1`, `base + plane2`
in range, and that argument needs `dSlot ≤ c.cap`, which is a consequence
of `Inv` and not of `Admissible`.

### (1d) the six body stages, the body, and the loop

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
