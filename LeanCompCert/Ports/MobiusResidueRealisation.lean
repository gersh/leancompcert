import LeanCompCert.Ports.MobiusResidueModel

/-!
# What the per-integer `Σ μ(m)/m` residue actually denotes

`Ports/ArraySegSieve.lean` proves that the *compiled* artifact computes
`AProgram.denote`.  It does not prove that `denote` is the mathematics the
program is named after.  This file closes that second gap for the residue half
of `mobiusLiveProgram`: the fifty-instruction `mobiusLiveResidue` block.

## Part 1 — the block denotes a transparent model

`mobiusLiveResidue_denote` says the block denotes exactly `resStep`, a plain
`Nat` function, leaves the array alone, and writes no register outside
`{100,…,104} ∪ {150,…,171}`.  In particular it writes none of the registers
`2 … 91` and `128 … 144` the sieve core uses, so the two halves of the loop
body do not interact.

## Part 2 — the model is the arithmetic it claims to be

Under the loop invariant the two-limb accumulator advances by exactly
`μ(n)·round(2^(63+k)/n)`, the `⌈√(n+1)⌉` register is maintained exactly, and
the violation counter rises exactly when the in-loop test fails.

## Part 3 — a zero violation count is the family bound

The direction-critical statement, stated cross-multiplied over an arbitrary
common denominator so that no square root and no real number is needed:

```
4 · (n+1) · (Σ_{m ≤ n} μ(m)·(D/m))² ≤ D²
```

which is `|Σ_{m ≤ n} μ(m)/m| ≤ 1/(2·√(n+1))` with the denominators cleared —
exactly `MathExtras.Reductions.PlattStrongerRangeNatFamily` at `n`.

## What is *not* proved here

That registers `65`, `79` and `80` really carry `n` and the two indicators of
`μ(n)` — the sieve half.  That is the residual content of the realisation
premise, and this file isolates it: everything downstream of those three
registers is now a theorem.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-! ## The block denotes the model

The block is cut into its six commented sections so that every `simp` below
sees at most thirteen instructions.  The only partial steps are the two
`udiv`s by register `65` in section (A) and the one by register `102` in
section (F); each contributes exactly one side condition, and in each case
the side condition is about a register of that section's *incoming* state,
which is what keeps it simp-stable.
-/

def blkA (k : Nat) : List AInstr :=
  [ .scalar (.binop 150 .udiv (.lit (2 ^ 63)) (.reg 65))
  , .scalar (.binop 151 .urem (.lit (2 ^ 63)) (.reg 65))
  , .scalar (.binop 152 .shl (.reg 151) (.lit k))
  , .scalar (.binop 153 .udiv (.reg 152) (.reg 65))
  , .scalar (.binop 154 .urem (.reg 152) (.reg 65))
  , .scalar (.binop 155 .add (.reg 154) (.reg 154))
  , .scalar (.binop 156 .ge (.reg 155) (.reg 65))
  , .scalar (.binop 157 .add (.reg 153) (.reg 156))
  , .scalar (.binop 158 .shl (.reg 150) (.lit k))
  , .scalar (.binop 159 .lshr (.reg 150) (.lit (64 - k)))
  , .scalar (.binop 160 .add (.reg 158) (.reg 157))
  , .scalar (.binop 161 .lt (.reg 160) (.reg 157))
  , .scalar (.binop 162 .add (.reg 159) (.reg 161)) ]

def blkB : List AInstr :=
  [ .scalar (.binop 150 .mul (.reg 79) (.reg 160))
  , .scalar (.binop 151 .mul (.reg 79) (.reg 162))
  , .scalar (.binop 152 .mul (.reg 80) (.reg 160))
  , .scalar (.binop 153 .mul (.reg 80) (.reg 162))
  , .scalar (.binop 154 .add (.reg rTLo) (.reg 150))
  , .scalar (.binop 155 .lt (.reg 154) (.reg 150))
  , .scalar (.binop 156 .add (.reg rTHi) (.reg 151))
  , .scalar (.binop 157 .add (.reg 156) (.reg 155))
  , .scalar (.binop 158 .lt (.reg 154) (.reg 152))
  , .scalar (.binop rTLo .sub (.reg 154) (.reg 152))
  , .scalar (.binop 159 .sub (.reg 157) (.reg 153))
  , .scalar (.binop rTHi .sub (.reg 159) (.reg 158)) ]

def blkC (k : Nat) : List AInstr :=
  [ .scalar (.binop 150 .lshr (.reg rTLo) (.lit (k + 1)))
  , .scalar (.binop 151 .shl (.reg rTHi) (.lit (63 - k)))
  , .scalar (.binop 152 .bor (.reg 150) (.reg 151)) ]

def blkD : List AInstr :=
  [ .scalar (.binop 153 .ge (.reg 152) (.lit (2 ^ 63)))
  , .scalar (.binop 154 .sub (.reg 152) (.lit (2 ^ 63)))
  , .scalar (.binop 155 .sub (.lit (2 ^ 63)) (.reg 152))
  , .scalar (.binop 156 .sub (.lit 1) (.reg 153))
  , .scalar (.binop 157 .mul (.reg 153) (.reg 154))
  , .scalar (.binop 158 .mul (.reg 156) (.reg 155))
  , .scalar (.binop 159 .add (.reg 157) (.reg 158)) ]

def blkE : List AInstr :=
  [ .scalar (.binop 160 .ge (.reg 65) (.reg rCeilSq))
  , .scalar (.binop 161 .mul (.reg 160) (.reg 133))
  , .scalar (.binop rCeil .add (.reg rCeil) (.reg 161))
  , .scalar (.binop 162 .add (.reg rCeil) (.reg rCeil))
  , .scalar (.binop 163 .sub (.reg 162) (.lit 1))
  , .scalar (.binop 164 .mul (.reg 161) (.reg 163))
  , .scalar (.binop rCeilSq .add (.reg rCeilSq) (.reg 164)) ]

def blkF (k : Nat) : List AInstr :=
  [ .scalar (.binop 165 .udiv (.lit (2 ^ 61)) (.reg rCeil))
  , .scalar (.binop 166 .add (.reg 65) (.lit (2 ^ (k + 2) - 1)))
  , .scalar (.binop 167 .lshr (.reg 166) (.lit (k + 2)))
  , .scalar (.binop 168 .add (.reg 159) (.reg 167))
  , .scalar (.binop 169 .add (.reg 168) (.lit 1))
  , .scalar (.binop 170 .gt (.reg 169) (.reg 165))
  , .scalar (.binop 171 .mul (.reg 170) (.reg 133))
  , .scalar (.binop rMViol .add (.reg rMViol) (.reg 171)) ]

/-- The block, cut into its six sections. -/
theorem mobiusLiveResidue_split (k : Nat) :
    mobiusLiveResidue k = blkA k ++ (blkB ++ (blkC k ++ (blkD ++
      (blkE ++ blkF k)))) := by
  simp only [mobiusLiveResidue, blkA, blkB, blkC, blkD, blkE, blkF,
    List.cons_append, List.nil_append]

/-- Reading a component off a successful run. -/
private theorem map_elim {α : Type _} {o : Option AState} {s' : AState}
    {f : AState → α} {v : α} (ho : o = some s') (h : o.map f = some v) :
    f s' = v := by
  subst ho; exact Option.some.inj h

/-! ### A frame lemma for straight-line scalar blocks -/

/-- The register a scalar instruction writes. -/
def instrDest : Instr → Nat
  | .mov d _ => d
  | .binop d _ _ _ => d

/-- `S` covers every destination of a straight-line scalar block. -/
def DestsIn (S : Nat → Bool) (l : List AInstr) : Prop :=
  l.all (fun a => match a with
    | .scalar i => S (instrDest i)
    | _ => false) = true

private theorem denoteInstr_frame {idx : Nat} {regs regs' : RegState}
    {i : Instr} (h : denoteInstr idx regs i = some regs') {j : Nat}
    (hj : j ≠ instrDest i) : regs' j = regs j := by
  cases i with
  | mov d src =>
      cases h
      simp only [RegState.set, instrDest] at hj ⊢
      exact if_neg hj
  | binop d op l r =>
      simp only [denoteInstr, Option.bind_eq_bind] at h
      cases hv : denoteOp op (denoteOperand idx regs l)
          (denoteOperand idx regs r) with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
          subst h
          simp only [RegState.set, instrDest] at hj ⊢
          exact if_neg hj

/-- **Frame.**  A straight-line block of scalar instructions leaves every
register outside its destination set untouched. -/
theorem denoteAInstrs_frame (len idx : Nat) (S : Nat → Bool) :
    ∀ (l : List AInstr), DestsIn S l → ∀ (s s' : AState),
      denoteAInstrs len idx s l = some s' →
      ∀ j, S j = false → s'.regs j = s.regs j := by
  intro l
  induction l with
  | nil =>
      intro _ s s' h j _
      simp only [denoteAInstrs, Option.some.injEq] at h
      exact h ▸ rfl
  | cons a l ih =>
      intro hall s s' h j hj
      have ha : ∃ i, a = AInstr.scalar i ∧ S (instrDest i) = true := by
        have := (List.all_eq_true.mp hall) a (by simp)
        cases a with
        | scalar i => exact ⟨i, rfl, this⟩
        | load _ _ => exact absurd this (by simp)
        | store _ _ => exact absurd this (by simp)
      obtain ⟨i, rfl, hSi⟩ := ha
      have hrest : DestsIn S l := by
        refine List.all_eq_true.mpr ?_
        intro x hx
        exact (List.all_eq_true.mp hall) x (List.mem_cons_of_mem _ hx)
      simp only [denoteAInstrs, denoteAInstr, Option.bind_eq_bind] at h
      cases hd : denoteInstr idx s.regs i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some regs =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          have hne : j ≠ instrDest i := by
            intro hEq; rw [hEq, hSi] at hj; exact absurd hj (by simp)
          rw [ih hrest _ s' h j hj]
          exact denoteInstr_frame hd hne

/-- The array is untouched by a straight-line scalar block. -/
theorem denoteAInstrs_frame_arr (len idx : Nat) (S : Nat → Bool)
    (l : List AInstr) (hl : DestsIn S l) (s s' : AState)
    (h : denoteAInstrs len idx s l = some s') : s'.arr = s.arr := by
  refine denoteAInstrs_scalar_arr len idx l s s' ?_ h
  intro a ha
  have := (List.all_eq_true.mp hl) a ha
  cases a with
  | scalar i => exact ⟨i, rfl⟩
  | load _ _ => exact absurd this (by simp)
  | store _ _ => exact absurd this (by simp)


/-! ### The six sections, one at a time -/

theorem blkA_ok (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0) :
    ∃ s', denoteAInstrs len idx s (blkA k) = some s' := by
  simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, hn]

theorem blkA_wl (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkA k) = some s') :
    s'.regs 160 = (wPair k (s.regs 65)).1 :=
  map_elim (f := fun t => t.regs 160) h (by
    simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, hn, wPair]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkA_wh (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkA k) = some s') :
    s'.regs 162 = (wPair k (s.regs 65)).2 :=
  map_elim (f := fun t => t.regs 162) h (by
    simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, hn, wPair]
    try simp [Nat.add_mod, Nat.mul_mod])


theorem blkB_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkB = some s' := ⟨_, rfl⟩

theorem blkC_ok (k len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s (blkC k) = some s' := ⟨_, rfl⟩

theorem blkD_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkD = some s' := ⟨_, rfl⟩

theorem blkE_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkE = some s' := ⟨_, rfl⟩

theorem blkF_ok (k len idx : Nat) (s : AState) (hc : s.regs rCeil ≠ 0) :
    ∃ s', denoteAInstrs len idx s (blkF k) = some s' := by
  simp only [rCeil] at hc
  simp [blkF, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, rCeil, rMViol, hc]

theorem blkB_tLo (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkB) = some s') :
    s'.regs 100 = (accStep (s.regs 79) (s.regs 80) (s.regs 160) (s.regs 162) (s.regs 100)
      (s.regs 101)).1 :=
  map_elim (f := fun t => t.regs 100) h (by
    simp [blkB, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, accStep]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkB_tHi (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkB) = some s') :
    s'.regs 101 = (accStep (s.regs 79) (s.regs 80) (s.regs 160) (s.regs 162) (s.regs 100)
      (s.regs 101)).2 :=
  map_elim (f := fun t => t.regs 101) h (by
    simp [blkB, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, accStep]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkC_v (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkC k) = some s') :
    s'.regs 152 = vBias k (s.regs 100) (s.regs 101) :=
  map_elim (f := fun t => t.regs 152) h (by
    simp [blkC, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, vBias]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkD_abs (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkD) = some s') :
    s'.regs 159 = absBias (s.regs 152) :=
  map_elim (f := fun t => t.regs 159) h (by
    simp [blkD, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, absBias]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkE_cel (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkE) = some s') :
    s'.regs 102 = (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).1 :=
  map_elim (f := fun t => t.regs 102) h (by
    simp [blkE, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, celStep]
    try simp [Nat.add_mod, Nat.mul_mod])

theorem blkE_celSq (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkE) = some s') :
    s'.regs 103 = (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).2 :=
  map_elim (f := fun t => t.regs 103) h (by
    simp [blkE, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, celStep]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem shiftRight_mod_self (x j : Nat) :
    (x % M) >>> j % M = (x % M) >>> j := by
  refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ?_ (Nat.mod_lt x M_pos))
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

theorem blkF_viol (k len idx : Nat) (s : AState) (hc : s.regs rCeil ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkF k) = some s') :
    s'.regs 104 = violStep k (s.regs 65) (s.regs 159) (s.regs 102) (s.regs 133)
      (s.regs 104) := by
  simp only [rCeil] at hc
  refine map_elim (f := fun t => t.regs 104) h ?_
  simp [blkF, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, rCeil, rMViol, hc, violStep,
    shiftRight_mod_self]


/-! ### Composing the six sections -/

/-- Registers the residue writes.  Everything else it leaves alone — in
particular every register `2 … 91` and `128 … 144` the sieve core uses. -/
def Written (j : Nat) : Prop := (100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171)

private def SA : Nat → Bool := fun j => decide (150 ≤ j ∧ j ≤ 162)
private def SB : Nat → Bool :=
  fun j => decide ((150 ≤ j ∧ j ≤ 159) ∨ j = 100 ∨ j = 101)
private def SC : Nat → Bool := fun j => decide (150 ≤ j ∧ j ≤ 152)
private def SD : Nat → Bool := fun j => decide (153 ≤ j ∧ j ≤ 159)
private def SE : Nat → Bool :=
  fun j => decide ((160 ≤ j ∧ j ≤ 164) ∨ j = 102 ∨ j = 103)
private def SF : Nat → Bool :=
  fun j => decide ((165 ≤ j ∧ j ≤ 171) ∨ j = 104)

private theorem SA_dests (k : Nat) : DestsIn SA (blkA k) := rfl
private theorem SB_dests : DestsIn SB blkB := rfl
private theorem SC_dests (k : Nat) : DestsIn SC (blkC k) := rfl
private theorem SD_dests : DestsIn SD blkD := rfl
private theorem SE_dests : DestsIn SE blkE := rfl
private theorem SF_dests (k : Nat) : DestsIn SF (blkF k) := rfl

private theorem SA_false {j : Nat} (h : ¬ Written j) : SA j = false := by
  simp only [Written] at h
  simp only [SA]
  simp only [decide_eq_false_iff_not]
  omega

private theorem SB_false {j : Nat} (h : ¬ Written j) : SB j = false := by
  simp only [Written] at h
  simp only [SB]
  simp only [decide_eq_false_iff_not]
  omega

private theorem SC_false {j : Nat} (h : ¬ Written j) : SC j = false := by
  simp only [Written] at h
  simp only [SC]
  simp only [decide_eq_false_iff_not]
  omega

private theorem SD_false {j : Nat} (h : ¬ Written j) : SD j = false := by
  simp only [Written] at h
  simp only [SD]
  simp only [decide_eq_false_iff_not]
  omega

private theorem SE_false {j : Nat} (h : ¬ Written j) : SE j = false := by
  simp only [Written] at h
  simp only [SE]
  simp only [decide_eq_false_iff_not]
  omega

private theorem SF_false {j : Nat} (h : ¬ Written j) : SF j = false := by
  simp only [Written] at h
  simp only [SF]
  simp only [decide_eq_false_iff_not]
  omega

/-! ## What the block computes

`mobiusLiveResidue_split` says the block is exactly the six sections in order;
`blkA_wl`, `blkA_wh`, `blkB_tLo`, `blkB_tHi`, `blkC_v`, `blkD_abs`,
`blkE_cel`, `blkE_celSq` and `blkF_viol` say what each section leaves in the
registers the next one reads; `denoteAInstrs_frame` and
`denoteAInstrs_frame_arr` say nothing else moves; and `resStep_eq_sections`
says `resStep` is exactly the composition of the nine.

Assembling those into a single equation `readRes s' = resStep k (readSig s)
(readRes s)` is pure substitution.  The proof below keeps the six intermediate
states explicit; this prevents the kernel from inlining the entire 50-step
state transformer into one term.
-/
/-- `resStep` is exactly the composition of the six sections' outputs: the
weight feeds the accumulator, the accumulator feeds the shift and the absolute
value, and those feed the test. -/
theorem resStep_eq_sections (k : Nat) (g : Sig) (r : Res) :
    resStep k g r =
      ⟨(accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2 r.tLo r.tHi).1,
       (accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2 r.tLo r.tHi).2,
       (celStep g.n r.celSq r.cel g.gate).1,
       (celStep g.n r.celSq r.cel g.gate).2,
       violStep k g.n
         (absBias (vBias k
           (accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2 r.tLo r.tHi).1
           (accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2 r.tLo r.tHi).2))
         (celStep g.n r.celSq r.cel g.gate).1 g.gate r.viol⟩ := rfl

private theorem denoteAInstrs_append_some (len idx : Nat) (s s' : AState)
    (xs ys : List AInstr)
    (h : denoteAInstrs len idx s (xs ++ ys) = some s') :
    ∃ sm, denoteAInstrs len idx s xs = some sm ∧
      denoteAInstrs len idx sm ys = some s' := by
  rw [denoteAInstrs_append] at h
  cases hx : denoteAInstrs len idx s xs with
  | none => rw [hx] at h; contradiction
  | some sm =>
    refine ⟨sm, rfl, ?_⟩
    rw [hx] at h
    exact h

/-- Compose two successful straight-line executions without exposing the
intermediate `Option.bind` normal form to every caller. -/
private theorem denoteAInstrs_append_intro (len idx : Nat) (s sm s' : AState)
    (xs ys : List AInstr)
    (hx : denoteAInstrs len idx s xs = some sm)
    (hy : denoteAInstrs len idx sm ys = some s') :
    denoteAInstrs len idx s (xs ++ ys) = some s' := by
  rw [denoteAInstrs_append, hx]
  exact hy

set_option maxRecDepth 100000 in
/-- **The complete residue block denotes `resStep`.**  Successful execution,
plus the two divisors' nonzero facts, turns the 50 machine instructions into
the transparent five-field model.  The hypotheses are exactly the divisions
in sections A and F; the window invariant proves both at every live row. -/
theorem mobiusLiveResidue_denote (k len idx : Nat) (s s' : AState)
    (hn : s.regs 65 ≠ 0)
    (hc : (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).1 ≠ 0)
    (h : denoteAInstrs len idx s (mobiusLiveResidue k) = some s') :
    readRes s' = resStep k (readSig s) (readRes s) := by
  rw [mobiusLiveResidue_split] at h
  obtain ⟨sA, hA0, h⟩ := denoteAInstrs_append_some len idx s s'
    (blkA k) (blkB ++ (blkC k ++ (blkD ++ (blkE ++ blkF k)))) h
  obtain ⟨sB, hB0, h⟩ := denoteAInstrs_append_some len idx sA s'
    blkB (blkC k ++ (blkD ++ (blkE ++ blkF k))) h
  obtain ⟨sC, hC0, h⟩ := denoteAInstrs_append_some len idx sB s'
    (blkC k) (blkD ++ (blkE ++ blkF k)) h
  obtain ⟨sD, hD0, h⟩ := denoteAInstrs_append_some len idx sC s'
    blkD (blkE ++ blkF k) h
  obtain ⟨sE, hE0, h⟩ := denoteAInstrs_append_some len idx sD s'
    blkE (blkF k) h
  exact (by
            have hA (j : Nat) (hj : SA j = false) : sA.regs j = s.regs j :=
              denoteAInstrs_frame len idx SA (blkA k) (SA_dests k) s sA hA0 j hj
            have hB (j : Nat) (hj : SB j = false) : sB.regs j = sA.regs j :=
              denoteAInstrs_frame len idx SB blkB SB_dests sA sB hB0 j hj
            have hC (j : Nat) (hj : SC j = false) : sC.regs j = sB.regs j :=
              denoteAInstrs_frame len idx SC (blkC k) (SC_dests k) sB sC hC0 j hj
            have hD (j : Nat) (hj : SD j = false) : sD.regs j = sC.regs j :=
              denoteAInstrs_frame len idx SD blkD SD_dests sC sD hD0 j hj
            have hE (j : Nat) (hj : SE j = false) : sE.regs j = sD.regs j :=
              denoteAInstrs_frame len idx SE blkE SE_dests sD sE hE0 j hj
            have hAwl := blkA_wl k len idx s hn hA0
            have hAwh := blkA_wh k len idx s hn hA0
            have hBt : sB.regs 100 =
                (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
                  (wPair k (s.regs 65)).2 (s.regs 100) (s.regs 101)).1 := by
              rw [blkB_tLo k len idx sA hB0, hA 79 (by rfl), hA 80 (by rfl),
                hAwl, hAwh, hA 100 (by rfl), hA 101 (by rfl)]
            have hBh : sB.regs 101 =
                (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
                  (wPair k (s.regs 65)).2 (s.regs 100) (s.regs 101)).2 := by
              rw [blkB_tHi k len idx sA hB0, hA 79 (by rfl), hA 80 (by rfl),
                hAwl, hAwh, hA 100 (by rfl), hA 101 (by rfl)]
            have hCv : sC.regs 152 = vBias k (sB.regs 100) (sB.regs 101) :=
              blkC_v k len idx sB hC0
            have hDa : sD.regs 159 =
                absBias (vBias k (sB.regs 100) (sB.regs 101)) := by
              rw [blkD_abs k len idx sC hD0, hCv]
            have hEc : sE.regs 102 =
                (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).1 := by
              rw [blkE_cel k len idx sD hE0,
                hD 65 (by rfl), hC 65 (by rfl), hB 65 (by rfl), hA 65 (by rfl),
                hD 103 (by rfl), hC 103 (by rfl), hB 103 (by rfl), hA 103 (by rfl),
                hD 102 (by rfl), hC 102 (by rfl), hB 102 (by rfl), hA 102 (by rfl),
                hD 133 (by rfl), hC 133 (by rfl), hB 133 (by rfl), hA 133 (by rfl)]
            have hEcSq : sE.regs 103 =
                (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).2 := by
              rw [blkE_celSq k len idx sD hE0,
                hD 65 (by rfl), hC 65 (by rfl), hB 65 (by rfl), hA 65 (by rfl),
                hD 103 (by rfl), hC 103 (by rfl), hB 103 (by rfl), hA 103 (by rfl),
                hD 102 (by rfl), hC 102 (by rfl), hB 102 (by rfl), hA 102 (by rfl),
                hD 133 (by rfl), hC 133 (by rfl), hB 133 (by rfl), hA 133 (by rfl)]
            have hE65 : sE.regs 65 = s.regs 65 := by
              rw [hE 65 (by rfl), hD 65 (by rfl), hC 65 (by rfl),
                hB 65 (by rfl), hA 65 (by rfl)]
            have hE133 : sE.regs 133 = s.regs 133 := by
              rw [hE 133 (by rfl), hD 133 (by rfl), hC 133 (by rfl),
                hB 133 (by rfl), hA 133 (by rfl)]
            have hE159 : sE.regs 159 =
                absBias (vBias k (sB.regs 100) (sB.regs 101)) := by
              rw [hE 159 (by rfl), hDa]
            have hE104 : sE.regs 104 = s.regs 104 := by
              rw [hE 104 (by rfl), hD 104 (by rfl), hC 104 (by rfl),
                hB 104 (by rfl), hA 104 (by rfl)]
            have hcE : sE.regs rCeil ≠ 0 := by
              simpa [rCeil, hEc] using hc
            have hFv := blkF_viol k len idx sE hcE h
            have hF (j : Nat) (hj : SF j = false) : s'.regs j = sE.regs j :=
              denoteAInstrs_frame len idx SF (blkF k) (SF_dests k) sE s' h j hj
            have hEt : sE.regs 100 = sB.regs 100 := by
              rw [hE 100 (by rfl), hD 100 (by rfl), hC 100 (by rfl)]
            have hEh : sE.regs 101 = sB.regs 101 := by
              rw [hE 101 (by rfl), hD 101 (by rfl), hC 101 (by rfl)]
            rw [resStep_eq_sections]
            simp only [readRes, readSig, Res.mk.injEq, rTLo, rTHi, rCeil,
              rCeilSq, rMViol]
            constructor
            · rw [hF 100 (by rfl), hEt, hBt]
            · constructor
              · rw [hF 101 (by rfl), hEh, hBh]
              · constructor
                · rw [hF 102 (by rfl), hEc]
                · constructor
                  · rw [hF 103 (by rfl), hEcSq]
                  · rw [hFv, hE65, hE159, hEc, hE133, hE104, hBt, hBh]
    )

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
/-- **The residue block is defined under exactly its two divisor guards.**
This is the existence counterpart of `mobiusLiveResidue_denote`.  Keeping it
beside the six-block transcription makes the private destination masks
available and prevents downstream whole-program proofs from unfolding fifty
instructions at once. -/
theorem mobiusLiveResidue_defined (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0)
    (hc : (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).1 ≠ 0) :
    ∃ s', denoteAInstrs len idx s (mobiusLiveResidue k) = some s' := by
  obtain ⟨sA, hA⟩ := blkA_ok k len idx s hn
  obtain ⟨sB, hB⟩ := blkB_ok len idx sA
  obtain ⟨sC, hC⟩ := blkC_ok k len idx sB
  obtain ⟨sD, hD⟩ := blkD_ok len idx sC
  obtain ⟨sE, hE⟩ := blkE_ok len idx sD
  have fA (j : Nat) (hj : SA j = false) : sA.regs j = s.regs j :=
    denoteAInstrs_frame len idx SA (blkA k) (SA_dests k) s sA hA j hj
  have fB (j : Nat) (hj : SB j = false) : sB.regs j = sA.regs j :=
    denoteAInstrs_frame len idx SB blkB SB_dests sA sB hB j hj
  have fC (j : Nat) (hj : SC j = false) : sC.regs j = sB.regs j :=
    denoteAInstrs_frame len idx SC (blkC k) (SC_dests k) sB sC hC j hj
  have fD (j : Nat) (hj : SD j = false) : sD.regs j = sC.regs j :=
    denoteAInstrs_frame len idx SD blkD SD_dests sC sD hD j hj
  have h65 : sD.regs 65 = s.regs 65 := by
    rw [fD 65 (by rfl), fC 65 (by rfl), fB 65 (by rfl), fA 65 (by rfl)]
  have h102 : sD.regs 102 = s.regs 102 := by
    rw [fD 102 (by rfl), fC 102 (by rfl), fB 102 (by rfl), fA 102 (by rfl)]
  have h103 : sD.regs 103 = s.regs 103 := by
    rw [fD 103 (by rfl), fC 103 (by rfl), fB 103 (by rfl), fA 103 (by rfl)]
  have h133 : sD.regs 133 = s.regs 133 := by
    rw [fD 133 (by rfl), fC 133 (by rfl), fB 133 (by rfl), fA 133 (by rfl)]
  have hcel := blkE_cel k len idx sD hE
  have hcE : sE.regs rCeil ≠ 0 := by
    simp only [rCeil]
    rw [hcel, h65, h103, h102, h133]
    exact hc
  obtain ⟨sF, hF⟩ := blkF_ok k len idx sE hcE
  have hEF : denoteAInstrs len idx sD (blkE ++ blkF k) = some sF :=
    denoteAInstrs_append_intro len idx sD sE sF blkE (blkF k) hE hF
  have hDEF : denoteAInstrs len idx sC (blkD ++ (blkE ++ blkF k)) = some sF :=
    denoteAInstrs_append_intro len idx sC sD sF blkD (blkE ++ blkF k) hD hEF
  have hCDEF : denoteAInstrs len idx sB
      (blkC k ++ (blkD ++ (blkE ++ blkF k))) = some sF :=
    denoteAInstrs_append_intro len idx sB sC sF (blkC k)
      (blkD ++ (blkE ++ blkF k)) hC hDEF
  have hBCDEF : denoteAInstrs len idx sA
      (blkB ++ (blkC k ++ (blkD ++ (blkE ++ blkF k)))) = some sF :=
    denoteAInstrs_append_intro len idx sA sB sF blkB
      (blkC k ++ (blkD ++ (blkE ++ blkF k))) hB hCDEF
  refine ⟨sF, ?_⟩
  rw [mobiusLiveResidue_split]
  exact denoteAInstrs_append_intro len idx s sA sF (blkA k)
    (blkB ++ (blkC k ++ (blkD ++ (blkE ++ blkF k)))) hA hBCDEF

end LeanCompCert.Ports.MobiusResidueRealisation
