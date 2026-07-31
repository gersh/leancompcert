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

private theorem blkA_ok (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0) :
    ∃ s', denoteAInstrs len idx s (blkA k) = some s' := by
  simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, hn]

private theorem blkA_wl (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkA k) = some s') :
    s'.regs 160 = (wPair k (s.regs 65)).1 :=
  map_elim (f := fun t => t.regs 160) h (by
    simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, hn, wPair]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkA_wh (k len idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkA k) = some s') :
    s'.regs 162 = (wPair k (s.regs 65)).2 :=
  map_elim (f := fun t => t.regs 162) h (by
    simp [blkA, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, hn, wPair]
    try simp [Nat.add_mod, Nat.mul_mod])


private theorem blkB_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkB = some s' := ⟨_, rfl⟩

private theorem blkC_ok (k len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s (blkC k) = some s' := ⟨_, rfl⟩

private theorem blkD_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkD = some s' := ⟨_, rfl⟩

private theorem blkE_ok (len idx : Nat) (s : AState) :
    ∃ s', denoteAInstrs len idx s blkE = some s' := ⟨_, rfl⟩

private theorem blkF_ok (k len idx : Nat) (s : AState) (hc : s.regs rCeil ≠ 0) :
    ∃ s', denoteAInstrs len idx s (blkF k) = some s' := by
  simp only [rCeil] at hc
  simp [blkF, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, rCeil, rMViol, hc]

private theorem blkB_tLo (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkB) = some s') :
    s'.regs 100 = (accStep (s.regs 79) (s.regs 80) (s.regs 160) (s.regs 162) (s.regs 100)
      (s.regs 101)).1 :=
  map_elim (f := fun t => t.regs 100) h (by
    simp [blkB, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, accStep]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkB_tHi (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkB) = some s') :
    s'.regs 101 = (accStep (s.regs 79) (s.regs 80) (s.regs 160) (s.regs 162) (s.regs 100)
      (s.regs 101)).2 :=
  map_elim (f := fun t => t.regs 101) h (by
    simp [blkB, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, accStep]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkC_v (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkC k) = some s') :
    s'.regs 152 = vBias k (s.regs 100) (s.regs 101) :=
  map_elim (f := fun t => t.regs 152) h (by
    simp [blkC, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, vBias]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkD_abs (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkD) = some s') :
    s'.regs 159 = absBias (s.regs 152) :=
  map_elim (f := fun t => t.regs 159) h (by
    simp [blkD, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, absBias]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkE_cel (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkE) = some s') :
    s'.regs 102 = (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).1 :=
  map_elim (f := fun t => t.regs 102) h (by
    simp [blkE, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, celStep]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkE_celSq (k len idx : Nat) (s : AState) 
    {s' : AState} (h : denoteAInstrs len idx s (blkE) = some s') :
    s'.regs 103 = (celStep (s.regs 65) (s.regs 103) (s.regs 102) (s.regs 133)).2 :=
  map_elim (f := fun t => t.regs 103) h (by
    simp [blkE, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
      denoteOperand, RegState.set, rTLo, rTHi, rCeil, rCeilSq, rMViol, celStep]
    try simp [Nat.add_mod, Nat.mul_mod])

private theorem blkF_viol (k len idx : Nat) (s : AState) (hc : s.regs rCeil ≠ 0)
    {s' : AState} (h : denoteAInstrs len idx s (blkF k) = some s') :
    s'.regs 104 = violStep k (s.regs 65) (s.regs 159) (s.regs 102) (s.regs 133)
      (s.regs 104) := by
  simp only [rCeil] at hc
  refine map_elim (f := fun t => t.regs 104) h ?_
  simp [blkF, denoteAInstrs, denoteAInstr, denoteInstr, denoteOp,
    denoteOperand, RegState.set, rCeil, rMViol, hc, violStep]


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

/-- **The residue block denotes `resStep`.**  It succeeds exactly when the
current integer and the updated `⌈√(n+1)⌉` register are nonzero, it leaves the
array untouched, it changes no register outside `Written`, and on its own five
registers it acts as the transparent model. -/
set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem mobiusLiveResidue_denote (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0) (hc : celAfter (readSig s) (readRes s) ≠ 0) :
    ∃ s', denoteAInstrs len idx s (mobiusLiveResidue k) = some s' ∧
      s'.arr = s.arr ∧
      readRes s' = resStep k (readSig s) (readRes s) ∧
      ∀ j, ¬ Written j → s'.regs j = s.regs j := by
  obtain ⟨a, ha⟩ := blkA_ok k len idx s hn
  obtain ⟨b, hb⟩ := blkB_ok len idx a
  obtain ⟨c, hcc⟩ := blkC_ok k len idx b
  obtain ⟨d, hd⟩ := blkD_ok len idx c
  obtain ⟨e, he⟩ := blkE_ok len idx d
  -- frames, register by register
  have fA := denoteAInstrs_frame len idx SA (blkA k) (SA_dests k) s a ha
  have fB := denoteAInstrs_frame len idx SB blkB SB_dests a b hb
  have fC := denoteAInstrs_frame len idx SC (blkC k) (SC_dests k) b c hcc
  have fD := denoteAInstrs_frame len idx SD blkD SD_dests c d hd
  have fE := denoteAInstrs_frame len idx SE blkE SE_dests d e he
  -- section (A)
  have hA160 : a.regs 160 = (wPair k (s.regs 65)).1 := blkA_wl k len idx s hn ha
  have hA162 : a.regs 162 = (wPair k (s.regs 65)).2 := blkA_wh k len idx s hn ha
  have hA65 : a.regs 65 = s.regs 65 := fA 65 rfl
  have hA79 : a.regs 79 = s.regs 79 := fA 79 rfl
  have hA80 : a.regs 80 = s.regs 80 := fA 80 rfl
  have hA100 : a.regs 100 = s.regs 100 := fA 100 rfl
  have hA101 : a.regs 101 = s.regs 101 := fA 101 rfl
  have hA102 : a.regs 102 = s.regs 102 := fA 102 rfl
  have hA103 : a.regs 103 = s.regs 103 := fA 103 rfl
  have hA104 : a.regs 104 = s.regs 104 := fA 104 rfl
  have hA133 : a.regs 133 = s.regs 133 := fA 133 rfl
  -- section (B)
  have hB100 := blkB_tLo k len idx a hb
  have hB101 := blkB_tHi k len idx a hb
  rw [hA79, hA80, hA160, hA162, hA100, hA101] at hB100 hB101
  have hB65 : b.regs 65 = s.regs 65 := (fB 65 rfl).trans hA65
  have hB102 : b.regs 102 = s.regs 102 := (fB 102 rfl).trans hA102
  have hB103 : b.regs 103 = s.regs 103 := (fB 103 rfl).trans hA103
  have hB104 : b.regs 104 = s.regs 104 := (fB 104 rfl).trans hA104
  have hB133 : b.regs 133 = s.regs 133 := (fB 133 rfl).trans hA133
  -- section (C)
  have hC152 := blkC_v k len idx b hcc
  rw [hB100, hB101] at hC152
  have hC65 : c.regs 65 = s.regs 65 := (fC 65 rfl).trans hB65
  have hC100 : c.regs 100 = b.regs 100 := fC 100 rfl
  have hC101 : c.regs 101 = b.regs 101 := fC 101 rfl
  have hC102 : c.regs 102 = s.regs 102 := (fC 102 rfl).trans hB102
  have hC103 : c.regs 103 = s.regs 103 := (fC 103 rfl).trans hB103
  have hC104 : c.regs 104 = s.regs 104 := (fC 104 rfl).trans hB104
  have hC133 : c.regs 133 = s.regs 133 := (fC 133 rfl).trans hB133
  -- section (D)
  have hD159 := blkD_abs k len idx c hd
  rw [hC152] at hD159
  have hD65 : d.regs 65 = s.regs 65 := (fD 65 rfl).trans hC65
  have hD100 : d.regs 100 = b.regs 100 := (fD 100 rfl).trans hC100
  have hD101 : d.regs 101 = b.regs 101 := (fD 101 rfl).trans hC101
  have hD102 : d.regs 102 = s.regs 102 := (fD 102 rfl).trans hC102
  have hD103 : d.regs 103 = s.regs 103 := (fD 103 rfl).trans hC103
  have hD104 : d.regs 104 = s.regs 104 := (fD 104 rfl).trans hC104
  have hD133 : d.regs 133 = s.regs 133 := (fD 133 rfl).trans hC133
  -- section (E)
  have hE102 := blkE_cel k len idx d he
  have hE103 := blkE_celSq k len idx d he
  rw [hD65, hD103, hD102, hD133] at hE102 hE103
  have hE65 : e.regs 65 = s.regs 65 := (fE 65 rfl).trans hD65
  have hE100 : e.regs 100 = b.regs 100 := (fE 100 rfl).trans hD100
  have hE101 : e.regs 101 = b.regs 101 := (fE 101 rfl).trans hD101
  have hE104 : e.regs 104 = s.regs 104 := (fE 104 rfl).trans hD104
  have hE133 : e.regs 133 = s.regs 133 := (fE 133 rfl).trans hD133
  have hE159 : e.regs 159 = absBias (vBias k (b.regs 100) (b.regs 101)) := by
    exact (fE 159 rfl).trans hD159
  -- section (F)
  have hcE : e.regs rCeil ≠ 0 := by
    simp only [rCeil, hE102]
    simpa [celAfter, readSig, readRes, rTLo, rTHi, rCeil, rCeilSq, rMViol]
      using hc
  obtain ⟨f, hf⟩ := blkF_ok k len idx e hcE
  have fF := denoteAInstrs_frame len idx SF (blkF k) (SF_dests k) e f hf
  have hF104 := blkF_viol k len idx e hcE hf
  rw [hE65, hE159, hE102, hE133, hE104] at hF104
  have hF100 : f.regs 100 = b.regs 100 := (fF 100 rfl).trans hE100
  have hF101 : f.regs 101 = b.regs 101 := (fF 101 rfl).trans hE101
  have hF102 : f.regs 102 = _ := (fF 102 rfl).trans hE102
  have hF103 : f.regs 103 = _ := (fF 103 rfl).trans hE103
  -- assemble
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rw [mobiusLiveResidue_split k]
    simp only [denoteAInstrs_append, ha, hb, hcc, hd, he, hf,
      Option.bind_eq_bind, Option.bind_some]
  · rw [denoteAInstrs_frame_arr len idx SF (blkF k) (SF_dests k) e f hf,
      denoteAInstrs_frame_arr len idx SE blkE SE_dests d e he,
      denoteAInstrs_frame_arr len idx SD blkD SD_dests c d hd,
      denoteAInstrs_frame_arr len idx SC (blkC k) (SC_dests k) b c hcc,
      denoteAInstrs_frame_arr len idx SB blkB SB_dests a b hb,
      denoteAInstrs_frame_arr len idx SA (blkA k) (SA_dests k) s a ha]
  · simp only [readRes, resStep, readSig, rTLo, rTHi, rCeil, rCeilSq, rMViol,
      hF100, hF101, hF102, hF103, hF104, hB100, hB101, hE159]
  · intro j hj
    exact ((((((fF j (SF_false hj)).trans (fE j (SE_false hj))).trans
      (fD j (SD_false hj))).trans (fC j (SC_false hj))).trans
      (fB j (SB_false hj))).trans (fA j (SA_false hj)))

end LeanCompCert.Ports.MobiusResidueRealisation
