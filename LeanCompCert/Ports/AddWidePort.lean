import LeanCompCert.Verified.AddWide
import LeanCompCert.Verified.ArrayBridge

/-!
# The two-limb accumulator as a program of the proved fragment

`Verified/AddWide.lean` proves the arithmetic: a pair of `u64` limbs driven by
`addWide` / `subWide` is `mod 2¹²⁸` arithmetic, exactly, with the carry
recovered by a comparison.  This module is the other half — the same steps as
`Verified.Reflect.Instr`s, with a denotation theorem saying the register file
computes those functions, so the accumulator can be dropped into any
`Program` or `AProgram` loop body.

## Four instructions, branchless

```
  lo ← lo + a.lo        -- add
  c  ← lo < a.lo        -- lt      the carry, by proved comparison
  hi ← hi + a.hi        -- add
  hi ← hi + c           -- add
```

The carry test reads `a.lo`, which the first instruction does not touch, so no
copy and no temporary is needed; that is the whole reason the sequence is four
instructions and not six.  The one-limb specializations — `+ a` and `− a` for a
`u64` `a`, which is what the `ψ` residual actually does (`+ lnFix(p)` at a test
point, `− 2^S·gap` between two) — are three instructions each.

## The register discipline

`addWideBody` takes its five register numbers as parameters, with the
separation conditions collected in `WideRegs`.  They are exactly the conditions
under which each instruction still sees the operand the previous one left:
the carry test needs `a.lo` unclobbered, the final `add` needs `c`
unclobbered, and the accumulator's own two limbs must be distinct.  Nothing
else is required — in particular the addend registers may be recomputed every
iteration by the surrounding body, which is how the gating multiplies work.
-/

namespace LeanCompCert.Ports.AddWidePort

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.AddWide

/-- The register machine's modulus is the limb base. -/
theorem M_eq_B64 : M = B64 := by decide

/-! ## Register separation -/

/-- The separation the four-instruction sequence needs: the accumulator's two
limbs and the carry scratch are distinct, and neither addend register is one
of them. -/
structure WideRegs (rLo rHi rC rAlo rAhi : Nat) : Prop where
  loHi : rLo ≠ rHi
  loC : rLo ≠ rC
  hiC : rHi ≠ rC
  aloLo : rAlo ≠ rLo
  aloHi : rAlo ≠ rHi
  aloC : rAlo ≠ rC
  ahiLo : rAhi ≠ rLo
  ahiHi : rAhi ≠ rHi
  ahiC : rAhi ≠ rC

/-! ## Stepping lemmas -/

theorem set_self (s : RegState) (i v : Nat) : (s.set i v) i = v := by
  simp [RegState.set]

theorem set_ne (s : RegState) {i j : Nat} (v : Nat) (h : j ≠ i) :
    (s.set i v) j = s j := by
  simp [RegState.set, h]

/-- One arithmetic instruction, consumed off the front of a list. -/
theorem denote_cons (index dest : Nat) (op : Op) (l r : Operand)
    (s : RegState) (rest : List Instr) (v : Nat)
    (h : denoteOp op (denoteOperand index s l) (denoteOperand index s r) = some v) :
    denoteInstrs index s (Instr.binop dest op l r :: rest)
      = denoteInstrs index (s.set dest v) rest := by
  show (denoteInstr index s (Instr.binop dest op l r)).bind
      (fun s => denoteInstrs index s rest) = _
  show ((denoteOp op (denoteOperand index s l) (denoteOperand index s r)).bind
      (fun result => some (s.set dest result))).bind
        (fun s => denoteInstrs index s rest) = _
  rw [h]
  rfl

/-! ## The bodies -/

/-- **The two-limb accumulator step**, four instructions. -/
def addWideBody (rLo rHi rC rAlo rAhi : Nat) : List Instr :=
  [ .binop rLo .add (.reg rLo) (.reg rAlo)
  , .binop rC .lt (.reg rLo) (.reg rAlo)
  , .binop rHi .add (.reg rHi) (.reg rAhi)
  , .binop rHi .add (.reg rHi) (.reg rC) ]

/-- Adding a single `u64`, three instructions: the high addend is `0`, so the
`hi ← hi + a.hi` step disappears. -/
def addWideLoBody (rLo rHi rC rA : Nat) : List Instr :=
  [ .binop rLo .add (.reg rLo) (.reg rA)
  , .binop rC .lt (.reg rLo) (.reg rA)
  , .binop rHi .add (.reg rHi) (.reg rC) ]

/-- Subtracting a single `u64`, three instructions.  The borrow is taken
**before** the low limb is overwritten, which is the mirror image of the carry
being taken after. -/
def subWideLoBody (rLo rHi rC rA : Nat) : List Instr :=
  [ .binop rC .lt (.reg rLo) (.reg rA)
  , .binop rLo .sub (.reg rLo) (.reg rA)
  , .binop rHi .sub (.reg rHi) (.reg rC) ]

/-! ## Denotation -/

/-- **The four instructions compute `addWide`.**  Stated in the form a loop
body consumes: the two accumulator limbs afterwards are the limbs of
`addWide`, and every register other than the accumulator and its carry
scratch is untouched. -/
theorem addWideBody_denote (rLo rHi rC rAlo rAhi : Nat)
    (hr : WideRegs rLo rHi rC rAlo rAhi) (index : Nat) (s : RegState) :
    ∃ s' : RegState,
      denoteInstrs index s (addWideBody rLo rHi rC rAlo rAhi) = some s'
      ∧ s' rLo = (addWide (s rLo, s rHi) (s rAlo, s rAhi)).1
      ∧ s' rHi = (addWide (s rLo, s rHi) (s rAlo, s rAhi)).2
      ∧ ∀ j, j ≠ rLo → j ≠ rHi → j ≠ rC → s' j = s j := by
  obtain ⟨hloHi, hloC, hhiC, haloLo, haloHi, haloC, hahiLo, hahiHi, hahiC⟩ := hr
  simp only [addWideBody]
  -- 1. `lo ← lo + a.lo`
  rw [denote_cons index rLo .add (.reg rLo) (.reg rAlo) s _
      ((s rLo + s rAlo) % M) rfl]
  -- 2. `c ← lo < a.lo`
  rw [denote_cons index rC .lt (.reg rLo) (.reg rAlo) _ _
      (if (s rLo + s rAlo) % M < s rAlo then 1 else 0) (by
        simp only [denoteOp, denoteOperand]
        simp only [show ((s.set rLo ((s rLo + s rAlo) % M)) rLo) = (s rLo + s rAlo) % M from
              set_self _ _ _,
          show ((s.set rLo ((s rLo + s rAlo) % M)) rAlo) = s rAlo from
              set_ne _ _ haloLo])]
  -- 3. `hi ← hi + a.hi`
  rw [denote_cons index rHi .add (.reg rHi) (.reg rAhi) _ _
      ((s rHi + s rAhi) % M) (by
        simp only [denoteOp, denoteOperand]
        simp only [show (((s.set rLo ((s rLo + s rAlo) % M)).set rC
                (if (s rLo + s rAlo) % M < s rAlo then 1 else 0)) rHi) = s rHi from by
              rw [set_ne _ _ hhiC, set_ne _ _ (Ne.symm hloHi)],
          show (((s.set rLo ((s rLo + s rAlo) % M)).set rC
                (if (s rLo + s rAlo) % M < s rAlo then 1 else 0)) rAhi) = s rAhi from by
              rw [set_ne _ _ hahiC, set_ne _ _ hahiLo]])]
  -- 4. `hi ← hi + c`
  rw [denote_cons index rHi .add (.reg rHi) (.reg rC) _ _
      (((s rHi + s rAhi) % M + (if (s rLo + s rAlo) % M < s rAlo then 1 else 0)) % M) (by
        simp only [denoteOp, denoteOperand]
        simp only [show ((((s.set rLo ((s rLo + s rAlo) % M)).set rC
                (if (s rLo + s rAlo) % M < s rAlo then 1 else 0)).set rHi
                  ((s rHi + s rAhi) % M)) rHi) = (s rHi + s rAhi) % M from
              set_self _ _ _,
          show ((((s.set rLo ((s rLo + s rAlo) % M)).set rC
                (if (s rLo + s rAlo) % M < s rAlo then 1 else 0)).set rHi
                  ((s rHi + s rAhi) % M)) rC)
              = (if (s rLo + s rAlo) % M < s rAlo then 1 else 0) from by
              rw [set_ne _ _ (Ne.symm hhiC), set_self]])]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [set_ne _ _ hloHi, set_ne _ _ hloHi, set_ne _ _ hloC, set_self]
    simp only [addWide, M_eq_B64]
  · rw [set_self]
    simp only [addWide, M_eq_B64]
  · intro j hjLo hjHi hjC
    rw [set_ne _ _ hjHi, set_ne _ _ hjHi, set_ne _ _ hjC, set_ne _ _ hjLo]

/-- **The three-instruction one-word add computes `addWideLo`.** -/
theorem addWideLoBody_denote (rLo rHi rC rA : Nat)
    (hloHi : rLo ≠ rHi) (hloC : rLo ≠ rC) (hhiC : rHi ≠ rC)
    (haLo : rA ≠ rLo) (haHi : rA ≠ rHi) (haC : rA ≠ rC)
    (index : Nat) (s : RegState) (hhi : s rHi < M) :
    ∃ s' : RegState,
      denoteInstrs index s (addWideLoBody rLo rHi rC rA) = some s'
      ∧ s' rLo = (addWideLo (s rLo, s rHi) (s rA)).1
      ∧ s' rHi = (addWideLo (s rLo, s rHi) (s rA)).2
      ∧ ∀ j, j ≠ rLo → j ≠ rHi → j ≠ rC → s' j = s j := by
  simp only [addWideLoBody]
  rw [denote_cons index rLo .add (.reg rLo) (.reg rA) s _
      ((s rLo + s rA) % M) rfl]
  rw [denote_cons index rC .lt (.reg rLo) (.reg rA) _ _
      (if (s rLo + s rA) % M < s rA then 1 else 0) (by
        simp only [denoteOp, denoteOperand]
        simp only [show ((s.set rLo ((s rLo + s rA) % M)) rLo) = (s rLo + s rA) % M from
              set_self _ _ _,
          show ((s.set rLo ((s rLo + s rA) % M)) rA) = s rA from
              set_ne _ _ haLo])]
  rw [denote_cons index rHi .add (.reg rHi) (.reg rC) _ _
      ((s rHi + (if (s rLo + s rA) % M < s rA then 1 else 0)) % M) (by
        simp only [denoteOp, denoteOperand]
        simp only [show (((s.set rLo ((s rLo + s rA) % M)).set rC
                (if (s rLo + s rA) % M < s rA then 1 else 0)) rHi) = s rHi from by
              rw [set_ne _ _ hhiC, set_ne _ _ (Ne.symm hloHi)],
          show (((s.set rLo ((s rLo + s rA) % M)).set rC
                (if (s rLo + s rA) % M < s rA then 1 else 0)) rC)
              = (if (s rLo + s rA) % M < s rA then 1 else 0) from set_self _ _ _])]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [set_ne _ _ hloHi, set_ne _ _ hloC, set_self]
    simp only [addWideLo, addWide, M_eq_B64]
  · rw [set_self]
    -- the `hi + a.hi` step of `addWide` is the identity here, so one `add` suffices
    have h0 : (s rHi + 0) % M = s rHi := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hhi]
    simp only [addWideLo, addWide, M_eq_B64]
    rw [show ((s rHi + 0) % B64) = s rHi from by rw [← M_eq_B64]; exact h0]
  · intro j hjLo hjHi hjC
    rw [set_ne _ _ hjHi, set_ne _ _ hjC, set_ne _ _ hjLo]

/-- **The three-instruction one-word subtract computes `subWideLo`.** -/
theorem subWideLoBody_denote (rLo rHi rC rA : Nat)
    (hloHi : rLo ≠ rHi) (hloC : rLo ≠ rC) (hhiC : rHi ≠ rC)
    (haLo : rA ≠ rLo) (haHi : rA ≠ rHi) (haC : rA ≠ rC)
    (index : Nat) (s : RegState) (hhi : s rHi < M) :
    ∃ s' : RegState,
      denoteInstrs index s (subWideLoBody rLo rHi rC rA) = some s'
      ∧ s' rLo = (subWideLo (s rLo, s rHi) (s rA)).1
      ∧ s' rHi = (subWideLo (s rLo, s rHi) (s rA)).2
      ∧ ∀ j, j ≠ rLo → j ≠ rHi → j ≠ rC → s' j = s j := by
  simp only [subWideLoBody]
  rw [denote_cons index rC .lt (.reg rLo) (.reg rA) s _
      (if s rLo < s rA then 1 else 0) rfl]
  rw [denote_cons index rLo .sub (.reg rLo) (.reg rA) _ _
      ((s rLo + (M - s rA)) % M) (by
        simp only [denoteOp, denoteOperand]
        simp only [show ((s.set rC (if s rLo < s rA then 1 else 0)) rLo) = s rLo from
              set_ne _ _ hloC,
          show ((s.set rC (if s rLo < s rA then 1 else 0)) rA) = s rA from
              set_ne _ _ haC])]
  rw [denote_cons index rHi .sub (.reg rHi) (.reg rC) _ _
      ((s rHi + (M - (if s rLo < s rA then 1 else 0))) % M) (by
        simp only [denoteOp, denoteOperand]
        simp only [show (((s.set rC (if s rLo < s rA then 1 else 0)).set rLo
                ((s rLo + (M - s rA)) % M)) rHi) = s rHi from by
              rw [set_ne _ _ (Ne.symm hloHi), set_ne _ _ hhiC],
          show (((s.set rC (if s rLo < s rA then 1 else 0)).set rLo
                ((s rLo + (M - s rA)) % M)) rC)
              = (if s rLo < s rA then 1 else 0) from by
              rw [set_ne _ _ (Ne.symm hloC), set_self]])]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [set_ne _ _ hloHi, set_self]
    simp only [subWideLo, subWide, M_eq_B64]
  · rw [set_self]
    have h0 : (s rHi + (M - 0)) % M = s rHi := by
      rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hhi]
    simp only [subWideLo, subWide, M_eq_B64]
    rw [show ((s rHi + (B64 - 0)) % B64) = s rHi from by rw [← M_eq_B64]; exact h0]
  · intro j hjLo hjHi hjC
    rw [set_ne _ _ hjHi, set_ne _ _ hjLo, set_ne _ _ hjC]

/-! ## Well-formedness, and the `AProgram` form

`AInstr.scalar` embeds a fragment instruction verbatim, so the same four
instructions are usable in an array-machine body with no wrapper beyond the
constructor.
-/

def addWideABody (rLo rHi rC rAlo rAhi : Nat) : List Verified.ArrayState.AInstr :=
  (addWideBody rLo rHi rC rAlo rAhi).map Verified.ArrayState.AInstr.scalar

def addWideLoABody (rLo rHi rC rA : Nat) : List Verified.ArrayState.AInstr :=
  (addWideLoBody rLo rHi rC rA).map Verified.ArrayState.AInstr.scalar

def subWideLoABody (rLo rHi rC rA : Nat) : List Verified.ArrayState.AInstr :=
  (subWideLoBody rLo rHi rC rA).map Verified.ArrayState.AInstr.scalar

theorem addWideBody_wf (regCount rLo rHi rC rAlo rAhi : Nat)
    (h1 : rLo < regCount) (h2 : rHi < regCount) (h3 : rC < regCount)
    (h4 : rAlo < regCount) (h5 : rAhi < regCount) :
    ∀ i ∈ addWideBody rLo rHi rC rAlo rAhi, i.WF regCount := by
  intro i hi
  simp only [addWideBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    exact ⟨by assumption, by assumption, by assumption⟩

/-! ## A standalone program, and kernel checks

`accProgram` is the accumulator run as a loop: `loopCount` copies of the
one-word add, from a carry-in.  It is the smallest program that exercises the
carry, and `Program.evalCC_compile` applies to it, so the emitted C provably
computes it.
-/

def rLo : Nat := 0
def rHi : Nat := 1
def rC : Nat := 2
def rA : Nat := 3
def regCount : Nat := 4

/-- Accumulate the literal `a` `count` times into a two-limb accumulator seeded
at `(seed, 0)`; the output register is the **high** limb, which is `0` until
the carry fires. -/
def accProgram (seed a count out : Nat) : Program := {
  regCount := regCount
  loopCount := count
  init := [.mov rLo (.lit seed), .mov rA (.lit a)]
  body := addWideLoBody rLo rHi rC rA
  epilogue := []
  output := out
}

theorem accProgram_wf (seed a count out : Nat) (hout : out < regCount) :
    (accProgram seed a count out).WF := by
  refine ⟨hout, ?_, ?_, ?_⟩
  · intro i hi
    simp only [accProgram, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨show rLo < regCount by decide, trivial⟩
    · exact ⟨show rA < regCount by decide, trivial⟩
  · intro i hi
    simp only [accProgram, addWideLoBody, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨show rLo < regCount by decide,
        show (Operand.reg rLo).WF regCount by decide,
        show (Operand.reg rA).WF regCount by decide⟩
    · exact ⟨show rC < regCount by decide,
        show (Operand.reg rLo).WF regCount by decide,
        show (Operand.reg rA).WF regCount by decide⟩
    · exact ⟨show rHi < regCount by decide,
        show (Operand.reg rHi).WF regCount by decide,
        show (Operand.reg rC).WF regCount by decide⟩
  · intro i hi; cases hi

/-- **The bridge.**  The compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the accumulator limb in the
output local. -/
theorem accProgram_compiled (seed a count out : Nat) (hout : out < regCount) :
    ((evalCCSequence Verified.emptyCCEnv (accProgram seed a count out).compile).bind
        (fun env => env ⟨(accProgram seed a count out).output + 1⟩)) =
      (accProgram seed a count out).denote.map (fun n => (n : Int)) :=
  Program.evalCC_compile _ (accProgram_wf seed a count out hout)

namespace Check

set_option maxRecDepth 20000000

/-- Three adds of `2⁶³` from a zero seed: the low limb wraps to `2⁶³` and the
high limb is `1`. -/
example : (accProgram 0 9223372036854775808 3 rLo).denote
    = some 9223372036854775808 := by decide

example : (accProgram 0 9223372036854775808 3 rHi).denote = some 1 := by decide

/-- …and it is `addWideLo` iterated, not merely a number that looks right. -/
example : (accProgram 0 9223372036854775808 3 rHi).denote
    = some (sumWide (List.replicate 3 9223372036854775808)).2 := by decide

example : (accProgram 0 9223372036854775808 3 rLo).denote
    = some (sumWide (List.replicate 3 9223372036854775808)).1 := by decide

/-- Forty accumulations of a production-scale `S = 48` logarithm term stay in
the low limb; the point of the check is that the *program* and the *function*
agree, at a value that is not a power of two. -/
example : (accProgram 0 8415356672702845 40 rLo).denote
    = some (sumWide (List.replicate 40 8415356672702845)).1 := by decide

end Check

end LeanCompCert.Ports.AddWidePort
